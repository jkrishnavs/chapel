/**************************************************
  Authors: Jyothi Krishna V S (jkrishnavs@gmail.com)
           Vassily Litvinov (vass@cray.com)
  The file explains a pass for Chapel compilers
 to identify use-after-free variables in Chapel.
  Research papers and presentations related to this file:
 
 1. Identifying Use-After-Free Variables in Fire-and-Forget Tasks 
    in CHIUW 17 
   slides[http://chapel.cray.com/CHIUW/2017/krishna-slides.pdf]


The overall flow of the algorithm is as follows.
a. Generation of CCFG: 
A CCFG is similar to our normal CFG,  with an additional type of edge
which represents the creation of a parallel begin task. The edge also
captures a partial happens-before relationship between the begin tasks
and the parent task. i.e. all Nodes (and contained operations) in the 
parent task (say P) from root to the node which is the source of 
begin edge (say S) happens before the first node of the begin task, which
is the destination of the begin edge (say D).

Graphically consider the following simple CCFG. Each node in the
data structure is represented using SyncGraphNode data structure. 

            R
            |
            A
            |
            S
            |\
            B D

Nodes R, A, S all happens before Node D. Whereas we cannot defintly say
anything about nodes B and D.
        

b. Expand Nested Functions:
Expanding the nested functions are improtant as root task variables (outer variables)
can be accessed by the begin tasks without any parameter passing by calling
one of the nested tasks (nested inside the root task, but not the begin task).

b. CCFG graph traversal. PPS generations:
PPS are superset of potential Partial program states 
(execution order of Nodes, represnted using VisitedMap data structure) 
that are possible at runtime. 
If any of the PPS points to a potential Use-After-Free variables
we report an error.


c. Reporting Unsafe uses of outer variables.
Once the unsafe variables are identified these are reported to the programmers.

***************************************************/

#include "passes.h"
#include "astutil.h"
#include "driver.h"
#include "expr.h"
#include "stmt.h"
#include "stlUtil.h"
#include "primitive.h"
#include "vec.h"
#include "view.h"
#include <set>
#include <algorithm>


#define CHPL_DOTGRAPH

enum GraphNodeStatus {
  NODE_UNKNOWN = 0, //NODE STATUS UNKNOWN
  NODE_SINGLE_WAIT_FULL,
  NODE_SYNC_SIGNAL_FULL,
  NODE_SYNC_SIGNAL_EMPTY,
  NODE_BLOCK_BEGIN, //A NEW BEGIN FUNCTION START HERE
  NODE_BLOCK_NESTED_FUNCTION, // A NEW FUNCTION NODE STARTS HERE
  NODE_START_LOOP,
  NODE_START_DOWHILE,
  NODE_START_WHILE,
  NODE_LOOP_END,
  NODE_START_IFELSE,
  NODE_END_IFELSE,
  NODE_NESTED_FUNCTION_CALL,
  CREATE_SYNC_NODE,
  CREATE_BRANCH_NODE,
  CREATE_FUNCTION_NODE,
  CREATE_BEGIN_NODE,
  CREATE_LOOP_NODE
};

enum SymbolState {
  SYMBOL_STATE_EMPTY =0,
  SYMBOL_STATE_FULL
};




struct SyncGraphNode;
struct UseInfo;
struct VisitedMap;

typedef BlockStmt Scope;
typedef Vec<Scope*> ScopeVec;
typedef std::vector<UseInfo*> UseInfoVector;
typedef std::set<UseInfo*> UseInfoSet;
typedef std::vector<SyncGraphNode*> SyncGraphVector;
typedef std::vector<SyncGraphNode*>::iterator SGI; 
typedef Map<FnSymbol*, SyncGraphNode*> FnSyncGraphMap;
typedef Vec<FnSymbol*> FnSymbolsVec;
typedef std::set<Symbol*> SymbolSet;
typedef std::set<SyncGraphNode*> SyncGraphSet;
typedef std::map<Symbol*, SymbolState> SymbolStateMap;



/****
     We can say The SyncGraph nodes represents
     a striped CCFG(Concurrent Control Flow Graph)
     Which stores data of sync Points and
     use of outer variables.
**/

//typedef Vec<UseInfo*> UseInfoVec;

static int counter = 0;



/*********************************
Sync Graph Node 
An object represents a node in CCFG graph
 ********************************/
struct SyncGraphNode {
  int __ID;
  FnSymbol* fnSymbol;
  CallExpr* intFuncCall; // Nested Function Call

  ScopeVec syncedScopes;    // These are the already defined sync points
                            // created due to sync statments, Cobegin, Coforall
                            // and Forall statments.


  Symbol* syncVar; 
  SyncGraphNode* parent;
  SyncGraphNode* child; // same function next BB
  
  CallExpr* syncExpr;
  GraphNodeStatus syncType;
  bool expandedFn; // if the functioncall in intFuncCall is already expanded


  UseInfoVector extVarInfoVec;
  SyncGraphNode(SyncGraphNode* i, FnSymbol *f, bool copyNestedFunctionCall = false) {
    __ID = counter ++;
    fnSymbol = f;
    extVarInfoVec.clear();
    syncedScopes.append(i->syncedScopes);
    syncType = i->syncType;
    syncVar = i->syncVar;
    if(copyNestedFunctionCall)
      intFuncCall = i->intFuncCall;
    expandedFn = i->expandedFn;
    child = NULL;
    parent = NULL;
  }

  SyncGraphNode(FnSymbol *f) {
    __ID = counter ++;
    fnSymbol = f;
    child = NULL;
    parent = NULL;
    syncType = NODE_UNKNOWN;
    intFuncCall = NULL;
    expandedFn = false;
    syncVar = NULL;
    extVarInfoVec.clear();
  }
  //  ~SyncGraphNode() {}
  virtual ~SyncGraphNode() {}
};


struct SyncGraphBranchNode: SyncGraphNode {
  SyncGraphNode* cChild; // conditionalNode child
  SyncGraphNode* joinNode;
  SyncGraphBranchNode(FnSymbol *f):SyncGraphNode(f){
    cChild = NULL;
    joinNode = NULL;
    syncType = NODE_START_IFELSE;
  }
  SyncGraphBranchNode(SyncGraphNode *i,FnSymbol* f, bool copy):SyncGraphNode(i,f, copy) {
    cChild = NULL;
    joinNode = NULL;
  }

  ~SyncGraphBranchNode(){}

};

/**
   IMPORTANT: The SyncGraphFunctionNode is NOT THE FIRST NODE OF FUNCTION.
   It is node of the PARENT FUNCTION to which the new function Node is attached.
 **/
struct SyncGraphFunctionNode: SyncGraphNode {
  SyncGraphNode* fChild; // nested functions including Begin
  
  SyncGraphFunctionNode(FnSymbol *f):SyncGraphNode(f){
    fChild = NULL;
  }
  SyncGraphFunctionNode(SyncGraphNode *i,FnSymbol* f, bool copy):SyncGraphNode(i,f, copy) {
    fChild = NULL;
  }
  ~SyncGraphFunctionNode(){}
};

  


// This bound start and end of loop.
/*
  We divide the Loops into Two Types :
  headed loops : For and while where the conditional 
  check is at the start
  tailed loop : 
 */
struct SyncGraphLoopNode: SyncGraphNode {
  /* 
   * The second parent. Since we create a  join node for each 
   * branch we will have only two parents at a time
   */
  SyncGraphNode* lParent;
  SymExpr *cond;
  SymExpr *start;
  bool headedLoop;
  SyncGraphNode* lChild; // The loop Child.

  SyncGraphNode* getlParent() {
    return lParent;
  }
  void setlParent(SyncGraphNode* p) {
    lParent = p;
  }

  SyncGraphNode* getlChild() {
    return lChild;
  }
  void setlChild(SyncGraphNode* c) {
    lChild = c;
  }

  
  void setStart(SymExpr* s) {
    start = s;
  }
  SymExpr* getStart() {
    return start;
  }

  void setCond(SymExpr* c) {
    cond = c;
  }
  SymExpr* getCond() {
    return cond;
  }

  
  SyncGraphLoopNode(FnSymbol *f):SyncGraphNode(f){
    lParent = NULL;
    lChild = NULL;
    start = NULL;
    cond = NULL;
    headedLoop = false;
  }
  SyncGraphLoopNode(SyncGraphNode *i, FnSymbol*f,   bool copy):SyncGraphNode(i,f, copy) {
    lParent = NULL;
    lChild = NULL;
    start = NULL;
    cond = NULL;
    headedLoop = false;
  }
  void setHeadedLoop(bool h) {
    headedLoop = h;
  }
  bool isHeadedLoop() {
    return headedLoop;
  }  
  ~SyncGraphLoopNode(){}
}; 


static SyncGraphBranchNode* getBranchNode(SyncGraphNode* n) {
  return dynamic_cast<SyncGraphBranchNode*> (n);
}  

static SyncGraphFunctionNode* getFunctionNode(SyncGraphNode* n) {
    return dynamic_cast<SyncGraphFunctionNode*> (n);
}  

static SyncGraphLoopNode* getLoopNode(SyncGraphNode* n) {
    return dynamic_cast<SyncGraphLoopNode*> (n);
}  



struct UseInfo {
  SymExpr* usePoint;
  SyncGraphNode* useNode;
  FnSymbol* fnSymbol;
  Symbol* symbol;
  bool checked;

  UseInfo(SyncGraphNode *node, FnSymbol* fn, SymExpr* expr, Symbol* s) {
    usePoint = expr;
    fnSymbol = fn;
    useNode = node;
    symbol = s;
    checked = false;
  }

  void setChecked() {
    checked = true;
  }

  bool  isChecked() {
    return checked;
  }

};



static SyncGraphVector gAnalysisRoots; // We will be creating multiple root for
                                   //  analyzing recursion and loops more
                                   // efficiently
static SymbolSet gSyncVars;
static void updateSafeInfos(VisitedMap* prev, SyncGraphVector& visitedNodes, UseInfoSet& safeInfoset, UseInfoSet& visitedtUseInfo);
static UseInfoVector gUseInfos;
static FnSymbol* gFnSymbolRoot;
static FnSyncGraphMap gFuncGraphMap; // start point of each function in Sync Graph
static bool gAllCallsSynced;
static std::set<Symbol*> gSingleSet;



//* The parallel program state PPS */
struct VisitedMap {

  SyncGraphSet destPoints; // Active Sync Node set
  SymbolStateMap symbolMap;
  SyncGraphSet visited; // All Visited  Nodes

  UseInfoSet visitedInfoSet; // Visited Info
  UseInfoSet safeInfoSet; // Safe Set Info.
  SyncGraphSet vSingles;  
  
  ~VisitedMap() {}

  VisitedMap(VisitedMap* prev,  SyncGraphSet& newDestPoints,  UseInfoSet& visitedInfos, SyncGraphVector& visitedNodes, SymbolState state) {
    destPoints = newDestPoints;
    visited.insert(visitedNodes.begin(),visitedNodes.end());
    
    if(prev != NULL && visitedNodes.size() > 0) {
      symbolMap = prev->symbolMap;
      Symbol* sync = visitedNodes.front()->syncVar;
      SymbolStateMap::iterator it = symbolMap.find(sync);
      INT_ASSERT(it != symbolMap.end());
      it->second = state;

      visited.insert(prev->visited.begin(), prev->visited.end());
      
      if(prev->safeInfoSet.size() > 0)
	safeInfoSet = prev->safeInfoSet;

      updateSafeInfos(prev, visitedNodes, safeInfoSet, visitedInfoSet);

      
      if(prev->vSingles.size() > 0)
	vSingles = prev->vSingles;
    } else {
      for_set(Symbol, curSymbol, gSyncVars) {
	symbolMap[curSymbol]=  SYMBOL_STATE_EMPTY;
      }
    }    

    if(visitedNodes.size() > 0) {
      if((visitedNodes.front())->syncType == NODE_SYNC_SIGNAL_FULL && gSingleSet.find((visitedNodes.front())->syncVar) != gSingleSet.end()) {
	vSingles.insert(visitedNodes.front());
      }
      
      if(visitedInfos.size() > 0)
	visitedInfoSet.insert(visitedInfos.begin(),visitedInfos.end());
    }
  }

  void appendData(UseInfoSet& visitedInfos, SyncGraphVector& visitedNodes) {
    visitedInfoSet.insert(visitedInfos.begin(), visitedInfos.end());
    visited.insert(visitedNodes.begin(), visitedNodes.end());
  }
    
};

struct std::vector<VisitedMap*> gListVisited;

/******************************
  Pre check Optimization
******************************/
static bool containsBeginFunction(FnSymbol* fn);


/*****************************
  Graph Generation Functions
*****************************/
static SyncGraphNode* handleBlockStmt(BlockStmt* stmt, SyncGraphNode *cur);
static SyncGraphNode* handleCondStmt(CondStmt* cond,SyncGraphNode* cur);
static SyncGraphNode* handleDefExpr(DefExpr* def, SyncGraphNode *cur);
static SyncGraphNode* handleExpr(Expr* expr, SyncGraphNode *cur);
static SyncGraphNode* handleFunction(FnSymbol* fn, SyncGraphNode *cur);
static SyncGraphNode* handleBegin(FnSymbol* fn, SyncGraphNode* cur);
static SyncGraphNode* handleCallExpr(CallExpr* fn, SyncGraphNode* cur);
static SyncGraphNode* handleSyncStatement(BlockStmt* block, SyncGraphNode* cur);
static SyncGraphNode* handleLoopStmt(BlockStmt* block,SyncGraphNode* cur);
static SyncGraphNode* handleBranching(SyncGraphBranchNode* start, SyncGraphNode* end,  SyncGraphNode* ifNode, SyncGraphNode* elseNode);


/******************************
Adding Outer variable details, Sync variable 
 details to Sync Graph Nodes
 *****************************/
static BlockStmt* getSyncBlockStmt(BlockStmt* def, SyncGraphNode *cur);
static void addExternVarDetails(FnSymbol* fn, Symbol* v, SymExpr* use, SyncGraphNode* node) ;
static Symbol* findBaseSymbol(Symbol* curSymbol);
static bool isOuterVar(Symbol* sym, FnSymbol* fn);
static void checkSyncedCalls(FnSymbol* fn);
static SyncGraphNode* addSyncExprs(Expr *expr, SyncGraphNode *cur);
static SyncGraphNode* addSymbolsToGraph(Expr* expr, SyncGraphNode *cur);
static ArgSymbol*  getTheArgSymbol(Symbol * sym, FnSymbol* parent);
static Scope* getOriginalScope(Symbol* sym);
static bool  ASTContainsBeginFunction(BaseAST* ast);


/********************************
Functions to skip synced scopes
*********************************/
static bool isInsideSyncStmt(Expr* expr);
static bool shouldSync(Scope* scope, SyncGraphNode* cur);
static int compareScopes(Scope* a, Scope * b);
static bool  refersOuterSymbols(Expr* expr, SyncGraphNode * cur);




/******************************
  Graph building Functions
******************************/
static SyncGraphNode* addChildNode(SyncGraphNode *cur, FnSymbol* fn, GraphNodeStatus status);
static SyncGraphNode* addElseChildNode(SyncGraphBranchNode *cur, FnSymbol *fn);


/*******************************
  Nested Function Expansion
*******************************/
static void copyUseInfoVec(SyncGraphNode *copy, SyncGraphNode* orig, FnSymbol* parent);
static SyncGraphNode* copyCFG(SyncGraphNode* parent, SyncGraphNode* branch, SyncGraphNode *endPoint);
static void expandAllNestedFunctions(SyncGraphNode* root, FnSymbolsVec &callStack, SyncGraphNode* stopPoint= NULL);
static bool refersToInternalFunctionCalls(BlockStmt* block);

/******************************
  Graph Clean Up Functions
******************************/
static void deleteSyncGraphNode(SyncGraphNode *node);
static void cleanUpSyncGraph(SyncGraphNode *root);
static void  exit_pass();

/*********************************
  Graph Traversal Functions Generation of PPS 
**********************************/
static void checkOrphanStackVar(SyncGraphNode *root);
//static void updateUnsafeUseInfos(VisitedMap* curVisited, SymbolStateMap& stateMap, SyncGraphSet& partialSet, UseInfoVec& useInfos);
static bool threadedMahjong(void);
static bool canVisitNext(SymbolStateMap& stateMap, SyncGraphNode* sourceSyncPoint);
static bool handleSingleSyncing(VisitedMap * curVisited);
static void collectAllAvailableSyncPoints(VisitedMap* curVisited, SyncGraphVector& newlyVisited,
					  SyncGraphVector& partialVisited, SyncGraphSet& partialSet, SymbolState newState);
static void collectUseInfos(VisitedMap* curVisited, SyncGraphVector& newlyVisited, UseInfoSet& useInfos);
static SyncGraphNode* getLastNode(SyncGraphNode* start);
static void checkNextSyncNode();
static VisitedMap* alreadyVisited(SyncGraphSet& dest, SymbolStateMap& map);

/*************************************
Helper functions for generating PPS and reporting error.
 ************************************/
static bool hasNextSyncPoint(SyncGraphNode * curNode);
static bool isASyncPoint(SyncGraphNode* cur);
static bool isASyncPointSkippingSingles(SyncGraphNode* cur, SyncGraphSet& filledSinglePoints);
static bool isInsideAllSyncedScopes(FnSymbol* calleeFn, SyncGraphNode* cur);
static bool isPartofBeginBranch(SyncGraphNode* curNode);

static bool verifyLoopEquivalenceForScope(SyncGraphLoopNode head1, SyncGraphLoopNode head2, Scope parentScope);


/**************************************
  Reporting Errors
**************************************/
static void provideWarning(UseInfo* var);



#ifdef CHPL_DOTGRAPH
static void dotGraph(SyncGraphNode* root);
static void digraph( SyncGraphNode* cur, std::string level);
#endif
/************** HEADER ENDS *******************/

/*************** DEBUG HELPER
The below code is useful for generating 
DOT graph representations of 
the CCFG. These are going to be useful 
for debugging. To enable this we need to 
uncomment #define CHPL_DOTGRAPH.
*****************************/
#ifdef CHPL_DOTGRAPH
#include <fstream>
#include <string>
#include <sstream>


/*********** HEADER *********************/

#ifdef CHPL_DOTGRAPH
std::string GraphNodeStatusStrings[] = {
  "UNKNOWN", //NODE STATUS UNKNOWN
  "SINGLE_WAIT_FULL",
  "SYNC_SIGNAL_FULL",
  "SYNC_SIGNAL_EMPTY",
  "BLOCK_BEGIN", //A NEW BEGIN FUNCTION START HERE
  "BLOCK_NESTED_FUNCTION", // A NEW FUNCTION NODE STARTS HERE
  "START_LOOP",
  "START_DOWHILE",
  "START_WHILE",
  "LOOP_END",
  "START_IFELSE",
  "END_IFELSE",
  "NESTED_FUNCTION_CALL"
};
#endif



#ifdef CHPL_DOTGRAPH


namespace stringpatch
{
  template < typename T > std::string to_string( const T& n )
  {
    std::ostringstream stm ;
    stm << n ;
    return stm.str() ;
  }
}
#endif


//static int dotGraphCounter = 0;
static std::ofstream outfile;
//static void digraph(std::ofstream& outfile, SyncGraphNode* cur, std::string level) {


static void digraph(SyncGraphNode* cur, std::string level) {
  std::string curSyncVar;
  if(cur->syncVar != NULL) {
   curSyncVar =  "node" + stringpatch::to_string(cur->__ID) +
      std::string(cur->syncVar->name, sizeof(cur->syncVar->name) -1);
  } else {
    curSyncVar =  "node" + stringpatch::to_string(cur->__ID);
  }
  // + "_" + GraphNodeStatusStrings[cur->syncType];
  if(cur->child != NULL) {
    std::string nextSyncVar;
    if(cur->child->syncVar != NULL) {
      nextSyncVar = "node" + stringpatch::to_string(cur->child->__ID) +
	std::string(cur->child->syncVar->name, sizeof(cur->child->syncVar->name) -1);
    } else {
      nextSyncVar = "node" + stringpatch::to_string(cur->child->__ID);
    }
    // outfile << curSyncVar << " -> " << nextSyncVar << "[label=ch]\n";
    std::cout << curSyncVar << " -> " << nextSyncVar << "[label=ch] \n";
    //    digraph(outfile, cur->child, level+ "O");
    digraph(cur->child, level+ "O");
  }

  if(SyncGraphBranchNode* ccur = dynamic_cast<SyncGraphBranchNode*>(cur)) {
    if(ccur->cChild != NULL) {
      std::string nextSyncVar;
      if(ccur->cChild->syncVar != NULL) {
	nextSyncVar = "node" + stringpatch::to_string(ccur->cChild->__ID) +
	  std::string(ccur->cChild->syncVar->name, sizeof(ccur->cChild->syncVar->name) - 1);
      } else {
	nextSyncVar = "node" + stringpatch::to_string(ccur->cChild->__ID);
      }
      // outfile << curSyncVar << " -> " << nextSyncVar << "[label=cc]\n";
      std::cout << curSyncVar << " -> " << nextSyncVar << "[label=cc]\n";
      //digraph(outfile, cur->cChild, level+ "C");
      digraph(ccur->cChild, level+ "C");
    }
  }

  // TODO ADD FOR LOOP NOde
  
  if(SyncGraphFunctionNode* fcur = dynamic_cast<SyncGraphFunctionNode*>(cur)){
    if(fcur->fChild != NULL) {
      std::string nextSyncVar;
      if(fcur->fChild->syncVar != NULL) {
	nextSyncVar =  "node" + stringpatch::to_string(fcur->fChild->__ID) +
	  std::string(fcur->fChild->syncVar->name, sizeof(fcur->fChild->syncVar->name) - 1);
      }  else {
	nextSyncVar =  "node" + stringpatch::to_string(fcur->fChild->__ID);
      }
      // outfile << curSyncVar << " -> " << nextSyncVar << "[label=fc]\n";
      if(fcur->syncType == NODE_BLOCK_BEGIN)
	std::cout << curSyncVar << " -> " << nextSyncVar << "[label=bfc]\n";
      else
	std::cout << curSyncVar << " -> " << nextSyncVar << "[label=fc]\n";
      //digraph(outfile, cur->fChild, level+ "F");
      digraph(fcur->fChild, level+ "F");
    }
  }
}

static void dotGraph(SyncGraphNode* root) {
  std::ofstream outfile;
  //  outfile.open("dot"+ itoa(dotGraphCounter++)  +".dat");
  outfile.open("dot.dat");
  // outfile<<"digraph G { \n";
  std::cout<<"digraph G { \n";
  //  std::string outputstr;
  //digraph(outfile, root, "r");
  digraph(root, "r");
  //  outfile<< "}\n";
  std::cout<< "}\n";

}
#endif




// Check if The PPS is already present in the queue. If already present we just megre 
 // the new PPS to this.
static VisitedMap* alreadyVisited(SyncGraphSet& dest, SymbolStateMap& map) {
  for_vector(VisitedMap, curVisited, gListVisited) {
    if(curVisited->destPoints == dest && curVisited->symbolMap == map) {
      return curVisited;
    }
  }
  return NULL;
}


/**
 We are matching the Equivalent loops that contain the FILL and EMPTY
operations on the same variable.
Once a perfect matching is found we remove both the loops
from our eveluation tree.
Assumption:If there exists a path with a matching and opposite loops,
where a variable access is "dangerous" there will be a path where 
the variable access is dangerous without considering both the loops.
 **/
static bool verifyLoopEquivalenceForScope(SyncGraphLoopNode head1, SyncGraphLoopNode head2, Scope parentScope) {
   // TODO
  /**
   * The loops are assumed to be equivalent if 
   * starting condition: Should be representing the same 
   constant value over the parent scope.
   * ending condition: Should be representing the same 
   constant value over the parent scope.
   * increment: equivalent increment
   **/


  
  return false;
  //   return true;
}




  // This function frees SyncGraphNode Nodes recursively.
  
static void deleteSyncGraphNode(SyncGraphNode *node) {
  if (node != NULL) {
    if(node->child != NULL && node->child->parent == node)
      deleteSyncGraphNode(node->child);

    SyncGraphFunctionNode* fn  = getFunctionNode(node);
    if(fn != NULL)
      deleteSyncGraphNode(fn->fChild);
    SyncGraphBranchNode* b = getBranchNode(node);
    if(b != NULL)
      deleteSyncGraphNode(b->cChild);
    
    // TODO do for loop Node as well
    
    delete node;
  }
}



// Function finds the bas Symbol of the current use.
// Used to identify the outer variable uses.
static Symbol* findBaseSymbol(Symbol* curSymbol) {
  Symbol* baseSymbol = curSymbol;
  Symbol* parentSymbol = baseSymbol->defPoint->parentSymbol;
  
  
  while (parentSymbol->hasFlag(FLAG_BEGIN)) { // IS a BEGIN task.
    CallExpr* beginCallExpr = toCallExpr(parentSymbol->defPoint->prev);
    Symbol* argSymbol = NULL;
    for_formals_actuals(formal, actual, beginCallExpr) {
      if (formal == curSymbol) {
	SymExpr *se = toSymExpr(actual);
	argSymbol = se->symbol();
	break;
      }
    }
    if(argSymbol == NULL) {
      break; // we have found the base symbol.
    } else {
      baseSymbol = argSymbol;
      parentSymbol = baseSymbol->defPoint->parentSymbol;
    }
  }
  
  return baseSymbol;
}


/**
   Clean up the Data-Control Graph.
**/
static void cleanUpSyncGraph(SyncGraphNode *node) {
  for_vector(UseInfo, cur, gUseInfos) {
    delete(cur);
  }
  
  for_vector(VisitedMap, curVisited, gListVisited) {
    delete(curVisited);
  }
  deleteSyncGraphNode(node);
  gAnalysisRoots.clear();
  gUseInfos.clear();
  gListVisited.clear();
  gFuncGraphMap.clear();
  gSyncVars.clear();
  gSingleSet.clear();
}


static void  exit_pass() {
  //  delete gAnalysisRoots;
  // delete gUseInfos;
}



static void copyUseInfoVec(SyncGraphNode *copy, SyncGraphNode* orig, FnSymbol* parent) { 
  for_vector(UseInfo, curInfo, orig->extVarInfoVec) {
    if(isOuterVar (curInfo->symbol, parent)) {
      UseInfo* newUseInfo = new UseInfo(copy, copy->fnSymbol, curInfo->usePoint, curInfo->symbol);
      gUseInfos.push_back(newUseInfo);
      copy->extVarInfoVec.push_back(newUseInfo);
    }
    
  }
}


static SyncGraphNode* getRightTypeofNode(SyncGraphNode* orig, FnSymbol* fn, bool flag) {
  // TODO We can use base class "SyncGraphNode" for SyncGraphFunctionNode
  // if the function attached is not begin node

  SyncGraphBranchNode* branch = getBranchNode(orig);
  if(branch != NULL)
    return new SyncGraphBranchNode(branch, fn, flag);
  SyncGraphFunctionNode* func = getFunctionNode(orig);
  if(func != NULL)
    return new SyncGraphFunctionNode(func, fn, flag);
  SyncGraphLoopNode* loop = getLoopNode(orig);
  if(loop != NULL)
    return new SyncGraphLoopNode(loop, fn, flag);

  return new SyncGraphNode(orig, fn, flag);
}

// Recursively make a copy of CFG
// if endPoint is not null we make copy until the endPoint.
// parent: parent node of newly generated Copy Node
// branch: node which is to be copied.
// endPoint : stop Copying once we reach this node. 
static SyncGraphNode* copyCFG(SyncGraphNode* parent, SyncGraphNode* branch, SyncGraphNode* endPoint) {
  
  if(branch == NULL)
    return NULL;
  SyncGraphNode* newNode = NULL;
  if(parent != NULL) {
    // copy info vec where our scope is determined by the parent
    // node
    
    newNode = getRightTypeofNode(branch, parent->fnSymbol, false);
    copyUseInfoVec(newNode, branch, parent->fnSymbol);
  } else {
    // parent is NULL. means the first node of a
    // begin branch. scope should be equivalent to the
    // node
    newNode = getRightTypeofNode(branch, branch->fnSymbol, false);
    copyUseInfoVec(newNode, branch, branch->fnSymbol);
  }
 
  if(branch->child != NULL && branch->child != endPoint) {
    SyncGraphNode* child = copyCFG(newNode, branch->child, endPoint);
    child->parent  = newNode;
    newNode->child = child;
  }
  

  SyncGraphBranchNode* bBranch = getBranchNode(branch);  
  
  if(bBranch!= NULL && bBranch->cChild != NULL) {
    endPoint =  bBranch->joinNode;
    SyncGraphNode* child = copyCFG(newNode, bBranch->cChild, endPoint);
    child->parent  = newNode;
    SyncGraphBranchNode* newBranch = getBranchNode(newNode);
    INT_ASSERT(newBranch != NULL);
    newBranch->cChild = child;
  }

  SyncGraphFunctionNode* fBranch = getFunctionNode(branch);  
  
  if(fBranch != NULL && fBranch->fChild != NULL && fBranch->fChild->fnSymbol->hasFlag(FLAG_BEGIN)) {
    SyncGraphNode* child = copyCFG(NULL, fBranch->fChild, NULL);
    child->parent  = newNode;
    SyncGraphFunctionNode* functionParent = getFunctionNode(parent);
    INT_ASSERT(functionParent != NULL);
    functionParent->fChild = child;
  }

  // TODO for Loop Node

  SyncGraphLoop Node loopNode = getLoopNode(branch);
  if(loopNode != NULL) {
    if(loopNode.isHeadedLoop() ==true) {
      
    } else {

    }
  } 
  
  return newNode;
}

/*
  returns The last node in the current strand of Graph
  start: repreosnts the start point
*/
inline static SyncGraphNode* getLastNode(SyncGraphNode* start) {
  SyncGraphNode* cur = start;
  while(cur ->child != NULL) {
    cur = cur->child;
  }
  return cur;
}

// curNode: Start point of search
static bool hasNextSyncPoint(SyncGraphNode * curNode) {
  if(curNode == NULL)
    return false;
  if(isASyncPoint(curNode) == true)
    return true;
  bool val = hasNextSyncPoint(curNode->child);
  
  SyncGraphBranchNode* branchNode = getBranchNode(curNode);
  if(branchNode != NULL && branchNode->cChild != NULL) {
    val &= hasNextSyncPoint(branchNode->cChild);
  }
  return val;
}



static bool isPartofBeginBranch(SyncGraphNode* curNode) {
  SyncGraphNode* parentNode = curNode;
  while(parentNode != NULL) {
    if(parentNode->fnSymbol->hasFlag(FLAG_BEGIN))
      return true;
    parentNode = parentNode->parent;
  }
  return false;
}

static void checkNextSyncNode() {
  for_vector(UseInfo, cur, gUseInfos) {
    SyncGraphNode *curNode = cur->useNode;
#ifdef CHPL_DOTGRAPH
    std::cout<<"The use is in node id "<<cur->useNode->__ID<<std::endl;
#endif
    if( hasNextSyncPoint(curNode) == false &&
	isPartofBeginBranch(curNode) == true) {
      // if this use  is part of a begin branch
      // we need to report error.
      
      provideWarning(cur);
    } 
  }
}



/**
   Expand all nested function calls. A check has been introduced to avoid infinite loop
   due to recursion.
   root : start point of nested function expansion :
   callStack: list of FnSymbols in the Graph
   stopPoint (optional): We expand the nested function until we reach this point.
                       default value is NULL.
**/
static void expandAllNestedFunctions(SyncGraphNode* root, FnSymbolsVec& callStack, SyncGraphNode* stopPoint) {
  SyncGraphNode* cur = root;
  while(cur != NULL) {
    if(cur == stopPoint)
      return;
    if(cur->intFuncCall != NULL && cur->expandedFn == false) {
      FnSymbol* curFun = cur->intFuncCall->theFnSymbol();
      SyncGraphNode* intFuncNode = gFuncGraphMap.get(curFun);
      if(intFuncNode != NULL && callStack.in(curFun) == NULL) {
	//SyncGraphNode* parentNode = cur->parent;
	int added = callStack.add_exclusive(curFun);
	// expand all nested functions recursively
	if(added == 1) {
	  expandAllNestedFunctions(intFuncNode, callStack, NULL);
	  FnSymbol* popped = callStack.pop();
	  INT_ASSERT(popped == curFun);
	}
	
	INT_ASSERT(getBranchNode(cur) == NULL && getFunctionNode(cur) == NULL);
	SyncGraphNode *oldChild = cur->child;
	SyncGraphNode* copy = copyCFG(cur, intFuncNode, NULL);
	/* update Pointers */
	copy->parent = cur;
	cur->child = copy;
	SyncGraphNode* endPoint = getLastNode(copy);
	INT_ASSERT(endPoint != NULL);
	endPoint->child = oldChild;
	oldChild->parent = endPoint;
	cur->expandedFn  = true;
	INT_ASSERT(endPoint != NULL);
	cur = endPoint;
      }
    }

    // TODO SyncGraphLoopNode

    SyncGraphBranchNode* branch = getBranchNode(cur);
    if(branch != NULL && branch->cChild != NULL ) {
      expandAllNestedFunctions(branch->cChild, callStack,branch->joinNode);
    }

    SyncGraphFunctionNode* func  = getFunctionNode(cur);
    if(func != NULL && func->fChild != NULL ) {
      expandAllNestedFunctions(func->fChild, callStack,stopPoint);
    }
    cur = cur->child;
  }
  return;
}


/**
   This function will compare two scopes and return the relationship.
   Return 0  : Not compareable
   Return 1  : The Scope A is embedded in Scope B. (includes A == B)
   Return -1 : The Scope B is strictly
   embedded in Scope A. (does not include B == A ).
   Assumes NULL emedded everything
**/
static int compareScopes(Scope* a, Scope* b) {
  if(a == b) {
    return 1;
  }

  if(a == NULL)
    return -1;

  if(b == NULL)
    return 1;
  
  Expr* parent = a->parentExpr;
  if(a->parentSymbol == b->parentSymbol) {
    while(parent) {
      if (parent == b)
        return 1;
      parent = parent->parentExpr;
    }
    parent = b->parentExpr;
    while(parent) {
      if (parent == a)
        return -1;
      parent = parent->parentExpr;
    }
  }
  return 0;
}


static SyncGraphNode* addFunctionNode(SyncGraphNode *cur, FnSymbol* fn, GraphNodeStatus status) {
   SyncGraphNode* childNode = new SyncGraphNode(fn);
   SyncGraphFunctionNode* fnNode = getFunctionNode(cur);
   INT_ASSERT(fnNode!= NULL);
   fnNode->fChild = childNode;
   childNode->syncedScopes.copy(cur->syncedScopes);
   return childNode;
}

/**
   Adding a child node to the current node.
   The FnSymbol passed should be the Function
   that will contain the node.
   This will help us distinguish the child nodes
   that are created due to sync points
   and the ones that are created for embedded Functions.
**/
static SyncGraphNode* addChildNode(SyncGraphNode *cur, FnSymbol* fn, GraphNodeStatus status) {
  SyncGraphNode* childNode = NULL;
  if(status == CREATE_BRANCH_NODE) {
    childNode = new SyncGraphBranchNode(fn);
  } else  if(status == CREATE_FUNCTION_NODE) {
    childNode = new SyncGraphFunctionNode(fn);
  } else if(status == CREATE_LOOP_NODE) {
    childNode = new SyncGraphLoopNode(fn);
  } else {
   childNode = new SyncGraphNode(fn);
  }
  
  childNode->parent = cur;
  INT_ASSERT(fn == cur->fnSymbol);
  cur->child = childNode;
  childNode->syncedScopes.copy(cur->syncedScopes);
  return childNode;
}


/**
   Add Else child of a conditional Node.
**/
static SyncGraphNode* addElseChildNode(SyncGraphBranchNode *cur, FnSymbol *fn) {
  SyncGraphNode* childNode = new SyncGraphNode(fn);
  childNode->parent = cur;
  cur->cChild = childNode;
  childNode->syncedScopes.copy(cur->syncedScopes);
  return childNode;
}


static void updateSafeInfos(VisitedMap* prev, SyncGraphVector& visitedNodes, UseInfoSet& safeInfoset, UseInfoSet& visitedUseInfo) {
  bool flag = false;
  for_set(UseInfo, curUseInfo, prev->visitedInfoSet) {
    flag = false;
    for_vector(SyncGraphNode, curNode, visitedNodes) {
      FnSymbol *parentFn = curNode->fnSymbol;
      if(curUseInfo->fnSymbol == parentFn) {
	flag = true;
	break;
      } 
    }
    if(flag ==true)
      safeInfoset.insert(curUseInfo);
    else
      visitedUseInfo.insert(curUseInfo);
  }
}


/**
   We need to make sure of the change of state in
   the sync/single varibale:

   The point of filling :
   =:
   writeEF:
   single_mark_and_signal_full/sync_mark_and_signal_full:


   The point of emptying:
   =:
   readFE:
   sync_mark_and_signal_empty:
   No emptying for single. So we have to assume all single variables
   that reach readFE to sync with the write point of the single.
 
**/
static SyncGraphNode* addSyncExprs(Expr *expr, SyncGraphNode *cur) {
  std::vector<CallExpr*> callExprs;
  collectCallExprs(expr, callExprs);
  FnSymbol* curFun = expr->getFunction();
  for_vector (CallExpr, call, callExprs) {
    if (call->theFnSymbol() != NULL) {
      if (!strcmp(call->theFnSymbol()->name, "=")) {
        SymExpr* symExpr = toSymExpr(call->getNextExpr(call->getFirstExpr()));
        std::string symName;
	Symbol* symPtr  = NULL;
        if (symExpr != NULL) {
          symName = symExpr->symbol()->name;
	  symPtr = findBaseSymbol(symExpr->symbol());
        }
        std::vector<CallExpr*> intCalls;
        collectCallExprs(call->theFnSymbol(), intCalls);
        for_vector (CallExpr, intCall, intCalls) {
          if (intCall->theFnSymbol() != NULL) {
            if (!strcmp(intCall->theFnSymbol()->name, "writeEF")) {
#ifdef CHPL_DOTGRAPH
	      std::cout<< "The symbol ptr full is "<<symPtr<<" with name "<<symExpr->symbol()->name<<std::endl;
#endif
	      INT_ASSERT(symPtr != NULL);
	      cur->syncVar = symPtr;
	      gSyncVars.insert(symPtr);
	      cur->syncType = NODE_SYNC_SIGNAL_FULL;
	      cur->syncExpr = call;
	      cur = addChildNode(cur, curFun, CREATE_SYNC_NODE);
            }
          }
        }
      } else if (!strcmp(call->theFnSymbol()->name, "_statementLevelSymbol")) {
        SymExpr* symExpr = toSymExpr(call->getNextExpr(call->getFirstExpr()));
        std::string symName;
	Symbol* symPtr;
        if (symExpr != NULL) {
          symName = symExpr->symbol()->name;
	  symPtr = findBaseSymbol(symExpr->symbol());
        }
        std::vector<CallExpr*> intCalls;
        collectCallExprs(call->theFnSymbol(), intCalls);
        for_vector (CallExpr, intCall, intCalls) {
          if (intCall->theFnSymbol() != NULL) {
            if (!strcmp(intCall->theFnSymbol()->name, "readFF")) {
#ifdef CHPL_DOTGRAPH
	      std::cout<< "The symbol ptr read is "<<symPtr<<" with name "<<symExpr->symbol()->name<<std::endl;
#endif
	      INT_ASSERT(symPtr != NULL);
	      cur->syncVar = symPtr;
	      gSyncVars.insert(symPtr);
	      gSingleSet.insert(symPtr);
	      cur->syncType = NODE_SINGLE_WAIT_FULL;
	      cur->syncExpr = call;
	      cur = addChildNode(cur, curFun, CREATE_SYNC_NODE);
	    } else if (!strcmp(intCall->theFnSymbol()->name, "readFE")) {
#ifdef CHPL_DOTGRAPH
	      std::cout<< "The symbol ptr read is "<<symPtr<<" with name "<<symExpr->symbol()->name<<std::endl;
#endif
	      cur->syncVar = symPtr;
	      gSyncVars.insert(symPtr);
	      cur->syncType = NODE_SYNC_SIGNAL_EMPTY;
	      cur->syncExpr = call;
	      cur = addChildNode(cur, curFun, CREATE_SYNC_NODE);
	    }
          }
        }
      }
    }
  }
  return cur;
}


/**
   Checks if the node is a sync point. ALready filled single point needs to be skipped.
 **/
static bool isASyncPointSkippingSingles(SyncGraphNode* cur, SyncGraphSet& filledSinglePoints) {
  if(isASyncPoint(cur)) {
    for_set(SyncGraphNode, filledSingle, filledSinglePoints) {
      if(cur->syncVar == filledSingle->syncVar) {
	//	checkUseInfoSafety(cur, visited);
	/**
	   IMP: Single special cases. We are asking to skip this single Node
	   as we have seen it sync already
	 **/
	return false;
      }
    }
    return true;
  }
  return false;
}


static bool isASyncPoint(SyncGraphNode * cur) {
  INT_ASSERT(cur != NULL);
  if(cur->syncType == NODE_SINGLE_WAIT_FULL ||
     cur->syncType == NODE_SYNC_SIGNAL_FULL ||
     cur->syncType == NODE_SYNC_SIGNAL_EMPTY ) {   
    return true;
  }
  return false;
}

static bool canVisitNext(SymbolStateMap& stateMap, SyncGraphNode* sourceSyncPoint) {
  SymbolStateMap::iterator state = stateMap.find(sourceSyncPoint->syncVar);
  INT_ASSERT(state != stateMap.end());
  // cases  2 & 3
  if( (state->second == SYMBOL_STATE_EMPTY && sourceSyncPoint->syncType == NODE_SYNC_SIGNAL_FULL) ||
      (state->second == SYMBOL_STATE_FULL  && sourceSyncPoint->syncType == NODE_SYNC_SIGNAL_EMPTY) ) 
    return true;
  return false;
}
 

/*
static void updateUnsafeUseInfos(VisitedMap* curVisited, SymbolStateMap& stateMap, SyncGraphSet& partialSet, UseInfoVec& useInfos) {
  // TODO currently we are syncing by the function later we
  // should sync by the scope.
  //  useInfos.insert(curVisited->useInfos.begin(), curVisited->useInfos.end());
  if(curVisited == NULL || partialSet.size() == 0)
    return;
  for_set(SyncGraphNode, curNode, partialSet) {
    FnSymbol *parentFn = curNode->fnSymbol;
    bool safeUse  = false;
    if(canVisitNext(stateMap, curNode) == true) {
      forv_Vec(UseInfo, curUseInfo, curVisited->unSyncedUses) {
	if(curUseInfo->fnSymbol == parentFn) {
	  // the sync point is same as that of the variable in use
	  // so variable is safe in this pass.
	  safeUse = true;
	}
	if(safeUse == false) {
	  // NOT SAFE... not yet
	  useInfos.push_back(curUseInfo);
	}
      }
    }
  }
}
*/

static void collectUseInfos(VisitedMap* curVisited, SyncGraphVector& newlyVisited, UseInfoSet& useInfos) {
  for_vector(SyncGraphNode, visited, newlyVisited) {
    if(visited->extVarInfoVec.size() > 0)
      useInfos.insert(visited->extVarInfoVec.begin(), visited->extVarInfoVec.end());

#ifdef CHPL_DOTGRAPH
	std::cout<<"The collecting for node id "<<visited->__ID<<std::endl;
#endif
  
    SyncGraphNode* parent = visited->parent;
    while(parent != NULL) {
      if(parent->extVarInfoVec.size() > 0) {
	UseInfo* st= parent->extVarInfoVec.front();
	if(curVisited == NULL ||
	   ( curVisited->visitedInfoSet.find(st) == curVisited->visitedInfoSet.end() && 
	     curVisited->safeInfoSet.find(st)    == curVisited->safeInfoSet.end())) {
	  useInfos.insert(parent->extVarInfoVec.begin(), parent->extVarInfoVec.end());
	} else {
	  break;
	}
      }
      parent  = parent->parent;
    }
  }
}

/**
   This Function recursively collects all begins statements between 'root' and all 'endPoints' and add the first
   'SyncPoint' of the begin statement in 'taskPoints'. If the begin function does not contain any 'syncPoint' we will
   not add them to the 'taskPoints' but any begin statement originating from this begin which has a 'syncPoint'
   will be added.
    curVisited : The current Visit Map (PPS)
    newlyVisited : 
**/
static void collectAllAvailableSyncPoints(VisitedMap* curVisited, SyncGraphVector& newlyVisited, SyncGraphVector& partialVisited, SyncGraphSet& partialSet,  SymbolState newState) {
  SyncGraphSet vSingles;

#ifdef CHPL_DOTGRAPH
  std::cout<<"front node  "<<newlyVisited.front()->__ID<<std::endl;
#endif

  if(newlyVisited.size() == 0)
    return;
  
  if(curVisited != NULL) {
    vSingles.insert(curVisited->vSingles.begin(), curVisited->vSingles.end());
  }
  
  unsigned int i = 0;
  SyncGraphNode* cur;
  
  while(i < partialVisited.size()) {
    cur = partialVisited.at(i);
    i++;
    while(cur != NULL) {
      SyncGraphFunctionNode* fn = getFunctionNode(cur);
      if(fn != NULL && fn->fChild != NULL && fn->fChild->fnSymbol->hasFlag(FLAG_BEGIN)) {
	if(isASyncPointSkippingSingles(fn->fChild, vSingles)) {
	  partialSet.insert(fn->fChild);	  
	} else {
	  partialVisited.push_back(fn->fChild);
	}
      }

      SyncGraphBranchNode* branch  = getBranchNode(cur);
      
      if(branch != NULL && branch->cChild != NULL) {
	SyncGraphVector partialRemoved(partialVisited.begin()+i, partialVisited.end());
	SyncGraphSet newPartialSet(partialSet.begin(), partialSet.end());
	if(isASyncPointSkippingSingles(branch->cChild, vSingles)) {
	  newPartialSet.insert(branch->cChild);
	} else {
	  partialRemoved.push_back(branch->cChild);
	}
	collectAllAvailableSyncPoints(curVisited, newlyVisited, partialRemoved, newPartialSet, newState);
      }

      if(cur->child != NULL) {
	if(isASyncPointSkippingSingles(cur->child, vSingles)) {
	  partialSet.insert(cur->child);
	  break;
	}
      }
      cur = cur->child;
    }
  }

  UseInfoSet useInfos;
  collectUseInfos(curVisited, newlyVisited, useInfos);

  if(partialSet.size() > 0) {
    //TODO if curVisited == NULL;
    VisitedMap* prev = NULL;
    if(curVisited != NULL) {
      SymbolStateMap stateMap = curVisited->symbolMap;
      SymbolStateMap::iterator it = stateMap.find(newlyVisited.front()->syncVar);
      INT_ASSERT(it != stateMap.end());
      it->second = newState;
      prev = alreadyVisited(partialSet, stateMap);
#ifdef CHPL_DOTGRAPH
      std::cout<<"Check visited map "<<std::endl;
#endif
    }
    if(prev == NULL) {
#ifdef CHPL_DOTGRAPH
      std::cout<<"New visited map "<<std::endl;
#endif
      
      VisitedMap* newVisit = new VisitedMap(curVisited, partialSet, useInfos, newlyVisited, newState);
      gListVisited.push_back(newVisit);
    } else {
#ifdef CHPL_DOTGRAPH
      std::cout<<"add to map "<<std::endl;
#endif
      prev->appendData(useInfos, newlyVisited);
    }
  } else  {
    if(curVisited != NULL) {
      UseInfoSet safeInfoSet;
      updateSafeInfos(curVisited, newlyVisited, safeInfoSet, useInfos);
    }

    if(useInfos.size() > 0) {
      for_set(UseInfo, cur, useInfos) {
#ifdef CHPL_DOTGRAPH
	std::cout<<"The error is in node id "<<cur->useNode->__ID<<std::endl;
#endif
	provideWarning(cur);
      }
    }
  }
}


/**
   This Function is called to report the error on 'expr' where the 'var' is not synced.
**/
static void provideWarning(UseInfo* var) {
  if(! var->isChecked() ) {
    var->setChecked();
    USR_WARN(var->usePoint,
	     "USEAFTERFREE Potential unsafe (use after free) use of variable %s here. Please make sure the variable use is properly synced.",
	     var->symbol->name);
  }
}







/**
   Since single variables once filled remians as such, we need to handle them seperately.
   Here once, we find a matching syncNode we bypass all syncPoints involving that single variable
**/
static bool handleSingleSyncing(VisitedMap * curVisited) {
  SyncGraphSet destPoints = curVisited->destPoints;
  SyncGraphVector syncPoints;
 
  for_set(SyncGraphNode, sourceSyncPoint, destPoints) {
    for_set(SyncGraphNode, syncedSingles, curVisited->vSingles) {
      if(sourceSyncPoint->syncVar == syncedSingles->syncVar) {
	syncPoints.push_back(sourceSyncPoint);
      }
    }
  }
  
  if( syncPoints.size() > 0) {
    for_vector(SyncGraphNode, curSingle, syncPoints) {
      destPoints.erase(curSingle);
    }
    collectAllAvailableSyncPoints(curVisited, syncPoints, syncPoints, destPoints,SYMBOL_STATE_FULL);
  }
  
  return false;
}

static SymbolState updateState(GraphNodeStatus status) {
  INT_ASSERT(status == NODE_SYNC_SIGNAL_FULL || status == NODE_SYNC_SIGNAL_EMPTY);
  if(status == NODE_SYNC_SIGNAL_FULL)
    return SYMBOL_STATE_FULL;
  return SYMBOL_STATE_EMPTY;
}


static bool threadedMahjong(void) {
  SyncGraphVector syncPoints;
  unsigned int i=0;
  while(i < gListVisited.size()) {
    VisitedMap *curVisited =  gListVisited.at(i);
    bool sucess = handleSingleSyncing(curVisited);
    if(!sucess) {
      SyncGraphSet destPoints = curVisited->destPoints;
      for_set(SyncGraphNode, sourceSyncPoint, destPoints) {
#ifdef CHPL_DOTGRAPH
	std::cout<<"Node ID to visit "<<sourceSyncPoint->__ID<<std::endl;
#endif
	if(canVisitNext(curVisited->symbolMap, sourceSyncPoint) == true) {
#ifdef CHPL_DOTGRAPH
	std::cout<<"Node ID  visited "<<sourceSyncPoint->__ID<<std::endl;
#endif	 
	  SyncGraphVector newlyMatched;
	  newlyMatched.push_back(sourceSyncPoint);
	  SyncGraphSet partialSet(curVisited->destPoints.begin(), 
				  curVisited->destPoints.end());
	  partialSet.erase(sourceSyncPoint);
	  SymbolState state = updateState(sourceSyncPoint->syncType);
	  collectAllAvailableSyncPoints(curVisited, newlyMatched, newlyMatched, partialSet, state);
	}
      }
    }
    i++;
  }
  return false;
}



static void checkOrphanStackVar(SyncGraphNode* root) {
  SyncGraphNode* startPoint = root;
  UseInfoSet useInfos;
  INT_ASSERT(startPoint->extVarInfoVec.size() == 0);
  checkNextSyncNode();
  if(isASyncPoint(startPoint) == true) {
    SyncGraphVector visited;
    SyncGraphSet destSyncPoints;
    destSyncPoints.insert(startPoint);
    VisitedMap* newVisit = new VisitedMap(NULL,  destSyncPoints,  useInfos, visited, SYMBOL_STATE_EMPTY);
    gListVisited.push_back(newVisit);    
  }  else {
    SyncGraphVector startPointVec;
    SyncGraphSet partialSet;
    startPointVec.push_back(startPoint);
    collectAllAvailableSyncPoints(NULL, startPointVec, startPointVec, partialSet, SYMBOL_STATE_EMPTY);
  }
  threadedMahjong( );
  return;
}


/***
    A modified copy of isOuterVar in
    flattenFunction.cpp
***/
static bool isOuterVar(Symbol* sym, FnSymbol* fn) {
  /**
     To do handle function calls.
  **/
  if (   sym->isParameter()               || // inclcudes isImmediate()
         sym->hasFlag(FLAG_TEMP)          || // exclude these
         sym->hasFlag(FLAG_CONST)         ||
         sym->hasFlag(FLAG_TYPE_VARIABLE) ||    // 'type' aliases or formals
         sym->hasFlag(FLAG_SINGLE)        ||
         sym->hasFlag(FLAG_SYNC)          ||
         isFnSymbol(sym)
         )
    return false;
  if (isArgSymbol(sym)) {
    ArgSymbol* argSym = toArgSymbol(sym);
    if (argSym->intent & INTENT_FLAG_REF) {
      return true;
    }
  }
  Symbol* symParent = sym->defPoint->parentSymbol;
  Symbol* parent = fn->defPoint->parentSymbol;
  bool flag = false;
  while (true) {
    if (!isFnSymbol(parent)) {
      flag = false;
      break;
    } else if (symParent == parent) {
      flag = true;
      break;
    } else {
      INT_ASSERT (parent->defPoint->parentSymbol &&
                  parent->defPoint->parentSymbol != parent); // ensure termination
      parent = parent->defPoint->parentSymbol;
    }
  }
  return flag;
}


static ArgSymbol*  getTheArgSymbol(Symbol* sym, FnSymbol* parent) {
  if(parent == NULL)
    return NULL;
  ArgSymbol* arg = NULL;
  for_formals(formal,parent) {
    if(strcmp(sym->name, formal->name) == 0) {
      arg = formal;
    }
  }
  if(arg != NULL)
    return arg;
  return NULL;
}


/**
   Get the scope of the symbol.
   If its a outer variable to the base function we return NULL.
**/
static Scope* getOriginalScope(Symbol* sym) {
  ArgSymbol* argSym;
  ArgSymbol* parentArgSymbol;
  Symbol* symParent;
  FnSymbol* symParentFunction;
  Symbol* parent;
  FnSymbol* parentFunction;
  if(isArgSymbol(sym)) {
    while (isArgSymbol(sym)) {
      argSym = toArgSymbol(sym);
      symParent  = sym->defPoint->parentSymbol;
      parent = symParent->defPoint->parentSymbol;
      parentFunction = toFnSymbol(parent);
      symParentFunction = toFnSymbol(symParent);
      if(parentFunction != NULL)
        parentArgSymbol = getTheArgSymbol(sym, parentFunction);
      if (argSym->intent & INTENT_FLAG_REF) {
        if(isFnSymbol(parent)) {
          if(parentArgSymbol != NULL) {
            // Go one level up. Parent of symParent is a function and
	    // also the symbol was founs in parent argument list.
            sym = parentArgSymbol;
          } else {
            // We reached the defining point.
            return parentFunction->body;
          }
        } else {
	  return symParentFunction->body;
        }
      }  else {
        return sym->defPoint->getScopeBlock();
      }
    }
  }
  return sym->defPoint->getScopeBlock();
}


/**
   checks if the expression expr refers any outer variables.
   if Yes add it to current list.
**/
static bool  refersOuterSymbols(Expr* expr, SyncGraphNode* cur) {
  std::vector<SymExpr*> symExprs;
  collectSymExprs(expr, symExprs);
  for_vector (SymExpr, se, symExprs) {
    Symbol* sym = se->symbol();
    if (isOuterVar(sym, expr->getFunction())) {
      Scope* block = getOriginalScope(sym);
      if(shouldSync(block, cur)) {
        return true;
      }
    }
  }
  return false;
}

/**
   Add use of outer variable details to 'node'.
**/
static void addExternVarDetails(FnSymbol* fn, Symbol* v, SymExpr* use, SyncGraphNode* node) {
  if(compareScopes(fn->body,gFnSymbolRoot->body) != 1)
    fn = gFnSymbolRoot;
  /*
    IMP: if the symbol root is beyond the gFnSymbolRoot it means the symbol was an argument 
    to the base function. In that case if the symbol is used in the base function, we need 
    not consider is as an outer variable.
   */
  if(node->fnSymbol != fn) {
    UseInfo * newUseInfo = new UseInfo(node, fn, use, v);
    gUseInfos.push_back(newUseInfo);
    node->extVarInfoVec.push_back(newUseInfo);
  }
}


/**
   Add outer Variables, begin Nodes, outer function calls etc
   to 'cur'.
**/
static SyncGraphNode* addSymbolsToGraph(Expr* expr, SyncGraphNode *cur) {
  std::vector<SymExpr*> symExprs;
  collectSymExprs(expr, symExprs);
  for_vector (SymExpr, se, symExprs) {
    Symbol* sym = se->symbol();
    if(sym->type == NULL)
      continue;
    else {
      if (!(isSyncType(sym->type)) &&
	  !(isSingleType(sym->type)) &&
	  isOuterVar(sym, expr->getFunction())) {
	BlockStmt* block = getOriginalScope(sym);
	if(shouldSync(block, cur)) {
	  FnSymbol* fnsymbol = block->getFunction();
	  addExternVarDetails(fnsymbol, sym, se, cur);
	  // cur->contents.add_exclusive(se);
	  // cur->syncScope.add(block);
	}
      }
    }
  }
  /**collect calls to functions **/
  std::vector<CallExpr*> callExprs;
  collectCallExprs(expr, callExprs);
  for_vector (CallExpr, call, callExprs) {
    FnSymbol* calleeFn = call->theFnSymbol();
    /**
       Conditions :
    1. The calleeFn definition should not be NULL
    2. TODO : CalleeFn Should not have begin Fn If it has 
    (we will handle it separately)
    3. User defined Function 
    4. Should be Nested Function
    5. Callee should NOT be beyond any of the synced scopes.
    (If it is beyond a synced scope all outer variables 
    accessed by the function will have the scope beyond the synced 
    scope. Hence all accesses are SAFE)
     **/
    if ( calleeFn != NULL
	 //&& !(caleeFn->hasFlag(FLAG_BEGIN))
        && (calleeFn->getModule()->modTag == MOD_USER)
        && isFnSymbol(calleeFn->defPoint->parentSymbol)
	 && isInsideAllSyncedScopes(calleeFn, cur) == true) {
      // Non begin used mod function could be an nested function
      // Number of calls to embedded functions should not be more than 1.
      INT_ASSERT(cur->intFuncCall == NULL);
      /**
	 Fix There can be call expressions without function Symbol
	 in that case we are not going to store it
       **/  
      SymExpr* baseCallExpr = toSymExpr(call);
      if(baseCallExpr != NULL)
	cur->intFuncCall = call; // Not assured to be embedded function call.
    }
  }
  if(cur->intFuncCall != NULL )
    cur = addChildNode(cur, cur->fnSymbol, CREATE_SYNC_NODE);
  
  cur = addSyncExprs(expr, cur);
  return cur;
}

// for finding if all calls to the base function is
// through a sync statement. If yes then we need not
// any variable that is passed to as argument.
static bool isInsideSyncStmt(Expr* expr) {
  while(expr != NULL) {
    if(isBlockStmt(expr)) {
      Expr* previous = expr->prev;
      if(isCallExpr(previous)) {
        if(toCallExpr(previous)->isPrimitive(PRIM_SET_END_COUNT)) {
          return true;
        }
      }
    }
    expr = expr->parentExpr;
  }
  return false;
}


/**
   Check if all calls th the fn is synced using sync statement. If yes, we need
   not worry about use of variable that are defined outside the sync statment.
**/
static void checkSyncedCalls(FnSymbol* fn) {
  gAllCallsSynced = true;
  forv_Vec(CallExpr, call, *fn->calledBy) {
    if(!isInsideSyncStmt(call)) {
      gAllCallsSynced = false;
      break;
    }
  }
}


/*
  Returns the block statment that is protected by the sync statement.
*/
static BlockStmt* getSyncBlockStmt(BlockStmt* block, SyncGraphNode *cur) {
  for_alist (node, block->body) {
    if(isCallExpr(node)) {
      if(toCallExpr(node)->isPrimitive(PRIM_SET_END_COUNT)) {
        if(isBlockStmt(node->next))
          return toBlockStmt(node->next);
      }
    }
  }
  return NULL;
}

/**
   The 'block' represents the scope of outer variable. Once the information
   about the block is provided the Function returns true if the use of the
   outer variable should considered as potentially unsafe (true).

   False means use of the outer variable is safe.
**/
static bool shouldSync(Scope* block, SyncGraphNode *cur) {
  if(block == NULL ||  gAllCallsSynced == true) {
    return false;
  }
  if(cur->syncedScopes.size() > 0) {
    forv_Vec(Scope, syncedScope, cur->syncedScopes) {
      if(compareScopes(syncedScope,block) == 1)
        return false;
    }
  }
  return true;
}

static bool isInsideAllSyncedScopes(FnSymbol* calleeFn, SyncGraphNode* cur) {
  Scope* block = calleeFn->body;
  if(cur->syncedScopes.size() > 0) {
    forv_Vec(Scope, syncedScope, cur->syncedScopes) {
      if(!(compareScopes(block,syncedScope) == 1))
        return false;
    }
  }
  
  return true;
}



/**
   The handle function are used the build the sync graph network where
   we collect information about sync points, outer variable use and
   begin statements.
**/
static SyncGraphNode* handleSyncStatement(Scope* block, SyncGraphNode* cur) {
  cur = addChildNode(cur,cur->fnSymbol, CREATE_SYNC_NODE);
  cur->syncedScopes.add(block);
  cur = handleBlockStmt(block,cur);
  cur = addChildNode(cur,cur->fnSymbol, CREATE_SYNC_NODE);
  cur->syncedScopes.pop();
  return cur;
}

static SyncGraphNode* handleBranching(SyncGraphBranchNode* start, SyncGraphNode* end,  SyncGraphNode* ifNode, SyncGraphNode* elseNode) {
  elseNode->child = end;
  start->joinNode = end;
  end->parent = ifNode;

  return end;
}

static SyncGraphNode* handleCondStmt(CondStmt* cond, SyncGraphNode* cur) {
  BlockStmt* thenBlock = cond->thenStmt;
  BlockStmt* elseBlock = cond->elseStmt;

  cur  = addChildNode(cur, cur->fnSymbol, CREATE_BRANCH_NODE);
  SyncGraphBranchNode* branch = getBranchNode(cur); 
  SyncGraphNode* ifNode = handleBlockStmt(thenBlock,cur);
  SyncGraphNode* endBranch  = addChildNode(ifNode, ifNode->fnSymbol, CREATE_SYNC_NODE);
  SyncGraphNode* elseNode = addElseChildNode(branch, branch->fnSymbol);
  if(elseBlock != NULL) {
    if( ASTContainsBeginFunction(elseBlock) ||
	refersOuterSymbols(elseBlock, branch) ) {
      elseNode = handleBlockStmt(elseBlock,elseNode);
    }
  }
  handleBranching(branch, endBranch,  ifNode, elseNode);
  return endBranch;
}



static bool refersToASyncSingleorAtomicVariable(BlockStmt* block) {
  std::vector<SymExpr*> symExprs;
  collectSymExprs(block, symExprs);
  
  for_vector(SymExpr, sym, symExprs) {
    Symbol* s = sym->symbol();
    if(s->hasFlag(FLAG_SINGLE) ||
       s->hasFlag(FLAG_SYNC)  ||
       s->hasFlag(FLAG_ATOMIC_TYPE))
      return true;
  }
  return false;
}

static SyncGraphNode* handleLoopStmt(BlockStmt* block,SyncGraphNode* cur) {
  // TODO we have to refine the conditions.
  /*
     We need not expand the loop if the loop does satisfy the following
    three conditions
    1. If the loop doesnot contain any begin functions.
    2. If the loop doesnot refer to any of the outer variables.
    3. If the loop doesnot contain any operations on A sync or single
    or atomic variables
    4. Or does not refers to internal function calls.
   */

  
  
  if(ASTContainsBeginFunction(block) == true    ||
     refersOuterSymbols(block, cur)             ||
     refersToASyncSingleorAtomicVariable(block) ||
     refersToInternalFunctionCalls(block)) {
    for_alist (node, block->body) {
      cur = handleExpr(node, cur);
    }
  }
  return cur;
}


static bool refersToInternalFunctionCalls(BlockStmt* block) {
  // TODO
  
  
  return false;
}

static SyncGraphNode* handleDefExpr(DefExpr* def, SyncGraphNode *cur) {
  if (isFnSymbol(def->sym)) {
    FnSymbol* fn = toFnSymbol(def->sym);
    cur = addChildNode(cur,cur->fnSymbol, CREATE_FUNCTION_NODE);
    SyncGraphFunctionNode* curFn = getFunctionNode(cur); 
    INT_ASSERT(curFn != NULL);
    if (fn->hasFlag(FLAG_BEGIN)) {
      handleBegin(fn, cur);
      cur->syncType = NODE_BLOCK_BEGIN;
    } else {
      handleFunction(fn, cur);
      cur->syncType = NODE_BLOCK_NESTED_FUNCTION;
    }
    INT_ASSERT(fn != def->getFunction());
    cur = addChildNode(cur, cur->fnSymbol, CREATE_SYNC_NODE);
  } else {
    //     addSymbolsToGraph(def, cur);
  }
  return cur;
}



static SyncGraphNode* handleBlockStmt(BlockStmt* stmt, SyncGraphNode *cur) {
  if(stmt->body.length == 0)
    return cur;
  bool handled = false;

  if( stmt->isLoopStmt() || stmt->isWhileStmt() ||
      stmt->isWhileDoStmt() || stmt->isDoWhileStmt()  ||
      stmt->isParamForLoop() ) {
    cur = handleLoopStmt(stmt,cur);
  } else if( stmt->isCoforallLoop() ) {
    // CO FOR ALL LOOP to go.
  }
  if(isDefExpr(stmt->body.first())) {
    DefExpr* def = toDefExpr(stmt->body.first());
    if(isVarSymbol(def->sym)) {
      VarSymbol* var = toVarSymbol(def->sym);
      if(strcmp(var->name, "_endCountSave") == 0) {
        BlockStmt* syncBlock = getSyncBlockStmt(stmt, cur);
	handled = true;
	if(syncBlock !=  NULL) {
          cur = handleSyncStatement(syncBlock, cur);
        } else {
	  /* The sync statment encloses a single statement 
	   hence no block involved */
	  cur = addChildNode(cur,cur->fnSymbol, CREATE_SYNC_NODE);
	  cur->syncedScopes.add(stmt);
	  for_alist (node, stmt->body) {
	    cur = handleExpr(node, cur);
	  }
	  cur = addChildNode(cur,cur->fnSymbol, CREATE_SYNC_NODE);
	  cur->syncedScopes.pop();
	}
      }
    }
  }

  if (handled == false) {
    for_alist (node, stmt->body) {
      cur = handleExpr(node, cur);
    }
  }
  return cur;
}

static SyncGraphNode* handleCallExpr(CallExpr* callExpr, SyncGraphNode *cur) {
  if (callExpr->isNamed("begin_fn")) {
    //   Auto created call no need to add.
  } else {
    cur = addSymbolsToGraph(callExpr, cur);
  }
  return cur;
}

static SyncGraphNode* handleExpr(Expr* expr, SyncGraphNode *cur){
  if (NamedExpr* named = toNamedExpr(expr)) {
    cur = handleExpr(named->actual, cur);
  } else if (DefExpr* def = toDefExpr(expr)) {
    cur  = handleDefExpr(def, cur);
  } else if (BlockStmt* block = toBlockStmt(expr)) {
    cur = handleBlockStmt(block, cur);
  } else if (CallExpr* callExpr = toCallExpr(expr)) {
    cur = handleCallExpr(callExpr, cur);
  } else if (CondStmt* contStmt = toCondStmt(expr)) {
    cur = handleCondStmt(contStmt, cur);
  } else {
    addSymbolsToGraph(expr, cur);
  }
  return cur;
}


static SyncGraphNode* handleBegin(FnSymbol* fn, SyncGraphNode* cur) {
  SyncGraphNode* childNode = addFunctionNode(cur, fn, CREATE_SYNC_NODE);
  gFuncGraphMap.put(fn,childNode);
  handleBlockStmt(fn->body, childNode);
  return cur;
}

static SyncGraphNode* handleFunction(FnSymbol* fn, SyncGraphNode *cur) {
  SyncGraphNode* newNode = NULL;
  if (cur == NULL) {
    newNode = cur  = new SyncGraphNode(fn);
    gAnalysisRoots.push_back(newNode);
  } else {
    // Nested Function node.
    newNode = addFunctionNode(cur, fn, CREATE_SYNC_NODE);
  }
  gFuncGraphMap.put(fn,newNode);
  handleBlockStmt(fn->body, newNode);
  return cur;
}



/**
   This function checks if the given outer function constains
   begin statement.
   If the current function is begin we return False since,
   we have already (recursively) added its parent into the list.
*/
static bool  ASTContainsBeginFunction(BaseAST* ast) {
  std::vector<CallExpr*> callExprs;
  collectCallExprs(ast, callExprs);
  for_vector(CallExpr, call, callExprs) {
    FnSymbol* caleeFn = call->theFnSymbol();
    if (caleeFn != NULL && caleeFn->hasFlag(FLAG_BEGIN)) {
      return true;
    }
  }
  return false;
}



/**
   The Function returns true is it has an embedded begin function.
**/
static bool containsBeginFunction(FnSymbol* fn) {
  // we need not analyze any embedded Begin function
  if (!(fn->getModule()->modTag == MOD_USER) || fn->hasFlag(FLAG_BEGIN)) {
    return false;
  }
  return ASTContainsBeginFunction(fn);
}


/**
   Start Point.
   Collects all functions that has embedded begin functions.
   And for each of the functions run the algorithm separately.
**/
void checkUseAfterLexScope() {
  // collect all functions that needs to be analyzed
  Vec<FnSymbol*> aFnSymbols;
  forv_Vec (FnSymbol, fn, gFnSymbols) {
    if (containsBeginFunction(fn) == true) {
      FnSymbol* cur = fn;
      bool found  = false;
      while (!(cur->defPoint->parentSymbol == NULL)) {
        if (toFnSymbol(cur->defPoint->parentSymbol) != NULL) {
          FnSymbol* parent = toFnSymbol(cur->defPoint->parentSymbol);
          if (aFnSymbols.in(parent) != NULL) {
            found  = true;
            break;
          }
          cur = parent;
        }else
          break;
      }
      if(!found)
        aFnSymbols.add_exclusive(fn);
    }
  }


  forv_Vec (FnSymbol, fn, aFnSymbols) {
#ifdef CHPL_DOTGRAPH
    print_view(fn);
#endif
    gFnSymbolRoot = fn;
    checkSyncedCalls(fn);
    SyncGraphNode* syncGraphRoot = handleFunction(fn, NULL);
    FnSymbolsVec callStack;
    callStack.add(fn);
    expandAllNestedFunctions(syncGraphRoot, callStack, NULL);
    
#ifdef CHPL_DOTGRAPH
    dotGraph(syncGraphRoot);
#endif
    checkOrphanStackVar(syncGraphRoot);
    cleanUpSyncGraph(syncGraphRoot);
  }
  
  exit_pass();
}
