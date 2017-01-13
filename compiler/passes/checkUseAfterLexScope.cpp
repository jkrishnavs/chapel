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
//#define CHPL_DOTGRAPH
#ifdef CHPL_DOTGRAPH
#include <fstream>
#include <string>
#include <sstream>

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


/*********** HEADER *********************/
enum GraphNodeStatus {
  NODE_UNKNOWN = 0, //NODE STATUS UNKNOWN
  NODE_SINGLE_WAIT_FULL,
  NODE_SYNC_SIGNAL_FULL,
  NODE_SYNC_SIGNAL_EMPTY,
  NODE_BLOCK_BEGIN, //A NEW BEGIN FUNCTION START HERE
  NODE_BLOCK_INTERNAL_FUNCTION, // A NEW FUNCTION NODE STARTS HERE
  NODE_START_LOOP,
  NODE_START_DOWHILE,
  NODE_START_WHILE,
  NODE_LOOP_END,
  NODE_START_IFELSE,
  NODE_END_IFELSE,
  NODE_INTERNAL_FUNCTION_CALL
};

enum SymbolStates {
  SYMBOL_STATE_EMPTY =0,
  SYMBOL_STATE_FULL
};

#ifdef CHPL_DOTGRAPH
std::string GraphNodeStatusStrings[] = {
  "UNKNOWN", //NODE STATUS UNKNOWN
  "SINGLE_WAIT_FULL",
  "SYNC_SIGNAL_FULL",
  "SYNC_SIGNAL_EMPTY",
  "BLOCK_BEGIN", //A NEW BEGIN FUNCTION START HERE
  "BLOCK_INTERNAL_FUNCTION", // A NEW FUNCTION NODE STARTS HERE
  "START_LOOP",
  "START_DOWHILE",
  "START_WHILE",
  "LOOP_END",
  "START_IFELSE",
  "END_IFELSE",
  "INTERNAL_FUNCTION_CALL"
};
#endif

typedef BlockStmt Scope;
typedef Vec<Scope*> ScopeVec;
/****
     We can say The SyncGraph nodes represents
     a striped CCFG(Concurrent Control Flow Graph)
     Which stores data of sync Points and
     use of External variables.
**/

struct UseInfo;
typedef Vec<UseInfo*> UseInfoVec;

static int counter = 0;

struct SyncGraph {
  int __ID;
  FnSymbol* fnSymbol;
  
  SyncGraph* parent;
  SyncGraph* child; // same function next BB
  SyncGraph* fChild; // internal Functions including Begin
  SyncGraph* cChild; // conditionalNode child
  SyncGraph* joinNode;
  
  CallExpr* syncExpr;
  GraphNodeStatus syncType;
  bool loopNode;
  bool conditionalNode;
  bool expandedFn; // if the functioncall in intFuncCall is already expanded
  //  Vec<SymExpr*>  contents;
  //  Vec<BlockStmt*> syncScope;
  //  Vec<Symbol*> variableFrontiers;
  CallExpr* intFuncCall; // Internal Function Call
  ScopeVec syncedScopes;    // These are the already defined sync points
                            // created due to sync statments, Cobegin, Coforall
                            // and Forall statments.
  UseInfoVec extVarInfoVec;
  //  UseInfoVec frontierVec;
  //  std::string syncVar;
  Symbol* syncVar;
  SyncGraph(SyncGraph* i, FnSymbol *f, bool copyInternalFunctionCall = false) {
    __ID = counter ++;
    fnSymbol = f;
    //    contents.copy(i->contents);
    infoVec.copy(i->infoVec);
    // frontierVec.copy(i->frontierVec);
    syncedScopes.append(i->syncedScopes);
    loopNode = i->loopNode;
    conditionalNode = i->conditionalNode;
    syncType = i->syncType;
    syncVar = i->syncVar;
    joinNode = i->joinNode;
    if(copyInternalFunctionCall)
      intFuncCall = i->intFuncCall;
    expandedFn = i->expandedFn;
    child = NULL;
    fChild = NULL;
    cChild = NULL;
  }

  SyncGraph(FnSymbol *f) {
    __ID = counter ++;
    fnSymbol = f;
    child = NULL;
    fChild = NULL;
    cChild = NULL;
    syncType = NODE_UNKNOWN;
    loopNode = false;
    conditionalNode = false;
    joinNode = NULL;
    intFuncCall = NULL;
    expandedFn = false;
  }
  ~SyncGraph() {}
};



struct UseInfo {
  SymExpr* usePoint;
  SyncGraph* useNode;
  FnSymbol* fnSymbol;
  std::string varName;
  bool checked;

  UseInfo(SyncGraph *node, FnSymbol* fn, SymExpr* expr, std::string name) {
    usePoint = expr;
    fnSymbol = fn;
    useNode = node;
    varName = name;
    // lastSyncPoint = NULL;
    //    nextSyncPoint =  NULL;
    checked = false;
  }

  void setChecked() {
    checked = true;
  }

  bool  isChecked() {
    return checked;
  }

  /*
  void setNextSyncNode(SyncGraph* node) {
    nextSyncPoint = node;
  }

  */
  /*
  void setLastSyncNode(SyncGraph *node) {
    lastSyncPoint = node;
  }
  */
  /*
  bool inherentlyUnSafe() {
    if(checked)
      return false;
    if(lastSyncPoint == NULL || nextSyncPoint == NULL){
      setChecked();
      return true;
    }
    return false;
  }  
  */
};



typedef std::vector<SyncGraph*> SyncGraphVector;
//typedef Vec<SyncGraph*> SyncGraphVec;
//typedef std::vector<SyncGraphVec&> SyncGraphVecVec;
typedef std::vector<SyncGraph*>::iterator SGI; 
typedef Map<FnSymbol*, SyncGraph*> FnSyncGraphMap;
typedef Vec<FnSymbol*> FnSymbolsVec;
typedef std::set<Symbol*> SymbolSet;
static SyncGraphVector gAnalysisRoots; // We will be creating multiple root for
                                   //  analyzing recursion and loops more
                                   // efficiently

static SymbolSet gSyncVars;

typedef std::set<SyncGraph*> SyncGraphSet;

typedef Map<Symbol*, SymbolStates> SymbolStatesMap;

static SyncGraphSet gFinalNodeSet;

//* The parallel program state PPS */
struct VisitedMap {
  SyncGraphSet destPoints;
  UseInfoVec unSyncedUses;
  SymbolStatesMap symbolMap;
  SyncGraphSet vSingles;
  VisitedMap() {}
  ~VisitedMap() {}

  SymbolStates getSyncState(Symbol* syncVar) {
    return symbolMap.get(syncVar);
  }
  
  VisitedMap(VisitedMap* prev, SyncGraphVector& newlyVisited, SyncGraphSet& newDestPoints,  SyncGraphSet& singles, UseInfoVec& infos) {
    destPoints.insert(newDestPoints.begin(), newDestPoints.end());
    vSingles.insert(singles.begin(), singles.end());
    unSyncedUses = infos;
    if(prev != NULL) {
      symbolMap = prev->symbolMap;
    } else {
      for_set(Symbol, curSymbol, gSyncVars) {
	symbolMap.put(curSymbol, SYMBOL_STATE_EMPTY);
      }     
    }
    /*
    for_vector(SyncGraph, newVisit, newlyVisited) {
      if(gFinalNodeSet.find(newVisit) != gFinalNodeSet.end())
	lvisited.insert(newVisit);    
    }
    */
  }
  
  

  /*  
      std::set<SyncGraph*> addtoVisited(SyncGraphVector& newSet) {
      for_vector(SyncGraph, cur, newSet) {
      visited.insert(cur);
      destPoints.erase(cur);
      }
      }
  */
  
  /*
    bool operator==(const std::set<SyncGraph*>& dest) {
    if(destPoints == dest) {
    return true;
    } else {
    return false;
    }
    }
  */
};

struct std::vector<VisitedMap*> gListVisited;

static bool alreadyVisited(SyncGraphSet& dest);

static bool alreadyVisited(SyncGraphSet& dest) {
  for_vector(VisitedMap, curMap, gListVisited) {
    if(curMap->destPoints == dest) {
      return true;
    }
  }
  return false;
}

static UseInfoVec gUseInfos;
static FnSymbol* gFnSymbolRoot;
static FnSyncGraphMap gFuncGraphMap; // start point of each function in Sync Graph
static bool gAllCallsSynced;
static void deleteSyncGraphNode(SyncGraph *node);
static void cleanUpSyncGraph(SyncGraph *root);
static void checkOrphanStackVar(SyncGraph *root);
static SyncGraph* addChildNode(SyncGraph *cur, FnSymbol* fn);
static SyncGraph* handleBlockStmt(BlockStmt* stmt, SyncGraph *cur);
static SyncGraph* handleCondStmt(CondStmt* cond,SyncGraph* cur);
static SyncGraph* handleDefExpr(DefExpr* def, SyncGraph *cur);
static SyncGraph* handleExpr(Expr* expr, SyncGraph *cur);
static SyncGraph* handleFunction(FnSymbol* fn, SyncGraph *cur);
static SyncGraph* handleBegin(FnSymbol* fn, SyncGraph* cur);
static SyncGraph* handleCallExpr(CallExpr* fn, SyncGraph* cur);
static SyncGraph* handleSyncStatement(BlockStmt* block, SyncGraph* cur);
static SyncGraph* handleLoopStmt(BlockStmt* block,SyncGraph* cur);
static bool isOuterVar(Symbol* sym, FnSymbol* fn);
static SyncGraph* addSyncExprs(Expr *expr, SyncGraph *cur);
static SyncGraph* addSymbolsToGraph(Expr* expr, SyncGraph *cur);
static bool containsBeginFunction(FnSymbol* fn);
static Scope* getOriginalScope(Symbol* sym);
//static bool clearUses(UseInfoVec uses, VisitedMap* curState);
static ArgSymbol*  getTheArgSymbol(Symbol * sym, FnSymbol* parent);
static BlockStmt* getSyncBlockStmt(BlockStmt* def, SyncGraph *cur);
static bool isInsideSyncStmt(Expr* expr);
static bool shouldSync(Scope* scope, SyncGraph* cur);
static void checkSyncedCalls(FnSymbol* fn);
static int compareScopes(Scope* a, Scope * b);
static SyncGraph* addElseChildNode(SyncGraph *cur, FnSymbol *fn);
static bool  refersExternalSymbols(Expr* expr, SyncGraph * cur);
static bool  ASTContainsBeginFunction(BaseAST* ast);
static void expandAllInternalFunctions(SyncGraph* root, FnSymbolsVec &fnSymbols, SyncGraph* stopPoint= NULL);
static SyncGraph* copyCFG(SyncGraph* parent, SyncGraph* branch, SyncGraph *endPoint);
//static SyncGraphVector getCopyofGraph(SyncGraph* start, FnSymbol* f);
static void addExternVarDetails(FnSymbol* fn, std::string v, SymExpr* use, SyncGraph* node) ;
static void provideWarning(UseInfo* var);
static bool sync(SyncGraph* source, SyncGraph* dest);
static void getSyncPoints(SyncGraph* source, SyncGraphVector& potentialDest, SyncGraphVector& syncPoints);

static SyncGraph* handleBranching(SyncGraph* start, SyncGraph* end,  SyncGraph* ifNode, SyncGraph* elseNode);
static bool threadedMahjong(void);

static bool handleSingleSyncing(SyncGraphVector& syncPoints, SyncGraphVector& destSyncPoints, VisitedMap* curVisited,  UseInfoVec & useInfos);
static SyncGraph* nextSyncPoint(SyncGraph* start, bool skipCurrent);
static void collectAllAvailableSyncPoints(VisitedMap* curVisited, SyncGraphVector& newlyremoved, SyncGraphSet& partialSet, SyncGraphVector& newlyVisited, UseInfoVec& useInfos);
// static void collectNextSyncPoints(SyncGraph*start, SyncGraphVector& syncPoints, SyncGraphVector& syncedSingle, bool skipCurrent);


// static void checkUseInfoSafety(SyncGraph* node, SyncGraphSet& visited);
// static void checkUseInfoSafety(SyncGraphVector& newlyVisited, SyncGraphSet& visited);

static SyncGraph* getLastNode(SyncGraph* start);

//static void setNextSyncNode();
//static void setLastSyncNode();
static SyncGraph* getNextDominatedNode(SyncGraph* cur);
static bool isASyncPoint(SyncGraph* cur);
static bool isASyncPointSkippingSingles(SyncGraph* cur, SyncGraphSet& filledSinglePoints);
//static int containsVec(SyncGraphVector& list, SyncGraph* cur);
#ifdef CHPL_DOTGRAPH
static void dotGraph(SyncGraph* root);
//static void digraph(std::ofstream& outfile, SyncGraph* cur, std::string level);
static void digraph( SyncGraph* cur, std::string level);
#endif
/************** HEADER ENDS *******************/


#ifdef CHPL_DOTGRAPH
//static int dotGraphCounter = 0;
static std::ofstream outfile;
//static void digraph(std::ofstream& outfile, SyncGraph* cur, std::string level) {
static void digraph(SyncGraph* cur, std::string level) {
  std::string curSyncVar =  "node" + stringpatch::to_string(cur->__ID) +
    std::string(cur->syncVar->name, sizeof(cur->syncVar->name) -1);
  // + "_" + GraphNodeStatusStrings[cur->syncType];
  if(cur->child != NULL) {
    std::string nextSyncVar = "node" + stringpatch::to_string(cur->child->__ID) +
      std::string(cur->child->syncVar->name, sizeof(cur->child->syncVar->name) -1);
    // outfile << curSyncVar << " -> " << nextSyncVar << "[label=ch]\n";
    std::cout << curSyncVar << " -> " << nextSyncVar << "[label=ch] \n";
    //    digraph(outfile, cur->child, level+ "O");
    digraph(cur->child, level+ "O");
  }

  if(cur->cChild != NULL) {
    std::string nextSyncVar = "node" + stringpatch::to_string(cur->cChild->__ID) +
      std::string(cur->cChild->syncVar->name, sizeof(cur->cChild->syncVar->name) - 1);
    // outfile << curSyncVar << " -> " << nextSyncVar << "[label=cc]\n";
    std::cout << curSyncVar << " -> " << nextSyncVar << "[label=cc]\n";
    //digraph(outfile, cur->cChild, level+ "C");
    digraph(cur->cChild, level+ "C");
  }

  if(cur->fChild != NULL) {
    std::string nextSyncVar = "node" + stringpatch::to_string(cur->fChild->__ID) +
      std::string(cur->fChild->syncVar->name, sizeof(cur->fChild->syncVar->name) - 1);
    // outfile << curSyncVar << " -> " << nextSyncVar << "[label=fc]\n";
    std::cout << curSyncVar << " -> " << nextSyncVar << "[label=fc]\n";
    //digraph(outfile, cur->fChild, level+ "F");
    digraph(cur->fChild, level+ "F");
  }
}

static void dotGraph(SyncGraph* root) {
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

/*
static bool clearUses(UseInfoVec uses, VisitedMap* curState) {
  forv_Vec(UseInfo, cur, uses) {
    if(curState->unSyncedUses.in(cur)){
      curState->unSyncedUses.remove(curState->unSyncedUses.index(cur));
    }
  }
}
*/

/*
static int containsVec(SyncGraphVector& list, SyncGraph* node) {
  int i = 0;
  for_vector(SyncGraph, cur, list) {
    if(node == cur)
      return i;
    i++;
  }
  return -1;
}

*/
/*
  This function frees SyncGraph Nodes recursively
*/

static void deleteSyncGraphNode(SyncGraph *node) {
  if (node != NULL) {
    if(node->child != NULL && node->child->parent == node)
      deleteSyncGraphNode(node->child);
    deleteSyncGraphNode(node->fChild);
    deleteSyncGraphNode(node->cChild);
    delete node;
  }
}


/**
   Clean up the Data-Control Graph.
**/
static void cleanUpSyncGraph(SyncGraph *node) {
  forv_Vec(UseInfo, cur, gUseInfos) {
    delete(cur);
  }
  for_vector(VisitedMap, curVisited, gListVisited) {
    delete(curVisited);
  }
  deleteSyncGraphNode(node);
  gAnalysisRoots.clear();
  gUseInfos.clear();
  gListVisited.clear();
  gFinalNodeSet.clear();
  gFuncGraphMap.clear();
  gSyncVars.clear();
}

/**
   recursively make a copy of CFG
   if endPoint is not null we make copy until the endPoint.
 **/
static SyncGraph* copyCFG(SyncGraph* parent, SyncGraph* branch, SyncGraph* endPoint) {
  if(branch == NULL)
    return NULL;
  SyncGraph* newNode = NULL;
  if(parent != NULL)
    newNode = new SyncGraph(branch, parent->fnSymbol, false);
  else
    newNode = new SyncGraph(branch, branch->fnSymbol, false);
  if(branch->child != NULL && branch->child != endPoint) {
    SyncGraph* child = copyCFG(newNode, branch->child, endPoint);
    child->parent  = newNode;
    newNode->child = child;
  }
  if(branch->cChild != NULL) {
    /* TODO: copy until joinNode Only*/
    endPoint =  branch->joinNode;
    SyncGraph* child = copyCFG(newNode, branch->cChild, endPoint);
    child->parent  = newNode;
    newNode->cChild = child;
  }
  if(branch->fChild != NULL && branch->fChild->fnSymbol->hasFlag(FLAG_BEGIN)) {
    SyncGraph* child = copyCFG(NULL, branch->fChild, NULL);
    child->parent  = newNode;
    parent->fChild = child;
  }
 
  return newNode;
}

inline static SyncGraph* getLastNode(SyncGraph* start) {
  SyncGraph* cur = start;
  while(cur ->child != NULL) {
    cur = cur->child;
  }
  return cur;
}


/**
   Expand all internal Function calls. A check has been introduced to avoid infinite loop
   due to recursion.
   root : start point of internal function expansion :
   fnSymbols: list of FnSymbols in the Graph
   stopPoint (optional): We expand the internal Function until we reach this point.
                       default value is NULL.
**/
static void expandAllInternalFunctions(SyncGraph* root, FnSymbolsVec& fnSymbols, SyncGraph* stopPoint) {
  SyncGraph* cur = root;
  while(cur != NULL) {
    if(cur == stopPoint)
      return;
    if(cur->intFuncCall != NULL && cur->expandedFn == false) {
      FnSymbol* curFun = cur->intFuncCall->theFnSymbol();
      SyncGraph* intFuncNode = gFuncGraphMap.get(curFun);
      if(intFuncNode != NULL && fnSymbols.in(curFun) == NULL) {
	//SyncGraph* parentNode = cur->parent;
	int added = fnSymbols.add_exclusive(curFun);
	// expand all internal Functions recursively
	if(added == 1) {
	  expandAllInternalFunctions(intFuncNode, fnSymbols, NULL);
	  FnSymbol* popped = fnSymbols.pop();
	  INT_ASSERT(popped == curFun);
	}
	INT_ASSERT(cur->cChild == NULL && cur->fChild == NULL);
	SyncGraph *oldChild = cur->child;
	SyncGraph* copy = copyCFG(cur, intFuncNode, NULL);
	/* update Pointers */
	copy->parent = cur;
	cur->child = copy;
	SyncGraph* endPoint = getLastNode(copy);
	INT_ASSERT(endPoint != NULL);
	endPoint->child = oldChild;
	oldChild->parent = endPoint;
	cur->expandedFn  = true;
	INT_ASSERT(endPoint != NULL);
	cur = endPoint;
      }
    }
    if(cur->cChild != NULL ) {
      expandAllInternalFunctions(cur->cChild, fnSymbols,cur->cChild->joinNode);
    }
    if(cur->fChild != NULL ) {
      expandAllInternalFunctions(cur->fChild, fnSymbols,stopPoint);
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

/**
   Adding a child node to the current node.
   The FnSymbol passed should be the Function
   that will contain the node.
   This will help us distinguish the child nodes
   that are created due to sync points
   and the ones that are created for embedded Functions.
**/
static SyncGraph* addChildNode(SyncGraph *cur, FnSymbol* fn) {
  SyncGraph* childNode = new SyncGraph(fn);
  childNode->parent = cur;
  if (fn == cur->fnSymbol) {
    cur->child = childNode;
    childNode->syncedScopes.copy(cur->syncedScopes);
  } else {
    cur->fChild = childNode;
    if(fn->hasFlag(FLAG_BEGIN)) {
      childNode->syncedScopes.copy(cur->syncedScopes);
    }
  }
  return childNode;
}


/**
   Add Else child of a conditional Node.
**/
static SyncGraph* addElseChildNode(SyncGraph *cur, FnSymbol *fn) {
  SyncGraph* childNode = new SyncGraph(fn);
  childNode->parent = cur;
  cur->cChild = childNode;
  return childNode;
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
   NOTE : TODO: Also we need to remove syncing with duplicate
   write to the single value.
**/
static SyncGraph* addSyncExprs(Expr *expr, SyncGraph *cur) {
  std::vector<CallExpr*> callExprs;
  collectCallExprs(expr, callExprs);
  FnSymbol* curFun = expr->getFunction();
  for_vector (CallExpr, call, callExprs) {
    if (call->theFnSymbol() != NULL) {
      if (!strcmp(call->theFnSymbol()->name, "=")) {
        SymExpr* symExpr = toSymExpr(call->getNextExpr(call->getFirstExpr()));
        std::string symName;
	Symbol* symPtr;
        if (symExpr != NULL) {
          symName = symExpr->var->name;
	  symPtr = symExpr->var;
        }
        std::vector<CallExpr*> intCalls;
        collectCallExprs(call->theFnSymbol(), intCalls);
        for_vector (CallExpr, intCall, intCalls) {
          if (intCall->theFnSymbol() != NULL) {
            if (!strcmp(intCall->theFnSymbol()->name, "writeEF")) {
	      cur->syncVar = symPtr;
	      gSyncVars.insert(symPtr);
	      cur->syncType = NODE_SYNC_SIGNAL_FULL;
	      cur->syncExpr = call;
	      cur = addChildNode(cur, curFun);
            }
          }
        }
      } else if (!strcmp(call->theFnSymbol()->name, "_statementLevelSymbol")) {
        SymExpr* symExpr = toSymExpr(call->getNextExpr(call->getFirstExpr()));
        std::string symName;
	Symbol* symPtr;
        if (symExpr != NULL) {
          symName = symExpr->var->name;
	  symPtr = symExpr->var;
        }
        std::vector<CallExpr*> intCalls;
        collectCallExprs(call->theFnSymbol(), intCalls);
        for_vector (CallExpr, intCall, intCalls) {
          if (intCall->theFnSymbol() != NULL) {
            if (!strcmp(intCall->theFnSymbol()->name, "readFF")) {
	      cur->syncVar = symPtr;
	      gSyncVars.insert(symPtr);
	      cur->syncType = NODE_SINGLE_WAIT_FULL;
	      cur->syncExpr = call;
	      cur = addChildNode(cur, curFun);
	    } else if (!strcmp(intCall->theFnSymbol()->name, "readFE")) {
	      cur->syncVar = symPtr;
	      gSyncVars.insert(symPtr);
	      cur->syncType = NODE_SYNC_SIGNAL_EMPTY;
	      cur->syncExpr = call;
	      cur = addChildNode(cur, curFun);
	    }
          }
        }
      }
    }
  }
  return cur;
}


/*

static void checkUseInfoSafety(SyncGraph* node, SyncGraphSet& visited) {
  if(node != NULL){
    forv_Vec(UseInfo, cur, node->infoVec) {
      if(visited.find(cur->lastSyncPoint) != visited.end()) {
	//	cur->setChecked();
	provideWarning(cur);
      }
    }
  }
}

static void checkUseInfoSafety(SyncGraphVector& newlyVisited, SyncGraphSet& visited) {
  for_vector(SyncGraph, node, newlyVisited) {
    checkUseInfoSafety(node, visited);
  }
}
*/


static SyncGraph* getNextDominatedNode(SyncGraph* cur) {
  if(cur->cChild == NULL) {
    return cur->child;
  } else {
    return cur->joinNode;
  }
}

/**
   Checks if the node is a sync point. ALready filled single point needs to be skipped.
 **/
static bool isASyncPointSkippingSingles(SyncGraph* cur, SyncGraphSet& filledSinglePoints) {
  if(isASyncPoint(cur)) {
    for_set(SyncGraph, filledSingle, filledSinglePoints) {
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

static bool isASyncPoint(SyncGraph * cur) {
  INT_ASSERT(cur != NULL);
  if(cur->syncType == NODE_SINGLE_WAIT_FULL ||
     cur->syncType == NODE_SYNC_SIGNAL_FULL ||
     cur->syncType == NODE_SYNC_SIGNAL_EMPTY ) {   
    return true;
  }
  return false;
}
 
/*
  Return the next SyncPoint of the current task from the 'start'.
*/
static SyncGraph* nextSyncPoint(SyncGraph* start, bool skipCurrent) {
  SyncGraph *cur =  start;  
  if(skipCurrent){
    cur = getNextDominatedNode(cur);
  }
  while(cur != NULL) {
    if(isASyncPoint(cur))
      return cur;
    cur = getNextDominatedNode(cur);
  }
  return NULL;
}



/*
  Return the next SyncPoint of the current task from the 'start'.
*/
/*
static void collectNextSyncPoints(SyncGraph* start, SyncGraphVector& nextSyncPoints, SyncGraphVector& syncedSingle, bool skipCurrent = false) {
  SyncGraphVector curList;
  unsigned int pos = 0;
  nextSyncPoints.clear();
  if(skipCurrent) {
    if(start->cChild != NULL) {
      curList.push_back(start->cChild);
    }
    if(start->child !=NULL) {
      curList.push_back(start->child);
    }
  } else {
    curList.push_back(start);
  }
  while(pos < curList.size()) {
    SyncGraph* cur = curList.at(pos);
      while(cur != NULL) {
	if(isASyncPoint(cur, syncedSingle)) {
	  if(containsVec(nextSyncPoints, cur) == -1)
	    nextSyncPoints.push_back(cur);
	  break;
	}
	if(cur->cChild != NULL) {
	  curList.push_back(cur->cChild);
	}
	cur = cur->child;
      }
      pos ++;
  }
}

*/

static void updateUnsafeUseInfos(VisitedMap* curVisited, SyncGraphVector& newlyRemoved, UseInfoVec& useInfos) {
  // TODO currently we are synying by the function later we
  // should sync by the scope.
  //  useInfos.insert(curVisited->useInfos.begin(), curVisited->useInfos.end());
  UseInfoVec::iterator it;
  for_vector(SyncGraph, curRemoved, newlyRemoved) {
    FnSymbol *parentFn = curRemoved->fnSymbol;
    bool safeUse  = false;
    for(it=curVisited->useInfos.begin() ; it < curVisited->useInfos.end(); it++ ) {
      if(*it->fnSymbol == parentFn) {
	// the sync point is same as that of the variable in use
	// so variable is safe in this pass.
	safeUse = true;
      }
      if(safeUse == false) {
	// NOT SAFE... not yet
	useInfos.push_back(*it);
      }
    }
  }
}

/**
   This Function recursively collects all begins statements between 'root' and all 'endPoints' and add the first
   'SyncPoint' of the begin statement in 'taskPoints'. If the begin function does not contain any 'syncPoint' we will
   not add them to the 'taskPoints' but any begin statement originating from this begin which has a 'syncPoint'
   will be added.
**/
static void collectAllAvailableSyncPoints(VisitedMap* curVisited, SyncGraphVector& newlyRemoved, SyncGraphSet& partialSet, SyncGraphVector& newlyVisited, UseInfoVec useInfos) {
  SyncGraphSet vSingles;
  // SyncGraphSet visited;

  if(newlyRemoved.size() == 0)
    return;
  updateUnsafeUseInfos(curVisited, newlyRemoved, useInfos);

  if(curVisited != NULL) {
    vSingles.insert(curVisited->vSingles.begin(),curVisited->vSingles.end());
    // visited.insert(curVisited->lVisited.begin(), curVisited->lVisited.end());
    useInfos.push_back(curVisited);
  }

  if(newlyVisited.size() > 0) {
    if(newlyVisited.front()->syncType == NODE_SINGLE_WAIT_FULL ||
       newlyVisited.back()->syncType == NODE_SINGLE_WAIT_FULL)
      vSingles.insert(newlyVisited.front());
  }
  
  unsigned int i = 0;
  SyncGraph* cur;
  while(i < newlyRemoved.size()) {
    cur = newlyRemoved.at(i);
    i++;
    while(cur != NULL) {
      if(cur->fChild != NULL && cur->fChild->fnSymbol->hasFlag(FLAG_BEGIN)) {
	if(isASyncPointSkippingSingles(cur->fChild, vSingles)) {
	  partialSet.insert(cur->fChild);	  
	} else {
	  newlyRemoved.push_back(cur->fChild);
	  useInfos.insert(useInfos.end(), cur->fChild->extVarInfoVec.begin(), cur->fChild->extVarInfoVec.end());
	}
      }
      
      if(cur->cChild != NULL) {
	SyncGraphVector partialRemoved(newlyRemoved.begin()+i, newlyRemoved.end());
	SyncGraphSet newPartialSet(partialSet.begin(), partialSet.end());
	UseInfoVec newUseInfoVec(useInfos.begin(),useInfos.end());
	if(isASyncPointSkippingSingles(cur->cChild, vSingles)) {
	  newPartialSet.insert(cur->cChild);
	} else {
	  partialRemoved.push_back(cur->cChild);
	}
	collectAllAvailableSyncPoints(curVisited, partialRemoved, newPartialSet, newlyVisited, newUseInfoVec);
      }

      if(cur->child != NULL) {
	if(isASyncPointSkippingSingles(cur->child, vSingles, visited)) {
	  partialSet.insert(cur->child);
	  break;
	}
      }
      cur = cur->child;
      useInfos.insert(useInfos.end(), cur->extVarInfoVec.begin(), cur->extVarInfoVec.end());
    }
  }
  
  if(partialSet.size() >  0 && alreadyVisited(partialSet) == false) {
      VisitedMap* newVisit = new VisitedMap(curVisited, newlyVisited, partialSet, vSingles, useInfos);
      gListVisited.push_back(newVisit);
  } else if(partialSet.size() == 0) {
    if(useInfos.size() > 0) {
      for_vector(UseInfo, cur, useInfos) {
	provideWarnings(cur);
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
	     "Potential unsafe (use after free) use of variable %s here. Please make sure the variable use is properly synced.",
	     var->varName.c_str());
  }
}




/**
   Returns true if the 'source' and 'dest' nodes matches.
**/
static bool sync(SyncGraph* source, SyncGraph* dest) {
  bool compatible = false;
  switch(source->syncType) {
  case NODE_SINGLE_WAIT_FULL:
    if(dest->syncType == NODE_SYNC_SIGNAL_FULL)
      compatible = true;
    break;

  case NODE_SYNC_SIGNAL_FULL:
    if(dest->syncType == NODE_SYNC_SIGNAL_EMPTY ||
       dest->syncType == NODE_SINGLE_WAIT_FULL)
      compatible = true;
    break;

  case NODE_SYNC_SIGNAL_EMPTY:
    if(dest->syncType == NODE_SYNC_SIGNAL_FULL)
      compatible = true;
    break;

  default:
    return false;
  }
  if(compatible)
    if(dest->syncVar == source->syncVar) {
      return true;
    }
  return false;
}









/**
   Collects all SyncPoints that can be used to sync with 'source' node from 'potentialDest'
   into 'syncPoints'.
**/
static void getSyncPoints(SyncGraph* source, SyncGraphVector& potentialDest, SyncGraphVector& syncPoints) {
  for_vector(SyncGraph, dest, potentialDest) {
    if(sync(source,dest)) {
      syncPoints.push_back(dest);
    }
  }
}


/**
   Since single variables once filled remians as such, we need to handle them seperately.
   Here once, we find a matching syncNode we bypass all syncPoints involving that single variable
**/
static bool handleSingleSyncing(SyncGraphVector& syncPoints, SyncGraphVector& destSyncPoints, VisitedMap *curVisited, UseInfoVec & useInfos) {
  // Single Nodes need not be pulled back as
  // once they are filled they remain filled and
  // we don't have any advantage for pulling it back.
  getSyncPoints(syncPoints.front(), destSyncPoints, syncPoints);
  INT_ASSERT(syncPoints.front()->syncType == NODE_SINGLE_WAIT_FULL ||
	     syncPoints.back()->syncType == NODE_SINGLE_WAIT_FULL);
  SyncGraphSet partialSet;
  partialSet.insert(curVisited->destPoints.begin(), curVisited->destPoints.end());
  for_vector(SyncGraph, curSingle, syncPoints) {
    partialSet.erase(curSingle);
  }
  SyncGraphVector newlyVisited(syncPoints.begin(), syncPoints.end());
  collectAllAvailableSyncPoints(curVisited, syncPoints, partialSet, newlyVisited);
  return true;
}


static bool threadedMahjong(void) {
  SyncGraphVector syncPoints;
  unsigned int i=0;
  // TODO update useInfos
  UseInfoVec useInfos;
  while(i < gListVisited.size()) {
    VisitedMap *curVisited =  gListVisited.at(i);
    SyncGraphSet destPoints = curVisited->destPoints;
    for_set(SyncGraph, sourceSyncPoint, destPoints) {
      SyncGraphVector destSyncPoints(destPoints.find(sourceSyncPoint), 
				     destPoints.end());
      syncPoints.clear();
      // CASE 2 & 3
      getSyncPoints(sourceSyncPoint, destSyncPoints, syncPoints);
      if(syncPoints.size() > 0) {
	if(sourceSyncPoint->syncType == NODE_SINGLE_WAIT_FULL ||
	   syncPoints.front()->syncType == NODE_SINGLE_WAIT_FULL) {
	  // CASE 1
	  handleSingleSyncing(syncPoints, destSyncPoints, curVisited); 
	  //  checkUseInfoSafety(syncPoints, curVisited->lvisited);
	} else {
	  //  checkUseInfoSafety(sourceSyncPoint, curVisited->lvisited);
	  SyncGraphSet partialSet(curVisited->destPoints.begin(), 
				  curVisited->destPoints.end());
	  partialSet.erase(sourceSyncPoint);
	  SyncGraphVector newlyMatched;
	  newlyMatched.push_back(sourceSyncPoint);
	  for_vector(SyncGraph, destSyncPoint, syncPoints) {
	    //  checkUseInfoSafety(destSyncPoint, curVisited->lvisited);
	    partialSet.erase(destSyncPoint);
	    newlyMatched.push_back(destSyncPoint);
	    SyncGraphVector newlyVisited(newlyMatched.begin(), newlyMatched.end());
	    collectAllAvailableSyncPoints(curVisited, newlyMatched, partialSet, newlyVisited);
	    newlyMatched.pop_back();
	    partialSet.insert(destSyncPoint);
	  }
	}
      } else {
	// if combined CASE 2 and CASE 3 fails try separate
	// case 2 if sync node is empty.
	SyncGraphVector newlyMatched;
	newlyMatched.push_back(sourceSyncPoint);
	SyncGraphSet partialSet(curVisited->destPoints.begin(), 
				curVisited->destPoints.end());
	partialSet.erase(sourceSyncPoint);
	SyncGraphVector newlyVisited(newlyMatched.begin(), newlyMatched.end());
	if (curVisited->getSymbolState(sourceSyncPoint->syncVar) == SYMBOL_STATE_EMPTY
	    && sourceSyncPoint->syncType == NODE_SYNC_SIGNAL_FULL) {
	  
	  collectAllAvailableSyncPoints(curVisited, newlyMatched, partialSet, newlyVisited);
	}
	if (curVisited->getSymbolState(sourceSyncPoint->syncVar) == SYMBOL_STATE_EMPTY
	    && sourceSyncPoint->syncType == NODE_SYNC_SINGLE_FULL) {
	collectAllAvailableSyncPoints(curVisited, newlyMatched, partialSet, newlyVisited);
	}
	// case 3 if sync node is full
	if (curVisited->getSymbolState(sourceSyncPoint->syncVar) == SYMBOL_STATE_FULL &&
	    sourceSyncPoint->syncType == NODE_SYNC_SIGNAL_EMPTY) {
	  collectAllAvailableSyncPoints(curVisited, newlyMatched, partialSet, newlyVisited);
	}
      }
    }
    i++;
  }
  return false;
}


/*
static void setNextSyncNode() {
  //  SyncGraphSet dummySet;
    forv_Vec(UseInfo, cur, gUseInfos) {
      SyncGraph* syncPoint = nextSyncPoint(cur->useNode, false);
      if(syncPoint  == NULL) {
	provideWarning(cur);
      } else {
	//	cur->setNextSyncNode(syncPoint);
	syncPoint->infoVec.add(cur);
      }

      #ifdef CHPL_DOTGRAPH
      if(syncPoint != NULL) {
	std::cout<< "The Next sync Node is node"<<stringpatch::to_string(syncPoint->__ID)
		 <<syncPoint->syncVar->name<<std::endl; 
      }
      #endif
    }
}

static void setLastSyncNode() {
  //  SyncGraphSet dummySet;
   forv_Vec(UseInfo, info, gUseInfos) {
    SyncGraph* curNode = info->useNode;
    INT_ASSERT(curNode->fnSymbol  != info->fnSymbol);
    while (curNode != NULL && curNode->fnSymbol  != info->fnSymbol) {
      curNode = curNode->parent;
    }
    INT_ASSERT(curNode != NULL);
    SyncGraph* nextSyncNode = nextSyncPoint(curNode, false);
    SyncGraph* syncNode = NULL;
    while(nextSyncNode != NULL) {
      syncNode = nextSyncNode;
      nextSyncNode = nextSyncPoint(nextSyncNode, true);
    }
    if(syncNode == NULL) {
      provideWarning(info);
    } else {
      info->setLastSyncNode(syncNode);
      gFinalNodeSet.insert(syncNode);
    }
   }
}

*/

static void checkOrphanStackVar(SyncGraph* root) {
  //bool checkedAll = true;
  //  setNextSyncNode();
  // setLastSyncNode();
  // forv_Vec(UseInfo, cur , gUseInfos) {
  //  if(! cur->isChecked()) {
  //   checkedAll = false;
  //  break;
  //  }
  //}

  //  if(checkedAll)
  //  return;
  SyncGraphVector startPointVec;
  SyncGraphSet destSyncPoints;
  SyncGraph* startPoint = root;
  UseInfoVec useinfos;
  while(isASyncPoint(startPoint) == true) {
    startPoint = startPoint->child;
  } 
  startPointVec.push_back(startPoint);
  //  SyncGraphVectorVec destSyncPoints;
  // destSyncPoints.insert(endPoints);
  SyncGraphVector dummy;
  // TODOcheck if root's infovec is ever added.
  collectAllAvailableSyncPoints(NULL, startPointVec, destSyncPoints, dummy, useInfos);
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
    if (argSym->intent == INTENT_REF) {
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
   If its an external Variable to the base function we return NULL.
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
      if (argSym->intent == INTENT_REF) {
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
   checks if the expression expr refers any external variables.
   if Yes add it to current list.
**/
static bool  refersExternalSymbols(Expr* expr, SyncGraph* cur) {
  std::vector<SymExpr*> symExprs;
  collectSymExprs(expr, symExprs);
  for_vector (SymExpr, se, symExprs) {
    Symbol* sym = se->var;
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
   Add use of external variable details to 'node'.
**/
static void addExternVarDetails(FnSymbol* fn, std::string v, SymExpr* use, SyncGraph* node) {
  if(compareScopes(fn->body,gFnSymbolRoot->body) != 1)
    fn = gFnSymbolRoot;
  /*
    IMP: if the symbol root is beyond the gFnSymbolRoot it means the symbol was an argument 
    to the base function. In that case if the symbol is used in the base function, we need 
    not consider is as an external variable.
   */
  if(node->fnSymbol != fn) {
    UseInfo * newUseInfo = new UseInfo(node, fn, use, v);
    gUseInfos.add(newUseInfo);
  }
}


/**
   Add external Variables, begin Nodes, external function calls etc
   to 'cur'.
**/
static SyncGraph* addSymbolsToGraph(Expr* expr, SyncGraph *cur) {
  std::vector<SymExpr*> symExprs;
  collectSymExprs(expr, symExprs);
  for_vector (SymExpr, se, symExprs) {
    Symbol* sym = se->var;
    if (!(isSyncType(sym->type)) &&
	!(isSingleType(sym->type)) &&
	isOuterVar(sym, expr->getFunction())) {
      BlockStmt* block = getOriginalScope(sym);
      if(shouldSync(block, cur)) {
        addExternVarDetails(block->getFunction(), sym->name, se, cur);
	// cur->contents.add_exclusive(se);
	// cur->syncScope.add(block);
      }
    }
  }
  /**collect calls to functions **/
  std::vector<CallExpr*> callExprs;
  collectCallExprs(expr, callExprs);
  for_vector (CallExpr, call, callExprs) {
    FnSymbol* caleeFn = call->theFnSymbol();
    if (caleeFn != NULL && !(caleeFn->hasFlag(FLAG_BEGIN))
        && (caleeFn->getModule()->modTag == MOD_USER)
        && isFnSymbol(caleeFn->defPoint->parentSymbol)) {
      // Non begin used mod function could be an internal function
      // Number of calls to embedded functions should not be more than 1.
      INT_ASSERT(cur->intFuncCall == NULL);
      cur->intFuncCall = call; // Not assured to be embedded function call.
    }
  }
  if(cur->intFuncCall != NULL )
    cur = addChildNode(cur, cur->fnSymbol);
  
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
static BlockStmt* getSyncBlockStmt(BlockStmt* block, SyncGraph *cur) {
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
   The 'block' represents the scope of external variable. Once the information
   about the block is provided the Function returns true if the use of the
   external variable should considered as potentially unsafe (true).

   False means use of the external variable is safe.
**/
static bool shouldSync(Scope* block, SyncGraph *cur) {
  // TODO : this should handle all cases where the
  // scope of declaration function fn is beyond
  // a sync statement then we need not worry  about
  // syncing it.

  if(block == NULL &&  gAllCallsSynced == true) {
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


/**
   The handle function are used the build the sync graph network where
   we collect information about sync points, external variable use and
   begin statements.
**/
static SyncGraph* handleSyncStatement(Scope* block, SyncGraph* cur) {
  cur->syncedScopes.add(block);
  cur = handleBlockStmt(block,cur);
  cur->syncedScopes.pop();
  return cur;
}

static SyncGraph* handleBranching(SyncGraph* start, SyncGraph* end,  SyncGraph* ifNode, SyncGraph* elseNode) {
  elseNode->child = end;
  start->joinNode = end;
  // end->isjoinNode = true;
  end->parent = ifNode;

  return end;
}

static SyncGraph* handleCondStmt(CondStmt* cond, SyncGraph* cur) {
  BlockStmt* thenBlock = cond->thenStmt;
  BlockStmt* elseBlock = cond->elseStmt;
  SyncGraph* startBranch = cur;
  cur = addChildNode(cur, cur->fnSymbol);
  SyncGraph* ifNode = handleBlockStmt(thenBlock,cur);
  SyncGraph* endBranch  = addChildNode(ifNode, ifNode->fnSymbol);
  SyncGraph* elseNode = addElseChildNode(startBranch, startBranch->fnSymbol);
  if(elseBlock != NULL) {
    if( ASTContainsBeginFunction(elseBlock) ||
	refersExternalSymbols(elseBlock, startBranch) ) {
      elseNode = handleBlockStmt(elseBlock,elseNode);
    }
  }
  handleBranching(startBranch, endBranch,  ifNode, elseNode);
  return endBranch;
}

static SyncGraph* handleLoopStmt(BlockStmt* block,SyncGraph* cur) {
  // TODO
  if(ASTContainsBeginFunction(block) == true || refersExternalSymbols(block, cur)) {
    for_alist (node, block->body) {
      cur = handleExpr(node, cur);
    }
  }
  return cur;
}

static SyncGraph* handleDefExpr(DefExpr* def, SyncGraph *cur) {
  if (isFnSymbol(def->sym)) {
    FnSymbol* fn = toFnSymbol(def->sym);
    if (fn->hasFlag(FLAG_BEGIN)) {
      handleBegin(fn, cur);
      cur->syncType = NODE_BLOCK_BEGIN;
    } else {
      handleFunction(fn, cur);
      cur->syncType = NODE_BLOCK_INTERNAL_FUNCTION;
    }
    INT_ASSERT(fn != def->getFunction());
    //    INT_ASSERT(cur->fnSymbol == def->getFunction());
    //    cur = addChildNode(cur, def->getFunction());
    cur = addChildNode(cur, cur->fnSymbol);
  } else {
    //     addSymbolsToGraph(def, cur);
  }
  return cur;
}



static SyncGraph* handleBlockStmt(BlockStmt* stmt, SyncGraph *cur) {
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
        if(syncBlock !=  NULL) {
          handled = true;
          cur = handleSyncStatement(syncBlock, cur);
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

static SyncGraph* handleCallExpr(CallExpr* callExpr, SyncGraph *cur) {
  if (callExpr->isNamed("begin_fn")) {
    //   Auto created call no need to add.
  } else {
    cur = addSymbolsToGraph(callExpr, cur);
  }
  return cur;
}

static SyncGraph* handleExpr(Expr* expr, SyncGraph *cur){
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


static SyncGraph* handleBegin(FnSymbol* fn, SyncGraph* cur) {
  SyncGraph* childNode = addChildNode(cur, fn);
  gFuncGraphMap.put(fn,childNode);
  handleBlockStmt(fn->body, childNode);
  return cur;
}

static SyncGraph* handleFunction(FnSymbol* fn, SyncGraph *cur) {
  SyncGraph* newNode = NULL;
  if (cur == NULL) {
    newNode = cur  = new SyncGraph(fn);
    gAnalysisRoots.push_back(newNode);
  } else {
    // Internal Function node.
    newNode = addChildNode(cur, fn);
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
  // TODO change it to maps.
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

  //  isInsideSyncStmt(NULL);
  forv_Vec (FnSymbol, fn, aFnSymbols) {
     //for_vector(FnSymbol, fn, aFnSymbols) {
    gFnSymbolRoot = fn;
    checkSyncedCalls(fn);
    SyncGraph* syncGraphRoot = handleFunction(fn, NULL);
    #ifdef CHPL_DOTGRAPH
    dotGraph(syncGraphRoot);
    #endif
    FnSymbolsVec fnSymbols;
    fnSymbols.add(fn);
    expandAllInternalFunctions(syncGraphRoot, fnSymbols, NULL);
    checkOrphanStackVar(syncGraphRoot);
    cleanUpSyncGraph(syncGraphRoot);
  }
}
