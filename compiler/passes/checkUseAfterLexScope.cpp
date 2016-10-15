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
//#define CHPL_DOTGRAPH
#ifdef CHPL_DOTGRAPH
#include <fstream>
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

struct SyncGraph {
  Vec<SymExpr*>  contents;
  Vec<BlockStmt*> syncScope;
  Vec<CallExpr*> intFuncCalls;
  ScopeVec syncedScopes;    // These are the already defined sync points
                            // created due to sync statments, Cobegin, Coforall
                            // and Forall statments.
  UseInfoVec infoVec;
  std::string syncVar;
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
  bool isjoinNode;
  SyncGraph(SyncGraph* i, FnSymbol *f) {
    fnSymbol = i->fnSymbol;
    contents.copy(i->contents);
    infoVec.copy(i->infoVec);
    syncedScopes.append(i->syncedScopes);
    loopNode = i->loopNode;
    conditionalNode = i->conditionalNode;
    syncType = i->syncType;
    syncVar = i->syncVar;
    joinNode = i->joinNode;
    isjoinNode = i->isjoinNode;
  }

  SyncGraph(FnSymbol *f) {
    fnSymbol = f;
    child = NULL;
    fChild = NULL;
    cChild = NULL;
    syncType = NODE_UNKNOWN;
    loopNode = false;
    conditionalNode = false;
    isjoinNode = false;
    joinNode = NULL;
  }
  ~SyncGraph() {}
};

struct UseInfo {
  SymExpr* usePoint;
  SyncGraph* useNode;
  FnSymbol* fnSymbol;
  SyncGraph* lastSyncPoint;
  SyncGraph* nextSyncPoint;
  std::string varName;
  bool checked;

  UseInfo(SyncGraph *node, FnSymbol* fn, SymExpr* expr, std::string name) {
    usePoint = expr;
    useNode = node;
    varName = name;
    lastSyncPoint = NULL;
    nextSyncPoint =  NULL;
    checked = false;
  }

  void setChecked(){
    checked = true;
  }

  bool  isChecked(){
    return checked;
  }

  void setNextSyncNode(SyncGraph* node) {
    nextSyncPoint = node;
  }

  void setLastSyncNode(SyncGraph *node) {
    lastSyncPoint = node;
  }

  bool inherentlyUnSafe() {
    if(checked)
      return false;
    if(lastSyncPoint == NULL || nextSyncPoint == NULL){
      setChecked();
      return true;
    }
    return false;
  }  
};



typedef std::vector<SyncGraph*> SyncGraphVec;
typedef std::vector<SyncGraphVec&> SyncGraphVecVec;
typedef std::vector<SyncGraph*>::iterator SGI; 
typedef Map<FnSymbol*, SyncGraph*> FnSyncGraphMap;
typedef Map<FnSymbol*, Vec<SyncGraph*>* > FnSyncGraphVecMap;
typedef Vec<FnSymbol*> FnSymbolsVec;
static SyncGraphVec analysisRoots; // We will be creating multiple root for
                                   //  analyzing recursion and loops more
                                   // efficiently

typedef std::set<SyncGraph*> SyncGraphSet;

struct VisitedMap {
  SyncGraphSet destPoints;
  SyncGraphSet visited;
  SyncGraphSet vSingles;
  VisitedMap() {
    
  }

  VisitedMap(VisitedMap& prev, SyncGraphVec& newlyVisited, SyncGraph* single = NULL) {
    destPoints = SyncGraphSet(prev.destPoints);
    visited = SyncGraphSet(prev.visited);
    vSingles = SyncGraphSet(prev.vSingles);
    if(single != NULL)
      vSingles.insert(single);
    for_vector(SyncGraph, cur, newlyVisited) {
      visited.insert(cur);
      destPoints.erase(cur);
    }
  }
  
  std::set<SyncGraph*> addtoVisited(SyncGraphVec& newSet) {
    for_vector(SyncGraph, cur, newSet) {
      visited.insert(cur);
      destPoints.erase(cur);
    }
  }

  bool operator==(const std::set<SyncGraph*>& dest) {
    if(destPoints == dest) {
      return true;
    } else {
      return false;
    }
  }
};

struct std::vector<VisitedMap*> visited;

static bool alreadyVisited(SyncGraphMap& dest) {

  for_vector(VisitedMap, curMap, visited) {
    if(curMap == dest) {
      return true;
    }
  }
  return false;
}



UseInfoVec useInfos;
static SyncGraphVec filledSinglePoints; // filled Single variables.

static FnSyncGraphMap funcGraphMap; // start point of each function in Sync Graph
static bool allCallsSynced;
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
static ArgSymbol*  getTheArgSymbol(std::string sym, FnSymbol* parent);
static BlockStmt* getSyncBlockStmt(BlockStmt* def, SyncGraph *cur);
static bool isInsideSyncStmt(Expr* expr);
static bool shouldSync(Scope* scope, SyncGraph* cur);
static void checkSyncedCalls(FnSymbol* fn);
static int compareScopes(Scope* a, Scope * b);
static SyncGraph* addElseChildNode(SyncGraph *cur, FnSymbol *fn);
static bool  refersExternalSymbols(Expr* expr, SyncGraph * cur);
static bool  ASTContainsBeginFunction(BaseAST* ast);
static void expandAllInternalFunctions(SyncGraph* root,FnSymbolsVec &fnSymbols, SyncGraph* endPoint = NULL);
static SyncGraph* inlineCFG(SyncGraph* inlineNode, SyncGraph* branch);
static void addExternVarDetails(FnSymbol* fn, std::string v,SymExpr* use, SyncGraph* node) ;
static SyncGraphVec getCopyofGraph(SyncGraph* start, FnSymbol* f);
static void provideWarning(UseInfo* var);
static bool sync(SyncGraph* source, SyncGraph* dest);
static void getSyncPoints(SyncGraph* source, SyncGraphVec& potentialDest, SyncGraphVec& syncPoints);


static bool threadedMahjong(SyncGraphVec& destSyncPoints);

static bool handleSingleSyncing( SyncGraphVec& syncPoints, VisitedMap& curVisited);
static SyncGraph* nextSyncPoint(SyncGraph* start, bool skipCurrent, VisitedMap& curVisited);
static void collectAllAvailableSyncPoints(VisitedMap& curVisited, VisitedMap& curVisited);
static void nextSyncPoints(SyncGraph*start, bool skipCurrent, VisitedMap& curVisited);


static void checkUseInfoSafety(SyncGraph* node, SyncGraphSet& visited);
static void checkUseInfoSafety(SyncGraphVec& newlyVisited, SyncGraphSet& visited);



static void setNextSyncNode();
static void setLastSyncNode();
static SyncGraph* getNextDominatedNode(SyncGraph* cur);
static bool isASyncPoint(SyncGraph* cur);
static int containsVec(SyncGraphVec& list, SyncGraph* cur);
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
  std::string curSyncVar = level + cur->syncVar;
  if(cur->child != NULL) {
    std::string nextSyncVar = level + "O" +cur->child->syncVar;
    // outfile << curSyncVar << " -> " << nextSyncVar << "[label=ch]\n";
    std::cout << curSyncVar << " -> " << nextSyncVar << "[label=ch] \n";
    //    digraph(outfile, cur->child, level+ "O");
    digraph(cur->child, level+ "O");
  }

  if(cur->cChild != NULL) {
    std::string nextSyncVar = level + "C" + cur->cChild->syncVar;
    // outfile << curSyncVar << " -> " << nextSyncVar << "[label=cc]\n";
    std::cout << curSyncVar << " -> " << nextSyncVar << "[label=cc]\n";
    //digraph(outfile, cur->cChild, level+ "C");
    digraph(cur->cChild, level+ "C");
  }

  if(cur->fChild != NULL) {
    std::string nextSyncVar = level + "F" + cur->fChild->syncVar;
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

static int containsVec(SyncGraphVec& list, SyncGraph* node) {
  int i = 0;
  for_vector(SyncGraph, cur, list) {
    if(node == cur)
      return i;
    i++;
  }
  return -1;
}


/*
  This function frees SyncGraph Nodes recursively
*/
static void deleteSyncGraphNode(SyncGraph *node) {
  if (node != NULL) {
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
  forv_Vec(UseInfo, cur, useInfos) {
    delete(cur);
  }
  deleteSyncGraphNode(node);
  analysisRoots.clear();
  useInfos.clear();
}

/*
  This function is used for creating a copy of function to inline
  the internal functions that are called from begins.
*/
static SyncGraphVec getCopyofGraph(SyncGraph* start, FnSymbol* f) {
  /**
     TODO decide what to de when we have a fChild here
  **/
  SyncGraphVec copy;
  SyncGraph* node = start;
  while (node != NULL) {
    SyncGraph * newnode = new SyncGraph(node, f);
    if (copy.size() > 0) {
      newnode->parent = copy.back();
      copy.back()->child = newnode;
    }
    copy.push_back(node);
  }
  return copy;
}


/**
   Inline the internal function with a copy generated using 'getCopyofGraph(...)'.
   // TODO :verify
**/
static SyncGraph* inlineCFG(SyncGraph* inlineNode, SyncGraph* branch) {
  if (inlineNode) {
    SyncGraph *oldChild = inlineNode->child;
    SyncGraphVec copy = getCopyofGraph(branch, inlineNode->fnSymbol);
    if (copy.size() > 0) {
      inlineNode->child = copy.front();
      copy.front()->parent = inlineNode;
      (copy.back())->child = oldChild;
      oldChild->parent = copy.back();
    }
    return copy.back();
  }
  return NULL;
}


/**
   Expand all internal Function calls. A check has been introduced to avoid infinite loop
   due to recursion.
**/
static void expandAllInternalFunctions(SyncGraph* root, FnSymbolsVec& fnSymbols, SyncGraph* endPoint) {
  SyncGraph* cur = root;
  SyncGraphVec endPoints;
  while(cur != NULL) {
    if(cur == endPoint)
      return;
    if(cur->intFuncCalls.count() != 0) {
      forv_Vec(CallExpr, fnCall, cur->intFuncCalls) {
        FnSymbol* curFun = fnCall->theFnSymbol();
        SyncGraph* intFuncNode = funcGraphMap.get(curFun);
        if(intFuncNode != NULL && fnSymbols.in(curFun) == NULL
           && fnSymbols.add_exclusive(curFun) == 1 ) {
          SyncGraph* endPoint = inlineCFG(cur, intFuncNode);
          endPoints.push_back(endPoint);
        }
      }
    }

    if(cur->cChild != NULL ) {
      expandAllInternalFunctions(cur->cChild, fnSymbols,cur->cChild->joinNode);
    }

    if(cur->fChild != NULL && cur->fChild->fnSymbol->hasFlag(FLAG_BEGIN)) {
      expandAllInternalFunctions(cur->fChild, fnSymbols);
    }

    if(endPoints.back() == cur) {
      fnSymbols.pop();
      endPoints.pop_back();
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
**/
static int compareScopes(Scope* a, Scope* b) {
  if(a == b) {
    return 1;
  }
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
        if (symExpr != NULL) {
          symName = symExpr->var->name;
        }
        std::vector<CallExpr*> intCalls;
        collectCallExprs(call->theFnSymbol(), intCalls);
        for_vector (CallExpr, intCall, intCalls) {
          if (intCall->theFnSymbol() != NULL) {
            if (!strcmp(intCall->theFnSymbol()->name, "writeEF")) {
	      cur->syncVar = symName;
	      cur->syncType = NODE_SYNC_SIGNAL_FULL;
	      cur->syncExpr = call;
	      cur = addChildNode(cur, curFun);
            }
          }
        }
      } else if (!strcmp(call->theFnSymbol()->name, "_statementLevelSymbol")) {
        SymExpr* symExpr = toSymExpr(call->getNextExpr(call->getFirstExpr()));
        std::string symName;
        if (symExpr != NULL) {
          symName = symExpr->var->name;
        }
        std::vector<CallExpr*> intCalls;
        collectCallExprs(call->theFnSymbol(), intCalls);
        for_vector (CallExpr, intCall, intCalls) {
          if (intCall->theFnSymbol() != NULL) {
            if (!strcmp(intCall->theFnSymbol()->name, "readFF")) {
	      cur->syncVar = symName;
	      cur->syncType = NODE_SINGLE_WAIT_FULL;
	      cur->syncExpr = call;
	      cur = addChildNode(cur, curFun);
	    } else if (!strcmp(intCall->theFnSymbol()->name, "readFE")) {
	      cur->syncVar = symName;
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




static void checkUseInfoSafety(SyncGraph* node, SyncGraphVec& visited) {
  if(node != NULL){
    forv_Vec(UseInfo, cur, node->infoVec) {
      if(!cur->isChecked() && containsVec(visited, cur->lastSyncPoint) != -1) {
	cur->setChecked();
	provideWarning(cur);
      }
    }
  }
}

static void checkUseInfoSafety(SyncGraphVec& newlyVisited, SyncGraphVec& visited) {
  for_vector(SyncGraph, node, newlyVisited) {
    checkUseInfoSafety(node, visited);
  }
}

static SyncGraph* getNextDominatedNode(SyncGraph* cur) {
  if(cur->cChild == NULL) {
    return cur->child;
  } else {
    return cur->joinNode;
  }
}

static bool isASyncPoint(SyncGraph * cur) {
  if(cur->syncType == NODE_SINGLE_WAIT_FULL ||
     cur->syncType == NODE_SYNC_SIGNAL_FULL ) {
    bool found = false;
    for_vector(SyncGraph, filledSingle, filledSinglePoints) {
      if(cur->syncVar.compare(filledSingle->syncVar) == 0) {
	found = true;
	break;
      }
    }
    if(!found)
      return true;
  }
  if(cur->syncType ==  NODE_SYNC_SIGNAL_FULL ||
     cur->syncType == NODE_SYNC_SIGNAL_EMPTY) {
    return true;
  }
  return false;
}
 
/*
  Return the next SyncPoint of the current task from the 'start'.
*/
static SyncGraph* nextSyncPoint(SyncGraph* start, bool skipCurrent = false) {
  SyncGraph * cur =  start;  
  if(skipCurrent){
    visited.push_back(cur);
    cur = getNextDominatedNode(cur);
  }
  while(cur != NULL) {
    if(isASyncPoint(cur))
      return cur;
    visited.push_back(cur);
    cur = getNextDominatedNode(cur);
  }
  return NULL;
}



/*
  Return the next SyncPoint of the current task from the 'start'.
*/
static void nextSyncPoints(SyncGraph* start, SyncGraphVec& nextSyncPoints, SyncGraphVec& syncPoints, bool skipCurrent = false) {
  SyncGraphVec curList;
  unsigned int pos = 0;
  nextSyncPoints.clear();
  if(skipCurrent) {
    visited.push_back(start);
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
	if(isASyncPoint(cur)) {
	  if(containsVec(nextSyncPoints, cur) == -1)
	    nextSyncPoints.push_back(cur);
	  break;
	}
	visited.push_back(cur);
	if(cur->cChild != NULL) {
	  curList.push_back(cur->cChild);
	}
	cur = cur->child;
      }
      pos ++;
  }
}



/**
   This Function recursively collects all begins statements between 'root' and all 'endPoints' and add the first
   'SyncPoint' of the begin statement in 'taskPoints'. If the begin function does not contain any 'syncPoint' we will
   not add them to the 'taskPoints' but any begin statement originating from this begin which has a 'syncPoint'
   will be added.
**/
static void collectAllAvailableSyncPoints(SyncGraph* root, SyncGraphVecVec& destSyncPoints, int pos) {
  SyncGraph* cur  = root;
  SyncGraphVec syncPoints;
  SyncGraphVec endPoints;
  // TODO
  while (cur != NULL && !isASyncNode(cur)) {
    if (cur->fChild != NULL && cur->fChild->fnSymbol->hasFlag(FLAG_BEGIN)) {
      SyncGraph* newBegin = cur->fChild;
      nextSyncPoints(newBegin, syncPoints);
      for_vector(SyncGraph, syncPoint, syncPoints) {
	if(syncPoint != NULL) {
	  taskPoints.push_back(syncPoint);
	}
	collectAllAvailableBeginGraphs(newBegin, destSync);
      }
    }
    if(cur->cChild!= NULL) {
      collectAllAvailableBeginGraphs(cur->cChild, endPoints, taskPoints, visited);
    }
    cur = cur->child;
  }
  return;
}


/**
   This Function is called to report the error on 'expr' where the 'var' is not synced.
**/
static void provideWarning(UseInfo* var) {
  
  USR_WARN(var->usePoint,
	   "Potential unsafe (use after free) use of variable %s here. Please make sure the variable use is properly synced.",
	   var->varName.c_str());
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
    if(dest->syncType == NODE_SYNC_SIGNAL_EMPTY || NODE_SINGLE_WAIT_FULL)
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
    if(dest->syncVar.compare(source->syncVar) == 0) {
      return true;
    }
  return false;
}









/**
   Collects all SyncPoints that can be used to sync with 'source' node from 'potentialDest'
   into 'syncPoints'.
**/
static void getSyncPoints(SyncGraph* source, SyncGraphVec& potentialDest, SyncGraphVec& syncPoints) {
  for_vector(SyncGraph, dest, potentialDest) {
    if(sync(source,dest)) {
      syncPoints.push_back(dest);
    }
  }
}


/**
   Since single variables once filled remians as such, we need to handle them seperately.
   Here once, we find a matching syncNode we bypass all syncPoints involving that single variable
   using the 'filledSinglePoints' list.
**/
static bool handleSingleSyncing(SyncGraphVec& destSyncPoints, SyncGraphVec& syncPoints) {
  // Single Nodes need not be pulled back as
  // once they are filled they remain filled and
  // we don't have any advantage for pulling it back.
  getSyncPoints(syncPoints.front(), destSyncPoints, syncPoints);
  for_vector(SyncGraph, syncPoint, syncPoints) {
    int index = containsVec(destSyncPoints, syncPoint);
    INT_ASSERT(index != -1);
    destSyncPoints.erase(destSyncPoints.begin()+index);
    nextSyncPoint(syncPoint, visited);
    if(nextPoint != NULL)
      destSyncPoints.push_back(nextPoint);
    collectAllAvailableBeginGraphs(syncPoint, nextPoint, destSyncPoints, visited);
  }
  filledSinglePoints.push_back(syncPoints.front());
  return true;
}


static bool threadedMahjong(SyncGraphVec& destSyncPoints) {
  SyncGraphVec newBegins, syncPoints, childDestPoints;
  SyncGraphVec subSyncDest, subVisited;
  SyncGraph * syncNode;
  if(destSyncPoints.size() == 0 || )
    return true;
  
  int i=0;
  
  for(i=startPoint; i< destSyncPoints.size()-endPoint; i++) {
    syncNode = destSyncPoints.at(i);
    syncPoints.clear();
    newBegins.clear();
    getSyncPoints(syncNode, destSyncPoints, syncPoints);
    for_vector() {
    collectAllAvailableBeginGraphs(syncNode, nextPoint, destSyncPoints);
    childDestPoints.clear();
    childDestPoints.add(destSyncPoints);
    SyncGraph* nextPoint = 
    if(syncPoints.size() > 0) {
      // TODO
      // when it comes to branches choose one at a time 
      
    } 
  }
  return false;
}



static void setNextSyncNode() {
    forv_Vec(UseInfo, cur, useInfos) {
      SyncGraph* syncPoint = nextSyncPoint(cur->useNode);
      if(syncPoint  != NULL) {
	cur->setNextSyncNode(syncPoint);
	syncPoint->useInfos.add(cur);
      }
    }
}

static void setLastSyncNode() {
   forv_Vec(UseInfo, info, useInfos) {
    SyncGraph* curNode = info->useNode;
    INT_ASSERT(curNode->fnSymbol  != info->fnSymbol);
    while (curNode != NULL && curNode->fnSymbol  != info->fnSymbol) {
      curNode = curNode->parent;
    }
    INT_ASSERT(curNode != NULL);
    SyncGraph* nextSyncNode = nextSyncPoint(curNode);
    SyncGraph* syncNode = NULL;
    while(nextSyncNode != NULL) {
      syncNode = nextSyncNode;
      nextSyncNode = nextSyncPoint(curNode);
    }
    info->setLastSyncNode(syncNode);
  }
}


static void checkOrphanStackVar(SyncGraph* root) {
  bool checkedAll = true;
  setNextSyncNode();
  setLastSyncNode();
  forv_Vec(UseInfo, cur , useInfos) {
    if(cur->inherentlyUnSafe()) {
      provideWarning(cur);
    } else {
      checkedAll = false;
    }
  }

  if(checkedAll)
    return;
  SyncGraphVec endPoints;
  SyncGraphVecVec destSyncPoints;
  destSyncPoints.push_back(endPoints);
  collectAllAvailableSyncPoints(root, destSyncPoints, 0);
  int i;
  for(i=0; i<destSyncPoints.size(); i++) {
    threadedMahjong(destSyncPoints, curVisited, visited, des);
  }
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


static ArgSymbol*  getTheArgSymbol(std::string sym,FnSymbol* parent) {
  if(parent == NULL)
    return NULL;
  for_formals(formal,parent) {
    if(sym.compare(formal->name) == 0) {
      return formal;
    }
  }
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
        parentArgSymbol = getTheArgSymbol(sym->name,parentFunction);
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
static void addExternVarDetails(FnSymbol* fn, std::string v,SymExpr* use, SyncGraph* node) {
  UseInfo * newUseInfo = new UseInfo(node, fn, use, v);
  useInfos.add(newUseInfo);
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
        cur->contents.add_exclusive(se);
        cur->syncScope.add(block);
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
      // Non begin used mod function
      // that is internal
      cur->intFuncCalls.add_exclusive(call);
    }
  }
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
  allCallsSynced = true;
  forv_Vec(CallExpr,call,*fn->calledBy) {
    //for_vector(CallExpr, call, fn->calledBy) {
    if(isInsideSyncStmt(call)) {
      allCallsSynced = false;
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

  if(block == NULL &&  allCallsSynced == true) {
    return false;
  }
  if(cur->syncedScopes.size() > 0) {
    forv_Vec(Scope, syncedScope, cur->syncedScopes) {
      //for_vector(Scope, syncedScope, cur->syncedScopes) {
      if(compareScopes(block,syncedScope) == 1)
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

static SyncGraph* handleCondStmt(CondStmt* cond, SyncGraph* cur) {
  BlockStmt* thenBlock = cond->thenStmt;
  BlockStmt* elseBlock = cond->elseStmt;
  cur = handleBlockStmt(thenBlock,cur);
  if(elseBlock != NULL) {
    if( ASTContainsBeginFunction(elseBlock) ||
	refersExternalSymbols(elseBlock, cur) ){
      SyncGraph* elseNode = addElseChildNode(cur,elseBlock->getFunction());
      elseNode = handleBlockStmt(elseBlock,elseNode);
      cur = addChildNode(cur,cond->getFunction());
      elseNode->child = cur;
    }
  }
  return cur;
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
  funcGraphMap.put(fn,childNode);
  handleBlockStmt(fn->body, childNode);
  return cur;
}

static SyncGraph* handleFunction(FnSymbol* fn, SyncGraph *cur=NULL) {
  SyncGraph* newNode = NULL;
  if (cur == NULL) {
    newNode = cur  = new SyncGraph(fn);
    analysisRoots.push_back(newNode);
  } else {
    // Internal Function node.
    newNode = addChildNode(cur, fn);
  }
  funcGraphMap.put(fn,newNode);
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

  isInsideSyncStmt(NULL);
  forv_Vec (FnSymbol, fn, aFnSymbols) {
     //for_vector(FnSymbol, fn, aFnSymbols) { 
    checkSyncedCalls(fn);
    SyncGraph* syncGraphRoot = handleFunction(fn);
    #ifdef CHPL_DOTGRAPH
    dotGraph(syncGraphRoot);
    #endif
    analysisRoots.push_back(syncGraphRoot);
    FnSymbolsVec fnSymbols;
    fnSymbols.add(fn);
    expandAllInternalFunctions(syncGraphRoot, fnSymbols);
    checkOrphanStackVar(syncGraphRoot);
    cleanUpSyncGraph(syncGraphRoot);
  }
}
