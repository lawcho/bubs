
// C port of the BUBS algorithm.

// Comments in this file focus on differences from the SML version

//////////////////
// Dependencies //
//////////////////

#include<stdlib.h>
#include<assert.h>
#include<stdbool.h>
#include<stddef.h>
#include<stdio.h>

#ifdef CONFIG_ENABLE_DEBUG_PRINTF
#define DEBUG_PRINTF(...) printf(__VA_ARGS__)
#else
#define DEBUG_PRINTF(...)
#endif

////////////////
// Data types //
////////////////

// Notes on memory layout (Lawrence Apr '23):
//  * SML "option" type is replaced by careful use of NULL pointers
//  * Pointers (implicit in SML) are avoided, instead sub-structures
//    are stored contiguously where possible, e.g.:
//      * ChildCell s are stored in parent-nodes
//      * Var nodes are stored inside Lam nodes
//      * The ChildCell and DL types are merged
//  * The 'uniq' field is scrapped (in favour of memory addresses)


typedef enum ChildCellTag_e
    {LamBody,AppFun,AppArg,Op2Arg1,Op2Arg2,Op1Arg} ChildCellTag;
typedef enum TermTag_e
    {VarT,LamT,AppT,Op2T,Op1T,Op0T,PrimT} TermTag;

typedef struct ChildCell_s ChildCell;
typedef struct Term_s Term;

struct ChildCell_s {
    ChildCellTag tag;   // must correpond to position in enclosing struct
    Term* child;        // NULL only during construction
    ChildCell* pred;    // NULL only during construction
    ChildCell* succ;    // NULL only during construction
};

// The 'Term' struct itself contains the fields common to each class of node
struct Term_s {
    TermTag tag;        // indicates the class of the enclosing struct
    ChildCell* parents; // NULL => node is garbage
};

typedef struct VarType_s VarType;
struct VarType_s {
    Term header;
    // variables store no extra info
};

typedef struct LamType_s LamType;
struct LamType_s {
    Term header;
    LamType* copy;      // NULL => no copy
    VarType lamVar;
    ChildCell lamBody;
};

typedef struct AppType_s AppType;
struct AppType_s {
    Term header;
    AppType* copy;      // NULL => no copy
    ChildCell appFun;
    ChildCell appArg;
};

typedef struct Op2Type_s Op2Type;
struct Op2Type_s {
    Term header;
    Op2Type* copy;      // NULL => no copy
    // A field named 'primop', pointing to a C function which takes
    // two args of type (Term **), and returns a value of type (Term *)
    // NULL only during construction
    Term* (*primop)(Term** , Term**);   // double indirection allows safe calling of whnf() in primop
    ChildCell op2Arg1;
    ChildCell op2Arg2;
};

typedef struct Op1Type_s Op1Type;
struct Op1Type_s {
    Term header;
    // A field named 'primop', pointing to a C function which takes
    // one arg of type (Term **), and returns a value of type (Term *)
    // NULL only during construction
    Term* (*primop)(Term**);    // double indirection allows safe calling of whnf() in primop
    ChildCell op1Arg;
};

typedef struct Op0Type_s Op0Type;
struct Op0Type_s {
    Term header;
    // A field named 'primop', pointing to a C function which takes
    // no args, and returns a value of type (Term *)
    // NULL only during construction
    Term* (*primop)(void);
};

typedef struct PrimType_s PrimType;
struct PrimType_s {
    Term header;
    unsigned int primData;
};

//////////////////////////////////////
// ChildCell manipulation functions //
//////////////////////////////////////

// These are prefixed with dl_ to avoid name clashes

// Check that a single cell in a DLL is well formed. O(1).
void dl_assert_wf_cc(ChildCell* cc){
    assert(cc != NULL);
    // Check that cc has pred and succ nodes
    assert (cc->pred != NULL);
    assert (cc->succ != NULL);
    // Check that cc's pred- and succ- pointers are bi-directional
    assert(cc->pred->succ == cc);
    assert(cc->succ->pred == cc);
}

// Check that a DLL is well formed. O(length of DLL).
// May loop on malformed DLLs.
void dl_assert_wf(ChildCell* cc) {
    if (cc == NULL) {return;}
    ChildCell* i = cc;
    // Scan forwards through the list, checking the invariant
    do {
        dl_assert_wf_cc(i);
        i = i->succ;
    } while(i != cc);
    // Scan backwards through the list, checking the invariant
    do {
        dl_assert_wf_cc(i);
        i = i->pred;
    } while(i != cc);
}

// Set a bi-directional link between cells.
// Only for use in other dl_ functions.
void dl_set_link (ChildCell* cc1, ChildCell* cc2) {
    // No WF assertions here since this function is used internally,
    // when the invariant is temporarily broken
    assert(cc1 != NULL);
    assert(cc2 != NULL);
    cc1->succ = cc2;
    cc2->pred = cc1;
}

// Getters & setters from SML impl. omitted (use C selectors instead)

// alias() replaced by C pointer equality _==_

// Does the (NULLable) pointer point to a singleton list?
bool dl_is_singleton (ChildCell* cc) {
    dl_assert_wf(cc);

    if (cc == NULL) {return false;}
    bool b1 = cc == cc->succ;
    bool b2 = cc == cc->pred;

    assert (b1 == b2); 
    return b1;
}

// Initialize a ChildCell as a singleton with an initial value
//  Repaces new(), since this function does not do allocation.
void dl_init (ChildCellTag tag, Term* child, ChildCell* cc) {
    assert (cc != NULL);

    cc->tag = tag;
    cc->succ = cc;
    cc->pred = cc;
    cc->child = child;

    dl_assert_wf(cc);
}

// Unlink a ChildCell from its surrounding list,
// and return another element from that list (NULL if there are no others)
ChildCell* dl_remove (ChildCell* cc) {
    dl_assert_wf(cc); assert (cc != NULL);

    if (dl_is_singleton (cc)) {
        return NULL;
    } else {
        ChildCell* s = cc->succ;
        ChildCell* p = cc->pred;
        dl_set_link (p, s);
        dl_set_link (cc, cc);

        dl_assert_wf(p);
        dl_assert_wf(cc);
        dl_assert_wf(s);
        return p;
    }
}

// Concatenate two lists in-place
//  Precondition: lists must be distinct
//  See the SML code for details of correctness & the precondition.
void dl_union (ChildCell* a, ChildCell* c) {
    dl_assert_wf(a); assert (a != NULL);
    dl_assert_wf(c); assert (c != NULL);

    ChildCell* b = a->succ;
    ChildCell* d = c->succ;
    dl_set_link (a, d);
    dl_set_link (c, b);

    dl_assert_wf(a);
    dl_assert_wf(b);
    dl_assert_wf(c);
    dl_assert_wf(d);
}

///////////////////////////////////////////////
// Tests for the ChildCell manipulating code //
///////////////////////////////////////////////

// Property under test: init() creates a singleton
void dl_test_singleton_init (void) {
    Term t; // no need to init this to test the DLL lib
    ChildCell cc;
    dl_init(LamBody, &t, &cc);
    assert(dl_is_singleton(&cc));
}

// Property under test: union() works as expected
void dl_test_singleton_remove (void) {
    Term t1; ChildCell cc1; dl_init(LamBody, &t1, &cc1);
    Term t2; ChildCell cc2; dl_init(LamBody, &t2, &cc2);
    Term t3; ChildCell cc3; dl_init(LamBody, &t3, &cc3);
    Term t4; ChildCell cc4; dl_init(LamBody, &t4, &cc4);
    dl_union(&cc1,&cc2);
    dl_union(&cc3,&cc4);
    dl_union(&cc4,&cc1);
    assert ((&cc1)->succ->succ->succ->succ == &cc1);
    assert ((&cc2)->succ->succ->succ->succ == &cc2);
    assert ((&cc3)->succ->succ->succ->succ == &cc3);
    assert ((&cc4)->succ->succ->succ->succ == &cc4);
    assert ((&cc1)->pred->pred->pred->pred == &cc1);
    assert ((&cc2)->pred->pred->pred->pred == &cc2);
    assert ((&cc3)->pred->pred->pred->pred == &cc3);
    assert ((&cc4)->pred->pred->pred->pred == &cc4);
}

////////////////////////////////////
// Coercion & Traversal functions //
////////////////////////////////////

// Inverse of C's arrow operator _->_
// Implementation from: https://en.wikipedia.org/wiki/Offsetof
// See also: http://www.kroah.com/log/linux/container_of.html
#define container_of(ptr, type, member) ((type *)((char *)(1 ? (ptr) : &((type *)0)->member) - offsetof(type, member)))

// Get the node containing a ChildCell
Term* ccParent(ChildCell* cc){
    switch (cc->tag){
    case AppFun: {return &(container_of(cc, AppType, appFun )->header);}
    case AppArg: {return &(container_of(cc, AppType, appArg )->header);}
    case LamBody:{return &(container_of(cc, LamType, lamBody)->header);}
    case Op2Arg1:{return &(container_of(cc, Op2Type, op2Arg1)->header);}
    case Op2Arg2:{return &(container_of(cc, Op2Type, op2Arg2)->header);}
    case Op1Arg: {return &(container_of(cc, Op1Type, op1Arg )->header);}
    default: {assert(false);}
    }
}

// Downcasts (check tag before use!)
LamType* term2Lam(Term* t)
    {assert(t->tag == LamT); return container_of(t, LamType, header);}
AppType* term2App(Term* t) 
    {assert(t->tag == AppT); return container_of(t, AppType, header);}
Op2Type* term2Op2(Term* t)
    {assert(t->tag == Op2T); return container_of(t, Op2Type, header);}
Op1Type* term2Op1(Term* t)
    {assert(t->tag == Op1T); return container_of(t, Op1Type, header);}
Op0Type* term2Op0(Term* t)
    {assert(t->tag == Op0T); return container_of(t, Op0Type, header);}
PrimType* term2Prim(Term* t)
    {assert(t->tag == PrimT); return container_of(t, PrimType, header);}

////////////////////////////
// Misc. setter functions //
////////////////////////////

// Add uplink(s) to a node's parent-list.
// Precondition: the two lists must be different.
void addToParents(Term* node, ChildCell* cc) {
    assert(node != NULL);
    assert(cc != NULL);
    if (node->parents == NULL) {
        node->parents = cc;
    } else {
        dl_union (node->parents , cc);
    }
}

// Replace the term poitned to by a ChildCell.
// Updates parent-lists, for both the old term and its replacement
// Precondition: cc is not in new's parent list
// Precondition: cc is not a singleton or NULL
void replaceCC(ChildCell* cc, Term* new){
    assert(cc != NULL);
    assert(!dl_is_singleton(cc));
    cc->child->parents = dl_remove(cc); // update cc->child's parent list
    assert(dl_is_singleton(cc));
    cc->child = new;
    addToParents(new,cc);
}

// Replace one term w/another in the DAG.
// Leaves the old term dead.
// Precondition: the terms are distinct
void replaceTerm(Term* old, Term* new) {
    assert(old != NULL);
    assert(new != NULL);
    assert(old != new);
    if (old->parents == NULL) {return;} // Old term has no parents => nothing to do
    ChildCell* cc = old->parents;
    do {
        cc->child = new;
        cc = cc->succ;
    } while (cc != old->parents);
    addToParents(new, old->parents);
    old->parents = NULL;    // old term now has no parents
}

///////////////////////
// Node constructors //
///////////////////////

// Construct a var-node on the heap
// Under the hood, this allocates a surrounding λ-node too.
VarType* mkVar (void) {
    LamType* lamNode = malloc(sizeof(LamType));
    lamNode->lamVar.header.tag = VarT;
    lamNode->lamVar.header.parents = NULL;
    return &(lamNode->lamVar);
}

// Initialize a λ-node on the heap
LamType* mkLam (bool selfRef, VarType* var, Term* body) {
    LamType* lamNode = container_of(var, LamType, lamVar);

    lamNode->header.tag = LamT;
    lamNode->header.parents = NULL;
    lamNode->copy = (selfRef ? lamNode : NULL);
    // lamNode->lamVar already initialized by mkVar
    dl_init(LamBody, body, &(lamNode->lamBody));

    addToParents(body, &(lamNode->lamBody));
    return lamNode;
}

// Construct an @-node on the heap
AppType* mkApp (bool selfRef, Term* fun, Term* arg) {
    AppType* appNode = malloc(sizeof(AppType));
    appNode->header.tag = AppT;
    appNode->header.parents = NULL;
    appNode->copy = (selfRef ? appNode : NULL);
    dl_init(AppFun, fun, &(appNode->appFun));
    dl_init(AppArg, arg, &(appNode->appArg));
    addToParents(fun, &(appNode->appFun));
    addToParents(arg, &(appNode->appArg));
    return appNode;
}

Op2Type* mkOp2 (bool selfRef, Term* (*primop)(Term** , Term**), Term* arg1, Term* arg2) {
    Op2Type* op2Node = malloc(sizeof(Op2Type));
    op2Node->header.tag = Op2T;
    op2Node->header.parents = NULL;
    op2Node->copy = (selfRef ? op2Node : NULL);
    op2Node->primop = primop;
    dl_init(Op2Arg1, arg1, &(op2Node->op2Arg1));
    dl_init(Op2Arg2, arg2, &(op2Node->op2Arg2));
    addToParents(arg1, &(op2Node->op2Arg1));
    addToParents(arg2, &(op2Node->op2Arg2));
    return op2Node;
}

Op1Type* mkOp1 (Term* (*primop)(Term**), Term* arg) {
    Op1Type* op1Node = malloc(sizeof(Op1Type));
    op1Node->header.tag = Op1T;
    op1Node->header.parents = NULL;
    op1Node->primop = primop;
    dl_init(Op1Arg, arg, &(op1Node->op1Arg));
    addToParents(arg, &(op1Node->op1Arg));
    return op1Node;
}

Op0Type* mkOp0 (Term* (*primop)(void)) {
    Op0Type* op0Node = malloc(sizeof(Op0Type));
    op0Node->header.tag = Op0T;
    op0Node->header.parents = NULL;
    op0Node->primop = primop;
    return op0Node;
}

PrimType* mkPrim (unsigned int primData) {
    PrimType* primNode = malloc(sizeof(PrimType));
    primNode->header.tag = PrimT;
    primNode->header.parents = NULL;
    primNode->primData = primData;
    return primNode;
}

// User-facing wrappers that return (Term *)

Term* var (VarType* varNode)
    {return &(varNode->header);}
Term* lam(VarType* var, Term* body)
    {return &(mkLam(false, var, body)->header);}
Term* app (Term* fun, Term* arg)
    {return &(mkApp(false, fun,arg)->header);}
Term* op2 (Term* (*primop)(Term** , Term**), Term* arg1, Term* arg2)
    {return &(mkOp2(false, primop, arg1, arg2)->header);}
Term* op1 (Term* (*primop)(Term**), Term* arg)
    {return &(mkOp1(primop, arg)->header);}
Term* op0 (Term* (*primop)(void))
    {return &(mkOp0(primop)->header);}
Term* prim (unsigned int data)
    {return &(mkPrim(data)->header);}

///////////////////////////////
// Pretty-printing functions //
///////////////////////////////

// Print a ChildCell tag to stdout.
void printCCTag (ChildCellTag t) {
    switch (t){
        case AppFun:    {printf("AppFun");  break;}
        case AppArg:    {printf("AppArg" ); break;}
        case LamBody:   {printf("LamBody"); break;}
        case Op2Arg1:   {printf("Op2Arg1"); break;}
        case Op2Arg2:   {printf("Op2Arg2"); break;}
        case Op1Arg:    {printf("Op1Arg" ); break;}
        default: {assert(false);}
    }
}

// Print a ChildCell to stdout
void printCC (ChildCell* cc) {
    assert(cc != NULL);
    printCCTag(cc->tag);
    printf(" %12p", ccParent(cc));
}

// Print the parents of a term to stdout, followed by newline
void printParents (Term* t) {
    printf ("(parents = [");
    if (t->parents != NULL){
        ChildCell* i = t->parents;
        do {
            printCC (i);
            printf(",");
            i = i->succ;
        } while (i != t->parents);
    }
    printf ("])\n");
}

// Print a term to stdout (pre-order depth-first traversal)
void pretty (Term* t) {
    printf("%12p |->    ",t); // print node address
    switch (t->tag) {       // print node using λ-calculus syntax
        case VarT: {
            printf("var%67s","");
            printParents(t);
            break;}
        case LamT: {
            LamType* lamNode = term2Lam(t);
            printf("\\ %12p . %12p%12s(copy = %12p)    ",
                &(lamNode->lamVar.header),
                lamNode->lamBody.child,
                "",
                lamNode->copy
                );
            printParents(t);
            pretty(lamNode->lamBody.child);
            break;}
        case AppT: {
            AppType* appNode = term2App(t);
            printf("%12p @ %12p%14s(copy = %12p)    ",
                appNode->appFun.child,
                appNode->appArg.child,
                "",
                appNode->copy
                );
            printParents(t);
            pretty(appNode->appFun.child);
            pretty(appNode->appArg.child);
            break;}
        case Op2T: {
            Op2Type* op2Node = term2Op2(t);
            printf("%12p <op2> %12p%12s(copy = %12p)    ",
                op2Node->op2Arg1.child,
                op2Node->op2Arg2.child,
                "",
                op2Node->copy
                );
            printParents(t);
            pretty(op2Node->op2Arg1.child);
            pretty(op2Node->op2Arg2.child);
            break;}
        case Op1T: {
            Op1Type* op1Node = term2Op1(t);
            printf("<op1> %12p%50s",
                op1Node->op1Arg.child,
                ""
                );
            printParents(t);
            pretty(op1Node->op1Arg.child);
            break;}
        case Op0T: {
            printf("<op0>%60s","");
            printParents(t);
            break;}
        case PrimT: {
            PrimType* primNode = term2Prim(t);
            printf("prim %u%50s",
                primNode->primData,
                "");
            printParents(t);
            break;}
        default: {assert(false);}
    }

}


// Print a ChildCell as a DOT sub-node
void dump_dot_CC_node(ChildCell* cc){
    assert(cc != NULL);
    printf("| {");
    printCCTag(cc->tag);
    printf("| { <");
    printCCTag(cc->tag);
    printf("_pred> | <");
    printCCTag(cc->tag);
    printf("_child> | <");
    printCCTag(cc->tag);
    printf("_succ>}}");
}

// Print the pointers out of a ChildCell as DOT edges.
void dump_dot_CC_edges(ChildCell* cc){
    assert(cc != NULL);

    // Print (cc->child)
    printf("n%p:",ccParent(cc));printCCTag(cc->tag);printf("_child:c ->");
    printf("n%p:parents [color=black];\n", cc->child);

    // Print (cc->pred)
    ChildCell* ccp = cc->pred;
    printf("n%p:", ccParent(cc ));printCCTag(cc ->tag);printf("_pred -> ");
    printf("n%p:", ccParent(ccp));printCCTag(ccp->tag);printf("_succ [constraint=false,color=lightgrey];\n");

    // Print (cc->succ)
    ChildCell* ccs = cc->succ;
    printf("n%p:", ccParent(cc ));printCCTag(cc ->tag);printf("_succ -> ");
    printf("n%p:", ccParent(ccs));printCCTag(ccs->tag);printf("_pred [constraint=false,color=lightgrey];\n");
}

// Helper for dump_dot
void dump_dot_Term(Term* t){
    assert(t != NULL);
    switch (t->tag){
        case VarT: {
            printf("n%p [label =\"VarT | <parents>\"];\n",t);
            printf("\n");
            break;}
        case LamT: {
            LamType* lamNode = term2Lam(t);
            printf("n%p [label =\"LamT | <parents> | <copy> | <lamVar> ",t);
            dump_dot_CC_node(&(lamNode->lamBody));
            printf("\"];\n");
            dump_dot_Term(lamNode->lamBody.child);
            dump_dot_Term(&(lamNode->lamVar.header));
            printf("\n");
            dump_dot_CC_edges(&(lamNode->lamBody));
            printf("n%p:lamVar -> n%p [headclip=true, color=darkgoldenrod, dir=none];\n",t,&(lamNode->lamVar.header));
            break;}
        case AppT: {
            AppType* appNode = term2App(t);
            printf("n%p [label =\"AppT | <parents> | <copy> ",t);
            dump_dot_CC_node(&(appNode->appFun));
            dump_dot_CC_node(&(appNode->appArg));
            printf("\"];\n");
            dump_dot_Term(appNode->appFun.child);
            dump_dot_Term(appNode->appArg.child);
            printf("\n");
            dump_dot_CC_edges(&(appNode->appFun));
            dump_dot_CC_edges(&(appNode->appArg));
            break;}
        case Op2T: {
            Op2Type* op2Node = term2Op2(t);
            printf("n%p [label =\"Op2T | <parents> | <copy> | %p ",t, op2Node->primop);
            dump_dot_CC_node(&(op2Node->op2Arg1));
            dump_dot_CC_node(&(op2Node->op2Arg2));
            printf("\"];\n");
            dump_dot_Term(op2Node->op2Arg1.child);
            dump_dot_Term(op2Node->op2Arg2.child);
            printf("\n");
            dump_dot_CC_edges(&(op2Node->op2Arg1));
            dump_dot_CC_edges(&(op2Node->op2Arg2));
            break;}
        case Op1T: {
            Op1Type* op1Node = term2Op1(t);
            printf("n%p [label =\"Op1T | <parents> | <copy> | %p ",t, op1Node->primop);
            dump_dot_CC_node(&(op1Node->op1Arg));
            printf("\"];\n");
            dump_dot_Term(op1Node->op1Arg.child);
            printf("\n");
            dump_dot_CC_edges(&(op1Node->op1Arg));
            break;}
        case Op0T: {
            Op0Type* op0Node = term2Op0(t);
            printf("n%p [label =\"Op0T | <parents> | <copy> | %p \"];\n",t, op0Node->primop);
            printf("\n");
            break;}
        case PrimT: {
            PrimType* primNode = term2Prim(t);
            printf("n%p [label =\"PrimT | <parents> | <primData> %d \"];\n",t, primNode->primData);
            printf("\n");
            break;}
        default: {assert(false);}
    }
    // printf("n%p [xlabel = \"%p\"];\n",t,t);
    if (t->parents != NULL) {  // print parent pointer
        printf("n%p:parents:c -> n%p:", t, ccParent(t->parents));
        printCCTag(t->parents->tag);
        printf("_child [constraint=false, weight=0, color=brown];\n");
    }
}

// Dump the whole BUBS heap on stdout, formatted into graphviz DOT code that draws it.
// The 1st arg tells where to print from, the 2nd arg tells what to highlight
void dump_dot(Term* root, Term* focus){
    // The 'strict' keyword tells graphviz to de-duplicates edges
    // (graphviz de-duplicates nodes by default)
    printf("digraph {\n");
    printf("splines=line;\n");
    printf("rankdir=TB;\n");
    printf("node [shape=record];\n");
    printf("edge [headclip=false,tailclip=false,arrowtail=dot,dir=both];\n");
    printf("\n");
    if(root != NULL) {
        // draw the graph
        dump_dot_Term(root);
    }
    if (focus != NULL){
        // Make the root red
        printf("n%p [style=filled,fillcolor = yellow];\n",focus);
    }
    printf("}\n");
}


////////////////////////
// Garbage collection //
////////////////////////

// Free a node (unless embedded in another node).
// Non-recursive.
void dealloc (Term* t){
    switch (t->tag) {
    case LamT:  {free(t); return;}
    case VarT:  {return;}   // don't free variables, they are stored inside λ-nodes
    case AppT:  {free(t); return;}
    case Op2T:  {free(t); return;}
    case Op1T:  {free(t); return;}
    case Op0T:  {free(t); return;}
    case PrimT: {free(t); return;}
    default: {assert(false);}
    }
}

// Unlink a term from just one of its parents (using a given uplink).
// Non-recursive. Does not de-allocate.
void unlinkChild (ChildCell* cc) {
    assert(cc != NULL);
    assert(cc->child != NULL);
    cc->child->parents = dl_remove (cc);
}

// Recursively free a dead node.
// Precondition: t is dead
void recFreeDeadNode (Term* t);

// Unlink a term from just one of its parents (using a given uplink),
//  and if this makes the child dead, then free it recursively
void recUnlinkChild (ChildCell* cc) {
    unlinkChild (cc);
    if (cc->child->parents == NULL) {recFreeDeadNode(cc->child);}
}

void recFreeDeadNode (Term* t) {
    assert(t->parents == NULL);
    DEBUG_PRINTF("Recursively freeing dead node at %p.\n", t);
    switch (t->tag) {
    case LamT:  {
        LamType* lamNode = term2Lam(t);
        recUnlinkChild(&(lamNode->lamBody));
        break;}
    case VarT:  {break;}
    case AppT:  {
        AppType* appNode = term2App(t);
        recUnlinkChild(&(appNode->appFun));
        recUnlinkChild(&(appNode->appArg));
        break;}
    case Op2T:  {
        Op2Type* op2Node = term2Op2(t);
        recUnlinkChild(&(op2Node->op2Arg1));
        recUnlinkChild(&(op2Node->op2Arg2));
        break;}
    case Op1T:  {
        Op1Type* op1Node = term2Op1(t);
        recUnlinkChild(&(op1Node->op1Arg));
        break;}
    case Op0T:  {break;}
    case PrimT: {break;}
    default: {assert(false);}
    }
    dealloc(t);
}

// Replace some dead term 'old' with another term 'new',
//  then free 'old' recursively (but avoid freeing 'new').
//  Returns 'new'.
Term* replaceProtectAndCollect (Term* old , Term* new) {
    DEBUG_PRINTF("Entering replaceProtectAndCollect(%p,%p)\n",old,new);
    assert(old != NULL);
    assert(new != NULL);

    replaceTerm(old, new);

    // Create a temporary ChildCell targeting 'new', to protect it from deletion
    ChildCell cc;
    dl_init(LamBody, new, &cc);
    addToParents(new, &cc);

    recFreeDeadNode(old);

    unlinkChild(&cc);    // Clean up temporary ChildCell
    DEBUG_PRINTF("Leaving replaceProtectAndCollect(%p,%p)\n",old,new);
    return new;
}

/////////////////////////////////
// Upcopying and copy-clearing //
/////////////////////////////////

// See SML code for explanation of the algorithm
void upcopyUplinks (Term* newChild, ChildCell* cc) {
    if (cc == NULL) {return;}   // No uplinks in list => stop recursion
    // Have uplinks => loop over them, spawning upcopies at each
    ChildCell* i = cc;
    do {Term* t = ccParent(i);
        DEBUG_PRINTF("Upcopying into term at %p.\n", t);
        switch (i->tag){    
        case LamBody:{
            LamType* lamNode = term2Lam(t);
            DEBUG_PRINTF("Cloning a λ-node from its only child.\n");
            if (lamNode->copy != NULL) {
                DEBUG_PRINTF("Copied up into an already-copied λ-node. "
                "Mutating the existing copy at %p and quitting\n",
                &(lamNode->copy->header));
                lamNode->copy->lamBody.child = newChild;
                newChild->parents = &(lamNode->copy->lamBody);
                dl_remove(&(lamNode->copy->lamBody));
            } else {
                VarType* new_var = mkVar();
                LamType* new_lam = mkLam(true, new_var, newChild);
                DEBUG_PRINTF("Allocated a copy of the λ-node on the heap, at %p.\n",&(new_lam->header));
                lamNode->copy = new_lam;
                DEBUG_PRINTF("Recursively upcopying the λ-var. "
                " (this should terminate somewhere in newChild)\n");
                upcopyUplinks(&(new_lam->lamVar.header), lamNode->lamVar.header.parents);
                DEBUG_PRINTF("Recursively upcopying parents of the λ-node at %p.\n",t);
                upcopyUplinks(&(new_lam->header), lamNode->header.parents);
            }
            break;}

        case AppFun: {
            AppType* appNode = term2App(ccParent(i));
            DEBUG_PRINTF("Cloning an @-node from the fun side.\n");
            if (appNode->copy != NULL) {
                DEBUG_PRINTF("Copied up into an already-copied @-node. "
                "Mutating the existing copy at %p and quitting\n",
                &(appNode->copy->header));
                replaceCC(&(appNode->copy->appFun), newChild);
            } else {
                AppType* new_app = mkApp(true, newChild, appNode->appArg.child);
                DEBUG_PRINTF("Allocated a copy of the @-node, at %p.\n",&(new_app->header));
                appNode->copy = new_app;
                DEBUG_PRINTF("Recursively upcopying parents of the @-node\n");
                upcopyUplinks (&(new_app->header), appNode->header.parents);
            }
            ;break;}

        case AppArg: {
            AppType* appNode = term2App(ccParent(i));
            DEBUG_PRINTF("Cloning an @-node from the arg side.\n");
            if (appNode->copy != NULL) {
                DEBUG_PRINTF("Copied up into an already-copied @-node. "
                "Mutating the existing copy at %p and quitting\n",
                &(appNode->copy->header));
                replaceCC(&(appNode->copy->appArg), newChild);
            } else {
                AppType* new_app = mkApp(true, appNode->appFun.child, newChild);
                DEBUG_PRINTF("Allocated a copy of the @-node, at %p.\n",&(new_app->header));
                appNode->copy = new_app;
                DEBUG_PRINTF("Recursively upcopying parents of the @-node\n");
                upcopyUplinks (&(new_app->header), appNode->header.parents);
            }
            ;break;}

        case Op2Arg1: {
            Op2Type* op2Node = term2Op2(ccParent(i));
            DEBUG_PRINTF("Cloning an op2-node from the arg1 side.\n");
            if (op2Node->copy != NULL) {
                DEBUG_PRINTF("Copied up into an already-copied op2-node. "
                "Mutating the existing copy at %p and quitting\n",
                &(op2Node->copy->header));
                replaceCC(&(op2Node->copy->op2Arg1), newChild);
            } else {
                Op2Type* new_op2 = mkOp2(true, op2Node->primop, newChild, op2Node->op2Arg2.child);
                DEBUG_PRINTF("Allocated a copy of the op2-node, at %p.\n",&(new_op2->header));
                op2Node->copy = new_op2;
                DEBUG_PRINTF("Recursively upcopying parents of the op2-node.\n");
                upcopyUplinks (&(new_op2->header), op2Node->header.parents);
            }
            ;break;}

        case Op2Arg2: {
            Op2Type* op2Node = term2Op2(ccParent(i));
            DEBUG_PRINTF("Cloning an op2-node from the arg2 side.\n");
            if (op2Node->copy != NULL) {
                DEBUG_PRINTF("Copied up into an already-copied op2-node. "
                "Mutating the existing copy at %p and quitting\n",
                &(op2Node->copy->header));
                replaceCC(&(op2Node->copy->op2Arg2), newChild);
            } else {
                Op2Type* new_op2 = mkOp2(true, op2Node->primop, op2Node->op2Arg1.child, newChild);
                DEBUG_PRINTF("Allocated a copy of the op2-node, at %p.\n",&(new_op2->header));
                op2Node->copy = new_op2;
                DEBUG_PRINTF("Recursively upcopying parents of the op2-node\n");
                upcopyUplinks (&(new_op2->header), op2Node->header.parents);
            }
            ;break;}

        case Op1Arg: {
            Op1Type* op1Node = term2Op1(ccParent(i));
            DEBUG_PRINTF("Cloning an op1 from its only child.\n");
            Op1Type* new_op1 = mkOp1(op1Node->primop, newChild);
            DEBUG_PRINTF("Recursively upcopying parents of the op1-node.\n");
            upcopyUplinks(&(new_op1->header), op1Node->header.parents);
            break;}
        default: {assert(false);}
        }
        i = i->succ;
    } while (i != cc);
}

// cleanUplinks follow the recursion path of upcopyUplinks,
// but clearing the copy slots instead of setting them
void cleanUplinks(ChildCell* cc) {
    if (cc == NULL) {return;}   // No uplinks in list => stop recursion
    // Have uplinks => loop over them, spawning upcleans at each
    ChildCell* i = cc;
    do {switch (i->tag){
        case LamBody: {
            Term* node = ccParent(i);
            LamType* lamNode = term2Lam(node);
            if (lamNode->copy != NULL){
                lamNode->copy->copy = NULL;
                lamNode->copy = NULL;
                cleanUplinks(lamNode->lamVar.header.parents);
                cleanUplinks(node->parents);
            }
            break;}
        case AppFun:    // fall through
        case AppArg: {
            Term* node = ccParent(i);
            AppType* appNode = term2App(ccParent(i));
            if (appNode->copy != NULL) {
                appNode->copy->copy = NULL;
                appNode->copy = NULL;
                cleanUplinks(node->parents);
            }
            break;}
        case Op2Arg1:   // fall through
        case Op2Arg2: {
            Term* node = ccParent(i);
            Op2Type* op2Node = term2Op2(node);
            if (op2Node->copy != NULL) {
                op2Node->copy->copy = NULL;
                op2Node->copy = NULL;
                cleanUplinks(node->parents);
            }
            break;}
        case Op1Arg: {
            Term* node = ccParent(i);
            cleanUplinks(node->parents);
            break;}
        default: {assert(false);}
        }
        i = i->succ;
    } while (i != cc);
}

///////////////////////////////////
// β-reduction, primop reduction //
///////////////////////////////////

// Contract a β-redex in-place (and return a pointer for convenience)
Term* reduceRedex(Term* t) {
    DEBUG_PRINTF("Entering reduceRedex(%p)\n",t);

    // Get pointers to relevant sub-terms
    assert(t->tag == AppT);
    AppType* a = term2App(t);
    assert(a->appFun.child->tag == LamT);
    LamType* l = term2Lam(a->appFun.child);
    Term* argterm = a->appArg.child;
    Term* varterm = &(l->lamVar.header);
    ChildCell* lampars = l->header.parents;

    Term* result;

    if (dl_is_singleton(lampars)) {
        DEBUG_PRINTF("Single-parent fast path.\n");
        replaceTerm(varterm, argterm);
        result = l->lamBody.child;
    }
    else if (varterm->parents == NULL) {
        DEBUG_PRINTF("Unused-variable fast path.\n");
        result = l->lamBody.child;
    }
    else {
        DEBUG_PRINTF("General case of β-reduction.\n");

        // Stack-allocate a λ-node to collect the result of upcopy
        LamType tmp;
        tmp.header.parents = NULL;
        tmp.lamVar.header.parents = NULL;
        dl_init(LamBody, NULL, &(tmp.lamBody));
        DEBUG_PRINTF("&tmp == %p\n",&tmp);
        DEBUG_PRINTF("&(tmp.lamBody) == %p\n",&(tmp.lamBody));
        DEBUG_PRINTF("&(tmp.header) == %p\n",&(tmp.header));

        // Upcopy, starting at [var ↦ argterm], stopping at l
        tmp.copy = &tmp;
        l->copy = &tmp;
        upcopyUplinks(argterm, varterm->parents);

        // Extract the output of the upcopy
        assert(tmp.lamBody.child != NULL);
        result = tmp.lamBody.child;

        // Upclean, starting at var, stopping at l
        l->copy = NULL;
        cleanUplinks(varterm->parents);

        // Remove tmp from result's parent list
        result->parents = dl_remove(&(tmp.lamBody));
    }
    DEBUG_PRINTF("Leaving reduceRedex(%p), about to replace %p with %p\n",t, t, result);
    return replaceProtectAndCollect(t, result);
}

// Reduce an op2-headed term
Term* reduceOp2 (Term* t){
    DEBUG_PRINTF("Entering reduceOp2(%p)\n",t);
    assert(t->tag == Op2T);
    Op2Type* op2Node = term2Op2(t);
    // invoke function pointer stored in op2Node
    Term* new_term = (op2Node->primop)(
        &(op2Node->op2Arg1.child),
        &(op2Node->op2Arg2.child));
    DEBUG_PRINTF("Leaving reduceOp2(%p), but first replacing %p with %p\n",t, t, new_term);
    return replaceProtectAndCollect (t, new_term);
}

// Reduce an op1-headed term
Term* reduceOp1 (Term* t){
    DEBUG_PRINTF("Entering reduceOp1(%p)\n",t);
    assert(t->tag == Op1T);
    Op1Type* op1Node = term2Op1(t);
    // invoke function pointer stored in op1Node
    Term* new_term = (op1Node->primop)(
        &(op1Node->op1Arg.child));
    DEBUG_PRINTF("Leaving reduceOp1(%p), but first replacing %p with %p\n",t, t, new_term);
    return replaceProtectAndCollect (t, new_term);
}

// Reduce an op0-headed term
Term* reduceOp0 (Term* t){
    DEBUG_PRINTF("Entering reduceOp0(%p)\n",t);
    assert(t->tag == Op0T);
    Op0Type* op0Node = term2Op0(t);
    // invoke function pointer stored in op1Node
    Term* new_term = (op0Node->primop)();
    DEBUG_PRINTF("Leaving reduceOp0(%p), but first replacing %p with %p\n",t, t, new_term);
    return replaceProtectAndCollect (t, new_term);
}

///////////////////
// Normalisation //
///////////////////

Term* global_print_root = NULL;
unsigned int whnf_count = 0;

// Reduce a term to weak-head normal form
Term* whnf(Term* t) {
    DEBUG_PRINTF("Entering whnf(%p)\n",t);
    assert(t != NULL);
    #ifdef CONFIG_DUMP_DOT_ON_WHNF
        printf("// BEGIN DOT DUMP\n");
        printf("// Call # %d of whnf()\n",++whnf_count);
        dump_dot(global_print_root,t);
        printf("// END DOT DUMP\n");
    #endif
    switch (t->tag) {
    case AppT:  {
        DEBUG_PRINTF("About to normalise fun-child of @-node %p\n",t);
        Term* norm_fun = whnf(term2App(t)->appFun.child);
        if (norm_fun->tag == LamT) {
            DEBUG_PRINTF("Fun-child of @-node %p normalised to a λ-node, about to β-contract.\n",t);
            return whnf(reduceRedex (t));
        } else {
            DEBUG_PRINTF("Fun-child of @-node %p didn't normalise to a λ-node, normalisation of @-node is blocked.\n",t);
            return t;
        }}
    case Op2T:  {return whnf(reduceOp2(t));}
    case Op1T:  {return whnf(reduceOp1(t));}
    case Op0T:  {return whnf(reduceOp0(t));}
    default: {
        DEBUG_PRINTF("Normalisation of %p blocked or completed, returning it without further modification.\n",t);
        return t;
        }
    }
}

///////////////
// Test data //
///////////////

// The term (λ x . x)
Term* build_id (void) {
    VarType* x = mkVar();
    return lam(x, var(x));
}

// The term (λ x . x)(λ y . y)
Term* build_ex2 (void) {
    return app (build_id(), build_id());
}

// The term (E E) where shared E = (λ x . x)
Term* build_ex3 (void) {
    Term* id = build_id();
    return app (id, id);
}

// 'chain of perals' examples from the BUBS 2010 paper
// i.e. stack of shared @-nodes, n deep, with id at the bottom
Term* build_pearls (unsigned int n) {
    Term* t = build_id();
    for (; n > 0; n--) {
        t = app(t,t);
    }
    return t;
}

// The term ((λ x . 4) 5)
Term* build_ex5 (void) {
    VarType* x = mkVar ();
    return app(lam(x, prim(4)), prim(5));
}

// A prim-op for addition
Term* op_add(Term** t1, Term** t2) {
    Term* t1n = whnf(*t1);
    Term* t2n = whnf(*t2);
    return prim(term2Prim(t1n)->primData + term2Prim(t2n)->primData);
}

// The term (11 + 25)
Term* build_ex6 (void) {
    return op2(op_add, prim (11), prim (25));
}

// The term (λ x . λ y . x + y)
Term* build_add (void) {
    VarType* x = mkVar();
    VarType* y = mkVar();
    return lam(x, lam(y, op2(op_add, var(x), var(y))));
}

// The term (λ f . f 11 25) (λ x . λ y . x + y)
Term* build_ex8 (void) {
    VarType* f = mkVar();
    Term* t1 = lam(f, app(app(var(f), prim(11)), prim(25)));
    return app(t1, build_add());
}

// The term ((1 + 2) + 3)
Term* build_ex9 (void) {
    return op2(op_add, op2(op_add, prim(1), prim(2)), prim(3));
}

// The term (A (A 1 2) 3) where A = (λ x . λ y . x + y)
Term* build_ex10 (void) {
    Term* a = build_add();
    Term* a12 = app(app(a, prim(1)),prim(2));
    Term* a123 = app(app(a, a12), prim(3));
    return a123;
}

// The term (λ f . f (f 1 2) 3) (λ x . λ y . x + y)
Term* build_ex11 (void) {
    VarType* f = mkVar ();
    Term* f12 = app(app(var (f), prim (1)), prim (2));
    Term* f123 = app(app(var (f), f12), prim (3));
    return app(lam(f, f123), build_add());
}


// The term (λ x . x + 10) 
Term* build_plus10 (void) {
    VarType* x = mkVar ();
    return lam(x, op2(op_add, var (x), prim (10)));
}

// The term (P (P 0))) where P = (λ x . x + 10) 
Term* build_ex13 (void) {
    Term* p = build_plus10 ();
    return app(p, app(p, prim (0)));
}

// The term (P (P (P (P (P (P (P 0))))))) where P = (λ x . x + 10) 
Term* build_ex14 (void) {
    Term* p = build_plus10 ();
    return app(p, app(p, app(p, app(p, app(p, app(p, app(p, prim (0))))))));
}

// The term (λ f . f (f 0)) (λ x . x + 10) 
Term* build_ex15 (void) {
    VarType* f = mkVar ();
    Term* lff0 = lam(f, app(var (f), app(var (f), prim (0))));
    return app (lff0, build_plus10());
}

// A prim-op for sequencing evaluation, and debug-printing numbers as a side effect
//  Based on https://hackage.haskell.org/package/base-4.18.0.0/docs/Debug-Trace.html#v:trace
//  (but prints numbers rather than strings)
Term* op_trace(Term** t1, Term** t2) {
    Term* t1n = whnf(*t1);
    printf ("%d\n", term2Prim(t1n)->primData);
    return *t2;
}

// The term (λ f . λ g . (f (1 trace 5)) + (g (2 trace 6))) 
Term* build_ex16 (void) {
    VarType* f = mkVar ();
    VarType* g = mkVar ();
    return lam(f, lam(g, op2(op_add,
        app(var (f), op2(op_trace, prim (1), prim (5))),
        app(var (g), op2(op_trace, prim (2), prim (6))))));
}

// The term ( (λ f . λ g . (f (1 trace 5)) + (g (2 trace 6))) (λ x . x) (λ y . 100) ) 
Term* build_ex17 (void) {
    VarType* x = mkVar ();
    VarType* y = mkVar ();
    return app(app(build_ex16(), lam(x, var (x))), lam(y, prim (100)));
}

// Scott-encoded 'true' constructor, (λ kt . λ kf . kt) 
Term* build_scott_true (void) {
    VarType* kt = mkVar ();
    VarType* kf = mkVar ();
    return lam(kt, lam(kf, var (kt)));
}

// Scott-encoded 'false' constructor, (λ kt . λ kf . kf) 
Term* build_scott_false (void) {
    VarType* kt = mkVar ();
    VarType* kf = mkVar ();
    return lam(kt, lam(kf, var (kf)));
}

// Priomop for testing if a number is zero. Returns a scott-encoded boolean 
Term* op_eqz (Term** t) {
    Term* tn = whnf(*t);
    if (term2Prim(tn)->primData == 0) {
        return build_scott_true();
    } else {
        return build_scott_false();
    }
}

// The term ((eqz 3) 100 200) 
Term* build_ex20 (void) {
    return app(app(op1(op_eqz, prim (3)),prim (100)),prim (200));
}

// The term ((eqz (0 + 0)) 100 200) 
Term* build_ex21 (void) {
    return app(app(op1(op_eqz, op2(op_add, prim (0), prim (0))),prim (100)),prim (200));
}

// A primop for subtraction 
Term* op_sub(Term** t1, Term** t2) {
    Term* t1n = whnf(*t1);
    Term* t2n = whnf(*t2);
    return prim (term2Prim(t1n)->primData - term2Prim(t2n)->primData);
}

// A primop for multiplication 
Term* op_mul(Term** t1, Term** t2) {
    Term* t1n = whnf(*t1);
    Term* t2n = whnf(*t2);
    return prim (term2Prim(t1n)->primData * term2Prim(t2n)->primData);
}

// A primop for less-than-or-equal testing. Returns a scott-encoded boolean. 
Term* op_leq(Term** t1, Term** t2) {
    Term* t1n = whnf(*t1);
    Term* t2n = whnf(*t2);
    if (term2Prim(t1n)->primData <= term2Prim(t2n)->primData) {
        return build_scott_true ();
    } else {
        return build_scott_false ();
    }
}

// The term fac = (λ n . (eqz n) 1 (n * {fac} (n - 1)))
//  Where curly braces denote macro expansion via an op0 node
Term* build_fac (void) {
    VarType* n = mkVar ();
    return lam(n, app(
            app(op1(op_eqz, var (n)), prim (1)),
            op2(op_mul,
                var (n),
                app(op0(build_fac),op2(op_sub, var (n), prim (1))))
        ));
}

// The term fib = (λ n . (n ≤ 1) 1 ({fib} (n - 1) + {fib} (n - 2)) )
//  Where curly braces denote macro expansion via an op0 node
Term* build_fib (void) {
    VarType* n = mkVar ();
    Term* guard = app(op2(op_leq, var (n), prim (1)), prim (1));
    Term* rec1 = app(op0(build_fib), op2(op_sub,var (n), prim (1)));
    Term* rec2 = app(op0(build_fib), op2(op_sub,var (n), prim (2)));
    return lam(n, app(guard,op2(op_add,rec1,rec2)));
}

// A primop for modulus 
Term* op_mod(Term** t1, Term** t2) {
    Term* t1n = whnf(*t1);
    Term* t2n = whnf(*t2);
    return prim (term2Prim(t1n)->primData % term2Prim(t2n)->primData);
}

// A primop for division 
Term* op_div(Term** t1, Term** t2) {
    Term* t1n = whnf(*t1);
    Term* t2n = whnf(*t2);
    return prim (term2Prim(t1n)->primData / term2Prim(t2n)->primData);
}

// A primop for integer equality testing. Returns a scott-encoded boolean. 
Term* op_ieq(Term** t1, Term** t2) {
    Term* t1n = whnf(*t1);
    Term* t2n = whnf(*t2);
    if (term2Prim(t1n)->primData == term2Prim(t2n)->primData) {
        return build_scott_true();
    } else {
        return build_scott_false();
    }
}

// The term collatz = (λ n . (n == 1) 1 ( (n % 2 ==0) ({collatz} (n / 2)) ({collatz} (3 * n + 1)) ) )
//  Where curly braces denote macro expansion via an op0 node
Term* build_collatz (void) {
    VarType* n = mkVar ();
    Term* guard = app(op2(op_ieq, var (n), prim (1)), prim (1));
    Term* test = op1(op_eqz, op2(op_mod, var (n), prim (2)));
    Term* rec1 = app(op0(build_collatz), op2(op_div, var (n), prim (2)));
    Term* rec2 = app(op0(build_collatz), op2(op_add, op2(op_mul, prim (3), var (n)), prim (1)));
    return lam(n, app(guard, app(app(test,rec1),rec2)));
}

// The term (E (λ m . m * 2)) + (E (λ n . n * 3)))
//  Where shared E = (λ f . f (f 1))
Term* build_ex25 (void) {
    VarType* f = mkVar ();
    Term* e = lam(f, app(var (f), app(var (f), prim (1))));
    VarType* m = mkVar ();
    Term* x2 = lam(m, op2(op_mul, var (m), prim (2)));
    VarType* n = mkVar ();
    Term* x3 = lam(n, op2(op_mul, var (n), prim (3)));
    return op2(op_add, app(e,x2), app(e, x3));
}

// The term ((M 1 2) + (M 3 4)))
//  Where shared M = (λ x . λ y . x * y)
Term* build_ex26 (void) {
    VarType* x = mkVar ();
    VarType* y = mkVar ();
    Term* m = lam(x, lam(y, op2(op_mul, var (x), var (y))));
    return op2(op_add, app(app(m,prim (1)), prim (2)), app(app(m, prim (3)), prim (4)));
}

////////////////////
// Complete tests //
////////////////////

void test_ex1(void) {pretty(whnf(build_id()));}     // expected output: printout of (λ x . x)
void test_ex2(void) {pretty(whnf(build_ex2()));}    // expected output: printout of (λ y . y)
void test_ex3(void) {pretty(whnf(build_ex3()));}    // expected output: printout of (λ x . x)
void test_pearls(unsigned int n) {pretty(whnf(build_pearls(n)));}   // expected output: printout of (λ x . x)
void test_ex5(void) {pretty(whnf(build_ex5()));}    // expected output: printout of (prim 4)
void test_ex6(void) {pretty(whnf(build_ex6()));}    // expected output: printout of (prim 36)
void test_ex8(void) {pretty(whnf(build_ex8()));}    // expected output: printout of (prim 36)
void test_ex9(void) {pretty(whnf(build_ex9()));}    // expected output: printout of (prim 6)
void test_ex10(void) {pretty(whnf(build_ex10()));}  // expected output: printout of (prim 6)
void test_ex11(void) {pretty(whnf(build_ex11()));}  // expected output: printout of (prim 6)
void test_ex13(void) {pretty(whnf(build_ex13()));}  // expected output: printout of (prim 20)
void test_ex14(void) {pretty(whnf(build_ex14()));}  // expected output: printout of (prim 70)
void test_ex15(void) {pretty(whnf(build_ex15()));}  // expected output: printout of (prim 20)
void test_ex17(void) {pretty(whnf(build_ex17()));}  // expected output: 1, then printout of (prim 105)
void test_ex20(void) {pretty(whnf(build_ex20()));}  // expected output: printout of (prim 200)
void test_ex21(void) {pretty(whnf(build_ex21()));}  // expected output: printout of (prim 100)
void test_fac(unsigned int n) {pretty(whnf(app(build_fac(),prim(n))));} // expected output: printout of (prim <factorial of n>)
void test_fib(unsigned int n) {pretty(whnf(app(build_fib(),prim(n))));} // expected output: printout of (prim <nth fibonacci number>)
void test_collatz(unsigned int n) {pretty(whnf(app(build_collatz(),prim(n))));} // expected output: printout of (prim 1)
void test_ex25(void) {pretty(whnf(build_ex25()));}  // expected output: printout of (prim 13)
void test_ex26(void) {pretty(whnf(build_ex26()));}  // expected output: printout of (prim 14)

/////////////////
// Entry point //
/////////////////

int main (void) {
    Term* t = build_ex26();
    global_print_root = lam(mkVar(), t);    // make t a root to avoid GC bugs
    whnf(t);
    return 0;
}

