
// C port of the BUBS algorithm.

// Comments in this file focus on differences from the SML version

//////////////////
// Dependencies //
//////////////////

#define _GNU_SOURCE
#include"bubs.h"
#include<stdlib.h>
#include<assert.h>
#include<stdbool.h>
#include<stddef.h>
#include<stdio.h>
#include<stdarg.h>

#ifdef CONFIG_ENABLE_DEBUG_PRINTFLN
#define DEBUG_PRINTFLN(...) ((printf("// "),printf(__VA_ARGS__),printf("\n"),fflush(stdout)))
#else
#define DEBUG_PRINTFLN(...)
#endif

#ifdef CONFIG_USE_DLADDR
// Print function pointers by resolving them to strings
// Pros: human-friendly, well-defined
// Cons: requires Linux and `gcc -rdynamic -ldl`
#include <dlfcn.h>
#define PRINT_FUN_PTR(p)({Dl_info tmp;dladdr(p,&tmp);printf("%s",tmp.dli_sname);})
#else
// Print function pointers directly as hex addresses
// Pros: portability
// Cons: undefined behaviour, not human-friendly
#define PRINT_FUN_PTR(p)(printf("%p",p))
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
    bool visited;  // used to avoid over-pretty-printing
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
static void dl_assert_wf_cc(ChildCell* cc){
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
static void dl_assert_wf(ChildCell* cc) {
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
static void dl_set_link (ChildCell* cc1, ChildCell* cc2) {
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
static bool dl_is_singleton (ChildCell* cc) {
    dl_assert_wf(cc);

    if (cc == NULL) {return false;}
    bool b1 = cc == cc->succ;
    bool b2 = cc == cc->pred;

    assert (b1 == b2); 
    return b1;
}

// Initialize a ChildCell as a singleton with an initial value
//  Repaces new(), since this function does not do allocation.
static void dl_init (ChildCellTag tag, Term* child, ChildCell* cc) {
    assert (cc != NULL);

    cc->tag = tag;
    cc->succ = cc;
    cc->pred = cc;
    cc->child = child;

    dl_assert_wf(cc);
}

// Unlink a ChildCell from its surrounding list,
// and return another element from that list (NULL if there are no others)
static ChildCell* dl_remove (ChildCell* cc) {
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
static void dl_union (ChildCell* a, ChildCell* c) {
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

// Assert that two ChildCell s are on the same DLL
static void dl_assert_member(ChildCell* a, ChildCell* b) {
    dl_assert_wf(a); assert(a != NULL);
    dl_assert_wf(b); assert(b != NULL);
    bool found = false;
    ChildCell* i = a;
    do {
        if (i == b) {
            found = true;
            break;
        }
        i = i->succ;
    } while(i != a);
    assert (found);
}

///////////////////////////////////////////////
// Tests for the ChildCell manipulating code //
///////////////////////////////////////////////

// Property under test: init() creates a singleton
// static void dl_test_singleton_init (void) {
//     Term t; // no need to init this to test the DLL lib
//     ChildCell cc;
//     dl_init(LamBody, &t, &cc);
//     assert(dl_is_singleton(&cc));
// }

// // Property under test: union() works as expected
// static void dl_test_singleton_remove (void) {
//     Term t1; ChildCell cc1; dl_init(LamBody, &t1, &cc1);
//     Term t2; ChildCell cc2; dl_init(LamBody, &t2, &cc2);
//     Term t3; ChildCell cc3; dl_init(LamBody, &t3, &cc3);
//     Term t4; ChildCell cc4; dl_init(LamBody, &t4, &cc4);
//     dl_union(&cc1,&cc2);
//     dl_union(&cc3,&cc4);
//     dl_union(&cc4,&cc1);
//     assert ((&cc1)->succ->succ->succ->succ == &cc1);
//     assert ((&cc2)->succ->succ->succ->succ == &cc2);
//     assert ((&cc3)->succ->succ->succ->succ == &cc3);
//     assert ((&cc4)->succ->succ->succ->succ == &cc4);
//     assert ((&cc1)->pred->pred->pred->pred == &cc1);
//     assert ((&cc2)->pred->pred->pred->pred == &cc2);
//     assert ((&cc3)->pred->pred->pred->pred == &cc3);
//     assert ((&cc4)->pred->pred->pred->pred == &cc4);
// }

////////////////////////////////////
// Coercion & Traversal functions //
////////////////////////////////////

// Inverse of C's arrow operator _->_
// Implementation from: https://en.wikipedia.org/wiki/Offsetof
// See also: http://www.kroah.com/log/linux/container_of.html
#define container_of(ptr, type, member) ((type *)((char *)(1 ? (ptr) : &((type *)0)->member) - offsetof(type, member)))

// Get the node containing a ChildCell
static Term* ccParent(ChildCell* cc){
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
static LamType* term2Lam(Term* t)
    {assert(t->tag == LamT); return container_of(t, LamType, header);}
static AppType* term2App(Term* t) 
    {assert(t->tag == AppT); return container_of(t, AppType, header);}
static Op2Type* term2Op2(Term* t)
    {assert(t->tag == Op2T); return container_of(t, Op2Type, header);}
static Op1Type* term2Op1(Term* t)
    {assert(t->tag == Op1T); return container_of(t, Op1Type, header);}
static Op0Type* term2Op0(Term* t)
    {assert(t->tag == Op0T); return container_of(t, Op0Type, header);}
static PrimType* term2Prim(Term* t)
    {assert(t->tag == PrimT); return container_of(t, PrimType, header);}

// API function
unsigned int from_prim(Term* t){
    return term2Prim(t)->primData;
} 

////////////////////////////
// Misc. setter functions //
////////////////////////////

// Add uplink(s) to a node's parent-list.
// Precondition: the two lists must be different.
static void addToParents(Term* node, ChildCell* cc) {
    assert(node != NULL);
    assert(cc != NULL);
    if (node->parents == NULL) {
        node->parents = cc;
    } else {
        dl_union (node->parents , cc);
    }
}

// Replace one term w/another in the DAG.
// Leaves the old term dead.
// Precondition: the terms are distinct
static void replaceTerm(Term* old, Term* new) {
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

// Initialise the fields of a Term header
static void init_Term(TermTag tag, Term* n){
    n->tag = tag;
    n->visited = false;
    n->parents = NULL;
}

// Construct a var-node on the heap
// Under the hood, this allocates a surrounding λ-node too.
// This function is not marked 'static' because it is in the API
VarType* mkVar (void) {
    LamType* lamNode = malloc(sizeof(LamType));

    init_Term(VarT, &(lamNode->lamVar.header));
    return &(lamNode->lamVar);
}

// Initialize a λ-node on the heap
static LamType* mkLam (bool clone, VarType* var, Term* body) {
    LamType* lamNode = container_of(var, LamType, lamVar);

    init_Term(LamT, &(lamNode->header));

    // lamNode->lamVar already initialized by mkVar
    dl_init(LamBody, body, &(lamNode->lamBody));
    if (clone){
        lamNode->copy = lamNode;
    } else {
        lamNode->copy = NULL;
        addToParents(body, &(lamNode->lamBody));
    }
    return lamNode;
}

// Construct an @-node on the heap
static AppType* mkApp (bool clone, Term* fun, Term* arg) {
    AppType* appNode = malloc(sizeof(AppType));

    init_Term(AppT, &(appNode->header));
    dl_init(AppFun, fun, &(appNode->appFun));
    dl_init(AppArg, arg, &(appNode->appArg));
    if (clone){
        appNode->copy = appNode;
    } else {
        appNode->copy = NULL;
        addToParents(fun, &(appNode->appFun));
        addToParents(arg, &(appNode->appArg));
    }
    return appNode;
}

static Op2Type* mkOp2 (bool clone, Term* (*primop)(Term** , Term**), Term* arg1, Term* arg2) {
    Op2Type* op2Node = malloc(sizeof(Op2Type));

    init_Term(Op2T, &(op2Node->header));
    op2Node->primop = primop;
    dl_init(Op2Arg1, arg1, &(op2Node->op2Arg1));
    dl_init(Op2Arg2, arg2, &(op2Node->op2Arg2));
    if (clone) {
        op2Node->copy = op2Node;
    } else {
        op2Node->copy = NULL;
        addToParents(arg1, &(op2Node->op2Arg1));
        addToParents(arg2, &(op2Node->op2Arg2));
    }
    return op2Node;
}

static Op1Type* mkOp1 (Term* (*primop)(Term**), Term* arg) {
    Op1Type* op1Node = malloc(sizeof(Op1Type));

    init_Term(Op1T, &(op1Node->header));
    op1Node->primop = primop;
    dl_init(Op1Arg, arg, &(op1Node->op1Arg));
    addToParents(arg, &(op1Node->op1Arg));
    return op1Node;
}

static Op0Type* mkOp0 (Term* (*primop)(void)) {
    Op0Type* op0Node = malloc(sizeof(Op0Type));

    init_Term(Op0T, &(op0Node->header));
    op0Node->primop = primop;
    return op0Node;
}

static PrimType* mkPrim (unsigned int primData) {
    PrimType* primNode = malloc(sizeof(PrimType));

    init_Term(PrimT, &(primNode->header));
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
static void printCCTag (ChildCellTag t) {
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
static void printCC (ChildCell* cc) {
    assert(cc != NULL);
    printCCTag(cc->tag);
    printf(" %12p", ccParent(cc));
}

// Print the parents of a term to stdout, followed by newline
static void printParents (Term* t) {
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

// Print a term to stdout (pre-order depth-first traversal w/ cut-off).
// Tests & sets the 'visited' flag
static void pretty_set (Term* t) {
    if (t->visited) {
        return;
    } else {
        t->visited = true;
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
                pretty_set(lamNode->lamBody.child);
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
                pretty_set(appNode->appFun.child);
                pretty_set(appNode->appArg.child);
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
                pretty_set(op2Node->op2Arg1.child);
                pretty_set(op2Node->op2Arg2.child);
                break;}
            case Op1T: {
                Op1Type* op1Node = term2Op1(t);
                printf("<op1> %12p%50s",
                    op1Node->op1Arg.child,
                    ""
                    );
                printParents(t);
                pretty_set(op1Node->op1Arg.child);
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
}
// Reset the 'visited' flag set by pretty_set.
static void pretty_clear (Term* t) {
    if (!t->visited) {
        return;
    } else {
        t->visited = false;
        switch (t->tag) {
            case VarT: {break;}
            case LamT: {
                LamType* lamNode = term2Lam(t);
                pretty_clear(lamNode->lamBody.child);
                break;}
            case AppT: {
                AppType* appNode = term2App(t);
                pretty_clear(appNode->appFun.child);
                pretty_clear(appNode->appArg.child);
                break;}
            case Op2T: {
                Op2Type* op2Node = term2Op2(t);
                pretty_clear(op2Node->op2Arg1.child);
                pretty_clear(op2Node->op2Arg2.child);
                break;}
            case Op1T: {
                Op1Type* op1Node = term2Op1(t);
                pretty_clear(op1Node->op1Arg.child);
                break;}
            case Op0T: {break;}
            case PrimT: {break;}
            default: {assert(false);}
        }
    }
}

// Pretty-print a term
// This function is not marked 'static' because it is in the API
void pretty(Term* t){
    assert(t != NULL);
    assert(!t->visited);// should hold for sub-terms too, but this is hard to test
    pretty_set(t);
    assert(t->visited); // should hold for sub-terms too, but this is hard to test
    pretty_clear(t);
}


// Print a ChildCell as a DOT sub-node
static void dump_dot_CC_node(ChildCell* cc){
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
static void dump_dot_CC_edges(ChildCell* cc){
    assert(cc != NULL);

    // Print (cc->child)
    if (cc->child != NULL){
        printf("n%p:",ccParent(cc));printCCTag(cc->tag);printf("_child:c ->");
        printf("n%p:parents [color=black id=cc%p_child];\n", cc->child, cc);
    }

    // Print (cc->pred)
    ChildCell* ccp = cc->pred;
    printf("n%p:", ccParent(cc ));printCCTag(cc ->tag);printf("_pred -> ");
    printf("n%p:", ccParent(ccp));printCCTag(ccp->tag);printf("_succ ");
    printf("[constraint=false,color=lightgrey, id=cc%p_pred];\n",cc);

    // Print (cc->succ)
    ChildCell* ccs = cc->succ;
    printf("n%p:", ccParent(cc ));printCCTag(cc ->tag);printf("_succ -> ");
    printf("n%p:", ccParent(ccs));printCCTag(ccs->tag);printf("_pred ");
    printf("[constraint=false,color=lightgrey, id=cc%p_succ];\n",cc);
}

// Dump graphviz DOT code to print a term. Recursive.
// Tests & sets the 'visited' flag
static void dump_dot_Term_set(Term* t){
    if (t == NULL) {
        return;
    } else if (t->visited) {
        return;
    } else {
        t->visited = true;
        switch (t->tag){
            case VarT: {
                printf("n%p [label =\"VarT | <parents>\", id=n%p];\n",t,t);
                printf("\n");
                break;}
            case LamT: {
                LamType* lamNode = term2Lam(t);
                printf("n%p [label =\"LamT | <parents> | <copy> | <lamVar> ",t);
                dump_dot_CC_node(&(lamNode->lamBody));
                printf("\", id=n%p];\n",t);
                dump_dot_Term_set(lamNode->lamBody.child);
                dump_dot_Term_set(&(lamNode->lamVar.header));
                if (lamNode->copy != NULL) {
                    Term* copy = &(lamNode->copy->header);
                    dump_dot_Term_set(copy);
                    printf("n%p:copy:c -> n%p [id = n%p_copy, color=darkgreen, headclip=true, constraint=false];\n", t, copy, t);
                }
                printf("\n");
                dump_dot_CC_edges(&(lamNode->lamBody));
                printf("n%p:lamVar -> n%p [headclip=true, color=darkgoldenrod, dir=none, id=n%p_lamvar];\n",
                t,&(lamNode->lamVar.header),t);
                break;}
            case AppT: {
                AppType* appNode = term2App(t);
                printf("n%p [label =\"AppT | <parents> | <copy> ",t);
                dump_dot_CC_node(&(appNode->appFun));
                dump_dot_CC_node(&(appNode->appArg));
                printf("\", id=n%p];\n",t);
                dump_dot_Term_set(appNode->appFun.child);
                dump_dot_Term_set(appNode->appArg.child);
                if (appNode->copy != NULL) {
                    Term* copy = &(appNode->copy->header);
                    dump_dot_Term_set(copy);
                    printf("n%p:copy:c -> n%p [id = n%p_copy, color=darkgreen, headclip=true, constraint=false];\n", t, copy, t);
                }
                printf("\n");
                dump_dot_CC_edges(&(appNode->appFun));
                dump_dot_CC_edges(&(appNode->appArg));
                break;}
            case Op2T: {
                Op2Type* op2Node = term2Op2(t);
                printf("n%p [label =\"Op2T | <parents> | <copy> | ",t);
                PRINT_FUN_PTR(op2Node->primop);
                dump_dot_CC_node(&(op2Node->op2Arg1));
                dump_dot_CC_node(&(op2Node->op2Arg2));
                printf("\", id=n%p];\n",t);
                dump_dot_Term_set(op2Node->op2Arg1.child);
                dump_dot_Term_set(op2Node->op2Arg2.child);
                if (op2Node->copy != NULL) {
                    Term* copy = &(op2Node->copy->header);
                    dump_dot_Term_set(copy);
                    printf("n%p:copy:c -> n%p [id = n%p_copy, color=darkgreen, headclip=true, constraint=false];\n", t, copy, t);
                }
                printf("\n");
                dump_dot_CC_edges(&(op2Node->op2Arg1));
                dump_dot_CC_edges(&(op2Node->op2Arg2));
                break;}
            case Op1T: {
                Op1Type* op1Node = term2Op1(t);
                printf("n%p [label =\"Op1T | <parents> | <copy> | ",t);
                PRINT_FUN_PTR(op1Node->primop);
                dump_dot_CC_node(&(op1Node->op1Arg));
                printf("\", id=n%p];\n",t);
                dump_dot_Term_set(op1Node->op1Arg.child);
                printf("\n");
                dump_dot_CC_edges(&(op1Node->op1Arg));
                break;}
            case Op0T: {
                Op0Type* op0Node = term2Op0(t);
                printf("n%p [label =\"Op0T | <parents> | <copy> | ",t);
                PRINT_FUN_PTR(op0Node->primop);
                printf(" \", id=n%p];\n",t);
                printf("\n");
                break;}
            case PrimT: {
                PrimType* primNode = term2Prim(t);
                printf("n%p [label =\"PrimT | <parents> | <primData> %d ",t, primNode->primData);
                printf("\", id=n%p];\n",t);
                printf("\n");
                break;}
            default: {assert(false);}
        }
        // printf("n%p [xlabel = \"%p\"];\n",t,t);
        if (t->parents != NULL) {  // print parent pointer
            printf("n%p:parents:c -> n%p:", t, ccParent(t->parents));
            printCCTag(t->parents->tag);
            printf("_child [constraint=false, headclip=true, weight=0, color=brown, id=n%p_parents];\n",t);
        }
    }
}

// Clear the 'visited' flag set by dump_dot_Term_set
static void dump_dot_Term_clear(Term* t){
    if (t == NULL) {
        return;
    } else if (!t->visited) {
        return;
    } else {
        t->visited = false;
        switch (t->tag){
            case VarT: {break;}
            case LamT: {
                LamType* lamNode = term2Lam(t);
                dump_dot_Term_clear(lamNode->lamBody.child);
                dump_dot_Term_clear(&(lamNode->lamVar.header));
                if (lamNode->copy != NULL) {dump_dot_Term_clear(&(lamNode->copy->header));}
                break;}
            case AppT: {
                AppType* appNode = term2App(t);
                dump_dot_Term_clear(appNode->appFun.child);
                dump_dot_Term_clear(appNode->appArg.child);
                if (appNode->copy != NULL) {dump_dot_Term_clear(&(appNode->copy->header));}
                break;}
            case Op2T: {
                Op2Type* op2Node = term2Op2(t);
                dump_dot_Term_clear(op2Node->op2Arg1.child);
                dump_dot_Term_clear(op2Node->op2Arg2.child);
                if (op2Node->copy != NULL) {dump_dot_Term_clear(&(op2Node->copy->header));}
                break;}
            case Op1T: {
                Op1Type* op1Node = term2Op1(t);
                dump_dot_Term_clear(op1Node->op1Arg.child);
                break;}
            case Op0T: {break;}
            case PrimT: {break;}
            default: {assert(false);}
        }
    }
}

Term* global_print_root = NULL;

// Dump the whole BUBS heap to stdout.
// See the header file for usage more documentation.
void dump_dot(char* label, unsigned int n,...){
    printf("// BEGIN DOT DUMP\n");
    printf("digraph {\n");
    if (label != NULL){
        printf("label = \"%s\"\n",label);
    }
    printf("rankdir=TB;\n");
    printf("splines=false;\n");
    printf("node [shape=record];\n");
    printf("edge [headclip=false,tailclip=false,arrowtail=dot,dir=both];\n");
    printf("\n");

    // Extract var args. Based on https://jameshfisher.com/2016/11/23/c-varargs/
    va_list argp;
    va_start (argp, n);
    Term* nodes [n];
    char* colors [n];   
    for (unsigned int i = 0; i < n; i++){
        nodes[i] = va_arg(argp, Term*);
        colors[i] = va_arg(argp, char*);
        assert(nodes[i] != NULL);
        assert(colors[i] != NULL);
    }
    va_end(argp);

    // Draw the graph
    if(global_print_root != NULL)
        {dump_dot_Term_set(global_print_root);}
    for (unsigned int i = 0; i < n; i++){
        dump_dot_Term_set(nodes[i]);
    }

    // Clear 'visited' flags set by drawing the graph
    if(global_print_root != NULL)
        {dump_dot_Term_clear(global_print_root);}
    for (unsigned int i = 0; i < n; i++){
        dump_dot_Term_clear(nodes[i]);
    }

    // Highlight the selected nodes
    for (unsigned int i = 0; i < n; i++){
        printf("n%p [style=filled,fillcolor = %s];\n",
        nodes[i],colors[i]);
    }
    printf("}\n");
    printf("// END DOT DUMP\n");
    fflush(stdout);
}


////////////////////////
// Garbage collection //
////////////////////////

// Free a node (unless embedded in another node).
// Non-recursive.
static void dealloc (Term* t){
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
static void unlinkCC (ChildCell* cc) {
    assert(cc != NULL);
    if(cc->child != NULL){
        dl_assert_member(cc->child->parents,cc);
        ChildCell* other = dl_remove(cc);
        if (cc->child->parents == cc){
            cc->child->parents = other;
        }
    }
    assert(dl_is_singleton(cc));
}

// Garbage collect a node. 
static void collectNode(Term* t);

// Unlink a term from just one of its parents (using a given uplink),
//  and if this makes the child dead, then free it recursively
static void recUnlinkChild (ChildCell* cc) {
    unlinkCC (cc);
    collectNode(cc->child);
}

static void collectNode (Term* t) {
    DEBUG_PRINTFLN("Entering collectNode(%p)", t);
    if (t->parents == NULL) {
        DEBUG_PRINTFLN("Node %p is dead, freeing recursively.", t);
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
    } else {
        DEBUG_PRINTFLN("Node %p is live, leaving it alone.", t);
    }
    DEBUG_PRINTFLN("Leaving collectNode(%p)", t);
}

// Replace some dead term 'old' with another term 'new',
//  then free 'old' recursively.
static Term* replaceAndCollect (Term* old , Term* new) {
    DEBUG_PRINTFLN("Entering replaceAndCollect(%p,%p)",old,new);
    assert(old != NULL); assert(old->parents != NULL);
    assert(new != NULL);

    replaceTerm(old, new);

    assert(new->parents != NULL);

    collectNode(old);

    assert(new->parents != NULL);

    DEBUG_PRINTFLN("Leaving replaceAndCollect(%p,%p)",old,new);
    return new;
}

// 'collectNode' is renamed to 'collect' in the API
void collect(Term* t) {
    collectNode(t);
}

/////////////////////////////////
// Upcopying and copy-clearing //
/////////////////////////////////

// See SML code for explanation of the algorithm
// Does NOT add link newly allocated nodes into co-parent lists.
static void upcopyUplinks (Term* newChild, ChildCell* cc) {
    if (cc == NULL) {return;}   // No uplinks in list => stop recursion
    // Have uplinks => loop over them, spawning upcopies at each
    ChildCell* i = cc;
    DEBUG_PRINTFLN("Begin upcopying parents of %p, inserting %p.", cc->child, newChild);
    do {Term* t = ccParent(i);
        DEBUG_PRINTFLN("In a loop upcopying into parents of %p.", cc->child);
        DEBUG_PRINTFLN("Upcopy entered %p (a parent of %p), inserting %p.", t, i->child, newChild);
        assert(i->child == cc->child);
        #ifdef CONFIG_DUMP_DOT_IN_REDUCTION
            dump_dot("Upcopying",3, newChild,"lightblue", i->child, "darkgreen", t, "lightgreen");
        #endif
        switch (i->tag){    
        case LamBody:{
            LamType* lamNode = term2Lam(t);
            DEBUG_PRINTFLN("Cloning a λ-node from its only child.");
            if (lamNode->copy != NULL) {
                DEBUG_PRINTFLN("Copied up into an already-copied λ-node. "
                "Mutating the existing copy at %p and quitting.",
                &(lamNode->copy->header));
                lamNode->copy->lamBody.child = newChild;
            } else {
                VarType* new_var = mkVar();
                LamType* new_lam = mkLam(true, new_var, newChild);
                DEBUG_PRINTFLN("Allocated a copy of the λ-node on the heap, at %p.",&(new_lam->header));
                lamNode->copy = new_lam;
                DEBUG_PRINTFLN("Recursively upcopying the λ-var. "
                " (this should terminate somewhere in newChild)");
                upcopyUplinks(&(new_lam->lamVar.header), lamNode->lamVar.header.parents);
                DEBUG_PRINTFLN("Recursively upcopying parents of the λ-node at %p.",t);
                upcopyUplinks(&(new_lam->header), lamNode->header.parents);
            }
            break;}

        case AppFun: {
            AppType* appNode = term2App(t);
            DEBUG_PRINTFLN("Cloning an @-node from the fun side.");
            if (appNode->copy != NULL) {
                DEBUG_PRINTFLN("Copied up into an already-copied @-node. "
                "Mutating the existing copy at %p and quitting.",
                &(appNode->copy->header));
                appNode->copy->appFun.child = newChild;
            } else {
                AppType* new_app = mkApp(true, newChild, appNode->appArg.child);
                DEBUG_PRINTFLN("Allocated a copy of the @-node, at %p.",&(new_app->header));
                appNode->copy = new_app;
                DEBUG_PRINTFLN("Recursively upcopying parents of the @-node");
                upcopyUplinks (&(new_app->header), appNode->header.parents);
            }
            ;break;}

        case AppArg: {
            AppType* appNode = term2App(t);
            DEBUG_PRINTFLN("Cloning an @-node from the arg side.");
            if (appNode->copy != NULL) {
                DEBUG_PRINTFLN("Copied up into an already-copied @-node. "
                "Mutating the existing copy at %p and quitting.",
                &(appNode->copy->header));
                appNode->copy->appArg.child = newChild;
            } else {
                AppType* new_app = mkApp(true, appNode->appFun.child, newChild);
                DEBUG_PRINTFLN("Allocated a copy of the @-node, at %p.",&(new_app->header));
                appNode->copy = new_app;
                DEBUG_PRINTFLN("Recursively upcopying parents of the @-node");
                upcopyUplinks (&(new_app->header), appNode->header.parents);
            }
            ;break;}

        case Op2Arg1: {
            Op2Type* op2Node = term2Op2(t);
            DEBUG_PRINTFLN("Cloning an op2-node from the arg1 side.");
            if (op2Node->copy != NULL) {
                DEBUG_PRINTFLN("Copied up into an already-copied op2-node. "
                "Mutating the existing copy at %p and quitting.",
                &(op2Node->copy->header));
                op2Node->copy->op2Arg1.child = newChild;
            } else {
                Op2Type* new_op2 = mkOp2(true, op2Node->primop, newChild, op2Node->op2Arg2.child);
                DEBUG_PRINTFLN("Allocated a copy of the op2-node, at %p.",&(new_op2->header));
                op2Node->copy = new_op2;
                DEBUG_PRINTFLN("Recursively upcopying parents of the op2-node.");
                upcopyUplinks (&(new_op2->header), op2Node->header.parents);
            }
            ;break;}

        case Op2Arg2: {
            Op2Type* op2Node = term2Op2(t);
            DEBUG_PRINTFLN("Cloning an op2-node from the arg2 side.");
            if (op2Node->copy != NULL) {
                DEBUG_PRINTFLN("Copied up into an already-copied op2-node. "
                "Mutating the existing copy at %p and quitting.",
                &(op2Node->copy->header));
                op2Node->copy->op2Arg2.child = newChild;
            } else {
                Op2Type* new_op2 = mkOp2(true, op2Node->primop, op2Node->op2Arg1.child, newChild);
                DEBUG_PRINTFLN("Allocated a copy of the op2-node, at %p.",&(new_op2->header));
                op2Node->copy = new_op2;
                DEBUG_PRINTFLN("Recursively upcopying parents of the op2-node");
                upcopyUplinks (&(new_op2->header), op2Node->header.parents);
            }
            ;break;}

        case Op1Arg: {
            Op1Type* op1Node = term2Op1(t);
            DEBUG_PRINTFLN("Cloning an op1 from its only child.");
            Op1Type* new_op1 = mkOp1(op1Node->primop, newChild);
            DEBUG_PRINTFLN("Recursively upcopying parents of the op1-node.");
            upcopyUplinks(&(new_op1->header), op1Node->header.parents);
            break;}
        default: {assert(false);}
        }
        #ifdef CONFIG_DUMP_DOT_IN_REDUCTION
            dump_dot("Upcopied",3, newChild,"lightblue", i->child, "darkgreen", t, "lightgreen");
        #endif
        i = i->succ;
    } while (i != cc);
    DEBUG_PRINTFLN("Done upcopying parents of %p, inserting %p.", cc->child, newChild);
}

static void linkCC(ChildCell* cc){
    assert(dl_is_singleton(cc));
    addToParents(cc->child, cc);
}

// cleanUplinks follow the recursion path of upcopyUplinks,
// but clearing the copy slots instead of setting them, and installing
// up- and co-parent- links (see the paper for why this can't be done in upcopyUplinks)
static void cleanUplinks(ChildCell* cc) {
    if (cc == NULL) {return;}   // No uplinks in list => stop recursion
    // Have uplinks => loop over them, spawning upcleans at each
    ChildCell* i = cc;
    do {Term* node = ccParent(i);
        DEBUG_PRINTFLN("Upcleaning into %p.",node);
        switch (i->tag){
        case LamBody: {
            LamType* lamNode = term2Lam(node);
            if (lamNode->copy != NULL){
                #ifdef CONFIG_DUMP_DOT_IN_REDUCTION
                    dump_dot("Upcleaning",2,node,"lightgreen",&(lamNode->copy->header),"lightblue");
                #endif
                linkCC(&(lamNode->copy->lamBody));
                lamNode->copy->copy = NULL;
                lamNode->copy = NULL;
                cleanUplinks(lamNode->lamVar.header.parents);
                cleanUplinks(node->parents);
            }
            break;}
        case AppFun:    // fall through
        case AppArg: {
            AppType* appNode = term2App(ccParent(i));
            if (appNode->copy != NULL) {
                #ifdef CONFIG_DUMP_DOT_IN_REDUCTION
                    dump_dot("Upcleaning",2,node,"lightgreen",&(appNode->copy->header),"lightblue");
                #endif
                linkCC(&(appNode->copy->appFun));
                linkCC(&(appNode->copy->appArg));
                appNode->copy->copy = NULL;
                appNode->copy = NULL;
                cleanUplinks(node->parents);
            }
            break;}
        case Op2Arg1:   // fall through
        case Op2Arg2: {
            Op2Type* op2Node = term2Op2(node);
            if (op2Node->copy != NULL) {
                #ifdef CONFIG_DUMP_DOT_IN_REDUCTION
                    dump_dot("Upcleaning",2,node,"lightgreen",&(op2Node->copy->header),"lightblue");
                #endif
                linkCC(&(op2Node->copy->op2Arg1));
                linkCC(&(op2Node->copy->op2Arg2));
                op2Node->copy->copy = NULL;
                op2Node->copy = NULL;
                cleanUplinks(node->parents);
            }
            break;}
        case Op1Arg: {
            #ifdef CONFIG_DUMP_DOT_IN_REDUCTION
                dump_dot("Upcleaning",1,node,"lightgreen");
            #endif
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
static Term* reduceRedex(Term* t) {
    DEBUG_PRINTFLN("Entering reduceRedex(%p)",t);

    // Get pointers to relevant sub-terms
    assert(t->tag == AppT);
    AppType* a = term2App(t);
    assert(a->appFun.child->tag == LamT);
    Term* lamterm = a->appFun.child;
    LamType* l = term2Lam(lamterm);
    Term* argterm = a->appArg.child;
    Term* varterm = &(l->lamVar.header);
    ChildCell* lampars = l->header.parents;

    #ifdef CONFIG_DUMP_DOT_IN_REDUCTION
        dump_dot("About to reduce β-redex",2,
        t,"orange",lamterm,"orange");
    #endif
    Term* result;

    if (dl_is_singleton(lampars)) {
        DEBUG_PRINTFLN("Single-parent fast path.");
        #ifdef CONFIG_DUMP_DOT_IN_REDUCTION
            dump_dot("About to substitute λ-body in place",4,
            t,"orange",lamterm,"orange",varterm,"darkgreen",argterm,"lightblue");
        #endif
        replaceTerm(varterm, argterm);
        #ifdef CONFIG_DUMP_DOT_IN_REDUCTION
            dump_dot("Replaced variable of single-parent λ-node",3,
            t,"orange",lamterm,"orange",argterm,"lightblue");
        #endif
        result = l->lamBody.child;
    }
    else if (varterm->parents == NULL) {
        DEBUG_PRINTFLN("Unused-variable fast path.");
        #ifdef CONFIG_DUMP_DOT_IN_REDUCTION
            dump_dot("Variable λ-node unused, no work to do",3,
            t,"orange",lamterm,"orange",varterm,"green");
        #endif
        result = l->lamBody.child;
    }
    else {
        DEBUG_PRINTFLN("General case of β-reduction.");

        // Stack-allocate a λ-node to collect the result of upcopy
        LamType tmp;
        init_Term(LamT,&(tmp.header));
        init_Term(VarT,&(tmp.lamVar.header));
        dl_init(LamBody, NULL, &(tmp.lamBody));
        DEBUG_PRINTFLN("&tmp == %p",&tmp);
        DEBUG_PRINTFLN("&(tmp.lamBody) == %p",&(tmp.lamBody));
        DEBUG_PRINTFLN("&(tmp.header) == %p",&(tmp.header));

        // Upcopy, starting at [var ↦ argterm], stopping at l
        tmp.copy = &tmp;
        l->copy = &tmp;
        #ifdef CONFIG_DUMP_DOT_IN_REDUCTION
            dump_dot("General case of β-reduction, about to upcopy",4,
            t,"orange",lamterm,"orange",varterm,"darkgreen",argterm,"lightblue");
        #endif
        upcopyUplinks(argterm, varterm->parents);

        // Extract the output of the upcopy
        assert(tmp.lamBody.child != NULL);
        result = tmp.lamBody.child;

        #ifdef CONFIG_DUMP_DOT_IN_REDUCTION
            dump_dot("Done upcopying to form the β-contractum, about to clean it up",3,
            t,"orange",lamterm,"orange",result,"olive");
        #endif
        // Upclean, starting at var, stopping at l
        l->copy = NULL;
        cleanUplinks(varterm->parents);

        #ifdef CONFIG_DUMP_DOT_IN_REDUCTION
            dump_dot("Cleaned up the β-contractum",3,
            t,"orange",lamterm,"orange",result,"olive");
        #endif
    }
    DEBUG_PRINTFLN("Leaving reduceRedex(%p), about to replace %p with %p",t, t, result);
    #ifdef CONFIG_DUMP_DOT_IN_REDUCTION
        dump_dot("Constructed the β-contractum",3,
        t,"orange",lamterm,"orange",result,"olive");
    #endif
    return replaceAndCollect(t, result);
}

// Reduce an op2-headed term
static Term* reduceOp2 (Term* t){
    DEBUG_PRINTFLN("Entering reduceOp2(%p)",t);
    assert(t->tag == Op2T);
    Op2Type* op2Node = term2Op2(t);
    #ifdef CONFIG_DUMP_DOT_IN_REDUCTION
        dump_dot("About to call function pointer in Op2 node",1,t,"orange");
    #endif
    Term* new_term = (op2Node->primop)(
        &(op2Node->op2Arg1.child),
        &(op2Node->op2Arg2.child));
    DEBUG_PRINTFLN("Leaving reduceOp2(%p), but first replacing %p with %p",t, t, new_term);
    return replaceAndCollect (t, new_term);
}

// Reduce an op1-headed term
static Term* reduceOp1 (Term* t){
    DEBUG_PRINTFLN("Entering reduceOp1(%p)",t);
    assert(t->tag == Op1T);
    Op1Type* op1Node = term2Op1(t);
    #ifdef CONFIG_DUMP_DOT_IN_REDUCTION
        dump_dot("About to call function pointer in Op1 node",1,t,"orange");
    #endif
    Term* new_term = (op1Node->primop)(
        &(op1Node->op1Arg.child));
    DEBUG_PRINTFLN("Leaving reduceOp1(%p), but first replacing %p with %p",t, t, new_term);
    return replaceAndCollect (t, new_term);
}

// Reduce an op0-headed term
static Term* reduceOp0 (Term* t){
    DEBUG_PRINTFLN("Entering reduceOp0(%p)",t);
    assert(t->tag == Op0T);
    Op0Type* op0Node = term2Op0(t);
    #ifdef CONFIG_DUMP_DOT_IN_REDUCTION
        dump_dot("About to call function pointer in Op0 node",1,t,"orange");
    #endif
    Term* new_term = (op0Node->primop)();
    DEBUG_PRINTFLN("Leaving reduceOp0(%p), but first replacing %p with %p",t, t, new_term);
    return replaceAndCollect (t, new_term);
}

///////////////////
// Normalisation //
///////////////////

// Reduce a term to weak-head normal form
Term* whnf(Term* t) {
    DEBUG_PRINTFLN("Entering whnf(%p)",t);
    assert(t != NULL);
    assert(t->parents != NULL); // normalising parent-less terms can cause subtle GC bugs
    #ifdef CONFIG_DUMP_DOT_ON_WHNF
        dump_dot("In whnf(), searching for terms to reduce",1,t,"yellow");
    #endif
    switch (t->tag) {
    case AppT:  {
        DEBUG_PRINTFLN("About to normalise fun-child of @-node %p",t);
        Term* norm_fun = whnf(term2App(t)->appFun.child);
        if (norm_fun->tag == LamT) {
            DEBUG_PRINTFLN("Fun-child of @-node %p normalised to a λ-node, about to β-contract.",t);
            return whnf(reduceRedex (t));
        } else {
            DEBUG_PRINTFLN("Fun-child of @-node %p didn't normalise to a λ-node, normalisation of @-node is blocked.",t);
            return t;
        }}
    case Op2T:  {return whnf(reduceOp2(t));}
    case Op1T:  {return whnf(reduceOp1(t));}
    case Op0T:  {return whnf(reduceOp0(t));}
    default: {
        DEBUG_PRINTFLN("Normalisation of %p blocked or completed, returning it without further modification.",t);
        return t;
        }
    }
}
