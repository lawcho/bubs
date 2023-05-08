
// Restricted interface for the BUBS evaluator

// Types
typedef struct VarType_s VarType;
typedef struct PrimType_s PrimType;
typedef struct Term_s Term;

// Operations for building terms on the heap.
VarType* mkVar(void);
Term* var(VarType* varNode);
Term* lam(VarType* var, Term* body);
Term* app (Term* fun, Term* arg);
Term* op2 (Term* (*primop)(Term** , Term**), Term* arg1, Term* arg2);
Term* op1 (Term* (*primop)(Term**), Term* arg);
Term* op0 (Term* (*primop)(void));
Term* prim (unsigned int data);

// Evaluate a term to Weak-Head Normal Form
//  Blocks if the term cannot be evalauted to WHNF.
//  Precondition: t has parents
Term* whnf(Term* t);

// Run the garbage collector at a term.
// No-op if the term has parents.
void collect(Term* t);

// Cast a term to a primtivie-data node and extract its value.
unsigned int from_prim (Term* t);

// Pretty-print a term to stdout.
void pretty(Term* t);

// Used in dump_dot
extern Term* global_print_root;

// Dump the whole BUBS heap on stdout, formatted into graphviz DOT code that draws it.
// Additionally, give the graph a label and highlight n nodes in n different colours.
// The graph is printed top-down from the following roots:
//  * The global variable global_print_root.
//  * The passed nodes to highlight.
void dump_dot(char* label, unsigned int n,...);
