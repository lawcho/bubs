
// Tests for the BUBS algorithm

#include"bubs.h"
#include<stdio.h>

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
    return prim(from_prim(t1n) + from_prim(t2n));
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
    printf ("%d\n", from_prim(t1n));
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
    if (from_prim(tn) == 0) {
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
    return prim (from_prim(t1n) - from_prim(t2n));
}

// A primop for multiplication 
Term* op_mul(Term** t1, Term** t2) {
    Term* t1n = whnf(*t1);
    Term* t2n = whnf(*t2);
    return prim (from_prim(t1n) * from_prim(t2n));
}

// A primop for less-than-or-equal testing. Returns a scott-encoded boolean. 
Term* op_leq(Term** t1, Term** t2) {
    Term* t1n = whnf(*t1);
    Term* t2n = whnf(*t2);
    if (from_prim(t1n) <= from_prim(t2n)) {
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
    return prim (from_prim(t1n) % from_prim(t2n));
}

// A primop for division 
Term* op_div(Term** t1, Term** t2) {
    Term* t1n = whnf(*t1);
    Term* t2n = whnf(*t2);
    return prim (from_prim(t1n) / from_prim(t2n));
}

// A primop for integer equality testing. Returns a scott-encoded boolean. 
Term* op_ieq(Term** t1, Term** t2) {
    Term* t1n = whnf(*t1);
    Term* t2n = whnf(*t2);
    if (from_prim(t1n) == from_prim(t2n)) {
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

// Trivial 1-ary prim-op.
Term* op_id(Term** t)
    {return *t;}

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
    Term* t =

    //  λ x . x
        "TODO: live code me!"

    global_print_root = t;
    dump_dot("",0);
}

    //  λ x . x + 2

    //  (λ x . x + 2) 3

    //  (λ x . x + 2) (3 × 4)

    //  (λ x . x + x) (3 × 4)

    //  f = (λ x . x + x)
    //  f (f (f (3 × 4)))

    //  big2 = (((λ x . x) (λ x . x)) ((λ x . x) 2))
    //  f = (λ x . x + big2)
    //  f (f (f (3 × 4)))

    //  (λ x . λ y . y) z 4

    //  (λ x . λ y . y) 4 z

