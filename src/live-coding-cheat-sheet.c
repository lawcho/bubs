
int main (void) {
    Term* t =

    //  λ x . x
        λ(x, var(x));

    global_print_root = t;
    dump_dot("",0);
}


int main (void) {
    Term* t =

    //  λ x . x + 2
        λ(x, op2(op_add, var(x), prim(2)));

    global_print_root = t;
    dump_dot("",0);
}


int main (void) {
    Term* t =

    //  (λ x . x + 2) 3
        app (λ(x, op2(op_add, var(x), prim(2)))
            , prim(3));

    global_print_root = op1(NULL,t);
    whnf(t);
}


int main (void) {
    Term* t =

    //  (λ x . x + 2) (3 × 4)
        app (λ(x, op2(op_add, var(x), prim(2)))
            , op2(op_mul, prim(3), prim(4)));

    global_print_root = op1(NULL,t);
    whnf(t);
}


int main (void) {
    Term* t =

    //  (λ x . x + x) (3 × 4)
        app (λ(x, op2(op_add, var(x), var(x)))
            , op2(op_mul, prim(3), prim(4)));

    global_print_root = op1(op_id,t);
    whnf(t);
}


int main (void) {
    Term* f =

    //  f = (λ x . x + x)
        λ(x, op2(op_add, var(x), var(x)));
    
    Term* t =

    //  f (f (f (3 × 4)))
        app(f, app(f, app(f, op2(op_add, prim(3), prim (4)))));

    global_print_root = op1(op_id,t);
    whnf(t);
}


int main (void) {
    Term* big2 =

    //  big2 = (((λ x . x) (λ x . x)) ((λ x . x) 2))
        app (app(λ(x, var(x)),λ(x, var(x)))
            ,app(λ(x, var(x)),prim(2)));

    Term* f =

    //  f = (λ x . x + big2)
        λ(x, op2(op_add, var(x) , big2));
    
    Term* t =

    //  f (f (f (3 × 4)))
        app(f, app(f, app(f, op2(op_add, prim(3), prim (4)))));

    global_print_root = op1(op_id,t);
    whnf(t);
}


int main (void) {
    VarType* z = mkVar();

    Term* t =

    //  (λ x . λ y . y) z 4
        app(app(
            λ(x, λ(y, var(y))) , var(z)) , prim(4)
        );

    global_print_root = op1(op_id,t);
    whnf(t);
}


int main (void) {
    VarType* z = mkVar();

    Term* t =

    //  (λ x . λ y . y) 4 z
        app(app(
            λ(x, λ(y, var(y))) , prim(4)) , var(z)
        );

    global_print_root = op1(op_id,t);
    whnf(t);
}

