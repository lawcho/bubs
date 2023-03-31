
(* This file contains a refactoring of the BUBS algorithm, aiming for...
*   * Easy portability to C
*   * Conciseness
*   * At-least-as-good performance as the original
*   * Testability
*   * Primitive data support
*)



(* Signature/header of in-place circular doubly-linked list library *)
signature DoubleLists = sig
    type 'a dl  (* Type of doubly-linked list cells *)
    val is_singleton : 'a dl -> bool    (* Is a cell part of a singleton list? *)
    val new : 'a -> 'a dl               (* Construct a list containing only one cell. *)
    val remove : 'a dl -> 'a dl option  (* Unlink a cell from its surrounding list, and find a cell in that list (if not empty). *)
    val get_pred : 'a dl -> 'a dl (* Navigate to the next cell in the list.       *)
    val get_succ : 'a dl -> 'a dl (* Navigate to the previous cell in the list.   *)
    val get_payload : 'a dl -> 'a           (* Retrieve the value stored at a cell *)
    val set_payload : 'a * 'a dl -> unit    (* Overwrite the value stored at a cell *)
    val alias : 'a dl * 'a dl -> bool       (* Test if two nodes are the same (i.e. stored as same location on heap) *)
    val union : 'a dl * 'a dl -> unit       (* Concatenate two lists in-place. Precondition: lists must be distinct *)
end


(*
* Major Change: make DLL implementation circular
*   This has the following benefits:
*       * Algorithmic performance boost: in-place merge is now O(1)
*       * Robustness: less possbility for bugs due to mis-handling 'ends' of the list
*)
structure DL :> DoubleLists = struct

    (* Type of doubly-linked list cells. Opaque. *)
    datatype 'a dl
        = CNode
            of 'a dl option ref     (* mutable poitner to predecessor cell (option is only for construction) *)
            * 'a ref                (* payload of DLL cell (ref is for 'set' operation) *)
            * 'a dl option ref      (* mutable poitner to predecessor cell (option is only for construction) *)

    (* Invariant:
    *   between library function calls, every dl
    *   is part of a well-formed circular DLL
    *)

    (* Helper function to set bi-directional links betwen cells. Internal. *)
    fun set_link (l as CNode(_,_,fwd), r as CNode(bak,_,_)) = (fwd := SOME r; bak := SOME l)

    (* API functions *)

    fun get_payload(CNode(_,ar,_)) = !ar
    fun set_payload (a, CNode (_,ar,_)) = (ar := a)

    fun get_succ (CNode(_,_,ref (SOME s))) = s
    |   get_succ _ = raise Match
    fun get_pred (CNode(ref (SOME p),_,_)) = p
    |   get_pred _ = raise Match

    fun alias (CNode(p1,_,_), CNode(p2,_,_)) =
        (* Compares the addresses of the pointers p1 and p2 (NOT the values of the pointers)
        *   (more info on SML ref equality tests at https://www.cl.cam.ac.uk/~lp15/MLbook/PDF/chapter8.pdf)
        *)
        p1 = p2

    fun is_singleton n = alias (n, get_pred n)

    fun new a = let
        val node = (CNode (ref NONE, ref a, ref NONE))
        val _ = set_link (node, node)
        in node end


    fun remove cell =
        (* For singleton lists, unlinking is a no-op *)
        if is_singleton cell then NONE
        else let
            val p = get_pred cell
            val s = get_succ cell
            val _ = set_link(p,s)
            in SOME p end

    fun union (a,c) = let
        val b = get_succ a
        val d = get_succ c
        (*
        * Union is implemented using the following O(1) graph transformtion:
        *
        *        (dashed lines show direct pointers, dotted lines show n-step links)
        *
        *
        *     ..                 ..             ..                 ..
        *    .  a               d  .           .  a               d  .
        *    .   \             /   .  set a-d  .   \_____________/   .
        *     .   \           /   .   set c-b   .                   .
        *      .   \         /   .   ========>   .    _________    .
        *       .   \       /   .                 .   \       /   .
        *        .   b     c   .                   .   b     c   .
        *         .   .   .   .                     .   .   .   .
        *          ...     ...                       ...     ...
        *)
        in (
            set_link(a, d);
            set_link(c, b))
        end
        (* Some notes about correctness:
        *
        * This algorithm obviously works when a≠b, c≠d, and the lists are distinct.
        *
        * It also happens to work when a=b or b=c or both:
        *
        *   When a=b:
        *
        *     __                 ..             __                 ..             __                 ..
        *    /  a               d  .           /  a               d  .           /  a               d  .
        *    \   \             /   .  set a-d  \   \_____________/   .  set c-a  \   \_____________/   .
        *     \   \           /   .             \                   .             \                   .
        *      \   \         /   .   ========>   \   ^         ^   .   ========>   \    _________    .
        *       \   \       /   .                 \   \       /   .                 \   \       /   .
        *        \   \     c   .                   \   \     c   .                   \   \     c   .
        *         \   \   .   .                     \   \   .   .                     \   \   .   .
        *          \__/    ...                       \__/    ...                       \__/    ...
        *
        *   When c=d:
        *     ..                 __             ..                 __             ..                 __
        *    .  a               d  \           .  a               d  \           .  a               d  \
        *    .   \             /   /  set a-d  .   \_____________/   /  set d-b  .   \_____________/   /
        *     .   \           /   /             .                   /             .                   /
        *      .   \         /   /   ========>   .   ^         ^   /   ========>   .    _________    /
        *       .   \       /   /                 .   \       /   /                 .   \       /   /
        *        .   b     /   /                   .   b     /   /                   .   b     /   /
        *         .   .   /   /                     .   .   /   /                     .   .   /   /
        *          ...    \__/                       ...    \__/                       ...    \__/
        *
        *   When a=b and c=d:
        *     __                 __             __                 __             __                 __
        *    /  a               d  \           /  a               d  \           /  a               d  \
        *    \   \             /   /  set a-d  \   \_____________/   /  set d-a  \   \_____________/   /
        *     \   \           /   /             \                   /             \                   /
        *      \   \         /   /   ========>   \   ^         ^   /   ========>   \    _________    /
        *       \   \       /   /                 \   \       /   /                 \   \       /   /
        *        \   \     /   /                   \   \     /   /                   \   \     /   /
        *         \   \   /   /                     \   \   /   /                     \   \   /   /
        *          \__/   \__/                       \__/   \__/                       \__/   \__/
        *
        * However, the algorithm may give the wrong result when the two lists are the same!
        *
        *   e.g. When  a-b..c-d, the list becomes split in two:
        *
        *     ..                 ..             ..                 ..             ..                 ..
        *    .  a               d  .           .  a               d  .           .  a               d  .
        *    .   \             /   .  set a-d  .   \_____________/   .  set c-b  .   \_____________/   .
        *     .   \           /   .             .                   .             .                   .
        *      .   \         /   .   ========>   .   ^         ^   .   ========>   .    _________    .
        *       .   \       /   .                 .   \       /   .                 .   \       /   .
        *        .   b.....c   .                   .   b.....c   .                   .   b.....c   .
        *         .           .                     .           .                     .           .
        *          ...........                       ...........                       ...........
        *
        * This is the reason for the distinct-list precondition.
        *)
end

(* Some properties of the DLL library, for testing *)
structure dll_testing = struct 

    fun prop_singleton_new x = DL.is_singleton (DL.new x)
    fun prop_singleton_remove c = (DL.remove c; DL.is_singleton c)
    fun prop_get_new a = (DL.get_payload(DL.new a) = a)
end

(* for simplicity, this is hard-coded rather than a parameter *)
type PrimValue = int

(* Signature/header of BUBS library *)
signature BUBS = sig
    type Term
    type VarType
    (* Functions for constructing UTλC terms *)
        val mkVar : string -> VarType           (* Construct a var-node *)
        val var : VarType -> Term               (* Construct a var-term *)
        val lam : VarType * Term -> Term        (* Construct a λ-term. The var may only occur in the body. *)
        val app : Term * Term -> Term           (* Construct an @-term *)
    (* Functions for evaluating terms *)
        val whnf : Term -> Term                 (* Reduce a term to weak-head normal form (as far as possible) *)
    (* Functions for inspecting terms *)
        val pretty : Term -> unit               (* Print a term to standard output *)
    (* Functions related to primitive data *)
        val prim : PrimValue -> Term                (* Construct a primitive-data term *)
        val get_prim : Term -> PrimValue option     (* Attempt to extract primitive data from a term *)
end

structure bubs :> BUBS = struct

    (* Core datatype definitions
    ******************************************************************************
    * There are three kinds of nodes: lambdas, var refs and applications.
    * Each kind gets its own ML datatype, instead of having a single,
    * three-constructor datatype. Why? It allows us to encode more structure
    * in the ML type system. E.g., the *parent* of a node can only be a lambda
    * or an app; not a var-ref. So we can define a two-constructor node-parent
    * type, ruling out the var-ref possibility. And so forth.
    *
    * Note, also, that some of these "foo option ref" record fields are because we
    * are constructing circular structure. Backpointers are initialised to
    * "ref NONE," then we slam in "SOME <node>" after we have later created <node>.
    *)

    (* bodyRef is the parent record belonging to our child node (our body) that
    * points back to us. I.e., suppose our body node N has three parents, of
    * which we are one. Then N has a three-element doubly-linked list (DLL)
    * of parent records, one for each parent. The one that points back to us
    * is the record sitting in *our* "bodyRef" field. This allows us to delink
    * ourselves from the child's parent list & detach the child in constant time
    * when copying up through the lambda node.
    *)
    datatype LambdaType = Lambda of {
        var: VarType, body: Term ref,
        bodyRef: ChildCell DL.dl option ref,    (* NONE only during construction *)
        parents: ChildCell DL.dl option ref,    (* NONE => node has no parents, i.e. is root of top-level term *)
        uniq: int}

    (* funcRef and argRef are similar to the bodyRef field
    * of the LambdaType record above.
    *)
    and AppType = App of {
        func: Term ref, arg: Term ref,
        funcRef : ChildCell DL.dl option ref,   (* NONE only during construction *)
        argRef : ChildCell DL.dl option ref,    (* NONE only during construction *)
        copy: AppType option ref,               (* NONE => no copy *)
        parents: ChildCell DL.dl option ref,    (* NONE => node has no parents, i.e. is root of top-level term *)
        uniq:int}

    and VarType = Var of {
        name: string,
        parents: ChildCell DL.dl option ref,    (* NONE => node has no parents, i.e. variable is unused *)
        uniq:int}

    and PrimType = Prim of {
        data: PrimValue,
        parents: ChildCell DL.dl option ref,   (* NONE => node has no parents, i.e. is root of top-level term *)
        uniq: int}

    (* Type of a general UTλC node. *)
    and Term
        = LambdaT of LambdaType
        | AppT of AppType
        | VarT of VarType
        | PrimT of PrimType

    (* This tells us what our relationship to our parents is. *)
    and ChildCell
        = AppFunc of AppType
        | AppArg of AppType
        | LambdaBody of LambdaType

    (* Get the parents of a Term. *)
    fun termParRef(LambdaT(Lambda{parents, ...}))   = parents
    |   termParRef(AppT(App{parents, ...}))         = parents
    |   termParRef(VarT(Var{parents, ...}))         = parents
    |   termParRef(PrimT(Prim{parents, ...}))       = parents

    (* Get the ID of a term *)
    fun getUniq (VarT (Var       {uniq = uniq,...})) = uniq
    |   getUniq (LambdaT (Lambda {uniq = uniq,...})) = uniq
    |   getUniq (AppT (App       {uniq = uniq,...})) = uniq
    |   getUniq (PrimT(Prim      {uniq = uniq,...})) = uniq

    (* A rather subtle point:
    *******************************************************************************
    * When we do upsearch/copying, we chase uplinks/backpointers, copying old tree
    * structure, creating new tree structure as we go. But we don't want to search
    * up through *new* structure by accident -- that might induce an infinite
    * search/copy. Now, the the only way we can have a link from an old node up to
    * a new parent is by cloning an app node -- when we create a new app, it has
    * one new child NC and one old child OC. So our new app node will be added to
    * the parent list of the old child -- and if we should later copy up through
    * the old child, OC, we'd copy up through the new app node -- that is, we'd
    * copy the copy. This could get us into an infinite loop. (Consider reducing
    *   (\x. x x) y
    * for example. Infinite-loop city.)
    *
    * We avoid this by setting copy slots in the newly-created copies
    * to point to themselves as copies. That way, the "copy from old into new structure"
    * case is handled by the sentinnel-checking code already in place.
    *
    * The BUBS 2010 algorithm took a different approach: it delayed installing uplinks
    * until the copy-clearing pass.
    *)

    (* Add uplink(s) to a node's parent-list. Precondition: the two lists must be different. *)
    fun addToParents(node, cclink) =
        let val p = termParRef node
        in case !p of
                NONE        => p := SOME cclink  (* no parents before => initialize the parent-pointer *)
            |   SOME cell   => DL.union (cell , cclink) (* already had parents => in-place merge is enough *)
        end

    (* freeDeadNode term -> unit
    ***************************************************************************
    * Precondition: term has no parents.
    *
    * A node with no parents can be freed. Furthermore, freeing a node
    * means we can remove it from the parent list of its children... and
    * should such a child thus become parentless, it, too can be freed.
    * So we have a recursive/DAG-walking/ref-counting sort of GC algo here.
    *
    * IMPORTANT: In this SML implementation, we don't actually *do* anything
    * with the freed nodes -- we don't, for instance, put them onto a free
    * list for later re-allocation. We just drop them on the floor and let
    * SML's GC collect them. But it doesn't matter -- this GC algo is *not
    * optional*. We *must* (recursively) delink dead nodes. Why? Because
    * we don't want subsequent up-copies to spend time copying up into dead
    * node subtrees. So we remove them as soon as a beta-reduction makes
    * them dead.
    *)

    fun freeDeadNode (AppT(App{func,funcRef,arg,argRef,parents,...})) = (
            unlinkChild (func, funcRef);
            unlinkChild (arg , argRef ))
    |   freeDeadNode (LambdaT(Lambda{body, bodyRef, parents,...})) = (
            unlinkChild (body, bodyRef))
    |   freeDeadNode (PrimT _) = () (* no child nodes for prim-data nodes *)
    (* We wouldn't actually want to dealloc a parentless var node, because
    * its binding lambda still retains a ref to it. Responsibility for
    * freeing a var node should be given to the code (just above) that
    * freed its lambda.
    *)
    |   freeDeadNode (VarT _) = ()

    (* Helper function for freeDeadNode.
    *   Unlink a term from just one of its parents (using a given uplink),
    *   and if this makes the child dead, then free it
    *)
    and unlinkChild (term, uplink) =
        case DL.remove (valOf(!uplink)) of
                NONE      => freeDeadNode (!term)
            |   SOME cell => termParRef (!term) := SOME cell;


    (* Helper for replaceChild. Inspect an uplink and update the relevant downlink. *)
    fun installChild(new, (LambdaBody(Lambda{body,...}))) = body := new
    |   installChild(new, (AppFunc(App{func,...})))       = func := new
    |   installChild(new, (AppArg(App{arg,...})))         = arg  := new

    (* Replace one child w/another in the tree.
    * - 'uplinksOfOld' is the parent dll for some term -- the old term.
    * - 'new' is the replacement term.
    * Add each element of the dll uplinksOfOld to new's parent list. Each such
    * element indicates some parental downlink; install new in the right slot
    * of the indicated parent.
    *
    *   Precondition: uplinksOfOld is a different list to new's parents
    *)
    fun replaceChild(NONE, _) = ()    (* Old term has no parents => nothing to do *)
    |   replaceChild(SOME uplinksOfOld, new) =
        let val i = ref uplinksOfOld  (* loop over each parent of old, installing a downlink to new *)
        in (installChild (new , DL.get_payload (!i));
            i := DL.get_succ (!i);
            while not (DL.alias(uplinksOfOld , !i)) do (
                installChild (new , DL.get_payload(!i));
                i := DL.get_succ (!i));
            (* After this function returns, the parents of new should include:
            *   *   the parents of old
            *   *   any paresnts new already had
            * So before reutrning, this function merges the two parent-lists in place.
            *)
            case !(termParRef new) of
                    NONE => ()
                |   SOME uplinksOfNew => DL.union(uplinksOfOld, uplinksOfNew)
        )
        end

    (* Replace one term with another, and free the old term. Return the new term. *)
    fun replaceAndFree (old , new) = (
        replaceChild (!(termParRef old), new);
        freeDeadNode old;
        new
        )

    (* Function for generating globally unique fresh numbers *)
    val counter = ref 0
    fun newUniq () = (
        counter := !counter + 1;
        !counter
    )

    (* Construct a Var-node on the heap *)
    fun mkVar (name : string) : VarType =
        Var{name = name, parents = ref NONE, uniq = newUniq()}

    val var = VarT

    (* Construct a λ-node on the heap 
    *   Precondition: 'var' should be free (and not occurring outside 'body' )
    *)
    fun lam' (var : VarType, body : Term) : LambdaType = let
        val bodyRef = ref NONE  (* Placholder *)
        (* Allocate the λ-node and initialize its easy fields*)
        val lamNode = Lambda 
            {var = var, body = ref body,    (* Install downlink to body immediately *)
            bodyRef = bodyRef,      (* To be updated soon *)
            parents = ref NONE,     (* No parents for this λ-node *)
            uniq = newUniq()
            }
        val cclink = DL.new (LambdaBody lamNode)    (* Allocate an uplink, pointing up to the λ-node *)
        val _ = bodyRef := SOME cclink              (* Update the λ-node to point to the uplink *)
        val _ = addToParents(body, cclink)          (* Add the uplink to the body's parent-list *)
        in lamNode end (* Return the λ-node *)
    fun lam (var : VarType , body : Term) : Term = LambdaT (lam'(var,body))

    (* Construct an @-node on the heap *)
    fun app' (selfRef : bool, func : Term, arg : Term) : AppType = let
        val funcRef = ref NONE      (* Placholder *)
        val argRef = ref NONE       (* Placholder *)
        val copy = ref NONE
        (* Allocate the @-node and initialize its easy fields*)
        val appNode = App {
            func = ref func, arg = ref arg,     (* Install downlinks to fun & arg subterms immediately *)
            funcRef = funcRef, argRef = argRef,             (* To be updated later *)
            copy = copy,
            parents = ref NONE,                             (* No parents for this @-node *)
            uniq = newUniq()
        }
        val cclink_func = DL.new (AppFunc appNode)          (* Allocate an uplink, pointing to the @-node (with func tag)   *)
        val cclink_arg  = DL.new (AppArg appNode)           (* Allocate an uplink, pointing to the @-node (with arg tag)    *)
        val _ = funcRef := SOME cclink_func                 (* Update the @-node to point to its func-child uplink          *)
        val _ = argRef  := SOME cclink_arg                  (* Update the @-node to point to its arg-child uplink           *)
        val _ = addToParents (func, cclink_func)            (* Add func->@-node uplink to func term's parent list           *)
        val _ = addToParents (arg, cclink_arg)              (* Add arc->@-node uplink to arg term's parent list             *)
        val _ = if selfRef then copy := SOME appNode else ()
        in appNode end
    fun app (func : Term , arg : Term) : Term = AppT (app'(false, func, arg))

    (* Construct a prim-data node on the heap *)
    fun prim (pv : PrimValue) : Term =
        PrimT (Prim {
            parents = ref NONE,
            data = pv,
            uniq = newUniq()
        })

    (* upcopyUplink (newChild , parRef) -> unit
    ******************************************************************************
    * The core up-copy function.
    * parRef represents a downlink dangling from some parent node.
    * - If the parent node is a previously-copied app node, mutate the
    *   copy to connect it to newChild via the indicated downlink, and quit
    * - If the parent is an app node that hasn't been copied yet, then
    *   make a copy of it, identical to parent except that the indicated downlink
    *   points to newChild. Stash the new copy away inside the parent. Then take
    *   the new copy and recursively upcopy it to all the parents of the parent.
    * - If the parent is a lambda node L (and, hence, the downlink is the
    *   "body-of-a-lambda" connection), make a new lambda with newChild as
    *   its body and a fresh var for its var. Then kick off an upcopy from
    *   L's var's parents upwards, replacing L's var with the fresh var.
    *   (These upcopies will guaranteed terminate on a previously-replicated
    *   app node somewhere below L.) Then continue upwards, upcopying the fresh
    *   lambda to all the parents of L.
    *)

    and upcopyUplink (newChild , LambdaBody(Lambda{var, parents,...})) = upcopyUplinks (lam (var, newChild) , !parents)
        (* Cloning an app from the func side *)
    |   upcopyUplink (newChild , AppFunc(App{copy as ref NONE, arg, parents, ...})) = let
            val new_app = app'(true, newChild, !arg)
            val _ = copy := SOME new_app
            in upcopyUplinks (AppT new_app, !parents) end

        (* Copied up into an already-copied app node. Mutate the existing copy & quit. *)
    |   upcopyUplink (newChild , AppFunc(App{copy = ref(SOME(App{func,...})), ...})) =
            func := newChild

        (* Cloning an app from the arg side *)
    |   upcopyUplink (newChild , AppArg(App{copy as ref NONE, func, parents, ...})) = let
            val new_app = app'(true, !func, newChild)
            val _ = copy := SOME new_app
            in upcopyUplinks (AppT new_app, !parents) end

        (* Copied up into an already-copied app node. Mutate the existing copy & quit. *)
    |   upcopyUplink (newChild , AppArg(App{copy = ref(SOME(App{arg,...})),...})) =
            arg := newChild

    (* Upcopy from a list of uplinks *)
    and upcopyUplinks (newChild , NONE) = ()    (* No uplinks in list => stop recursion *)
    |   upcopyUplinks (newChild , SOME ps) =    (* Have uplinks => loop over them, spawning upcopies at each *)
            let val i = ref ps
            in (upcopyUplink (newChild, DL.get_payload (!i));
                i := DL.get_succ (!i);
                while not (DL.alias(ps , !i)) do (
                    upcopyUplink (newChild, DL.get_payload (!i));
                    i := DL.get_succ (!i))
            ) end


    (* Functions implementing the copy-clearing algorithm.
    *   This algorithm traverses a term upwards from a given node,
    *   unlinking application nodes from their copies,
    *   It traverses the same nodes as the upcopy algorithm itself.
    *)
    (* Clean upwards starting at an @-node *)
    fun cleanApp (App{copy = ref NONE,...}) = ()   (* Don't recurse up into already-cleared app nodes *)
    |   cleanApp (App{copy = copy1 as ref (SOME(App{copy = copy2,...})),parents,...}) = (
            copy1 := NONE;   (* Clear original app's copy-pointer *)
            copy2 := NONE;   (* Clear app's copy's copy-pointer (it should be pointing to itself) *)
            cleanUplinks(!parents) (* Recurse into the parents of the @-node *)
            (* This function does NOT recurse into the parents of the copy,
            *   since it is following the recursion path of upcopy.
            *)
        )
    (* Clean upwards starting at a var-node *)
    and cleanVar(Var{parents=varpars,...}) = cleanUplinks (!varpars)
    (* Clean upwards starting at a λ-node *)
    and cleanLambda(Lambda{parents,var,...}) = (cleanVar var; cleanUplinks (!parents))
    (* Clean upwards starting at a list of uplinks *)
    and cleanUplinks NONE = ()
    |   cleanUplinks (SOME ps) =    (* loop over parents, spawning an upclean at each *)
            let val i = ref ps
            in (cleanUplink (DL.get_payload (!i));
                i := DL.get_succ (!i);
                while not (DL.alias(ps , !i)) do (
                    cleanUplink (DL.get_payload (!i));
                    i := DL.get_succ (!i))
            ) end
    (* Clean upwards starting at any given uplink *)
    and cleanUplink(AppFunc a) = cleanApp a
    |   cleanUplink(AppArg a) = cleanApp a
    |   cleanUplink(LambdaBody l) = cleanLambda l

    (* Contract a β-redex; raise an exception if the term isn't a redex. *)

    fun reduceRedex(t as AppT (a as App{funcRef, func = func as ref(LambdaT l),
                        argRef, arg = ref argterm,
                        copy = copy,
                        parents, ...})) =
        let val Lambda {var, body, bodyRef, parents = lampars, ...} = l
            val Var{parents = varpars, ...} = var
            val contractum = if DL.is_singleton(valOf(!lampars))   (* valOf safe here because lampas must include at least a *)

                    (* The lambda has only one parent -- the app node we're
                    * reducing, which is about to die. So we can mutate the
                    * lambda's body. Just alter all parents of the lambda's vars to
                    * point to ARGTERM instead of the var, and we're done!
                    *)
                    then (replaceChild(!varpars, argterm);
                            !body)

                    (* Fast path: If lambda's var has no refs,
                    * the contractum is just the lambda's body, as-is.
                    *)
                    else if not (isSome (!varpars)) then !body
                    else (

                    (* The standard case. We know two things:
                    * 1. The λ-node has multiple parents, so it will survive the
                    *    reduction, and so its body will be copied, not altered.
                    * 2. The var occurs in the body, so we'll have to do some substitution.
                    * 3. The body has exactly one parent (the λ-node)
                    *
                    * To construct the contractum, we upcopy the redex's lambda' var-occurences.
                    *   HOWEVER we want to ensure that the upcopy doesnt't go into the redex's parents
                    *   or into the redex's lambda's other parents (which would waste time & space)
                    *
                    * To achieve this, we...
                    *   * Make the @-node a sentinnel for upcopy, by setting its copy slot to point to itself
                    *       * The prevents upcopy into the @-node's parents
                    *       * This also allows us to easily find the root of the contractum afterwards
                    *   * Temporarily set the body's parent to the @-node, bypassing the λ-node
                    *       * This prevents upcopy into the λ-node's other parents
                    *
                    * N.B. The BUBS 2010 algorithm took a different approach to stopping upcopy,
                    *   which involved scanning down into the lambda's body to find an @-node to use as a sentinnel
                    *   However that made the code quite complex with many special cases, so I have avoided it.
                    *
                    * The current algorithm copies no more (up to constant factors) than the BUBS 2010 algorithm
                    *   -- to prove this, observe that the redex's lambda's var occurs somewhere in the redex's lambda's body,
                    *   so all the leading lambdas in the body must be single-parented (because of lexical scope).
                    *   Therefore the new procedure for sentinnel-setting casues no more copying than the BUBS 2010 procedure for sentinel-setting.
                    *)
                copy := SOME a;                                         (* Set @-node's copy-pointer to itself *)
                DL.set_payload (AppFunc a, valOf(!(termParRef(!body))));      (* Temporarily set body' parent-pointer *)
                upcopyUplinks (argterm, !varpars);                          (* Upcopy, starting with var->argterm *)
                DL.set_payload (LambdaBody l, valOf(!(termParRef(!body))));   (* Reset the body's parent-pointer *)
                !func   (* The upcopy has constructed the contractum, and stored it in the func. child of the @-node *)
                )
        (* We've constructed the contractum & reset all the copy slots. *)
        in  replaceAndFree(t , contractum) end (* Replace the old term with the contractum & free the dead node *)
    |   reduceRedex _ = raise Match

    (* Normalise a term to WHNF and return a pointer to the new root.
    * N.B. This function can be called on open terms,
    *   in which case they will evaluate the term as much as possible towards WHNF.
    *)
    fun whnf(t as AppT(App{func, arg, ...})) =
        (whnf(!func);   (* This updates fields in app as a side-effect *)
        case !func of
            (* When E1 normalises to λ-node, we reduce (E1 $ E2) and return a pointer to that *)
                LambdaT _   => whnf(reduceRedex t)
            (* When E1 fails to normalises to a λ-node, we can't normalise (E1 $ E2) to WHNF, so we stop *)
            | _             => t
        )
    |   whnf t = t    (* Already WHNF (or stuck) *)
    
    (* Test a node to see if it holds prim data or not *)
    fun get_prim (PrimT (Prim {data = pv,... })) = SOME pv
    |   get_prim _ = NONE

    (*  Pretty-printing-related functions *)

    fun showUniq (term : Term) = PolyML.makestring (getUniq term)

    (* Pretty-printing function.
    *   Sometimes prints a term twice, but always terminates, and always prints the whole term
    *   (unlike SML's built-in printer)
    *   Ignores uplinks.
    *)
    fun pretty (t : Term) : unit = (
        print (showUniq t ^ " |->    ");
        (case t of 
                VarT (Var {name = name,...}) => (print ("var '" ^ name ^ "'\n"))
            |   LambdaT (Lambda {var = Var {name = name,uniq = vu, ...}, body = ref body, ...})
                    => (print ("\\ " ^ PolyML.makestring vu ^ " ('" ^ name ^ "') . " ^ showUniq body ^ "\n"); pretty body)
            |   AppT (App {func = ref func, arg = ref arg,...})
                    => (print (showUniq func ^ " @ " ^ showUniq arg ^ "\n"); pretty func; pretty arg)
            |   PrimT (Prim {data = pv,...})
                    => (print ("prim " ^ PolyML.makestring pv ^ "\n"))
        )
    )
end
open bubs

(* Test data *)

(* Example: (λ x . x) *)
fun build_id () : Term = let
    val v = mkVar "x"
    in lam (v, var v) end

(* Example: (λ x . x)(λ y . y) *)
fun build_ex2 () : Term =
    app (build_id (), build_id ())

(* Example: (E $ E) where shared E = (λ x . x) *)
fun build_ex3 () : Term = let
    val id = build_id ()
    in app (id , id) end

(* 'chain of perals' examples from the BUBS 2010 paper *)
(* i.e. stack of shared @-nodes, n deep, with id at the bottom *)
fun build_pearls 0 = build_id()
  | build_pearls n = let
  val chain = build_pearls (n - 1)
  in app (chain, chain) end

(* The term ((λ x . 4) 5) *)
fun build_ex5 () = let
    val vx = mkVar "x"
    in app (lam(vx, prim 4), prim 5) end

(* Complete tests *)
fun test_ex2 () = pretty(whnf(build_ex2()));          (* expected output: printout of (λ x . x) *)
fun test_ex3 () = pretty(whnf(build_ex3()));          (* expected output: printout of (λ x . x) *)
fun test_pearls n = pretty (whnf(build_pearls n));    (* expected output: printout of (λ x . x) *)
fun test_ex5 () = pretty(whnf(build_ex5()));          (* expected output: printout of (prim 4) *)
