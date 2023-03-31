
(* This code is adapted from from the BUBS 2010 paper's appendix.
    I have added some definition it was missing, and some testing utilities.
    Otherwise the code is exactly as in the paper (up to whitespace)
    Tested with Poly/ML 5.7.1
*)

(* In-place non-circular doubly-linked list library *)
(* Not shown in the 2010 paper *)
structure DoubleLists = struct
    (* Type of doubly-linked lists, aka DLLs *)
    (* This exact datatype is required by pattern matches made in the BUBS implementation *)
    datatype 'a dl
        = NIL
        | Node
            of 'a dl ref    (* predecessor link *)
            * 'a            (* payload of DLL cell *)
            * 'a dl ref     (* successor link *)
        ;

    (* Construct a singleton DLL *)
    fun new a = Node (ref NIL, a, ref NIL)
    ;

    (* Unlink a single cell from a DLL                      *)
    (* Returns lists before/after the removed element       *)
    fun remove NIL = (NIL, NIL)
      | remove (x as Node (xp, _, xs)) = (
            (* Update x's predecessor node  *)
            (case !xp of NIL => () | (Node (_,_,xps)) => xps := !xs);
            (* Update x's successor node    *)
            (case !xs of NIL => () | (Node (xsp,_,_)) => xsp := !xp);
            (* No explicit de-allocation needed (SML does this automatically) *)
            (!xp,!xs)
        )
    ;

    (* Find the first link in a DLL *)
    fun seek_first NIL = NIL
      | seek_first (x as Node(ref NIL,_,_)) = x
      | seek_first (     Node(ref p  ,_,_)) = seek_first p
    
    (* Find the last link in a DLL *)
    fun seek_last NIL = NIL
      | seek_last (x as Node(_,_,ref NIL)) = x
      | seek_last (     Node(_,_,ref s  )) = seek_last s

    (* Concatenate two DLLs
    * i.e. take pointers into DLLs dl1 and dl2
    *   and construct a DLL dl3 such that dl3 = dl1 ++ dl2
    *   Returns a pointer to the start of dl3
    * This rather ineffecient (O(n) time),
    *   since the lists in this library are non-circular,
    *   so must be traversed to find the ends
    *)
    fun add_before (dl1, dl2) = (
        (* Find ends of lists *)
        case seek_last dl1  of NIL => dl2 | (dl1_last as Node(_,_,dl1_succ)) => (
        case seek_first dl2 of NIL => dl1 | (dl2_first as Node(dl2_pred,_,_)) => (
        (* Link ends *)
        dl1_succ := dl2_first;
        dl1_succ := dl2_first;
        (* Find & return first element *)
        seek_first dl1
    )))

    (* Apply a function to all the items after a given point in a DLL,
    * and throw away the results
    *)
    fun app f NIL = ()
      | app f (Node (_,x,n)) = (f x; app f (! n))
    ;

end

(* Function for generating globally unique fresh numbers *)
(* Not shown in the 2010 paper *)
val counter = ref 0
fun newUniq () = (
    counter := !counter + 1;
    !counter
)

(****************************************************************************)
(* Begin code from 2010 BUBS paper                                          *)
(****************************************************************************)

(* Bottom-up Beta Substitution *)

structure DL = DoubleLists

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
    var: VarType, body: Term option ref,
    bodyRef: ChildCell DL.dl option ref,
    parents: ChildCell DL.dl ref,
    uniq: int}

(* funcRef and argRef are similar to the bodyRef field
* of the LambdaType record above.
*)
and AppType = App of {
    func: Term option ref, arg: Term option ref,
    funcRef : ChildCell DL.dl option ref,
    argRef : ChildCell DL.dl option ref,
    copy: AppType option ref,
    parents: ChildCell DL.dl ref,
    uniq:int}

and VarType = Var of {
    name: string,
    parents: ChildCell DL.dl ref,
    uniq:int}

(* Type of a general LC node. *)
and Term
    = LambdaT of LambdaType
    | AppT of AppType
    | VarT of VarType

(* This tells us what our relationship to our parents is. *)
and ChildCell
    = AppFunc of AppType
    | AppArg of AppType
    | LambdaBody of LambdaType

(* Get the parents of a Term. *)
fun termParRef(LambdaT(Lambda{parents, ...}))   = parents
  | termParRef(AppT(App{parents, ...}))         = parents
  | termParRef(VarT(Var{parents, ...}))         = parents

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
* We eliminate this problem in the following way: we don't install *up* links
* to app nodes when we copy. We just make the downlinks from the new app node
* to its two children. So the upcopy search won't ever chase links from old
* structure up to new structure; it will only see old structure.
*
* We *do* install uplinks from a lambda's body to a newly created lambda node,
* but this link always goes from new structure up to new structure, so it will
* never affect the our search through old structure. The only way we can have a
* new parent with an old child is when the parent is an app node.
*
* When we are done, we then make a pass over the new structure, installing the
* func->app-node or arg->app-node uplinks. We do this in the copy-clearing
* pass -- as we wander the old app nodes, clearing their cache slots, we take
* the corresponding new app node and install backpointers from its children
* up to it.
*
* In other words, for app nodes, we only create downlinks, and later bring the
* backpointer uplinks into sync with them.
*)

(* Given a term and a ChildCell, add the childcell to term's parents. *)
fun addToParents(node, cclink) =
    let val p = termParRef node
    in p := DL.add_before(!p, cclink)
    end

(* Is dll exactly one elt in length? *)
(* ML pattern matching rules.        *)
fun len1 (DL.Node(_,_,ref DL.NIL))  = true
  | len1 _                          = false

(* clearCopies(redlam, topapp)
******************************************************************************
* When we're finished constructing the contractum, we must clean out the
* app nodes' copy slots (reset them to NONE) to reset everything for the next
* reduction.
* - REDLAM is the lambda we reduced.
*
* - TOPAPP is the highest app node under the reduced lambda -- it holds
*   the highest copy slot we have to clear out. If we clear it first, then
*   we are guaranteed that any upwards copy-clearing search started below it
*   will terminate upon finding an app w/an empty copy slot.
*
* Every lambda from REDLAM down to TOPAPP had its var as the origin of an
* upcopy:
* - For REDLAM, the upcopy mapped its var to the redex's argument term.
* - The other, intermediate lambdas *between* REDLAM & TOPAPP (might be zero
*   of these) were copied to fresh lambdas, so their vars were mapped to
*   fresh vars, too.
* So, now, for each lambda, we must search upwards from the lambda's var,
* clearing cached copies at app nodes, stopping when we run into an
* already-cleared app node.
*
* This cache-clearing upsearch is performed by the internal proc cleanUp.
* (Get it?)
*
* When we created fresh app nodes during the upcopy phase, we *didn't*
* install uplinks from their children up to the app nodes -- this ensures
* the upcopy doesn't copy copies. So we do it now.
*)

fun clearCopies(redlam, topapp) =
    let val App{copy=topcopy,...} = topapp                      (* Clear out top*)
        val ref(SOME(App{arg,argRef, func, funcRef,...})) = topcopy
        val _ = topcopy := NONE                                 (* app & install*)
        val _ = addToParents(valOf(!arg), valOf(!argRef));      (* uplinks to   *)
        val _ = addToParents(valOf(!func), valOf(!funcRef));    (* its copy.    *)

    fun cleanUp(AppFunc(App{copy=ref NONE,...})) = ()
      | cleanUp(AppFunc(App{copy as ref(SOME(App{arg, argRef,
                                                 func, funcRef,...})),
                            parents,...})) =
        (copy := NONE;
         addToParents(valOf(!arg), valOf(!argRef));     (* Add uplinks  *)
         addToParents(valOf(!func), valOf(!funcRef));   (* to copy      *)
         DL.app cleanUp (!parents))
      | cleanUp(AppArg(App{copy=ref NONE,...})) = ()
      | cleanUp(AppArg(App{copy as ref(SOME(App{arg, argRef,
                                                func, funcRef,...})),
                           parents,...})) =
        (copy := NONE;
         addToParents(valOf(!arg), valOf(!argRef));     (* Add uplinks *)
         addToParents(valOf(!func), valOf(!funcRef));   (* to copy.    *)
         DL.app cleanUp (!parents))
      | cleanUp(LambdaBody(Lambda{parents,var,...})) =
        (varClean var; DL.app cleanUp (!parents))

    and varClean(Var{parents=varpars,...}) = DL.app cleanUp (!varpars)

    fun lambdascan(Lambda{var, body=ref(SOME b),...}) =
        (varClean var;
         case b of LambdaT l => lambdascan l | _ => ())

    in lambdascan redlam
    end

(* freeDeadNode term -> unit
***************************************************************************
* Precondition: (termParents term) is empty -- term has no parents.
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

fun freeDeadNode node =
    let
        fun free(AppT(App{func=ref(SOME functerm), funcRef,
                          arg=ref(SOME argterm), argRef,
                          parents, ...})) =
        (delPar(functerm, valOf(!funcRef)); (* Node no longer parent    *)
         delPar(argterm, valOf(!argRef)))   (* of func or arg children. *)  
          | free(LambdaT(Lambda{body=ref(SOME bodyterm),    (* Lambda no longer *)
                                bodyRef, parents, ...})) =  (* parent of body. *)
            delPar(bodyterm, valOf(!bodyRef))
        (* We wouldn't actually want to dealloc a parentless var node, because
        * its binding lambda still retains a ref to it. Responsibility for
        * freeing a var node should be given to the code (just above) that
        * freed its lambda.
        *)
          | free(VarT _) = ()

        (* Remove CCLINK from TERM's parent's dll.
        * If TERM's parent list becomes empty, it's dead, too, so free it.
        *)
        and delPar(term, cclink) =
            case DL.remove cclink of (* Returns the dll elts before & after cclink. *)
                (DL.NIL, after) => let val parref = termParRef term
                                   in parref := after;
                                      case after of DL.NIL    => free term
                                                  | DL.Node _ => ()
                                   end
                | _ => ()
    in free node
    end

(* Replace one child w/another in the tree.
* - OLDPREF is the parent dll for some term -- the old term.
* - NEW is the replacement term.
* Add each element of the dll !OLDPREF to NEW's parent list. Each such
* element indicates some parental downlink; install NEW in the right slot
* of the indicated parent. When done, set OLDPREF := NIL.
*
* Actually, we don't move the dll elements over to NEW's parent list one at
* a time -- that involves redundant writes. E.g., if !OLDPREF is 23 elements
* long, don't move the elements over one at a time -- they are already nicely
* linked up. Just connect the last elt of !OLDPREF & the first element of
* NEW's existing parent list, saving 22*2=44 writes. Because it physically
* hurts to waste cycles.
*)
fun replaceChild(oldpref, new) =
    let val cclinks = !oldpref
    val newparref = termParRef new

    fun installChild(LambdaBody(Lambda{body,...})) = body := SOME new
      | installChild(AppFunc(App{func,...}))       = func := SOME new
      | installChild(AppArg(App{arg,...}))         = arg := SOME new

    fun lp(prev, prevnext, DL.NIL) =
        (prevnext := !newparref ;
         case !newparref of DL.NIL           => ()
                          | DL.Node(p, _, _) => p := prev)
      | lp(prev, prevnext, node as DL.Node(_,cc, n as ref next)) =
          (installChild cc; lp(node, n, next))

    in case cclinks of DL.NIL => ()
                    | node as DL.Node(_,cc,n as ref next) =>
                        (oldpref := DL.NIL; installChild cc;
                        lp(node, n,next); newparref := cclinks)
    end

(* Allocate a fresh lambda L and a fresh var V. Install BODY as the body of
* the lambda -- L points down to BODY, and L is added to BODY's parent list.
* The fresh var's name (semantically irrelevant, but handy for humans) is
* copied from oldvar's name.
*
* Once this is done, kick off an OLDVAR->V upcopy to fix up BODY should it
* contain any OLDVAR refs.
*)
fun newLambda(oldvar, body) =
    let val Var{name, parents = varparents, ...} = oldvar
        val var = Var{name = name,
                  uniq = newUniq(),
                  parents = ref DL.NIL}
        val bodyRefCell = ref NONE
        val ans = Lambda{var = var,
                     body = ref(SOME body),
                     bodyRef = bodyRefCell,
                     uniq = newUniq(),
                     parents = ref DL.NIL}
        val cclink = DL.new(LambdaBody ans)
    in  bodyRefCell := SOME cclink;
        addToParents(body, cclink);
        (* Propagate the new var up through the lambda's body. *)
        DL.app (upcopy (VarT var)) (!varparents);
        LambdaT ans
    end

(* Allocate a fresh app node, with the two given params as its children.
* DON'T install this node on the children's parent lists -- see "a subtle
* point" above for the reason this would get us into trouble.
*)
and newApp(func, arg) =
    let val funcRef = ref NONE
        val argRef  = ref NONE
        val app     = App{func = ref(SOME func),
                          arg  = ref(SOME arg),
                          funcRef = funcRef,
                          argRef = argRef,
                          copy = ref NONE,
                          parents = ref DL.NIL,
                          uniq = newUniq()}
    in funcRef := SOME( DL.new(AppFunc app) );
       argRef  := SOME( DL.new(AppArg app) );
       app
    end

(* upcopy newChild parRef -> unit
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

and upcopy newChild (LambdaBody(Lambda{var, parents,...})) =
    DL.app (upcopy (newLambda(var, newChild))) (!parents)

    (* Cloning an app from the func side *)
    | upcopy new_child (AppFunc(App{copy as ref NONE, arg, parents, ...})) =
      let val new_app = newApp(new_child, valOf(!arg))
      in copy := SOME new_app;
          DL.app (upcopy (AppT new_app)) (!parents)
      end

    (* Copied up into an already-copied app node. Mutate the existing copy & quit. *)
    | upcopy newChild (AppFunc(App{copy = ref(SOME(App{func,...})), ...})) =
        func := SOME newChild

    (* Cloning an app from the arg side *)
    | upcopy new_child (AppArg(App{copy as ref NONE, func, parents, ...})) =
        let val new_app = newApp(valOf(!func), new_child)
        in copy := SOME new_app;
            DL.app (upcopy (AppT new_app)) (!parents)
        end

    (* Copied up into an already-copied app node. Mutate the existing copy & quit. *)
    | upcopy newChild (AppArg(App{copy = ref(SOME(App{arg,...})),...})) =
      arg := SOME newChild

(* Contract a redex; raise an exception if the term isn't a redex. *)

fun reduce(a as App{funcRef, func = ref(SOME(LambdaT l)),
                    argRef, arg = ref(SOME argterm),
                    parents, ...}) =
    let val Lambda {var, body, bodyRef, parents = lampars, ...} = l
        val Var{parents = vpars as ref varpars, ...} = var
        val ans = if len1(!lampars)

                  (* The lambda has only one parent -- the app node we're
                  * reducing, which is about to die. So we can mutate the
                  * lambda. Just alter all parents of the lambda's vars to
                  * point to ARGTERM instead of the var, and we're done!
                  *)
                  then (replaceChild(vpars, argterm);
                        valOf(!body))

                  (* Fast path: If lambda's var has no refs,
                  * the answer is just the lambda's body, as-is.
                  *)
                  else if varpars = DL.NIL then valOf(!body)

                  (* The standard case. We know two things:
                  * 1. The lambda has multiple pars, so it will survive the
                  *    reduction, and so its body be copied, not altered.
                  * 2. The var has refs, so we'll have to do some substitution.
                  *    First, start at BODY, and recursively search down
                  *    through as many lambdas as possible.
                  *
                  * - If we terminate on a var, the var is our lambda's var,
                  *   for sure. (OTW, #2 wouldn't be true.) So just return
                  *   BODY back up through all these down-search lambda-
                  *   skipping calls, copying the initial lambdas as we go.
                  * - If we terminate on an app, clone the app & stick the
                  *   clone in the app's copy slot. Now we can do our VAR->ARG
                  *   up-copy stuff knowing that all upcopying will guaranteed
                  *   terminate on a cached app node.
                  *
                  * When we return up through the initial-lambda-skipping
                  * recursion, we add on copies of the lambdas through
                  * which we are returning, *and* we also pass up that top
                  * app node we discovered. We will need it in the
                  * subsequent copy-clearing phase.
                  *)

                else let fun scandown(v as VarT _) = (argterm,NONE) (* No app! *)
                           | scandown(l as LambdaT(Lambda{body,var,...})) =
                             let val (body',topapp) = scandown(valOf(!body))
                                 val l' = newLambda(var, body')
                             in (l', topapp)
                             end
                           | scandown(AppT(a as App{arg,func,copy,...})) =
                             (* Found it -- the top app.          *)
                             (* Clone & cache it, then kick off a *)
                             (* var->arg upcopy.                  *)
                             let val a' = newApp(valOf(!func), valOf(!arg))
                             in copy := SOME a';
                                DL.app (upcopy argterm) varpars;
                                (AppT a', SOME a)
                              end

                        val (ans, maybeTopApp) = scandown (valOf(!body))

                        (* Clear out the copy slots of the app nodes. *)
                        in case maybeTopApp of
                              NONE => ()
                            | SOME app => clearCopies(l,app);
                            ans
                        end
    (* We've constructed the contractum & reset all the copy slots. *)
    in replaceChild(parents, ans);          (* Replace redex w/the contractrum. *)
        freeDeadNode (AppT a);              (* Dealloc the redex.               *)
        ans                                 (* Done.                            *)
    end

(* Call-by-name reduction to weak head-normal form. *)
fun normaliseWeakHead(AppT(app as App{func, arg, ...})) =
    (normaliseWeakHead(valOf(!func));
     case valOf(!func) of LambdaT _ => normaliseWeakHead(reduce app)
                        | _         => ())
  | normaliseWeakHead _ = ()

(* Normal-order reduction to normal form. *)
fun normalise(AppT(app as App{func, arg, uniq,...})) =
    (normaliseWeakHead(valOf(!func));
     case valOf(!func) of LambdaT _ => normalise(reduce app)
                        | VarT _    => normalise(valOf(!arg))
                        | app'      => (normalise app';
                                        normalise(valOf(!arg))))
  | normalise(LambdaT(Lambda{body,...})) = normalise(valOf(!body))
  | normalise _ = ()


(****************************************************************************)
(* End code from 2010 BUBS paper                                            *)
(****************************************************************************)

(*******************************)
(* Begin Testing Infrasructure *)
(*******************************)

(* Variant of normaliseWeakHead that returns a pointer to the normalised term.
* Handy for when the term to normalise has no parents.
* N.B. both this function and normaliseWeakHead can be called on open terms,
*   in which case they will evaluate the term as much as possible towards WHNF.
*)
fun normaliseWeakHead'(t as AppT(app as App{func, arg, ...})) =
    (normaliseWeakHead(valOf(!func));   (* This updates fields in app as a side-effect *)
     case valOf(!func)
        (* When E1 reduces to λ-node, we reduce (E1 $ E2) and return a pointer to that *)
        of LambdaT _=> normaliseWeakHead'(reduce app)
        (* When E1 fails to reduce to a λ-node, we can't reduce (E1 $ E2) to WHNF, so we stop *)
        | _         => t
    )
  | normaliseWeakHead' t = t    (* Already WHNF *)

(* Code for building terms on the heap
*   Unlike the newLambda and newVariable terms,
*   these are intended for building test data (not internal use by upcopy)
*   So they do as much setup as possible (including installing uplinks).
*)

(* Construct a Var-node on the heap *)
fun mkVar (name) : VarType = (
    Var{name = name, parents = ref DL.NIL, uniq = newUniq()}
)

(* Construct a λ-node on the heap 
*   Precondition: 'var' should be free (and not occurring outside 'body' )
*)
fun mkLambda (var : VarType, body : Term) : LambdaType = let
    val bodyRef = ref NONE  (* Placholder *)
    (* Allocate the λ-node and initialize its easy fields*)
    val lamNode = Lambda 
        {var = var, body = ref (SOME body), (* Install downlink to body immediately *)
        bodyRef = bodyRef,      (* To be updated soon *)
        parents = ref DL.NIL,   (* No parents for this λ-node *)
        uniq = newUniq()
        }
    val cclink = DL.new (LambdaBody lamNode)    (* Allocate an uplink, pointing up to the λ-node *)
    val _ = bodyRef := SOME cclink              (* Update the λ-node to point to the uplink *)
    val _ = addToParents(body, cclink)          (* Add the uplink to the body's parent-list *)
    in lamNode end (* Return the λ-node *)

(* Construct an @-node on the heap *)
fun mkApp (func : Term, arg : Term) : AppType = let
    val funcRef = ref NONE      (* Placholder *)
    val argRef = ref NONE       (* Placholder *)
    (* Allocate the @-node and initialize its easy fields*)
    val appNode = App {
        func = ref (SOME func), arg = ref (SOME arg),   (* Install downlinks to fun & arg subterms immediately *)
        funcRef = funcRef, argRef = argRef,             (* To be updated later *)
        copy = ref NONE,                                (* No copy for this @-node *)
        parents = ref DL.NIL,                           (* No parents for this @-node *)
        uniq = newUniq()
    }
    val cclink_func = DL.new (AppFunc appNode)          (* Allocate an uplink, pointing to the @-node (with func tag)   *)
    val cclink_arg  = DL.new (AppArg appNode)           (* Allocate an uplink, pointing to the @-node (with arg tag)    *)
    val _ = funcRef := SOME cclink_func                 (* Update the @-node to point to its func-child uplink          *)
    val _ = argRef  := SOME cclink_arg                  (* Update the @-node to point to its arg-child uplink           *)
    val _ = addToParents (func, cclink_func)            (* Add func->@-node uplink to func term's parent list           *)
    val _ = addToParents (arg, cclink_arg)              (* Add arc->@-node uplink to arg term's parent list             *)
    in appNode end

(* Term-returning variants *)
fun mkLambda' (var : VarType, body : Term) : Term = LambdaT (mkLambda (var,body))
fun mkApp' (func : Term, body : Term) : Term = AppT (mkApp (func, body))

(*  Pretty-printing-related functions *)

(* Misc. helper functions *)
fun getUniq (VarT (Var       {uniq = uniq,...})) = uniq
  | getUniq (LambdaT (Lambda {uniq = uniq,...})) = uniq
  | getUniq (AppT (App       {uniq = uniq,...})) = uniq


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
        |   LambdaT (Lambda {var = Var {name = name,uniq = vu, ...}, body = ref (SOME body), ...})
                => (print ("\\ " ^ PolyML.makestring vu ^ " ('" ^ name ^ "') . " ^ showUniq body ^ "\n"); pretty body)
        |   AppT (App {func = ref (SOME func), arg = ref (SOME arg),...})
                => (print (showUniq func ^ " @ " ^ showUniq arg ^ "\n"); pretty func; pretty arg)
    )
)

(* Test data *)

(* Example: (λ x . x) *)
fun build_id () : Term = let
    val var = mkVar "x"
    in mkLambda' (var, VarT var) end

(* Example: (λ x . x)(λ y . y) *)
fun build_ex2 () : Term =
    mkApp' (build_id (), build_id ())

(* Example: (E $ E) where shared E = (λ x . x) *)
fun build_ex3 () : Term = let
    val id = build_id ()
    in mkApp' (id , id) end

(* 'chain of perals' examples from the BUBS 2010 paper *)
(* i.e. stack of shared @-nodes, n deep, with id at the bottom *)
fun build_pearls 0 = build_id()
  | build_pearls n = let
  val chain = build_pearls (n - 1)
  in mkApp' (chain, chain) end

(* Complete tests *)
fun test_ex2 () = pretty(normaliseWeakHead'(build_ex2()));          (* expected output: printout of (λ x . x) *)
fun test_ex3 () = pretty(normaliseWeakHead'(build_ex3()));          (* expected output: printout of (λ x . x) *)
fun test_pearls n = pretty (normaliseWeakHead'(build_pearls n));    (* expected output: printout of (λ x . x) *)

