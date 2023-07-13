(** Definition of Lm (STLC with mutability).

    Authors: Edward Lee, Ondrej Lhotak

    This work is based off the POPL'08 Coq tutorial
    authored by: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    Table of contents:
      - #<a href="##syntax">Syntax (pre-terms)</a>#
      - #<a href="##open">Opening</a>#
      - #<a href="##lc">Local closure</a>#
      - #<a href="##env">Environments</a>#
      - #<a href="##values">Values</a>#
      - #<a href="##stores">Stores</a>#
      - #<a href="##reduction">Reduction</a>#
      - #<a href="##immutability">Immutability equivalence</a>#
      - #<a href="##auto">Automation</a>#
*)

Require Export FmMeta.Metatheory.
Require Export String.
Require Export Fsub.Label.
Require Export Fsub.Signatures.
Require Export Fsub.LabelMap.
Require Export Coq.Program.Equality.
Require Export Fsub.Tactics.


(* ********************************************************************** *)
(** * #<a name="syntax"></a># Syntax (pre-terms) *)

(** We use a locally nameless representation for Fm, where bound
    variables are represented as natural numbers (de Bruijn indices)
    and free variables are represented as [atom]s.  The type [atom],
    defined in the MetatheoryAtom library, represents names: there are
    infinitely many atoms, equality is decidable on atoms, and it is
    possible to generate an atom fresh for any given finite set of
    atoms.

    We say that the definitions below define pre-types ([typ]) and
    pre-expressions ([exp]) coupled with pre record components ([rec_comp]), 
    collectively pre-terms, since the datatypes admit terms, such as 
    [(typ_all typ_top (typ_bvar 3))], where indices are unbound.  
    A term is locally closed when it contains no unbound indices.

    Note that indices for bound type variables are distinct from
    indices for bound expression variables.  We make this explicit in
    the definitions below of the opening operations. *)

Inductive exp : Set :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_let : exp -> exp -> exp
  (* New expressions for mutable boxes -- constructor, destructor, label *)
  | exp_box : exp -> exp
  | exp_unbox : exp -> exp
  | exp_set_box : exp -> exp -> exp
  | exp_ref : label -> exp
  (* New expressions for sealed references -- introduction form *)
  | exp_seal : exp -> exp
  (* New expressions for records -- constructor, destructors *)
  | exp_record : rec_comp -> exp
  | exp_record_read : exp -> atom -> exp
  | exp_record_write: exp -> atom -> exp -> exp
with rec_comp : Set :=
  (* What a record consists of: a list of bindings 
     of atoms to expressions or locations/labels in the store. *)
  | rec_empty : rec_comp
  | rec_exp : atom -> exp -> rec_comp -> rec_comp
  | rec_ref : atom -> label -> rec_comp -> rec_comp
.

(** We declare the constructors for indices and variables to be
    coercions.  For example, if Coq sees a [nat] where it expects an
    [exp], it will implicitly insert an application of [exp_bvar];
    similar behavior happens for [atom]s.  Thus, we may write
    [(exp_abs typ_top (exp_app 0 x))] instead of [(exp_abs typ_top
    (exp_app (exp_bvar 0) (exp_fvar x)))]. *)

Coercion exp_bvar : nat >-> exp.
Coercion exp_fvar : atom >-> exp.


(* ********************************************************************** *)
(** * #<a name="open"></a># Opening terms *)

(** Opening replaces an index with a term.  This operation is required
    if we wish to work only with locally closed terms when going under
    binders (e.g., the typing rule for [exp_abs]).  It also
    corresponds to informal substitution for a bound variable, which
    occurs in the rule for beta reduction.

    We need to define three functions for opening due the syntax of
    Fsub, and we name them according to the following convention.
      - [tt]: Denotes an operation involving types appearing in types.
      - [te]: Denotes an operation involving types appearing in
        expressions.
      - [ee]: Denotes an operation involving expressions appearing in
        expressions.
    As records need to be defined alongside expressions, there are also
    helper forms for records:
      - [te_record]: Denotes an operation involving types appearing
        in records.
      - [ee_record]: Denotes an operation involving expressions appearing
        in records.

    The notation used below for decidable equality on natural numbers
    (e.g., [K == J]) is defined in the CoqEqDec library, which is
    included by the Metatheory library.  The order of arguments to
    each "open" function is the same.  For example, [(open_tt_rec K U
    T)] can be read as "substitute [U] for index [K] in [T]."

    Note that we assume [U] is locally closed (and similarly for the
    other opening functions).  This assumption simplifies the
    implementations of opening by letting us avoid shifting.  Since
    bound variables are indices, there is no need to rename variables
    to avoid capture.  Finally, we assume that these functions are
    initially called with index zero and that zero is the only unbound
    index in the term.  This eliminates the need to possibly subtract
    one in the case of indices. *)

Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if k == i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs e1 => exp_abs (open_ee_rec (S k) f e1)
  | exp_app e1 e2 => exp_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_let e1 e2 => exp_let (open_ee_rec k f e1) (open_ee_rec (S k) f e2)
  | exp_box e => exp_box (open_ee_rec k f e)
  | exp_unbox e => exp_unbox (open_ee_rec k f  e)
  | exp_set_box b e => exp_set_box (open_ee_rec k f b) (open_ee_rec k f e)
  | exp_ref l => exp_ref l
  | exp_seal e => exp_seal (open_ee_rec k f e)
  | exp_record r => exp_record (open_ee_record_rec k f r)
  | exp_record_read e a => exp_record_read (open_ee_rec k f e) a
  | exp_record_write e1 a e2 => exp_record_write (open_ee_rec k f e1) a (open_ee_rec k f e2)
  end
with
  open_ee_record_rec (k : nat) (f : exp) (r : rec_comp)  {struct r} : rec_comp :=
  match r with 
  | rec_empty => rec_empty
  | rec_exp a e r => rec_exp a (open_ee_rec k f e) (open_ee_record_rec k f r)
  | rec_ref a l r => rec_ref a l (open_ee_record_rec k f r)
  end.

(** Many common applications of opening replace index zero with an
    expression or variable.  The following definitions provide
    convenient shorthands for such uses.  Note that the order of
    arguments is switched relative to the definitions above.  For
    example, [(open_tt T X)] can be read as "substitute the variable
    [X] for index [0] in [T]" and "open [T] with the variable [X]."
    Recall that the coercions above let us write [X] in place of
    [(typ_fvar X)], assuming that [X] is an [atom]. *)

Definition open_ee e1 e2 := open_ee_rec 0 e2 e1.


(* ********************************************************************** *)
(** * #<a name="lc"></a># Local closure *)

(** Recall that [typ] and [exp] and [rec_comp] define pre-terms; these datatypes
    admit terms that contain unbound indices.  A term is locally
    closed, or syntactically well-formed, when no indices appearing in
    it are unbound.  The proposition [(type T)] holds when a type [T]
    is locally closed, and [(expr e)] holds when an expression [e] is
    locally closed.

    The inductive definitions below formalize local closure such that
    the resulting induction principles serve as structural induction
    principles over (locally closed) types and (locally closed)
    expressions.  In particular, unlike the situation with pre-terms,
    there are no cases for indices.  Thus, these induction principles
    correspond more closely to informal practice than the ones arising
    from the definitions of pre-terms.

    The interesting cases in the inductive definitions below are those
    that involve binding constructs, e.g., [typ_all].  Intuitively, to
    check if the pre-term [(typ_all T1 T2)] is locally closed, we must
    check that [T1] is locally closed and that [T2] is locally closed
    when opened with a variable.  However, there is a choice as to how
    many variables to quantify over.  One possibility is to quantify
    over only one variable ("existential" quantification), as in
<<
  type_all : forall X T1 T2,
      type T1 ->
      type (open_tt T2 X) ->
      type (typ_all T1 T2) .
>>  Or, we could quantify over as many variables as possible ("universal"
    quantification), as in
<<
  type_all : forall T1 T2,
      type T1 ->
      (forall X : atom, type (open_tt T2 X)) ->
      type (typ_all T1 T2) .
>>  It is possible to show that the resulting relations are equivalent.
    The former makes it easy to build derivations, while the latter
    provides a strong induction principle.  McKinna and Pollack used
    both forms of this relation in their work on formalizing Pure Type
    Systems.

    We take a different approach here and use "cofinite"
    quantification: we quantify over all but finitely many variables.
    This approach provides a convenient middle ground: we can build
    derivations reasonably easily and get reasonably strong induction
    principles.  With some work, one can show that the definitions
    below are equivalent to ones that use existential, and hence also
    universal, quantification. *)

Inductive expr : exp -> Prop :=
  | expr_var : forall x,
      expr (exp_fvar x)
  | expr_abs : forall L e1,
      (forall x : atom, x `notin` L -> expr (open_ee e1 x)) ->
      expr (exp_abs e1)
  | expr_app : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_app e1 e2)
  | expr_let : forall L e1 e2,
      expr e1 ->
      (forall x : atom, x `notin` L -> expr (open_ee e2 x)) ->
      expr (exp_let e1 e2)
  | expr_box : forall e,
      expr e ->
      expr (exp_box e)
  | expr_unbox : forall e,
      expr e ->
      expr (exp_unbox e)
  | expr_set_box : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_set_box e1 e2)
  | expr_ref : forall l,
      expr (exp_ref l)
  | expr_seal : forall e,
      expr e ->
      expr (exp_seal e)
  | expr_record : forall r,
      record_comp r ->
      expr (exp_record r)
  | expr_record_read : forall e a,
      expr e ->
      expr (exp_record_read e a)
  | expr_record_write : forall e1 a e2,
      expr e1 ->
      expr e2 ->
      expr (exp_record_write e1 a e2)
with record_comp : rec_comp -> Prop :=
  | record_comp_empty :
      record_comp (rec_empty)
  | record_comp_exp : forall a e r,
      expr e ->
      record_comp r -> 
      record_comp (rec_exp a e r)
  | record_comp_ref : forall a e r,
      record_comp r ->
      record_comp (rec_ref a e r)
.


(** #<a name="body_e_doc"></a># We also define what it means to be the
    body of an abstraction, since this simplifies slightly the
    definition of reduction and subsequent proofs.  It is not strictly
    necessary to make this definition in order to complete the
    development. *)

Definition body_e (e : exp) :=
  exists L, forall x : atom, x `notin` L -> expr (open_ee e x).


(* ********************************************************************** *)
(** * #<a name="env"></a># Environments *)

(** In our presentation of System F with subtyping, we use a single
    environment for both typing and subtyping assumptions.  We
    formalize environments by representing them as association lists
    (lists of pairs of keys and values) whose keys are atoms.

    The Metatheory and MetatheoryEnv libraries provide functions,
    predicates, tactics, notations and lemmas that simplify working
    with environments.  They treat environments as lists of type [list
    (atom * A)].  The notation [(x ~ a)] denotes a list consisting of
    a single binding from [x] to [a].

    Since environments map [atom]s, the type [A] should encode whether
    a particular binding is a typing or subtyping assumption.  Thus,
    we instantiate [A] with the type [binding], defined below. *)

Inductive binding : Set :=
  | bind_typ : binding.

Inductive signature : Set :=
  | bind_sig : signature.

(** A binding [(X ~ bind_sub T)] records that a type variable [X] is a
    subtype of [T], and a binding [(x ~ bind_typ U)] records that an
    expression variable [x] has type [U].

    We define an abbreviation [env] for the type of environments, and
    an abbreviation [empty] for the empty environment.

    Note: Each instance of [Notation] below defines an abbreviation
    since the left-hand side consists of a single identifier that is
    not in quotes.  These abbreviations are used for both parsing (the
    left-hand side is equivalent to the right-hand side in all
    contexts) and printing (the right-hand side is pretty-printed as
    the left-hand side).  Since [nil] is normally a polymorphic
    constructor whose type argument is implicit, we prefix the name
    with "[@]" to signal to Coq that we are going to supply arguments
    to [nil] explicitly. *)

Notation env := (list (atom * binding)).
Notation empty := (@nil (atom * binding)).

Notation sig := (list (label * signature)).
Notation sempty := (@nil (label * signature)).

(** In addition to [env] for environments, we have a similar environment 
    [sig] for typing stores, mapping labels to types ([signature]s). *)

(** #<b>#Examples:#</b># We use a convention where environments are
    never built using a cons operation [((x, a) :: E)] where [E] is
    non-[nil].  This makes the shape of environments more uniform and
    saves us from excessive fiddling with the shapes of environments.
    For example, Coq's tactics sometimes distinguish between consing
    on a new binding and prepending a one element list, even though
    the two operations are convertible with each other.

    Consider the following environments written in informal notation.
<<
  1. (empty environment)
  2. x : T
  3. x : T, Y <: S
  4. E, x : T, F
>>  In the third example, we have an environment that binds an
    expression variable [x] to [T] and a type variable [Y] to [S].
    In Coq, we would write these environments as follows.
<<
  1. empty
  2. x ~ bind_typ T
  3. Y ~ bind_sub S ++ x ~ bind_typ T
  4. F ++ x ~ bind_typ T ++ E
>> The symbol "[++]" denotes list concatenation and associates to the
    right.  (That notation is defined in Coq's List library.)  Note
    that in Coq, environments grow on the left, since that is where
    the head of a list is. *)

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_typ : forall (E : env) (x : atom),
      wf_env E ->
      x `notin` dom E ->
      wf_env (x ~ bind_typ  ++ E).

Inductive wf_sig : env -> sig -> Prop :=
  | wf_sig_empty : forall E,
      wf_env E ->
      wf_sig E sempty
  | wf_sig_typ : forall (E : env) (R : sig) (l : label),
      wf_sig E R ->
      LabelSetImpl.notin l (Signatures.dom R) ->
      wf_sig E (l ~ bind_sig ++ R).

(* ********************************************************************** *)
(** * #<a name="values"></a># Values *)

Inductive value : exp -> Prop :=
  | value_abs : forall e1,
      expr (exp_abs e1) ->
      value (exp_abs e1)
  | value_ref : forall l,
      value (exp_ref l)
  | value_sealed_ref : forall l,
      value (exp_seal (exp_ref l))
  | value_record : forall r,
      value_record_comp r ->
      value (exp_record r)
  | value_sealed_record : forall r,
      value_record_comp r ->
      value (exp_seal (exp_record r))
with value_record_comp : rec_comp -> Prop :=
  | value_rec_empty :
      value_record_comp rec_empty
  | value_rec_ref : forall a l r,
      value_record_comp r -> 
      value_record_comp (rec_ref a l r)
.



(* ********************************************************************** *)
(** * #<a name="stores"></a> Stores *)

(**
  A store is simply just a mapping from labels to values.
*)
Notation store := (LabelMap exp).
Notation empty_store := (LabelMapImpl.empty store).

(**
  A well formed store maps labels to values.
*)
Definition well_formed_store (s : store) :=
  forall l v, LabelMapImpl.MapsTo l v s -> value v.

(**
  To ease proofs on stores, it is useful to have a way to pick
  a fresh label not in a store.
*)
Lemma label_map_in_iff_keys : forall l (s : store),
  LabelMapImpl.In l s <-> List.In l (List.map fst (LabelMapImpl.elements s)).
Proof with eauto.
  intros; split; intro In...
  + destruct In as [e MapsTo].
    apply LabelMapImpl.elements_1 in MapsTo.
    set (L := LabelMapImpl.elements s) in *.
    induction L; subst...
    * inversion MapsTo...
    * destruct a as [l' e']; simpl in *...
      inversion MapsTo as [? ? Eq|?]; subst...
      inversion Eq...
  + apply List.in_map_iff in In.
    destruct In as [[l' e] [EqH In]]; simpl in *; subst.
    unshelve epose proof (proj2 (InA_alt (@LabelMapImpl.eq_key_elt exp) (l, e) (LabelMapImpl.elements s)) _)
      as InEltImp.
    exists (l, e); repeat split...
    eexists. eapply LabelMapImpl.elements_2...
Qed.

Definition exists_fresh_label_for_store (s : store) : {l | ~ LabelMapImpl.In l s }.
Proof.
  exists (Label.fresh (List.map fst (LabelMapImpl.elements s))).
  intro NotFr.
  apply label_map_in_iff_keys in NotFr.
  apply Label.fresh_not_in in NotFr; auto.
Defined.

Definition fresh_label_for_store (s : store) := proj1_sig (exists_fresh_label_for_store s).


(* ********************************************************************** *)
(** * #<a name="reduction"></a># Reduction *)

Fixpoint record_dom (r : rec_comp)  {struct r} : atoms :=
    match r with
    | rec_empty => {}
    | rec_exp a e r => {{ a }} `union` record_dom r
    | rec_ref a l r => {{ a }} `union` record_dom r
    end.

Fixpoint record_lookup_ref (a : atom) (r : rec_comp) : option label :=
    match r with 
    | rec_ref a' l r => if (a === a') then Some l else record_lookup_ref a r
    | _ => None
    end.
Notation "r # a" := (record_lookup_ref a r) (at level 70).

Inductive red : exp -> store -> exp -> store -> Prop :=
  | red_app_1 : forall e1 e1' s1 s1' e2,
      expr e2 ->
      red e1 s1 e1' s1' ->
      red (exp_app e1 e2) s1 (exp_app e1' e2) s1'
  | red_app_2 : forall e1 e2 s2 e2' s2',
      value e1 ->
      red e2 s2 e2' s2' ->
      red (exp_app e1 e2) s2 (exp_app e1 e2') s2'
  | red_abs : forall e1 s1 v2,
      well_formed_store s1 ->
      expr (exp_abs e1) ->
      value v2 ->
      red (exp_app (exp_abs e1) v2) s1 (open_ee e1 v2) s1
  | red_let_1 : forall e1 e1' s1 s1' e2,
      red e1 s1 e1' s1' ->
      body_e e2 ->
      red (exp_let e1 e2) s1 (exp_let e1' e2) s1'
  | red_let : forall v1 e2 s2,
      well_formed_store s2 ->
      value v1 ->
      body_e e2 ->
      red (exp_let v1 e2) s2 (open_ee e2 v1) s2
  | red_box_1 : forall e1 e1' s1 s1',
      red e1 s1 e1' s1' ->
      red (exp_box e1) s1 (exp_box e1') s1'
  | red_box_ref : forall v1 l s1,
      well_formed_store s1 ->
      value v1 ->
      l = fresh_label_for_store s1 ->
      red (exp_box v1) s1 (exp_ref l) (LabelMapImpl.add l v1 s1)
  | red_unbox_1 : forall e1 e1' s1 s1',
      red e1 s1 e1' s1' ->
      red (exp_unbox e1) s1 (exp_unbox e1') s1'
  | red_unbox_ref : forall l v1 s1,
      well_formed_store s1 ->
      value v1 ->
      LabelMapImpl.MapsTo l v1 s1 ->
      red (exp_unbox (exp_ref l)) s1 v1 s1
  | red_unbox_sealed_ref : forall l v1 s1,
      well_formed_store s1 ->
      value v1 ->
      LabelMapImpl.MapsTo l v1 s1 ->
      red (exp_unbox (exp_seal (exp_ref l))) s1 (exp_seal v1) s1
  | red_set_box_1 : forall e1 s1 e1' s1' e2,
      expr e2 ->
      red e1 s1 e1' s1' ->
      red (exp_set_box e1 e2) s1 (exp_set_box e1' e2) s1'
  | red_set_box_2 : forall v1 e2 s2 e2' s2',
      value v1 ->
      red e2 s2 e2' s2' ->
      red (exp_set_box v1 e2) s2 (exp_set_box v1 e2') s2'
  | red_set_box_ref : forall l v1 v2 s1,
      well_formed_store s1 ->
      value v1 ->
      value v2 ->
      LabelMapImpl.MapsTo l v1 s1 ->
      red (exp_set_box (exp_ref l) v2) s1 v1 (LabelMapImpl.add l v2 s1)
  | red_seal_1 : forall e1 s1 e1' s1',
      red e1 s1 e1' s1' ->
      red (exp_seal e1) s1 (exp_seal e1') s1'
  | red_seal_abs : forall e1 s1,
      well_formed_store s1 ->
      expr (exp_abs e1) ->
      red (exp_seal (exp_abs e1)) s1 (exp_abs e1) s1
  | red_seal_sealed_ref: forall l s1,
      well_formed_store s1 ->
      red (exp_seal (exp_seal (exp_ref l))) s1 (exp_seal (exp_ref l)) s1
  | red_seal_sealed_record : forall r s1,
      well_formed_store s1 ->
      value_record_comp r ->
      red (exp_seal (exp_seal (exp_record r))) s1 (exp_seal (exp_record r)) s1
  | red_record : forall r1 s1 r1' s1',
      red_record_comp r1 s1 r1' s1' ->
      red (exp_record r1) s1 (exp_record r1') s1'
  | red_record_read_1 : forall a e1 e1' s1 s1',
      red e1 s1 e1' s1' ->
      red (exp_record_read e1 a) s1 (exp_record_read e1' a) s1'
  | red_record_read_ref : forall r a l v1 s1,
      well_formed_store s1 ->
      value_record_comp r ->
      record_lookup_ref a r = Some l ->
      value v1 ->
      LabelMapImpl.MapsTo l v1 s1 ->
      red (exp_record_read (exp_record r) a) s1 v1 s1
  | red_sealed_record_read_ref : forall r a l v1 s1,
      well_formed_store s1 ->
      value_record_comp r ->
      record_lookup_ref a r = Some l ->
      value v1 ->
      LabelMapImpl.MapsTo l v1 s1 ->
      red (exp_record_read (exp_seal (exp_record r)) a) s1 (exp_seal v1) s1
  | red_record_write_1 : forall a e1 s1 e1' s1' e2,
      expr e2 ->
      red e1 s1 e1' s1' ->
      red (exp_record_write e1 a e2) s1 (exp_record_write e1' a e2) s1'
  | red_record_write_2 : forall a v1 e2 s2 e2' s2',
      value v1 ->
      red e2 s2 e2' s2' ->
      red (exp_record_write v1 a e2) s2 (exp_record_write v1 a e2') s2'
  | red_record_write_ref : forall a l r v1 v2 s1,
      well_formed_store s1 ->
      value_record_comp r ->
      record_lookup_ref a r = Some l ->
      value v1 ->
      value v2 ->
      LabelMapImpl.MapsTo l v1 s1 ->
      red (exp_record_write (exp_record r) a v2) s1 v1 (LabelMapImpl.add l v2 s1)
with red_record_comp : rec_comp -> store -> rec_comp -> store -> Prop :=
  | red_record_exp_1 : forall a e1 s1 e1' s1' r1,
      record_comp r1 ->
      red e1 s1 e1' s1' ->
      red_record_comp (rec_exp a e1 r1) s1 (rec_exp a e1' r1) s1'
  | red_record_exp_2 : forall a v r1 s1 l,
      well_formed_store s1 ->
      record_comp r1 ->
      value v ->
      l = fresh_label_for_store s1 ->
      red_record_comp (rec_exp a v r1) s1 (rec_ref a l r1) (LabelMapImpl.add l v s1)
  | red_record_ref : forall a l r1 s1 r1' s1',
      red_record_comp r1 s1 r1' s1' ->
      red_record_comp (rec_ref a l r1) s1 (rec_ref a l r1') s1'
.

Notation "< e1 | s1 > --> < e1' | s1' >" := (red e1 s1 e1' s1') (at level 69).
Notation "< r1 | s1 > -->r < r1' | s1' >" := (red_record_comp r1 s1 r1' s1') (at level 69).

Inductive redm : exp -> store -> exp -> store -> Prop :=
  | redm_eq : forall e s e' s',
    e = e' -> s = s' -> redm e s e' s'
  | redm_step : forall e s e'' s'' e' s', 
    red e s e'' s'' ->
    redm e'' s'' e' s' ->
    redm e s e' s'.

Notation "< e1 | s1 > -->* < e1' | s1' >" := (redm e1 s1 e1' s1') (at level 69).

(* ********************************************************************** *)
(** * #<a name="immutability"></a># Immutability Equivalence *)

(**
  In order to prove that we can add seals freely whenever the typing judgment
  allows us to do so we need a notion of when two expressions are "equivalent" modulo
  seals.

  [sealcomp] captures this notion.  Whenever we have sealcomp e1 e2, we know
  that e2 is equivalent to e1 except with additional seals.  Note that
  [sealcomp] is a pre-ordering, and this is important, as expressions
  with additional seals take additional steps to reduce compared to the
  same expression with seals removed.
*)

Inductive sealcomp : exp -> exp -> Prop :=
  | sealcomp_fvar : forall (x : atom),
      sealcomp x x
  | sealcomp_bvar : forall (n : nat),
      sealcomp n n
  | sealcomp_abs : forall e1 e2,
      sealcomp e1 e2 ->
      sealcomp (exp_abs e1) (exp_abs e2)
  | sealcomp_app : forall e1 e2 f1 f2,
      sealcomp e1 f1 ->
      sealcomp e2 f2 ->
      sealcomp (exp_app e1 e2) (exp_app f1 f2)
  | sealcomp_let : forall e1 e2 f1 f2,
      sealcomp e1 f1 ->
      sealcomp e2 f2 ->
      sealcomp (exp_let e1 e2) (exp_let f1 f2)
  | sealcomp_box : forall e1 e2,
      sealcomp e1 e2 ->
      sealcomp (exp_box e1) (exp_box e2)
  | sealcomp_unbox : forall e1 e2,
      sealcomp e1 e2 ->
      sealcomp (exp_unbox e1) (exp_unbox e2)
  | sealcomp_set_box : forall e1 e2 f1 f2,
      sealcomp e1 f1 ->
      sealcomp e2 f2 ->
      sealcomp (exp_set_box e1 e2) (exp_set_box f1 f2)
  | sealcomp_ref : forall l,
      sealcomp (exp_ref l) (exp_ref l)
  | sealcomp_seal : forall e1 e2,
      sealcomp e1 e2 ->
      sealcomp (exp_seal e1) (exp_seal e2)
  | sealcomp_record : forall r1 r2,
      sealcomp_rec_comp r1 r2 ->
      sealcomp (exp_record r1) (exp_record r2)
  | sealcomp_record_read : forall e1 e2 x,    
      sealcomp e1 e2 ->
      sealcomp (exp_record_read e1 x) (exp_record_read e2 x)
  | sealcomp_record_write : forall e1 f1 x e2 f2,
      sealcomp e1 f1 ->
      sealcomp e2 f2 ->
      sealcomp (exp_record_write e1 x e2) (exp_record_write f1 x f2)
  | sealcomp_multiple_seal : forall e1 e2,
      sealcomp e1 e2 ->
      sealcomp e1 (exp_seal e2)
with sealcomp_rec_comp : rec_comp -> rec_comp -> Prop :=
  | sealcomp_rec_empty :
      sealcomp_rec_comp (rec_empty) (rec_empty)
  | sealcomp_rec_exp : forall a e1 e2 r1 r2,
      sealcomp_rec_comp r1 r2 ->
      sealcomp e1 e2 ->
      sealcomp_rec_comp (rec_exp a e1 r1) (rec_exp a e2 r2)
  | sealcomp_rec_ref : forall a l r1 r2,
      sealcomp_rec_comp r1 r2 ->
      sealcomp_rec_comp (rec_ref a l r1) (rec_ref a l r2)
.

Definition sealcomp_store (s1 : store) (s2 : store) :=
  (forall l v, (LabelMapImpl.MapsTo l v s1) ->
      exists v', (LabelMapImpl.MapsTo l v' s2) /\ sealcomp v v') /\
  (forall l v', (LabelMapImpl.MapsTo l v' s2) ->
      exists v, (LabelMapImpl.MapsTo l v s1) /\ sealcomp v v').

Notation "e1 <e= e2" := (sealcomp e1 e2) (at level 60).
Notation "r1 <r= r2" := (sealcomp_rec_comp r1 r2) (at level 60).
Notation "s1 <s= s2" := (sealcomp_store s1 s2) (at level 60).

(* ********************************************************************** *)
(** * #<a name="count_seals"></a># Counting seals *)
Fixpoint seal_count (e : exp)  {struct e} : nat :=
  match e with
  | exp_bvar i => 0
  | exp_fvar x => 0
  | exp_abs e1 => (seal_count e1)
  | exp_app e1 e2 => (seal_count e1) + (seal_count e2)
  | exp_let e1 e2 => (seal_count e1) + (seal_count e2)
  | exp_box e => (seal_count e)
  | exp_unbox e => (seal_count e)
  | exp_set_box b e => (seal_count b) + (seal_count e)
  | exp_ref l => 0
  | exp_seal e => (S (seal_count e))
  | exp_record r => (seal_count_record r)
  | exp_record_read e a => (seal_count e)
  | exp_record_write e1 a e2 => (seal_count e1) + (seal_count e2)
  end
with
  seal_count_record (r : rec_comp)  {struct r} : nat :=
  match r with 
  | rec_empty => 0
  | rec_exp a e r => (seal_count e) + (seal_count_record r)
  | rec_ref a l r => (seal_count_record r)
  end.  
Arguments seal_count e /.
Arguments seal_count_record r /.

Notation "| f |" := (seal_count f) (at level 69).

(* ********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We declare most constructors as [Hint]s to be used by the [auto]
    and [eauto] tactics.  We exclude constructors from the subtyping
    and typing relations that use cofinite quantification.  It is
    unlikely that [eauto] will find an instantiation for the finite
    set [L], and in those cases, [eauto] can take some time to fail.
    (A priori, this is not obvious.  In practice, one adds as hints
    all constructors and then later removes some constructors when
    they cause proof search to take too long.) *)

#[export] Hint Constructors  expr record_comp  wf_env wf_sig value red value_record_comp red_record_comp : core. 
#[export] Hint Constructors sealcomp sealcomp_rec_comp : core.
#[export] Hint Constructors redm : core.
