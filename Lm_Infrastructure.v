(** Infrastructure lemmas and tactic definitions for STLC + mutability.

    Authors: Edward Lee, Ondrej Lhotak

    This work is based off the POPL'08 Coq tutorial
    authored by: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    This file contains a number of definitions, tactics, and lemmas
    that are based only on the syntax of the language at hand.  While
    the exact statements of everything here would change for a
    different language, the general structure of this file (i.e., the
    sequence of definitions, tactics, and lemmas) would remain the
    same.

    Table of contents:
      - #<a href="##fv">Free variables</a>#
      - #<a href="##subst">Substitution</a>#
      - #<a href="##gather_atoms">The "gather_atoms" tactic</a>#
      - #<a href="##properties">Properties of opening and substitution</a>#
      - #<a href="##lc">Local closure is preserved under substitution</a>#
      - #<a href="##nf-properties"> Additional properties of normal forms under opening and substitution</a>#
      - #<a href="##auto">Automation</a>#
      - #<a href="##body">Properties of body_e</a># *)

Require Export Fsub.Lm_Definitions.


(* ********************************************************************** *)
(** * #<a name="fv"></a># Free variables *)

(** In this section, we define free variable functions.  The functions
    [fv_tt] and [fv_te] calculate the set of atoms used as free type
    variables in a type or expression, respectively.  The function
    [fv_ee] calculates the set of atoms used as free expression
    variables in an expression.  Cases involving binders are
    straightforward since bound variables are indices, not names, in
    locally nameless representation. *)

Fixpoint fv_ee (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => {{ x }}
  | exp_abs e1 => (fv_ee e1)
  | exp_app e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_let e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_box e => (fv_ee e)
  | exp_unbox e => (fv_ee e)
  | exp_set_box e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_ref l => {}
  | exp_seal e => (fv_ee e)
  | exp_record r => (fv_ee_record r)
  | exp_record_read e a => (fv_ee e)
  | exp_record_write e1 a e2 => (fv_ee e1) `union` (fv_ee e2)
  end
with fv_ee_record (r : rec_comp) {struct r} : atoms :=
  match r with
  | rec_empty => {}
  | rec_exp a e r => (fv_ee e) `union` (fv_ee_record r)
  | rec_ref a l r => (fv_ee_record r)
  end.


(* ********************************************************************** *)
(** * #<a name="subst"></a># Substitution *)

(** In this section, we define substitution for expression and type
    variables appearing in types, expressions, and environments.
    Substitution differs from opening because opening replaces indices
    whereas substitution replaces free variables.  The definitions
    below are relatively simple for two reasons.
      - We are using locally nameless representation, where bound
        variables are represented using indices.  Thus, there is no
        need to rename variables to avoid capture.
      - The definitions below assume that the term being substituted
        in, i.e., the second argument to each function, is locally
        closed.  Thus, there is no need to shift indices when passing
        under a binder. *)


Fixpoint subst_ee (z : atom) (u : exp) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => if x == z then u else e
  | exp_abs e1 => exp_abs (subst_ee z u e1)
  | exp_app e1 e2 => exp_app (subst_ee z u e1) (subst_ee z u e2)
  | exp_let e1 e2 => exp_let (subst_ee z u e1) (subst_ee z u e2)
  | exp_box e => exp_box (subst_ee z u e)
  | exp_unbox e => exp_unbox (subst_ee z u e)
  | exp_set_box e1 e2 => exp_set_box (subst_ee z u e1) (subst_ee z u e2)
  | exp_ref l => exp_ref l
  | exp_seal e => exp_seal (subst_ee z u e)
  | exp_record r => exp_record (subst_ee_record z u r)
  | exp_record_read e a => exp_record_read (subst_ee z u e) a
  | exp_record_write e1 a e2 => exp_record_write (subst_ee z u e1) a (subst_ee z u e2)
  end
with subst_ee_record (z : atom) (u : exp) (r : rec_comp) {struct r} : rec_comp :=
  match r with
  | rec_empty => rec_empty
  | rec_exp a e r => rec_exp a (subst_ee z u e) (subst_ee_record z u r)
  | rec_ref a l r => rec_ref a l (subst_ee_record z u r)
  end.

(* ********************************************************************** *)
(** * #<a name="gather_atoms"></a># The "[gather_atoms]" tactic *)

(** The Metatheory and MetatheoryAtom libraries define a number of
    tactics for working with cofinite quantification and for picking
    fresh atoms.  To specialize those tactics to this language, we
    only need to redefine the [gather_atoms] tactic, which returns the
    set of all atoms in the current context.

    The definition of [gather_atoms] follows a pattern based on
    repeated calls to [gather_atoms_with].  The one argument to this
    tactic is a function that takes an object of some particular type
    and returns a set of atoms that appear in that argument.  It is
    not necessary to understand exactly how [gather_atoms_with] works.
    If we add a new inductive datatype, say for kinds, to our
    language, then we would need to modify [gather_atoms].  On the
    other hand, if we merely add a new type, say products, then there
    is no need to modify [gather_atoms]; the required changes would be
    made in [fv_tt]. *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let D := gather_atoms_with (fun x : exp => fv_ee x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  constr:(A `union` B  `union` D  `union` F).


(* ********************************************************************** *)
(** * #<a name="properties"></a># Properties of opening and substitution *)

(** The following lemmas provide useful structural properties of
    substitution and opening.  While the exact statements are language
    specific, we have found that similar properties are needed in a
    wide range of languages.

    Below, we indicate which lemmas depend on which other lemmas.
    Since [te] functions depend on their [tt] counterparts, a similar
    dependency can be found in the lemmas.

    The lemmas are split into three sections, one each for the [tt],
    [te], and [ee] functions.  The most important lemmas are the
    following:
      - Substitution and opening commute with each other, e.g.,
        [subst_tt_open_tt_var].
      - Opening a term is equivalent to opening the term with a fresh
        name and then substituting for that name, e.g.,
        [subst_tt_intro].

    We keep the sections as uniform in structure as possible.  In
    particular, we state explicitly strengthened induction hypotheses
    even when there are more concise ways of proving the lemmas of
    interest. *)

(* ********************************************************************** *)
(** ** Properties of expression substitution in expressions *)

(** This section follows the structure of the previous two sections. *)

Lemma open_ee_rec_expr_aux : forall e j v u i,
  i <> j ->
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e
with open_ee_record_rec_expr_aux : forall e j v u i,
  i <> j ->
  open_ee_record_rec j v e = open_ee_record_rec i u (open_ee_record_rec j v e) ->
  e = open_ee_record_rec i u e.  
Proof with congruence || eauto.
------
  induction e; intros j v u i Neq H; simpl in *; inversion H; f_equal...
  Case "exp_bvar".
    destruct (j===n)... destruct (i===n)...
------
  induction e; intros j v u i Neq H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_ee_rec_expr : forall u e k,
  expr e ->
  e = open_ee_rec k u e
with open_ee_record_rec_expr : forall u e k,
  record_comp e ->
  e = open_ee_record_rec k u e.
Proof with auto.
------
  intros u e k Hexpr. revert k.
  induction Hexpr; intro k; simpl; f_equal; auto*;
  try solve [
    unfold open_ee in *;
    pick fresh x;
    eapply open_ee_rec_expr_aux with (j := 0) (v := exp_fvar x);
    auto
  | unfold open_te in *;
    pick fresh X;
    eapply open_ee_rec_type_aux with (j := 0) (V := typ_fvar X);
    auto
  ].
------
  intros u e k Hexpr. revert k.
  induction Hexpr; intro k; simpl; f_equal; auto*.  
Qed.

Lemma subst_ee_fresh : forall (x: atom) u e,
  x `notin` fv_ee e ->
  e = subst_ee x u e
with subst_ee_record_fresh : forall (x: atom) u e,
  x `notin` fv_ee_record e ->
  e = subst_ee_record x u e.
Proof with auto.
------
  intros x u e; induction e; simpl; intro H; f_equal...
  Case "exp_fvar".
    destruct (a==x)...
    contradict H; fsetdec.
------
  intros x u e; induction e; simpl; intro H; f_equal...
Qed.

Lemma subst_ee_open_ee_rec : forall e1 e2 x u k,
  expr u ->
  subst_ee x u (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_ee x u e2) (subst_ee x u e1)
with subst_ee_record_open_ee_record_recrec : forall e1 e2 x u k,
  expr u ->
  subst_ee_record x u (open_ee_record_rec k e2 e1) =
    open_ee_record_rec k (subst_ee x u e2) (subst_ee_record x u e1).
Proof with auto.
------
  intros e1 e2 x u k WP. revert k.
  induction e1; intros k; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n); subst...
  Case "exp_fvar".
    destruct (a == x); subst... apply open_ee_rec_expr...
------
  intros e1 e2 x u k WP. revert k.
  induction e1; intros k; simpl; f_equal...
Qed.

Lemma subst_ee_open_ee : forall e1 e2 x u,
  expr u ->
  subst_ee x u (open_ee e1 e2) =
    open_ee (subst_ee x u e1) (subst_ee x u e2).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ee_open_ee_rec...
Qed.

Lemma subst_ee_open_ee_var : forall (x y:atom) u e,
  y <> x ->
  expr u ->
  open_ee (subst_ee x u e) y = subst_ee x u (open_ee e y).
Proof with congruence || auto.
  intros x y u e Neq Wu.
  unfold open_ee.
  rewrite subst_ee_open_ee_rec...
  simpl.
  destruct (y == x)...
Qed.

Lemma subst_ee_intro_rec : forall x e u k,
  x `notin` fv_ee e ->
  open_ee_rec k u e = subst_ee x u (open_ee_rec k (exp_fvar x) e)
with subst_ee_record_intro_rec : forall x e u k,
  x `notin` fv_ee_record e ->
  open_ee_record_rec k u e = subst_ee_record x u (open_ee_record_rec k (exp_fvar x) e).
Proof with congruence || auto.
------
  induction e; intros u k Fr; simpl in *; f_equal...
  Case "exp_bvar".
    destruct (k === n)... simpl. destruct (x == x)...
  Case "exp_fvar".
    destruct (a == x)... contradict Fr; fsetdec.
------
  induction e; intros u k Fr; simpl in *; f_equal...
Qed.

Lemma subst_ee_intro : forall x e u,
  x `notin` fv_ee e ->
  open_ee e u = subst_ee x u (open_ee e x).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ee_intro_rec...
Qed.


(* *********************************************************************** *)
(** * #<a name="lc"></a># Local closure is preserved under substitution *)

(** While these lemmas may be considered properties of substitution, we
    separate them out due to the lemmas that they depend on. *)


(** The following lemma depends on [subst_ee_open_ee_var] and
    [subst_ee_open_te_var]. *)

Lemma subst_ee_expr : forall z e1 e2,
  expr e1 ->
  expr e2 ->
  expr (subst_ee z e2 e1)
with subst_ee_record_expr : forall z e1 e2,
  record_comp e1 ->
  expr e2 ->
  record_comp (subst_ee_record z e2 e1).
Proof with auto.
------
  intros z e1 e2 He1 He2.
  induction He1; simpl; auto;
  try solve [
    econstructor;
    try instantiate (1 := L `union` singleton z);
    intros;
    try rewrite subst_ee_open_ee_var;
    try rewrite subst_ee_open_te_var;
    instantiate;
    auto
  ].
  Case "expr_var".
    destruct (x == z)...
------
  intros z e1 e2 He1 He2.
  induction He1; simpl; auto.
Qed.


(* *********************************************************************** *)
(** * #<a name="body"></a># Properties of [body_e] *)

(** The two kinds of facts we need about [body_e] are the following:
      - How to use it to derive that terms are locally closed.
      - How to derive it from the facts that terms are locally closed.

    Since we use it only in the context of [exp_let] and [exp_sum]
    (see the definition of reduction), those two constructors are the
    only ones we consider below. *)

Lemma expr_let_from_body : forall e1 e2,
  expr e1 ->
  body_e e2 ->
  expr (exp_let e1 e2).
Proof.
  intros e1 e2 H [J1 J2].
  pick fresh y and apply expr_let; auto.
Qed.

Lemma body_from_expr_let : forall e1 e2,
  expr (exp_let e1 e2) ->
  body_e e2.
Proof.
  intros e1 e2 H.
  unfold body_e.
  inversion H; eauto.
Qed.

Lemma open_ee_body_e : forall e1 e2,
  body_e e1 -> expr e2 -> expr (open_ee e1 e2).
Proof.
  intros e1 e2 [L H] J.
  pick fresh x.
  rewrite (subst_ee_intro x); auto using subst_ee_expr.
Qed.

Lemma record_dom_subst_ee_fresh : forall a x u r,
  a `notin` record_dom r ->
  a `notin` record_dom (subst_ee_record x u r).
Proof with eauto.
  intros.
  dependent induction r; simpl record_dom in *; simpl subst_ee_record in *...
Qed.


(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We add as hints the fact that local closure is preserved under
    substitution.  This is part of our strategy for automatically
    discharging local-closure proof obligations. *)

#[export] Hint Resolve subst_ee_expr : core.

(** We also add as hints the lemmas concerning [body_e]. *)

#[export] Hint Resolve expr_let_from_body body_from_expr_let : core.
#[export] Hint Resolve open_ee_body_e : core.

(** When reasoning about the [binds] relation and [map], we
    occasionally encounter situations where the binding is
    over-simplified.  The following hint undoes that simplification,
    thus enabling [Hint]s from the MetatheoryEnv library. *)

#[export] Hint Resolve record_dom_subst_ee_fresh : core.

