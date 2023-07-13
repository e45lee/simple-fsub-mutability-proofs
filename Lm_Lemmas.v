(** Administrative lemmas for Fsub.

    Authors: Edward Lee, Ondrej Lhotak

    Authors: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    This file contains a number of administrative lemmas that we
    require for proving type-safety.  The lemmas mainly concern the
    relations [wf_typ] and [wf_env].

    This file also contains regularity lemmas, which show that various
    relations hold only for locally closed terms.  In addition to
    being necessary to complete the proof of type-safety, these lemmas
    help demonstrate that our definitions are correct; they would be
    worth proving even if they are unneeded for any "real" proofs.

    Table of contents:
      - #<a href="##typp">Properties of type</a>#
      - #<a href="##wft">Properties of wf_typ</a>#
      - #<a href="##oktwft">Properties of wf_env and wf_typ</a>#
      - #<a href="##okt">Properties of wf_env</a>#
      - #<a href="##subst">Properties of substitution</a>#
      - #<a href="##regularity">Regularity lemmas</a>#
      - #<a href="##auto">Automation</a># *)

Require Export Fsub.Lm_Infrastructure.
  
(* ********************************************************************** *)
(** * #<a name="oktwft"></a># Properties of [wf_env], [wf_sig], and [wf_typ] *)

Lemma uniq_from_wf_env : forall E,
  wf_env E ->
  uniq E.
Proof.
  intros E H; induction H; auto.
Qed.

Lemma uniq_from_wf_sig : forall E R,
  wf_sig E R ->
  Signatures.uniq R.
Proof.
  intros E R H; induction H; auto. 
Qed.

(** We add [uniq_from_wf_env] as a hint here since it helps blur the
    distinction between [wf_env] and [uniq] in proofs.  The lemmas in
    the MetatheoryEnv library use [uniq], whereas here we naturally
    have (or can easily show) the stronger [wf_env].  Thus,
    [uniq_from_wf_env] serves as a bridge that allows us to use the
    environments library. *)

#[export] Hint Resolve uniq_from_wf_env : core.
#[export] Hint Resolve uniq_from_wf_sig : core.


(* ********************************************************************** *)
(** * #<a name="regularity"></a># Regularity of relations *)

Lemma value_regular : forall e,
  value e ->
  expr e
with value_record_regular : forall r,
  value_record_comp r ->
  record_comp r.
Proof.
------
  clear value_regular.
  intros e H. induction H; auto.
------
  clear value_record_regular.
  intros r H. induction H; auto.
Qed.

Lemma well_formed_store_add : forall l v s,
  well_formed_store s ->
  value v ->
  well_formed_store (LabelMapImpl.add l v s).
Proof with eauto.
  intros * WfS Value l' v' MapsTo.
  destruct (l' == l); subst.
  - eapply LabelMapFacts.add_mapsto_iff in MapsTo; intuition; subst...
  - eapply LabelMapFacts.add_mapsto_iff in MapsTo; intuition; subst...
Qed.
#[export] Hint Resolve well_formed_store_add : core.

Lemma red_regular : forall e s e' s',
  red e s e' s' ->
  expr e /\ well_formed_store s /\ expr e' /\ well_formed_store s'
with red_record_comp_regular : forall r s r' s',
  red_record_comp r s r' s' ->
  record_comp r /\ well_formed_store s /\ record_comp r' /\ well_formed_store s'.
Proof with try solve [auto | intuition auto].
------
  clear red_regular.
  intros e s e' s' H.
  induction H; assert(J := value_regular)...
  Case "red_abs".
    split... split... inversion H0. pick fresh y. rewrite (subst_ee_intro y)...
  Case "red_record".
    destruct (red_record_comp_regular _ _ _ _ H)...
------
  clear red_record_comp_regular.
  intros r s r' s' H.
  induction H; assert(J := value_regular)...
  Case "red_record_exp_1".
    destruct (red_regular _ _ _ _ H0)...
Qed.

Lemma expr_multistep : forall e s e' s',
  redm e s e' s' ->
  expr e ->
  expr e'.
Proof with eauto.
  intros * Red Expr.
  induction Red; subst...
  edestruct (red_regular _ _ _ _ H); intuition.
Qed.

Lemma well_formed_store_multistep : forall e s e' s',
  redm e s e' s' ->
  well_formed_store s ->
  well_formed_store s'.
Proof with eauto.
  intros * Red Expr.
  induction Red; subst...
  edestruct (red_regular _ _ _ _ H); intuition.
Qed.

Lemma wf_sig_regular : forall E R,
  wf_sig E R ->
  wf_env E.
Proof with eauto.
  intros. induction H...
Qed.

(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** The lemma [uniq_from_wf_env] was already added above as a hint
    since it helps blur the distinction between [wf_env] and [uniq] in
    proofs.

    As currently stated, the regularity lemmas are ill-suited to be
    used with [auto] and [eauto] since they end in conjunctions.  Even
    if we were, for example, to split [sub_regularity] into three
    separate lemmas, the resulting lemmas would be usable only by
    [eauto] and there is no guarantee that [eauto] would be able to
    find proofs effectively.  Thus, the hints below apply the
    regularity lemmas and [type_from_wf_typ] to discharge goals about
    local closure and well-formedness, but in such a way as to
    minimize proof search.

    The first hint introduces an [wf_env] fact into the context.  It
    works well when combined with the lemmas relating [wf_env] and
    [wf_typ].  We choose to use those lemmas explicitly via [(auto
    using ...)] tactics rather than add them as hints.  When used this
    way, the explicitness makes the proof more informative rather than
    more cluttered (with useless details).

    The other three hints try outright to solve their respective
    goals. *)

(* wf_env /\ wf_sig /\ expr /\ wf_typ *)

#[export] Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: wf_sig _ _ |- _ => apply (wf_sig_regular _ _ H)
  end : core.

#[export] Hint Extern 1 (expr ?e) =>
  match goal with
  | H: red ?e _ _ _ |- _ => apply (proj1 (red_regular _ _ _ _ H))
  | H: red _ _ ?e _ |- _ => apply (proj1 (proj2 (proj2 (red_regular _ _ _ _ H))))
  end : core.

#[export] Hint Extern 1 (well_formed_store ?s) =>
  match goal with 
  | H: red _ ?s _ _ |- _ => apply (proj1 (proj2 (red_regular _ _ _ _ H)))
  | H: red _ _ _ ?s |- _ => apply (proj2 (proj2 (proj2 (red_regular _ _ _ _ H))))
  end : core.

#[export] Hint Extern 1 (record_comp ?e) =>
  match goal with
  | H: red_record_comp ?e _ _ _ |- _ => apply (proj1 (red_record_comp_regular _ _ _ _ H))
  | H: red_record_comp _ _ ?e _ |- _ => apply (proj1 (proj2 (proj2 (red_record_comp_regular _ _ _ _ H))))
  end : core.


#[export] Hint Resolve value_regular value_record_regular expr_multistep well_formed_store_multistep : core.
