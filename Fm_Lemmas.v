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

Require Export Fsub.Fm_Infrastructure.

(* ********************************************************************** *)
(** * #<a name="typp"></a># Properties of [type] *)

(** Inversion hints for when a type is locally closed. *)
Lemma type_from_type_mut : forall T,
  type (typ_mut mut_readonly T) ->
  type T.
Proof with eauto.
  intros.
  inversion H...
Qed.

Lemma type_from_left_type_int : forall T1 T2,
  type (typ_int T1 T2) ->
  type T1.
Proof with eauto.
  intros.
  inversion H...
Qed.

Lemma type_from_right_type_int : forall T1 T2,
  type (typ_int T1 T2) ->
  type T2.
Proof with eauto.
  intros.
  inversion H...
Qed.

Lemma type_from_arrow_type_param : forall T1 T2,
  type (typ_arrow T1 T2) ->
  type T1.
Proof with eauto.
  intros.
  inversion H...
Qed.

Lemma type_from_arrow_type_return : forall T1 T2,
  type (typ_arrow T1 T2) ->
  type T2.
Proof with eauto.
  intros...
  inversion H...
Qed.

#[export] Hint Resolve 
  type_from_type_mut type_from_left_type_int type_from_right_type_int
  type_from_arrow_type_param type_from_arrow_type_return : core.


(* ********************************************************************** *)
(** * #<a name="wft"></a># Properties of [wf_typ] *)

(** If a type is well-formed in an environment, then it is locally
    closed. *)

Lemma type_from_wf_typ : forall E T,
  wf_typ E T -> type T.
Proof.
  intros E T H; induction H; eauto.
Qed.

Lemma type_arrow_arg_from_wf_typ_arrow : forall E T1 T2,
  wf_typ E (typ_arrow T1 T2) ->
  type T1.
Proof with eauto.
  intros.  inversion H; eauto; subst...
  eapply type_from_wf_typ...
Qed.

Lemma type_arrow_result_from_arrow : forall E T1 T2,
  wf_typ E (typ_arrow T1 T2) ->
  type T2.
Proof with eauto.
  intros.  inversion H; eauto; subst...
  eapply type_from_wf_typ...
Qed.

#[export] Hint Immediate type_arrow_arg_from_wf_typ_arrow 
  type_arrow_result_from_arrow : core.

(** The remaining properties are analogous to the properties that we
    need to show for the subtyping and typing relations. *)

Lemma wf_typ_weakening : forall T E F G,
  wf_typ (G ++ E) T ->
  uniq (G ++ F ++ E) ->
  wf_typ (G ++ F ++ E) T.
Proof with simpl_env; eauto.
  intros T E F G Hwf_typ Hk.
  remember (G ++ E) as F'.
  generalize dependent G.
  induction Hwf_typ; intros G Hok Heq; subst...
  Case "type_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    apply H0...
Qed.

Lemma wf_typ_weaken_head : forall T E F,
  wf_typ E T ->
  uniq (F ++ E) ->
  wf_typ (F ++ E) T.
Proof.
  intros.
  rewrite_env (empty ++ F++ E).
  auto using wf_typ_weakening.
Qed.

Lemma wf_typ_narrowing : forall V U T E F X,
  wf_typ (F ++ X ~ bind_sub V ++ E) T ->
  wf_typ (F ++ X ~ bind_sub U ++ E) T.
Proof with simpl_env; eauto.
  intros V U T E F X Hwf_typ.
  remember (F ++ X ~ bind_sub V ++ E) as G.
  generalize dependent F.
  induction Hwf_typ; intros F Heq; subst...
  Case "wf_typ_var".
    analyze_binds H...
  Case "typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    apply H0...
Qed.

Lemma wf_typ_strengthening : forall E F x U T,
 wf_typ (F ++ x ~ bind_typ U ++ E) T ->
 wf_typ (F ++ E) T.
Proof with simpl_env; eauto.
  intros E F x U T H.
  remember (F ++ x ~ bind_typ U ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq; subst...
  Case "wf_typ_var".
    analyze_binds H...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    apply H1...
Qed.

Lemma wf_typ_subst_tb : forall F Q E Z P T,
  wf_typ (F ++ Z ~ bind_sub Q ++ E) T ->
  wf_typ E P ->
  uniq (map (subst_tb Z P) F ++ E) ->
  wf_typ (map (subst_tb Z P) F ++ E) (subst_tt Z P T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ bind_sub Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_tt...
  Case "wf_typ_var".
    destruct (X == Z); subst...
    SCase "X <> Z".
      analyze_binds H...
      apply (wf_typ_var (subst_tt Z P U))...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) (Y ~ bind_sub T1 ++ F) ++ E).
    apply H0...
Qed.

Lemma wf_typ_open : forall E U T1 T2,
  uniq E ->
  wf_typ E (typ_all T1 T2) ->
  wf_typ E U ->
  wf_typ E (open_tt T2 U).
Proof with simpl_env; eauto.
  intros E U T1 T2 Ok WA WU.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_tt_intro X)...
  rewrite_env (map (subst_tb X U) empty ++ E).
  eapply wf_typ_subst_tb...
Qed.

Lemma wf_typ_arrow_arg_from_arrow : forall E T1 T2,
  wf_typ E (typ_arrow T1 T2) ->
  wf_typ E T1.
Proof.
  intros.  inversion H; eauto.
Qed.

Lemma wf_typ_arrow_result_from_arrow : forall E T1 T2,
  wf_typ E (typ_arrow T1 T2) ->
  wf_typ E T2.
Proof.
  intros.  inversion H; eauto.
Qed.

#[export] Hint Resolve wf_typ_arrow_arg_from_arrow wf_typ_arrow_result_from_arrow : core.

Lemma wf_typ_from_wf_mut_typ : forall E T,
  wf_typ E (typ_mut mut_readonly T) ->
  wf_typ E T.
Proof with eauto.
  intros * WfmT.
  inversion WfmT...
Qed.
#[export] Hint Resolve wf_typ_from_wf_mut_typ : core.

Lemma wf_typ_from_wf_typ_box : forall E T,
  wf_typ E (typ_box T) ->
  wf_typ E T.
Proof with eauto.
  intros * WfBT.
  inversion WfBT...
Qed.
#[export] Hint Resolve wf_typ_from_wf_typ_box : core.

Lemma wf_typ_from_wf_typ_readonly_box : forall E T,
  wf_typ E (typ_mut mut_readonly (typ_box T)) ->
  wf_typ E T.
Proof with eauto.
  intros * WfBRT.
  inversion WfBRT...
Qed.

#[export] Hint Resolve  wf_typ_from_wf_typ_readonly_box : core.

Lemma wf_typ_int_left_from_wf_typ_int : forall E T1 T2,
  wf_typ E (typ_int T1 T2) ->
  wf_typ E T1.
Proof with eauto.
  intros * Wf. inversion Wf...
Qed.

Lemma wf_typ_int_right_from_wf_typ_int : forall E T1 T2,
  wf_typ E (typ_int T1 T2) ->
  wf_typ E T2.
Proof with eauto.
  intros * Wf. inversion Wf...
Qed.

#[export] Hint Resolve wf_typ_int_left_from_wf_typ_int
  wf_typ_int_right_from_wf_typ_int : core.

Lemma wf_typ_from_wf_typ_record : forall E a T,
  wf_typ E (typ_record a T) ->
  wf_typ E T.
Proof with eauto.
  intros * WfBT.
  inversion WfBT...
Qed.
#[export] Hint Resolve wf_typ_from_wf_typ_record : core.

Lemma wf_typ_from_wf_typ_readonly_record : forall E a T,
  wf_typ E (typ_mut mut_readonly (typ_record a T)) ->
  wf_typ E T.
Proof with eauto.
  intros * WfBRT.
  inversion WfBRT...
Qed.
#[export] Hint Resolve  wf_typ_from_wf_typ_readonly_record : core.

  
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

Lemma wf_typ_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  wf_typ E U.
Proof with auto using wf_typ_weaken_head.
  induction 1; intros J; analyze_binds J...
  injection BindsTacVal; intros; subst...
Qed.

Lemma wf_typ_from_binds_sig : forall x U E R,
  wf_sig E R ->
  Signatures.binds x (bind_sig U) R ->
  wf_typ E U.
Proof with auto.
  induction 1; intros J; Signatures.destruct_binds_hyp J...
  (** Something goes wrong, so we have to invert manually. *)
  inversion BindsTac; inversion H2; subst...
Qed.

Lemma wf_box_typ_from_binds_sig : forall x U E R,
  wf_env E ->
  wf_sig E R ->
  Signatures.binds x (bind_sig U) R ->
  wf_typ E (typ_box U).
Proof with eauto using wf_typ_from_binds_sig.
  intros...
Qed.
  
Lemma wf_typ_from_wf_env_typ : forall x T E,
  wf_env (x ~ bind_typ T ++ E) ->
  wf_typ E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.

Lemma wf_typ_from_wf_env_sub : forall x T E,
  wf_env (x ~ bind_sub T ++ E) ->
  wf_typ E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.

(** Additional properties of in_intersection and wellformedness *)
Lemma in_intersection_trans : forall S T1 T2,
  in_intersection S T1 ->
  in_intersection T1 T2 ->
  in_intersection S T2.
Proof with eauto.
  intros.
  dependent induction H0; subst...
Qed.

Lemma wf_in_intersection : forall E T T',
  in_intersection T T' ->
  wf_typ E T' ->
  wf_typ E T.
Proof with eauto.
  intros * Int WfT'.
  dependent induction Int; subst...
Qed.
#[export] Hint Resolve wf_in_intersection : core.

(** Additional properties of normal forms and wellformedness. *)
Lemma merge_mutability_wellformed : forall E T,
  wf_typ E T ->
  wf_typ E (merge_mutability T mut_readonly).
Proof with eauto; try repeat fold merge_mutability.
  intros * Wf.
  induction Wf; simpl...
Qed.

#[export] Hint Resolve merge_mutability_wellformed : core.

Lemma normal_form_wellformed : forall E T,
  wf_typ E T ->
  wf_typ E (normal_form_typing T).
Proof with eauto; try repeat fold merge_mutability;
  try repeat fold normal_form_typing.
  intros * Wf.
  induction Wf; simpl...
  - apply wf_typ_all with (L := L)...
    intros X Fr.
    rewrite <- normal_form_open_tt...
    rewrite_env (empty ++ X ~ bind_sub (normal_form_typing T1) ++ E).
    eapply wf_typ_narrowing...
Qed.

#[export] Hint Resolve normal_form_wellformed : core.


(* ********************************************************************** *)
(** * #<a name="okt"></a># Properties of [wf_env] *)

(** These properties are analogous to the properties that we need to
    show for the subtyping and typing relations. *)

Lemma wf_env_narrowing : forall V E F U X,
  wf_env (F ++ X ~ bind_sub V ++ E) ->
  wf_typ E U ->
  wf_env (F ++ X ~ bind_sub U ++ E).
Proof with eauto using wf_typ_narrowing.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_strengthening : forall x T E F,
  wf_env (F ++ x ~ bind_typ T ++ E) ->
  wf_env (F ++ E).
Proof with eauto using wf_typ_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_subst_tb : forall Q Z P E F,
  wf_env (F ++ Z ~ bind_sub Q ++ E) ->
  wf_typ E P ->
  wf_env (map (subst_tb Z P) F ++ E).
Proof with eauto 6 using wf_typ_subst_tb.
  induction F; intros Wf_env WP; simpl_env;
    inversion Wf_env; simpl_env in *; simpl subst_tb...
Qed.

Lemma wf_sig_weakening : forall R E F G,
  wf_sig (G ++ E) R ->
  wf_env (G ++ F ++ E) ->
  wf_sig (G ++ F ++ E) R.
Proof with eauto using wf_typ_weakening.
  intros T E F G Hwf_sig Hk.
  remember (G ++ E) as F'.
  generalize dependent G.
  induction Hwf_sig; intros G Hok Heq; subst...
Qed.

Lemma wf_sig_weaken_head: forall R E F,
  wf_sig E R ->
  wf_env (F ++ E) ->
  wf_sig (F ++ E) R.
Proof with eauto using wf_sig_weakening.
  intros...
  rewrite_sig (empty ++ F ++ E)...
Qed.

Lemma wf_sig_narrowing : forall V E F U X R,
  wf_sig (F ++ X ~ bind_sub V ++ E) R ->
  wf_typ E U ->
  wf_sig (F ++ X ~ bind_sub U ++ E) R.
Proof with eauto using wf_typ_narrowing, wf_env_narrowing.
  intros V E F U X R WfSig WfTyp.
  dependent induction WfSig...
Qed.

Lemma wf_sig_strengthening : forall x T E F R,
  wf_sig (F ++ x ~ bind_typ T ++ E) R ->
  wf_sig (F ++ E) R.
Proof with eauto using wf_typ_strengthening, wf_env_strengthening.
  intros x T E F R WfSig.
  dependent induction WfSig...
Qed.

Lemma wf_sig_weaken_head_map : forall E f (F : env) R,
  wf_sig E R ->
  wf_env ((map f F) ++ E) ->
  wf_sig ((map f F) ++ E) R.
Proof.
  intros * Wf ?.
  rewrite_env (empty ++ map f F ++ E).
  apply wf_sig_weakening; simpl_env; eauto.
Qed.

(* ********************************************************************** *)
(** * #<a name="subst"></a># Environment is unchanged by substitution for a fresh name *)

Lemma notin_fv_tt_open : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_tt T.
Proof.
 intros Y X T. unfold open_tt.
 generalize 0.
 induction T; simpl; intros k Fr; eauto.
Qed.

Lemma notin_fv_wf : forall E (X : atom) T,
  wf_typ E T ->
  X `notin` dom E ->
  X `notin` fv_tt T.
Proof with auto.
  intros E X T Wf_typ.
  induction Wf_typ; intros Fr; simpl...
  Case "wf_typ_var".
    assert (X0 `in` (dom E))...
    eapply binds_In; eauto.
    assert (X <> X0) by fsetdec. fsetdec.
  Case "wf_typ_all".
    apply notin_union...
    pick fresh Y.
    apply (notin_fv_tt_open Y)...
Qed.

Lemma map_subst_tb_id : forall G Z P,
  wf_env G ->
  Z `notin` dom G ->
  G = map (subst_tb Z P) G.
Proof with auto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf; eauto.
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf; eauto.
Qed.


(* ********************************************************************** *)
(** * #<a name="regularity"></a># Regularity of relations *)

Lemma sub_regular : forall E S T,
  sub E S T ->
  wf_env E /\ wf_typ E S /\ wf_typ E T.
Proof with simpl_env; try solve [auto | intuition auto].
  intros E S T H.
  induction H...
  Case "sub_trans_tvar".
    intuition eauto.
  Case "sub_all".
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh Y and apply wf_typ_all...
      destruct (H1 Y)...
      rewrite_env (empty ++ Y ~ bind_sub S1 ++ E).
      apply (wf_typ_narrowing T1)...
    SCase "Third of original three conjuncts".
      pick fresh Y and apply wf_typ_all...
      destruct (H1 Y)...
Qed.

Lemma typing_regular : forall E R e T,
  typing E R e T ->
  wf_env E /\ wf_sig E R /\ expr e /\ wf_typ E T
with typing_record_regular : forall E R r T,
  typing_record_comp E R r T ->
  wf_env E /\ wf_sig E R /\ record_comp r /\ wf_typ E T.
Proof with simpl_env; try solve [auto | intuition auto].
------
  clear typing_regular.
  intros E R e T H; induction H...
  Case "typing_var".
    repeat split...
    eauto using wf_typ_from_binds_typ.
  Case "typing_abs".
    pick fresh y.
    destruct (H1 y) as [Hok [HokR [J K]]]...
    repeat split. inversion Hok... assumption.
    SCase "Second of original three conjuncts".
      pick fresh x and apply expr_abs.
        eauto using type_from_wf_typ, wf_typ_from_wf_env_typ.
        destruct (H1 x)...
    SCase "Third of original three conjuncts".
      apply wf_typ_arrow; eauto using wf_typ_from_wf_env_typ.
      rewrite_env (empty ++ E).
      eapply wf_typ_strengthening; simpl_env; eauto.
  Case "typing_app".
    repeat split...
    destruct IHtyping1 as [_ [_ [_ K]]].
    inversion K...
  Case "typing_tabs".
    pick fresh Y.
    destruct (H1 Y) as [Hok [HokR [J K]]]...
    inversion Hok; subst.
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh X and apply expr_tabs.
        eauto using type_from_wf_typ, wf_typ_from_wf_env_sub...
        destruct (H1 X)...
    SCase "Third of original three conjuncts".
      pick fresh Z and apply wf_typ_all...
      destruct (H1 Z)...
  Case "typing_tapp".
    destruct (sub_regular _ _ _ H1) as [R1 [R2 R3]].
    repeat split...
    SCase "Second of original three conjuncts".
      apply expr_tapp...
      eauto using type_from_wf_typ.
    SCase "Third of original three conjuncts".
      destruct IHtyping as [R1' [R2' [R3' R4']]].
      eapply wf_typ_open; eauto.
  Case "typing_sub".
    repeat split...
    destruct (sub_regular _ _ _ H1)...
  Case "typing_let".
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh y and apply expr_let...
      destruct (H2 y) as [K1 [K2 [K3 K4]]]...
    SCase "Third of original three conjuncts".
      pick fresh y.
      destruct (H2 y) as [K1 [K2 [K3 K4]]]...
      rewrite_env (empty ++ E).
      eapply wf_typ_strengthening; simpl_env; eauto.
  Case "typing_ref".
    repeat split...
    eapply wf_box_typ_from_binds_sig with (x := l) (R := R)...
  Case "typing_record".
    destruct (typing_record_regular _ _ _ _ H)...
  Case "typing_record_read".
    repeat split...
    eapply wf_typ_from_wf_typ_record with (a := a)...
  Case "typing_record_read_readonly".
    repeat split...
    econstructor...
    eapply wf_typ_from_wf_typ_readonly_record with (a := a)...
------
  clear typing_record_regular.
  intros E R r T H; induction H...
  Case "typing_record_exp".
    destruct IHtyping_record_comp as [? [? [? ?]]]...
    unshelve epose proof (typing_regular E R e T _)...
  Case "typing_record_ref".
    destruct IHtyping_record_comp as [? [? [? ?]]]...
    unshelve epose proof (wf_typ_from_binds_sig l T E R _ _)...
Qed.

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
  Case "red_tabs".
    split... split... inversion H0. pick fresh Y. rewrite (subst_te_intro Y)...
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
  | H: sub _ _ _ |- _ => apply (proj1 (sub_regular _ _ _ H))
  | H: typing _ _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ _ H))
  | H: typing_record_comp _ _ _ _ |- _ => apply (proj1 (typing_record_regular _ _ _ _ H))
  | H: wf_sig _ _ |- _ => apply (wf_sig_regular _ _ H)
  end : core.

#[export] Hint Extern 1 (wf_sig ?E ?R) =>
  match goal with
  | H: typing _ _ _ _ |- _ => apply (proj1 (proj2 (typing_regular _ _ _ _ H)))
  | H: typing_record_comp _ _ _ _ |- _ => apply (proj1 (proj2 (typing_record_regular _ _ _ _ H)))
  end : core.

#[export] Hint Extern 1 (wf_typ ?E ?T) =>
  match goal with
  | H: typing E _ _ T |- _ => apply (proj2 (proj2 (proj2 (typing_regular _ _ _ _ H))))
  | H: typing_record_comp E _ _ T |- _ => apply (proj2 (proj2 (proj2 (typing_record_regular _ _ _ _ H))))
  | H: sub E T _ |- _ => apply (proj1 (proj2 (sub_regular _ _ _ H)))
  | H: sub E _ T |- _ => apply (proj2 (proj2 (sub_regular _ _ _ H)))
  end : core.

#[export] Hint Extern 1 (type ?T) =>
  let go E := apply (type_from_wf_typ E); auto in
  match goal with
  | H: typing ?E _ _ T |- _ => go E
  | H: typing_record ?E _ _ T |- _ => go E
  | H: sub ?E T _ |- _ => go E
  | H: sub ?E _ T |- _ => go E
  | H: wf_typ ?E T |- _  => go E
  end : core.

#[export] Hint Extern 1 (expr ?e) =>
  match goal with
  | H: typing _ _ ?e _ |- _ => apply (proj1 (proj2 (proj2 (typing_regular _ _ _ _ H))))
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
  | H: typing_record_comp _ _ ?e _ |- _ => apply (proj1 (proj2 (proj2 (typing_record_regular _ _ _ _ H))))
  | H: red_record_comp ?e _ _ _ |- _ => apply (proj1 (red_record_comp_regular _ _ _ _ H))
  | H: red_record_comp _ _ ?e _ |- _ => apply (proj1 (proj2 (proj2 (red_record_comp_regular _ _ _ _ H))))
  end : core.

#[export] Hint Extern 1 (wf_typ ?E ?T) =>
  match goal with
  | H: sub E (typ_mut _ T) _ |- _ => 
    apply (wf_typ_from_wf_mut_typ _ _ _ 
    (proj1 (sub_regular _ _ _ H)) (proj1 (proj2 (sub_regular _ _ _ H))))
  | H: sub E _ (typ_mut _ T) |- _ => 
    apply (wf_typ_from_wf_mut_typ _ _ _ 
    (proj1 (sub_regular _ _ _ H)) (proj2 (proj2 (sub_regular _ _ _ H))))
end : core.

#[export] Hint Resolve expr_multistep well_formed_store_multistep : core.
