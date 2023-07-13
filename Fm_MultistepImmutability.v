(** Multi-step immutability lemmas

    Authors: Edward Lee, Ondrej Lhotak

    This work is based off the POPL'08 Coq tutorial
    authored by: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    This file contains the main proofs concerning results around
    multi-step immutability -- namely, when if a term is well-typed,
    subterms which are typed readonly can be sealed to no ill effect.
*)
Require Export Fsub.Fm_Immutability.

Definition lt_seal_count (e : exp) (f: exp) := (seal_count e) < (seal_count f).
Lemma lt_seal_count_wf : well_founded lt_seal_count.
Proof with eauto.
  apply well_founded_ltof.
Qed.

Definition safety_valuem_stmt (e : exp) (s : store) (f : exp) := forall ns R T,
  sealcomp_store s ns ->
  sealcomp e f ->
  value e ->
  typing_store empty R ns ->
  typing empty R f T ->
  exists f' ns', sealcomp e f' /\ sealcomp_store s ns' /\ value f' /\
    redm f ns f' ns'.

Lemma safety_valuem (e : exp) (s : store) (f : exp): safety_valuem_stmt e s f.
Proof with eauto.
  unshelve epose proof (Fix lt_seal_count_wf
    (safety_valuem_stmt e s)) as Ind.
  apply Ind. clear f.
  intros f IndProp.
  unfold lt_seal_count in *.
  unfold safety_valuem_stmt.
  intros...
  unshelve epose proof (progress f ns R T _ _)
    as [Value | [f' [ns' Redf]]]...
  - exists f. exists ns...
  - unshelve epose proof (safety_value e s f ns f' ns' _ _ _ _)
      as [StoreComp [SealComp WellFounded]]...
    unshelve epose proof 
      (preservation empty R f ns f' ns' T _ _ _)
      as [R' [WfSig [Typ' STyp']]]...
    edestruct IndProp with (y := f')
      as [f'' [ns'' [SealComp'' [StoreComp'' [ValueF'' Redf'']]]]]...
    exists f''. exists ns''...
Qed.

Definition safety_stepm_stmt (e : exp) (s : store) (e' : exp) (s' : store) (f : exp) := forall ns R T,
  sealcomp_store s ns ->
  sealcomp e f ->
  red e s e' s' ->
  typing_store empty R ns ->
  typing empty R f T ->
  exists f' ns', sealcomp e' f' /\ sealcomp_store s' ns' /\
    redm f ns f' ns'.

Lemma safety_stepm (e : exp) (s : store) (e': exp) (s': store) (f : exp): safety_stepm_stmt e s e' s' f.
Proof with eauto.
  unshelve epose proof (Fix lt_seal_count_wf
    (safety_stepm_stmt e s e' s')) as Ind.
  apply Ind. clear f.
  intros f IndProp.
  unfold lt_seal_count in *.
  unfold safety_stepm_stmt.
  intros.
  unshelve epose proof (progress f ns R T _ _)
    as [Value | [f' [ns' Redf]]]...
  + exfalso. eapply irreducible_value with (e := e)...
    eapply sealcomp_value with (f := f)...
  + unshelve epose proof (safety_step e s e' s' f ns f' ns' _ _ _ _)
      as [[SealS' [Seal' Wf]] | [SealS' Seal']]...
    - unshelve epose proof 
        (preservation empty R f ns f' ns' T _ _ _)
        as [R' [WfSig [Typ' STyp']]]...
      destruct (IndProp f' Wf ns' (R' ++ R) T)
        as [f'' [ns'' [Seal'' [SealS'' Redm]]]]...
      exists f''. exists ns''. repeat (split; eauto).
    - exists f'. exists ns'. repeat (split; eauto).
Qed.

Lemma preservation_multistep : forall E R e s e' s' T,
  typing E R e T ->
  typing_store E R s ->
  redm e s e' s' ->
  exists R', wf_sig E (R' ++ R) /\ 
    typing E (R' ++ R) e' T /\
    typing_store E (R' ++ R) s'.
Proof with eauto.
  intros * Typ TypS RedM.
  generalize dependent R.
  induction RedM; intros; subst...
  + exists sempty...
  + unshelve epose proof (preservation E R e s e'' s'' T _ _ _)
      as [R'' [WfSigR'' [TypE'' WfStore'']]]...
    unshelve epose proof (IHRedM (R'' ++ R) _ _)
      as [R' ?]...
    exists (R' ++ R''); simpl_env in *...
Qed.

Lemma multistep_trans : forall e e' e'' s s' s'',
  redm e s e' s' ->
  redm e' s' e'' s'' ->
  redm e s e'' s''.
Proof with auto.
  intros.
  induction H; subst...
  eapply redm_step... assumption.
Qed.

(** Lemma 5.8 *)
Lemma safety_multistep : forall e s e' s' f ns R T,
  sealcomp_store s ns ->
  sealcomp e f ->
  redm e s e' s' ->
  typing_store empty R ns ->
  typing empty R f T -> 
  exists f' ns', sealcomp e' f' /\ sealcomp_store s' ns' /\ redm f ns f' ns'.
Proof with eauto.
  intros * StoreComp SealComp Redem TypNS TypF.
  generalize dependent ns. generalize dependent f. generalize dependent R.   
  dependent induction Redem; subst...
  + intros. exists f. exists ns. split...
  + intros.
    unshelve epose proof (safety_stepm e s e'' s'' f ns R T _ _ _ _ _)
      as [f'' [ns'' [Seal'' [StoreComp'' Redf'']]]]...
    unshelve epose proof (preservation_multistep _ R f ns _ _ _ _ _ Redf'')
      as [R'' [WfSig'' [Typf'' WfStoreNS'']]]...
    destruct IHRedem with (f := f'') (ns := ns'')
      (R := R'' ++ R) as [f' [ns' [eLf [s'Lns' Redf''m]]]]...
    exists f'. exists ns'. split... split...
    eapply multistep_trans...
Qed.

(** Lemma 5.9 *)
Lemma safety_value_multistep : forall e s e' s' f ns R T,
  sealcomp_store s ns ->
  sealcomp e f ->
  redm e s e' s' ->
  value e' ->
  typing_store empty R ns ->
  typing empty R f T -> 
  exists f' ns', sealcomp e' f' /\ sealcomp_store s' ns' /\ value f' /\ redm f ns f' ns'.
Proof with eauto.
  intros * StoreComp SealComp Redem TypNS TypF.
  generalize dependent ns. generalize dependent f. generalize dependent R.   
  dependent induction Redem; subst...
  + intros.
    unshelve epose proof (safety_valuem e' s' f ns R T _ _ _ _ _)
      as [f' [ns' [e'Lf [s'Lns' [ValueF' Redf']]]]]...
    exists f'. exists ns'...
  + intros.
    unshelve epose proof (safety_stepm e s e'' s'' f ns R T _ _ _ _ _)
      as [f'' [ns'' [Seal'' [StoreComp'' Redf'']]]]...
    unshelve epose proof (preservation_multistep _ R f ns _ _ _ _ _ Redf'')
      as [R'' [WfSig'' [Typf'' WfStoreNS'']]]...
    destruct IHRedem with (f := f'') (ns := ns'')
      (R := R'' ++ R) as [f' [ns' [eLf [s'Lns' [Valuef Redf''m]]]]]...
    exists f'. exists ns'. split... split... split...
    eapply multistep_trans...
Qed.

Inductive redm_monotone_component : exp -> store -> exp -> store -> Prop :=
  | redm_monotone_component_eq : forall e s,
    redm_monotone_component e s e s
  | redm_monotone_component_step : forall e s e'' s'' e' s', 
    red e s e'' s'' ->
    seal_count e'' < seal_count e ->
    redm_monotone_component e'' s'' e' s' ->
    redm_monotone_component e s e' s'.

Inductive redm_monotone : exp -> store -> exp -> store -> Prop :=
  | redm_monotone_step : forall e s e' s',
    redm_monotone_component e s e' s' ->
    redm_monotone e s e' s'
  | redm_monotone_jump : forall e s e' s' e'' s'' e''' s''', 
    redm_monotone_component e s e' s' ->
    red e' s' e'' s'' ->
    not (seal_count e'' < seal_count e') ->
    redm_monotone e'' s'' e''' s''' ->
    redm_monotone e s e''' s'''.

Notation "< e1 | s1 > -->M* < e1' | s1' >" := (redm_monotone e1 s1 e1' s1') (at level 69).
Notation "< e1 | s1 > -->C* < e1' | s1' >" := (redm_monotone_component e1 s1 e1' s1') (at level 69).

#[export] Hint Constructors  redm_monotone_component redm_monotone : core.

Lemma redm_to_monotone : forall e s e' s',
  redm e s e' s' -> redm_monotone e s e' s'.
Proof with eauto.
  intros.
  induction H; subst...
  unshelve epose proof (lt_dec (seal_count e'') (seal_count e)) as [LeSeal | NLeSeal]...
  + destruct IHredm; subst...
Qed.

Definition safety_component_stepm'_stmt (f : exp) := forall e s ns f' ns',
  expr e ->
  well_formed_store s ->
  sealcomp_store s ns ->
  sealcomp e f ->
  redm_monotone_component f ns f' ns' ->
  (exists e' s', redm e s e' s' /\ sealcomp_store s' ns' /\ sealcomp e' f').
Lemma safety_component_step' (f : exp) : safety_component_stepm'_stmt f.
Proof with eauto.
  intros.
  unshelve epose proof (Fix lt_seal_count_wf
    (safety_component_stepm'_stmt)) as Ind.
  apply Ind. clear f.
  intros f IndProp.
  unfold lt_seal_count in *.
  unfold safety_component_stepm'_stmt.
  intros * Expr WfStore StoreComp SealComp Redf_Mono.
  destruct Redf_Mono; subst...
  + exists e. exists s...
  + unshelve epose proof (safety_step' e s e0 s0 e'' s'' _ _ _ _ _)
    as [[StoreComp'' [SealComp'' WellFounded]]|
      [e''' [s''' [Rede''' [StoreComp''' SealComp''']]]]]...
    * eapply (IndProp e'')...
    * edestruct (IndProp e'') with (e := e''') (s := s''') (ns := s'') (f' := e')
        as [e'''' [s'''' [Rede'''' [StoreComp'''' SealComp'''']]]]...
      exists e''''. exists s''''...
Qed.

Lemma safety_multistep' : forall e s f ns f' ns',
  expr e ->
  well_formed_store s ->
  sealcomp_store s ns ->
  sealcomp e f ->
  redm f ns f' ns' ->
  (exists e' s', redm e s e' s' /\ sealcomp_store s' ns' /\ sealcomp e' f').
Proof with eauto using safety_component_step'.
  intros * Expr WfS StoreComp SealComp Redf_Monotone.
  apply redm_to_monotone in Redf_Monotone.
  generalize dependent s. generalize dependent e.
  induction Redf_Monotone; intros...
  * eapply safety_component_step'...
  * eapply safety_component_step' in H as 
      [g [t [StepsG [StoreCompG SealCompG]]]]...
    unshelve epose proof (safety_step' g t e' s' e'' s'' _ _ _ _ _)
      (** admits here are regularity lemmas *)
      as [[? [? Bad]] | [g'' [t'' [Redg'' [StoreCompG'' SealCompG'']]]]]...
    - intuition.
    - unshelve epose proof (IHRedf_Monotone g'' _ _ t'' _ _)
        as [g''' [t''' [RedG''' [StoreCompG''' SealCompG''']]]]...
      exists g'''. exists t'''. split...
      eapply multistep_trans with (e' := g) (s' := t)...
Qed.

(** Lemma 5.12 *)
Lemma safety_value_multistep' : forall e s f ns f' ns',
  expr f ->
  expr e ->
  well_formed_store s ->
  sealcomp_store s ns ->
  sealcomp e f ->
  redm f ns f' ns' ->
  value f' ->
  (exists e' s', redm e s e' s' /\ sealcomp_store s' ns' /\ sealcomp e' f' /\ value e').
Proof with eauto using safety_component_step'.
  intros * Expr WfS StoreComp SealComp Redf_Monotone ValueF.
  edestruct (safety_multistep') with (e := e) (s := s) (ns := ns) (f := f) (f' := f') (ns' := ns')
    as [e' [s' ?]]; intuition...
  exists e'. exists s'... intuition.
  eapply sealcomp_value with (f := f')...
Qed.

Lemma sealcomp_rec_comp_same_dom : forall r1 r2,
  sealcomp_rec_comp r1 r2 ->
  record_dom r1 [=] record_dom r2.
Proof with eauto.
  intros.
  induction H; simpl; fsetdec.
Qed.

Lemma sealcomp_typed : forall E R e f T,
  typing E R f T ->
  sealcomp e f ->
  typing E R e T
with sealcomp_typed_record : forall E R e f T,
  typing_record_comp E R f T ->
  sealcomp_rec_comp e f ->
  typing_record_comp E R e T.
Proof with eauto.
------
  clear sealcomp_typed.
  intros.
  generalize dependent e.
  dependent induction H; intros;
    inversion select (sealcomp _ _); subst...
  - eapply typing_abs with (L := L)...
  - eapply typing_tabs with (L := L)...
  - eapply typing_let with (L := L)...
  - eapply typing_sub with (S := T); auto.
    eapply sub_readonly_mutable.
    eapply sub_reflexivity...
------
  clear sealcomp_typed_record.
  intros.
  generalize dependent e.
  dependent induction H; intros;
    inversion select (sealcomp_rec_comp _ _); subst...
  - eapply typing_record_exp...
    rewrite sealcomp_rec_comp_same_dom...
  - eapply typing_record_ref...
    rewrite sealcomp_rec_comp_same_dom...
Qed.


Lemma storecomp_typed : forall E R s s',
  well_formed_store s' ->
  typing_store E R s ->
  sealcomp_store s' s ->
  typing_store E R s'.
Proof with eauto.
  intros * Wf Typ Seal.
  unfold typing_store, well_formed_store in *.
  inversion Seal; constructor.
  * intros T Binds.
    unshelve epose proof ((proj1 (Typ l)) T Binds)
      as [v [MapsS [TypV ValueV]]].
    unshelve epose proof (H0 l v MapsS)
      as [v' [MapsV' CompV']]...
    unshelve epose proof (Wf l v' _)...
    exists v'; intuition...
    eapply sealcomp_typed...
  * intros v' MapsS'.
    unshelve epose proof (H l v' MapsS')
      as [v [MapsS CompS]]...
    unshelve epose proof ((proj2 (Typ l)) v MapsS)
      as [T [ValueV [TypT BindsL]]]...
    exists T; intuition...
    eapply sealcomp_typed...
Qed.


(** Lemma 5.13 *)
Lemma typed_safety_value_multistep' : forall e s f ns f' ns' E R T,
  expr f ->
  expr e ->
  well_formed_store s ->
  sealcomp_store s ns ->
  sealcomp e f ->
  redm f ns f' ns' ->
  value f' ->
  typing E R f T ->
  typing_store E R ns ->
  typing E R e T /\ 
    (exists e' s' R', redm e s e' s' /\ sealcomp_store s' ns' /\ sealcomp e' f' /\ value e' /\ typing E (R' ++ R) e' T).
Proof with eauto using safety_component_step'.
  intros * ExprF ExprE WfS StoreComp SealComp Redf_Monotone ValueF TypingF TypingNS.
  split...
  - eapply sealcomp_typed...
  - unshelve epose proof (safety_value_multistep' e s f ns f' ns' _ _ _ _ _ _ _)
      as [e' [s' [RedE [CompS [CompE ValueE]]]]]...
    unshelve epose proof (preservation_multistep E R e s e' s' T _ _ _)
      as [R' [WfR' [TypingE' TypingS']]]...
      eapply sealcomp_typed...
      eapply storecomp_typed...

    exists e'. exists s'. exists (R'). intuition.
Qed.
