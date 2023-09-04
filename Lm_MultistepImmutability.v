(** Multi-step immutability lemmas

    Authors: Edward Lee, Ondrej Lhotak

    This work is based off the POPL'08 Coq tutorial
    authored by: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    This file contains the main proofs concerning results around
    multi-step immutability -- namely, when if a term is well-typed,
    subterms which are typed readonly can be sealed to no ill effect.

    - #<a href="##lemma_3.8">Lemma 3.8</a>#
*)

Require Export Fsub.Lm_Immutability.
Definition lt_seal_count (e : exp) (f: exp) := (seal_count e) < (seal_count f).
Lemma lt_seal_count_wf : well_founded lt_seal_count.
Proof with eauto.
  apply well_founded_ltof.
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

(** Monotone reduction; here, we want to relate how reduction relates
    to the number of seals in each term.

    A reduction sequence can be broken up into segments (redm_monotone_component)
    where the seal count goes down; seal counts go up in betweeen segments (redm_monotone_jump).

    This is useful for the immutability equivalence proof as reductions which result in a jump
    in the sealed program must correspond to actual reduction steps in the original program.
*)
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
      as [[? [? Bad]] | [g'' [t'' [Redg'' [StoreCompG'' SealCompG'']]]]]...
    - intuition.
    - unshelve epose proof (IHRedf_Monotone g'' _ _ t'' _ _)
        as [g''' [t''' [RedG''' [StoreCompG''' SealCompG''']]]]...
      exists g'''. exists t'''. split...
      eapply multistep_trans with (e' := g) (s' := t)...
Qed.

(** #<a name="lemma_3.8"># Lemma 3.8 *)
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
