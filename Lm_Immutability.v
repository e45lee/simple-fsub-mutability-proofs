(** Lemmas on re-sealing and typing and single-step immutability safety

    Authors: Edward Lee, Ondrej Lhotak

    This work is based off the POPL'08 Coq tutorial
    authored by: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    This file contains the main proofs concerning results around
    immutability -- namely, when if a term is well-typed,
    subterms which are typed readonly can be sealed to no ill effect.
*)
Require Export Fsub.Lm_Lemmas.

(**
  We need a notion of store consistency to prove that reduction
  takes the same steps; all locations must be the same even
  if they do not store the same values.
*)
Definition consistent_store (s s' : store) :=
  forall l, (LabelMapImpl.In l s) <-> (LabelMapImpl.In l s').

Lemma consistent_store_symmetric : forall s s',
  consistent_store s s' <-> consistent_store s' s.
Proof with eauto.
  intros. unfold consistent_store... intuition;
    destruct (H l)...
Qed.

#[export] Hint Resolve consistent_store_symmetric : core.

(**
  ...as we need to show that after reduction if two stores
  were consistent they still are consistent as the
  fresh label generated for both was the same label.
  *)
Lemma consistent_fresh_label_for_store : forall s ns,
  consistent_store s ns ->
  fresh_label_for_store s = fresh_label_for_store ns.
Proof with eauto.
  intros * InEquiv; unfold consistent_store in InEquiv.
  assert (forall l, In l (List.map fst (LabelMapImpl.elements s)) <->
                    In l (List.map fst (LabelMapImpl.elements ns))) as Equiv.
  intros; repeat rewrite <- label_map_in_iff_keys in *...
  unfold fresh_label_for_store, exists_fresh_label_for_store; simpl.
  apply Label.fresh_permute...
Qed.


(* ********************************************************************** *)
(** * #<a name="sealcomp"></a># Properties of [sealcomp] *)

Lemma sealcomp_reflexive : forall e,
    sealcomp e e
with sealcomp_rec_comp_reflexive : forall r,
    sealcomp_rec_comp r r.
Proof with eauto.
------
    clear sealcomp_reflexive.
    induction e...
------
    clear sealcomp_rec_comp_reflexive.
    induction r...
Qed.
#[export] Hint Resolve sealcomp_reflexive : core.

Lemma sealcomp_transitive : forall e f g,
  sealcomp e f ->
  sealcomp f g ->
  sealcomp e g
with sealcomp_rec_comp_transitive : forall e f g,
  sealcomp_rec_comp e f ->
  sealcomp_rec_comp f g ->
  sealcomp_rec_comp e g.
Proof with eauto.
------
  clear sealcomp_transitive.
  intros * eLf fLg.
  dependent induction e; dependent induction f; dependent induction g;
    try solve [inversion eLf; inversion fLg; eauto 4].
  all : inversion fLg; subst; econstructor...
------
  clear sealcomp_rec_comp_transitive.
  intros * eLf fLg.
  dependent induction e; dependent induction f; dependent induction g;
    try solve [inversion eLf; inversion fLg; eauto 4].
Qed.

Lemma sealcomp_inversion : forall e f,
  sealcomp (exp_seal e) f ->
  sealcomp e f.
Proof with eauto.
  intros * Seal.
  dependent induction Seal...
Qed.
#[export] Hint Resolve sealcomp_inversion : core.


(* ********************************************************************** *)
(** * #<a name="sealcomp_open"></a># Properties of [sealcomp] under opening *)

Lemma sealcomp_open_ee_rec : forall k e1 e2 v1 v2,
  sealcomp e1 e2 ->
  sealcomp v1 v2 ->
  sealcomp (open_ee_rec k v1 e1) (open_ee_rec k v2 e2)
with sealcomp_rec_comp_open_ee_rec : forall k e1 e2 v1 v2,
  sealcomp_rec_comp e1 e2 ->
  sealcomp v1 v2 ->
  sealcomp_rec_comp (open_ee_record_rec k v1 e1) (open_ee_record_rec k v2 e2).
Proof with eauto.
------
  clear sealcomp_open_ee_rec.
  intros * e1Le2 v1Lv2.
  generalize dependent k.
  dependent induction e1Le2; intros; simpl...
  + destruct (k == n)...
------
  clear sealcomp_rec_comp_open_ee_rec.
  intros * e1Le2 v1Lv2.
  generalize dependent k.
  dependent induction e1Le2; intros...
  + econstructor...
  + econstructor...
Qed.
#[export] Hint Resolve sealcomp_open_ee_rec : core.

Lemma sealcomp_open_ee : forall e1 e2 v1 v2,
  sealcomp e1 e2 ->
  sealcomp v1 v2 ->
  sealcomp (open_ee e1 v1) (open_ee e2 v2).
Proof with eauto.
  intros... apply sealcomp_open_ee_rec...
Qed.
#[export] Hint Resolve sealcomp_open_ee : core.


(* ********************************************************************** *)
(** * #<a name="sealcomp_store"></a># Properties of [sealcomp_store] *)

Lemma sealcomp_store_reflexive : forall s,
    sealcomp_store s s.
Proof with eauto.
    intros. split...
Qed.
#[export] Hint Resolve sealcomp_store_reflexive : core.

Lemma sealcomp_store_transitive : forall s t u,
    sealcomp_store s t ->
    sealcomp_store t u ->
    sealcomp_store s u.
Proof with eauto using sealcomp_transitive.
  intros * sLt tLu.
  destruct sLt. destruct tLu.
  split; intros...
  + destruct (H l v) as [x [Maps Seal]]...
    destruct (H1 l x)  as [x2 [Maps2 Seal2]]...
  + destruct (H2 l v') as [x [Maps Seal]]...
    destruct (H0 l x)  as [x2 [Maps2 Seal2]]...
Qed.

Lemma sealcomp_stores_are_consistent : forall s s',
  sealcomp_store s s' ->
  consistent_store s s'.
Proof with eauto.
  intros.
  inversion H; subst...
  split; intros In...
  + destruct In as [v Maps].
    destruct (H0 l v) as [v' [Maps' Less]]...
    eexists v'...
  + destruct In as [v Maps].
    destruct (H1 l v) as [v' [Maps' Less]]...
    eexists v'...
Qed.

#[export] Hint Resolve sealcomp_stores_are_consistent : core.

Lemma sealcomp_store_after_add : forall l s s' v v',
  sealcomp_store s s' ->
  sealcomp v v' ->
  sealcomp_store (LabelMapImpl.add l v s) (LabelMapImpl.add l v' s').
Proof with eauto.
  intros * sLs' vLv'.
  split; intros l1 v1 MapsTo; 
    rewrite LabelMapFacts.add_mapsto_iff in *;
    destruct MapsTo as [[EqL EqV] | [NeqL MapsTo']]; subst...
  + exists v'... split...
    LabelMapFacts.map_iff...
  + destruct sLs' as [Left Right]...
    destruct (Left l1 v1) as [v1' [Maps v1Lv1']]...
    exists v1'... split...
    LabelMapFacts.map_iff; right; split...
  + exists v... split...
    LabelMapFacts.map_iff...
  + destruct sLs' as [Left Right]...
    destruct (Right l1 v1) as [v1' [Maps v1Lv1']]...
    exists v1'... split...
    LabelMapFacts.map_iff; right; split...
Qed.
#[export] Hint Resolve sealcomp_store_after_add : core.


(* ********************************************************************** *)
(** * #<a name="sealed_records"></a># Properties of [rec_comp]s that are sealed *)

Lemma sealcomp_record_consistent : forall r r' x res,
  sealcomp_rec_comp r r' ->
  record_lookup_ref x r = res ->
  record_lookup_ref x r' = res.
Proof with eauto.
  intros * rLr' Eq.
  dependent induction rLr'...
  simpl in *; destruct (x == a)...
Qed.

Lemma sealcomp_record_consistent_lt : forall r r' x res,
  sealcomp_rec_comp r' r ->
  record_lookup_ref x r = res ->
  record_lookup_ref x r' = res.
Proof with eauto.
  intros * rLr' Eq.
  dependent induction rLr'...
  simpl in *; destruct (x == a)...
Qed.

(* ********************************************************************** *)
(** * #<a name="sealed_values"></a># Properties of [value]s that are sealed *)

Lemma irreducible_value : forall e s f s',
  value e ->
  ~ red e s f s'
with irreducible_record_value : forall e s f s',
  value_record_comp e ->
  ~ red_record_comp e s f s'.
Proof with eauto.
------
  clear irreducible_value.
  intros * Val Rede.
  inversion Rede; subst; inversion Val; subst...
  + inversion Rede; subst...
    inversion H3; subst...
  + inversion H; subst...
    eapply irreducible_record_value...
  + eapply irreducible_record_value...
------
  clear irreducible_record_value.
  intros * Val Rede.
  induction Rede; subst; inversion Val; subst;
      try solve [inversion Rede; eauto]...
Qed.

Lemma sealcomp_value : forall e f,
  expr e ->
  expr f ->
  sealcomp e f ->
  value f ->
  value e
with sealcomp_rec_comp_value : forall e f,
  record_comp e ->
  record_comp f ->
  sealcomp_rec_comp e f ->
  value_record_comp f ->
  value_record_comp e.
Proof with eauto.
------
  clear sealcomp_value.
  intros * Expe Expf Seal Value.
  induction Seal; inversion Value; subst...
  + inversion Seal...
  + inversion Seal; subst...
    econstructor...
    eapply sealcomp_rec_comp_value with (f := r)...
    inversion Expe; subst. inversion H1; subst...
  + econstructor...
    eapply sealcomp_rec_comp_value with (f := r2)...
    inversion Expe...
------
  clear sealcomp_rec_comp_value.
  intros * Expe Expf Seal Value.
  induction Seal; inversion Value; subst...
  econstructor...
  apply IHSeal... inversion Expe...
Qed.

(* ********************************************************************** *)
(** * #<a name="safety_value"></a># Reduction when equivalent modulo sealing to a value *)

Lemma safety_value : forall e s f ns f' ns',
  sealcomp_store s ns ->
  sealcomp e f ->
  value e ->
  red f ns f' ns' ->
  sealcomp_store s ns' /\ sealcomp e f' /\ (seal_count f') < (seal_count f)
with safety_record_value : forall e s f ns f' ns',
  sealcomp_store s ns ->
  sealcomp_rec_comp e f ->
  value_record_comp e ->
  red_record_comp f ns f' ns' ->
  sealcomp_store s ns' /\ sealcomp_rec_comp e f' /\ (seal_count_record f') < (seal_count_record f).
Proof with eauto; try solve [simpl; intuition].
------
  clear safety_value.
  intros *  sLns eLf Vale.
  generalize dependent ns'.
  generalize dependent f'.
  dependent induction eLf; intros; try solve [try inversion Vale; try inversion H; eauto].
  * inversion Vale; subst...
    + inversion H; subst; try solve [inversion eLf]...
      - edestruct IHeLf as [SSComp [SComp Count]]...
      - inversion eLf; repeat (split; eauto)...
      - inversion eLf; repeat (split; eauto)...
    + inversion H; subst; try solve [inversion eLf]...
      - edestruct IHeLf as [SSComp [SComp Count]]...
      - inversion eLf; repeat (split; eauto)...
      - inversion eLf; repeat (split; eauto)...
  * inversion H0; subst...  
    edestruct (safety_record_value) as [SSComp [SComp Count]]...
    inversion Vale...
  * inversion H; subst...
    edestruct IHeLf as [SSComp [SComp Count]]...
------
  clear safety_record_value.
  intros * sLns eLf Vale.
  generalize dependent ns'.
  generalize dependent f'.
  dependent induction eLf; intros; try solve [try inversion Vale; try inversion H; eauto].
  inversion Vale; subst...
  inversion H; subst; try solve [edestruct IHeLf as [SSComp [SComp Count]]; eauto]...
Qed.

(* ********************************************************************** *)
(** * #<a name="safety"></a># Reduction when equivalent modulo sealing *)

(** Lemma 3.6 / 5.3 *)
Lemma safety_step' : forall e s f ns f' ns',
  expr e ->
  well_formed_store s ->
  sealcomp_store s ns ->
  sealcomp e f ->
  red f ns f' ns' ->
  (sealcomp_store s ns' /\ sealcomp e f' /\ seal_count f' < seal_count f) \/ 
  (exists e' s', red e s e' s' /\ sealcomp_store s' ns' /\ sealcomp e' f')
with safety_record_step' : forall e s f ns f' ns',
  record_comp e ->
  well_formed_store s ->
  sealcomp_store s ns ->
  sealcomp_rec_comp e f ->
  red_record_comp f ns f' ns' ->
  (sealcomp_store s ns' /\ sealcomp_rec_comp e f' /\ seal_count_record f' < seal_count_record f) \/ 
  (exists e' s',  red_record_comp e s e' s'/\ sealcomp_store s' ns' /\ sealcomp_rec_comp e' f').
Proof with eauto; try solve [simpl; eauto; intuition].
------
  clear safety_step'.
  intros * ExprE WfS sLns eLf Redf.
  generalize dependent ns'.
  generalize dependent f'.
  dependent induction eLf; intros; try solve [try inversion Redf; eauto].
  Case "red_app". {
    inversion ExprE; inversion Redf; subst...
    + edestruct IHeLf1 with (ns' := ns') as [[SealS1 [Seal1 Count]] | [e' [s' [Rede [SealS2 Seal2]]]]]...
      right... exists (exp_app e' e2)... exists s'...
    + assert (expr (exp_app f1 f2)) as ExprF1F2... inversion ExprF1F2; subst...
      unshelve epose proof (sealcomp_value _ _ _ _ eLf1 _) as ValueE1...
      edestruct IHeLf2 with (ns' := ns') as [[SealS1 [Seal1 Count]] | [e' [s' [Rede [SealS2 Seal2]]]]]...
      right... exists (exp_app e1 e')... exists s'...
    + assert (expr (exp_app (exp_abs e4) f2)) as ExprF1F2... inversion ExprF1F2; subst...
      unshelve epose proof (sealcomp_value _ _ _ _ eLf1 _) as ValueE1...
      unshelve epose proof (sealcomp_value _ _ _ _ eLf2 _) as ValueE2...
      inversion ValueE1; inversion eLf1; subst; try discriminate...
      inversion select (exp_abs _ = exp_abs  _); subst...
      right... exists (open_ee e0 e2)... exists s...
  }
  Case "red_let". { 
    inversion ExprE; inversion Redf; subst...
    + edestruct IHeLf1 with (ns' := ns') as [[SealS1 [Seal1 Count]] | [e' [s' [Rede [SealS2 Seal2]]]]]...
      right... eexists... exists s'... split...
    + assert (expr (exp_let f1 f2)) as ExprF1F2... inversion ExprF1F2; subst...
      unshelve epose proof (sealcomp_value _ _ _ _ eLf1 _) as ValueE1...
      right... exists (open_ee e2 e1)... exists s... split...
  }
  Case "red_box". {
    inversion ExprE; inversion Redf; subst...
    + edestruct IHeLf with (ns' := ns') as [[SealS1 [Seal1 Count]] | [e' [s' [Rede [SealS2 Seal2]]]]]...
      right... eexists... eexists...
    + assert (expr (exp_box e2)) as ExprE2... inversion ExprE2...
      unshelve epose proof (sealcomp_value _ _ _ _ eLf _) as ValueE1...
      right... eexists. eexists. split...
      erewrite <- consistent_fresh_label_for_store...
      eapply consistent_store_symmetric.
      apply sealcomp_stores_are_consistent...
  }
  Case "red_unbox". {
    inversion ExprE; inversion Redf; subst...
    + edestruct IHeLf with (ns' := ns') as [[SealS1 [Seal1 Count]] | [e' [s' [Rede [SealS2 Seal2]]]]]...
      right... eexists... eexists...
    + inversion eLf; subst...
      right...
      destruct (sLns) as [Left Right]...
      destruct (Right l f') as [v' [MapS' e'Lv']]...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns' l f')) _) as R1...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff s l v')) _) as R2...
      exists v'. eexists...
    + inversion eLf; subst...
      * inversion select (_ <e= exp_ref _); subst...
        right...
        destruct (sLns) as [Left Right]...
        destruct (Right l v1) as [v' [MapS' e'Lv']]...
        unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns' l v1)) _) as R1...
        unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff s l v')) _) as R2...
        exists (exp_seal v'). eexists... split...
      * inversion select (_ <e= exp_ref _); subst...
        right...
        destruct (sLns) as [Left Right]...
        destruct (Right l v1) as [v' [MapS' e'Lv']]...
        unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns' l v1)) _) as R1...
        unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff s l v')) _) as R2...
        exists v'. eexists... split...
  }
  Case "red_set_box". {
    assert (expr (exp_set_box f1 f2)) as ExprF1F2...
    inversion ExprE; inversion ExprF1F2; subst...
    inversion Redf; subst...
    + edestruct IHeLf1 with (ns' := ns') as [[SealS1 [Seal1 Count]] | [e' [s' [Rede [SealS2 Seal2]]]]]...
      right... exists (exp_set_box e' e2). eexists...
    + edestruct IHeLf2 with (ns' := ns') as [[SealS1 [Seal1 Count]] | [e' [s' [Rede [SealS2 Seal2]]]]]...
      right... exists (exp_set_box e1 e'). eexists... split...
      constructor...
      eapply sealcomp_value with (f := f1)...
    + inversion eLf1; subst...
      right...
      destruct (sLns) as [Left Right]...
      destruct (Right l f') as [v' [MapS' e'Lv']]...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns l f')) _) as R1...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff s l v')) _) as R2...
      exists v'. exists (LabelMapImpl.add l e2 s)... split... constructor...
      eapply sealcomp_value with (f := f2)...
  }
  Case "red_seal". { 
    inversion ExprE; inversion Redf; subst...
    + edestruct IHeLf with (ns' := ns') as [[SealS1 [Seal1 Count]] | [e' [s' [Rede [SealS2 Seal2]]]]]...
      right... eexists. eexists. split...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf _ ) as ValueE1...
      inversion eLf; subst...
      right... eexists. eexists. split...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf _ ) as ValueE1...
      inversion eLf; subst...
      inversion select (_ <e= exp_ref _); subst.
      right...
      exists (exp_seal (exp_ref l))...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf _ ) as ValueE1...
      inversion eLf; subst...
      inversion select (_ <e= exp_record _); subst.
      right... eexists. eexists. split...
      inversion ValueE1; subst...
  }
  Case "red_record". {
    inversion ExprE; inversion Redf; subst...
    unshelve epose proof (safety_record_step' r1 s r2 ns r1' ns')
      as [[SealS1 [Seal1 Count]] | [e' [s' [Rede [SealS2 Seal2]]]]]...
    right... eexists. eexists...
  }
  Case "red_record_read". {
    inversion ExprE; inversion Redf; subst...
    + edestruct IHeLf with (ns' := ns') as [[SealS1 [Seal1 Count]] | [e' [s' [Rede [SealS2 Seal2]]]]]...
      right... eexists... eexists...
    + inversion eLf; subst...
      right...
      destruct (sLns) as [Left Right]...
      destruct (Right l f') as [v' [MapS' e'Lv']]...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns' l f')) _) as R1...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff s l v')) _) as R2...
      exists v'. eexists... split...
      eapply red_record_read_ref...
      eapply sealcomp_rec_comp_value with (f := r)...
        inversion select (expr (exp_record _))...
      eapply sealcomp_record_consistent_lt...
    + inversion eLf; subst...
      * inversion select (_ <e= exp_record _); subst...
        right...
        destruct (sLns) as [Left Right]...
        destruct (Right l v1) as [v' [MapS' e'Lv']]...
        unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns' l v1)) _) as R1...
        unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff s l v')) _) as R2...
        exists (exp_seal v'). eexists... split... 
        eapply red_sealed_record_read_ref...
        eapply sealcomp_rec_comp_value with (f := r)...
        inversion select (expr (exp_seal (exp_record _))); 
          inversion select (expr (exp_record _ )); subst...
        eapply sealcomp_record_consistent_lt...
      * inversion select (_ <e= exp_record _); subst...
        right...
        destruct (sLns) as [Left Right]...
        destruct (Right l v1) as [v' [MapS' e'Lv']]...
        unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns' l v1)) _) as R1...
        unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff s l v')) _) as R2...
        exists v'. eexists... split...
        eapply red_record_read_ref...
        eapply sealcomp_rec_comp_value with (f := r)...
        inversion select (expr (exp_record _))...
        eapply sealcomp_record_consistent_lt...
  }
  Case "red_record_write". {
    assert (expr (exp_record_write f1 x f2)) as ExprF1F2...
    inversion ExprE;
    inversion ExprF1F2; subst...
    inversion Redf; subst...
    + edestruct IHeLf1 with (ns' := ns') as [[SealS1 [Seal1 Count]] | [e' [s' [Rede [SealS2 Seal2]]]]]...
      right... exists (exp_record_write e' x e2). eexists...
    + edestruct IHeLf2 with (ns' := ns') as [[SealS1 [Seal1 Count]] | [e' [s' [Rede [SealS2 Seal2]]]]]...
      right... exists (exp_record_write e1 x e'). eexists... split... constructor...
      eapply sealcomp_value with (f := f1)...
    + inversion eLf1; subst...
      right...
      destruct (sLns) as [Left Right]...
      destruct (Right l f') as [v' [MapS' e'Lv']]...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns l f')) _) as R1...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff s l v')) _) as R2...
      exists v'. exists (LabelMapImpl.add l e2 s)... split... constructor...
      eapply sealcomp_rec_comp_value with (f := r)...
      inversion select (expr (exp_record r1))...
      eapply sealcomp_record_consistent_lt...
      eapply sealcomp_value with (f := f2)...
  }
  Case "red_seal". {
    inversion Redf; subst...
    edestruct IHeLf with (ns' := ns') as [[SealS1 [Seal1 Count]] | [e' [s' [Rede [SealS2 Seal2]]]]]...
    right... eexists. eexists. split...
  }
------
  clear safety_record_step'.
  intros * RecCompE WfS sLns eLf Redf.
  generalize dependent ns'.
  generalize dependent f'.

  dependent induction eLf; intros; try solve [try inversion Redf; eauto].
  Case "red_record_exp". {
    inversion RecCompE; subst...
    assert (record_comp (rec_exp a e2 r2)) as RecCompE2R2...
    inversion RecCompE2R2; subst...
    inversion Redf; subst...
    + unshelve epose proof (safety_step' e1 s e2 ns _ _ _ _)
        as [[SealS1 [Seal1 Count]] | [e' [s' [Rede [SealS2 Seal2]]]]]...
      right... eexists. eexists. split...
    + right. erewrite <- consistent_fresh_label_for_store...
      eexists. eexists. split.
      eapply red_record_exp_2...
      eapply sealcomp_value with (f := e2)...
      split...
  }
  Case "red_record_ref". {
    inversion RecCompE;
    inversion Redf; subst...
    destruct IHeLf
      with (f' := r1') (ns' := ns') as [[SealS1 [Seal1 Count]] | [e' [s' [Rede [SealS2 Seal2]]]]]...
    right... eexists. eexists. split...
  }
Qed.


(** Lemma 3.5 / 5.2 *)
Lemma safety_step : forall e s e' s' f ns f' ns',
  sealcomp_store s ns ->
  sealcomp e f ->
  red e s e' s' ->
  red f ns f' ns' ->
  (sealcomp_store s ns' /\ sealcomp e f' /\ seal_count f' < seal_count f) \/ (sealcomp_store s' ns' /\ sealcomp e' f')
with safety_record_step : forall e s e' s' f ns f' ns',
  sealcomp_store s ns ->
  sealcomp_rec_comp e f ->
  red_record_comp e s e' s' ->
  red_record_comp f ns f' ns' ->
  (sealcomp_store s ns' /\ sealcomp_rec_comp e f' /\ seal_count_record f' < seal_count_record f) \/ (sealcomp_store s' ns' /\ sealcomp_rec_comp e' f').
Proof with eauto; try solve [simpl; eauto; intuition].
------
  clear safety_step.
  intros * sLns eLf Rede Redf.
  generalize dependent s'.
  generalize dependent e'.
  generalize dependent ns'.
  generalize dependent f'.
  dependent induction eLf; intros; try solve [try inversion Rede; try inversion Redf; eauto].
  Case "red_app". {
    inversion Rede; inversion Redf; subst...
    + edestruct IHeLf1 with (ns' := ns') as [[SealS1 [Seal1 Count]] | [SealS2 Seal2]]...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf1 _) as ValueE1...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf1 _) as ValueE2...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (safety_value e1 s f1 ns e1' ns' _ _ _ _) as [Store SComp]...
    + edestruct IHeLf2 with (ns' := ns') as [[SealS1 [Seal1 Count]] | [SealS2 Seal2]]...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf2 _) as ValueE2...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (safety_value (exp_abs e0) ns f1 ns e1' ns' _ _ _ _) as [Store SComp]...
      left; split...
      eapply sealcomp_store_transitive...
    + unshelve epose proof (safety_value e2 ns f2 ns e2' ns' _ _ _ _) as [Store SComp]...
      left; split...
      eapply sealcomp_store_transitive...
    + (** sealcomp over opens *)
      inversion eLf1...
  }
  Case "red_let". { 
    inversion Rede; inversion Redf; subst...
    + edestruct IHeLf1 with (ns' := ns') as [[SealS1 [Seal1 Count]] | [SealS2 Seal2]]...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf1 _) as ValueE1...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (safety_value e1 s' f1 ns e1' ns' _ _ _ _) as [Store SComp]...
  }
  Case "red_box". {
    inversion Rede; inversion Redf; subst...
    + edestruct IHeLf with (ns' := ns') as [[SealS1 [Seal1 Count]] | [SealS2 Seal2]]...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf _) as ValueE1...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (safety_value e1 s e2 ns e1' ns' _ _ _ _) as [Store SComp]...
    + erewrite <- consistent_fresh_label_for_store...
  }
  Case "red_unbox". {
    inversion Rede; inversion Redf; subst...
    + edestruct IHeLf with (ns' := ns') as [[SealS1 [Seal1 Count]] | [SealS2 Seal2]]...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf _) as ValueE1...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf _ )as ValueE1...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (safety_value (exp_ref l) s' e2 ns e1' ns' _ _ _ _)
      as [Store SComp]...
    + inversion eLf; subst...
      right... split...
      destruct (sLns) as [Left Right]...
      destruct (Left l0 e') as [v' [MapsNS' e'Lv']]...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns' l0 f')) _) as R1...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns' l0 v')) _) as R2...
      rewrite R1 in *; inversion R2; subst...
    + inversion eLf; subst...
      inversion select (exp_ref _ <e= exp_ref _); subst...
      right... split...
      destruct (sLns) as [Left Right]...
      destruct (Left l0 e') as [v' [MapsNS' e'Lv']]...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns' l0 v')) _) as R1...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns' l0 v0)) _) as R2...
      rewrite R1 in *; inversion R2; subst...
    + unshelve epose proof (safety_value (exp_seal (exp_ref l)) s' e2 ns e1' ns' _ _ _ _)
      as [Store SComp]...
    + inversion eLf; subst...
    + inversion eLf;  inversion select (_ <e= exp_ref _); subst...
      right... split...
      destruct (sLns) as [Left Right]...
      destruct (Left l0 v1) as [v' [MapsNS' e'Lv']]...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns' l0 v')) _) as R1...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns' l0 v0)) _) as R2...
      rewrite R1 in *; inversion R2; subst...
  }
  Case "red_set_box". { 
    inversion Rede; inversion Redf; subst...
    + edestruct IHeLf1 with (ns' := ns') as [[SealS1 [Seal1 Count]] | [SealS2 Seal2]]...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf1 _) as ValueE1...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf1 _ ) as ValueE1...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (safety_value e1 s f1 ns e1' ns' _ _ _ _)
      as [Store SComp]...
    + edestruct IHeLf2 with (ns' := ns') as [[SealS1 Seal1] | [SealS2 Seal2]]...
    + unshelve epose proof (sealcomp_value e2 f2 _ _ _ _)...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (safety_value (exp_ref l) s f1 ns e1' ns' _ _ _ _)
      as [Store SComp]...
    + unshelve epose proof (safety_value e2 s f2 ns e2' ns' _ _ _ _)
      as [Store SComp]...
    + inversion eLf1; subst...
      right; split...
      destruct sLns as [Left Right]...
      destruct (Left l0 e') as [f'' [MapsF LtF]]...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns l0 f'')) _) as R1...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns l0 f')) _) as R2...
      rewrite R1 in R2; inversion R2; subst...
  }
  Case "red_seal". { 
    inversion Rede; inversion Redf; subst...
    + edestruct IHeLf as [[LeftS [LeftC Count]] | [RightS RightC]]...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf _ ) as ValueE1...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf _ ) as ValueE1...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf _ ) as ValueE1...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (safety_value (exp_abs e0) s' e2 ns e1' ns' _ _ _ _)
      as [Store SComp]...
    + unshelve epose proof (safety_value (exp_ref l) s' e2 ns e1' ns' _ _ _ _)
      as [Store SComp]...
    + unshelve epose proof (safety_value (exp_record r) s' e2 ns e1' ns' _ _ _ _)
      as [Store SComp]...
  }
  Case "red_record". {
    inversion Rede; inversion Redf; subst...
    unshelve epose proof (safety_record_step r1 s r1' s' r2 ns r1'0 ns' _ _ _ _)
      as [[StoreLeft [LtLeft Count]] | [StoreRight LtRight]]...
  }
  Case "red_record_read". {
    inversion Rede; inversion Redf; subst...
    + edestruct IHeLf with (ns' := ns') as [[SealS1 [Seal1 Count]] | [SealS2 Seal2]]...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf _) as ValueE1...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf _ )as ValueE1...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (safety_value (exp_record r) s' e2 ns e1' ns' _ _ _ _)
      as [Store SComp]...
    + inversion eLf; subst...
      right... split...
      rewrite (sealcomp_record_consistent r r0 x (Some l)) in *...
      inversion select (Some l = Some l0); subst...
      destruct (sLns) as [Left Right]...
      destruct (Left l0 e') as [v' [MapsNS' e'Lv']]...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns' l0 f')) _) as R1...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns' l0 v')) _) as R2...
      rewrite R1 in *; inversion R2; subst...
    + inversion eLf; subst...
      inversion select (exp_record r <e= exp_record r0); subst...
      rewrite (sealcomp_record_consistent r r0 x (Some l)) in *...
      inversion select (Some l = Some l0); subst...
      right... split...
      destruct (sLns) as [Left Right]...
      destruct (Left l0 e') as [v' [MapsNS' e'Lv']]...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns' l0 v')) _) as R1...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns' l0 v0)) _) as R2...
      rewrite R1 in *; inversion R2; subst...
    + unshelve epose proof (safety_value (exp_seal (exp_record r)) s' e2 ns e1' ns' _ _ _ _)
      as [Store SComp]...
    + inversion eLf; subst...
    + inversion eLf;
        [inversion select (exp_record _ <e= exp_record _)|
         inversion select (exp_seal (exp_record _) <e= exp_record _)]; subst...
      rewrite (sealcomp_record_consistent r r0 x (Some l)) in *...
      inversion select (Some l = Some l0); subst...
      right... split...
      destruct (sLns) as [Left Right]...
      destruct (Left l0 v1) as [v' [MapsNS' e'Lv']]...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns' l0 v')) _) as R1...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns' l0 v0)) _) as R2...
      rewrite R1 in *; inversion R2; subst...
  }
  Case "red_record_write". {
    inversion Rede; inversion Redf; subst...
    + edestruct IHeLf1 with (ns' := ns') as [[SealS1 [Seal1 Count]] | [SealS2 Seal2]]...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf1 _) as ValueE1...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (sealcomp_value _ _ _ _ eLf1 _ ) as ValueE1...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (safety_value e1 s f1 ns e1' ns' _ _ _ _)
      as [Store SComp]...
    + edestruct IHeLf2 with (ns' := ns') as [[SealS1 [Count Seal1]] | [SealS2 Seal2]]...
    + unshelve epose proof (sealcomp_value e2 f2 _ _ _ _)...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (safety_value (exp_record r) s f1 ns e1' ns' _ _ _ _)
      as [Store SComp]...
    + unshelve epose proof (safety_value e2 s f2 ns e2' ns' _ _ _ _)
      as [Store SComp]...
    + inversion eLf1; subst...
      rewrite (sealcomp_record_consistent r r0 x (Some l)) in *...
      inversion select (Some l = Some l0); subst...
      right; split...
      destruct sLns as [Left Right]...
      destruct (Left l0 e') as [f'' [MapsF LtF]]...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns l0 f'')) _) as R1...
      unshelve epose proof ((proj1 (LabelMapFacts.find_mapsto_iff ns l0 f')) _) as R2...
      rewrite R1 in R2; inversion R2; subst...
  }
  Case "red_seal". {
    inversion Redf; subst...
    unshelve epose proof (IHeLf e1' ns' _ e' s' _) as
      [[StoreLeft [CompLeft Count]] | [StoreRight CompRight]]...
  }
------
  clear safety_record_step.
  intros * sLns eLf Rede Redf.
  generalize dependent s'.
  generalize dependent e'.
  generalize dependent ns'.
  generalize dependent f'.
  dependent induction eLf; intros; try solve [try inversion Rede; try inversion Redf; eauto].
  Case "red_record_exp". {
    inversion Rede; inversion Redf; subst...
    + unshelve epose proof (safety_step e1 s e1' s' e2 ns e1'0 ns' _ _ _ _)
        as [[LeftStore [LeftComp Count]] | [RightStore RightComp]]...
    + unshelve epose proof (sealcomp_value _ _ _ _ H _) as ValueE2...
      exfalso; eapply irreducible_value...
    + unshelve epose proof (safety_value e1 s e2 ns e1' ns' _ _ _ _)
        as [StoreComp [SComp Count]]...
    + erewrite <- consistent_fresh_label_for_store...
  }
  Case "red_record_ref". {
    inversion Rede; inversion Redf; subst...
    unshelve epose proof (IHeLf r1'0 ns' _  r1' s' _) as
      [[StoreLeft [CompLeft Count]] | [StoreRight CompRight]]...
  }
Qed.
