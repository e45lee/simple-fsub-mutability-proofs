(** Additional administrative lemmas concering normal forms for Fsub.

    Authors: Edward Lee, Ondrej Lhotak

    Authors: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    This file contains a number of administrative lemmas that we
    require for proving type-safety.  These lemmas mainly concern
    the predicates [in_normal_form] as well as the normalization functions
    [merge_mutability] and [normal_form_typing].  These lemmas
    are necessary for relating syntactically inequivalent but semantically
    equivalent types: types like:

      readonly (readonly X) and (readonly X)

    Table of contents:
      - #<a href="##normal_forms">Lemmas concering normal forms</a>#
      - #<a href="##lemma_4.2">Lemma 4.2 (normalizing is idempotent) </a>#

*)
Require Export Fsub.Fm_Lemmas.

(* ********************************************************************** *)
(** * #<a name="normal_forms"></a># Lemmas concerning normal forms *)

Lemma merge_mutability_type : forall T,
  type T ->
  type (merge_mutability T mut_readonly).
Proof with simpl in *; auto; repeat fold merge_mutability in *.
  intros * Typ.
  dependent induction Typ...
  + apply type_all with (L := L)...
Qed.
#[export] Hint Resolve merge_mutability_type : core.

Lemma normal_form_type : forall T,
  type T ->
  type (normal_form_typing T).
Proof with simpl in *; auto; repeat fold merge_mutability in *; repeat fold normal_form_typing in *.
  intros * Typ.
  dependent induction Typ...
  + apply type_all with (L := L)... intros. rewrite <- normal_form_open_tt...
Qed.
#[export] Hint Resolve normal_form_type : core.


Lemma normal_forms_merge : forall T m,
  in_normal_form T ->
  in_normal_form (merge_mutability T m).
Proof with eauto; try fold merge_mutability in *; simpl.
  intros.
  destruct m...
  dependent induction H; try unfold merge_mutability in *...
  econstructor...
  econstructor...
  econstructor...
Qed.
#[export] Hint Resolve normal_forms_merge : core.

Lemma normal_forms : forall T,
  type T ->
  in_normal_form (normal_form_typing T).
Proof with eauto; 
  try fold normal_form_typing in *; 
  try fold merge_mutability in *; try congruence;
  simpl in *.
  intros.
  dependent induction H; try unfold normal_form_typing in *;
    try unfold merge_mutability in *; subst...
  pick fresh Y and apply all_in_normal_form...
  rewrite <- normal_form_open_tt...
Qed.
#[export] Hint Resolve normal_forms : core.

Lemma normal_form_multiple_mut : forall T,
  normal_form_typing (typ_mut mut_readonly (typ_mut mut_readonly T)) =
    normal_form_typing (typ_mut mut_readonly T).
Proof with eauto; try repeat fold merge_mutability; try repeat fold normal_form_typing.
  intros; simpl...
  induction T; subst...
  - unfold normal_form_typing...
    destruct m...
    rewrite IHT...
  - unfold normal_form_typing...
    unfold merge_mutability...
    rewrite IHT1...
    rewrite IHT2...
Qed.
#[export] Hint Rewrite normal_form_multiple_mut : core.

Lemma normal_form_unique : forall T,
  type T ->
  in_normal_form T ->
  T = (normal_form_typing T).
Proof with eauto;
  try repeat fold merge_mutability; try repeat fold normal_form_typing.
  intros * Typ Norm.
  dependent induction Norm; inversion Typ; subst; simpl; try solve [eauto; f_equal; eauto]...
  - f_equal...
    apply open_tt_normal_equal_rec with (L := (L `union` L0)) (k := 0)...
  - f_equal...
    inversion H0; subst...
    f_equal...
  - f_equal...
    inversion H0; subst...
    f_equal...
Qed.

Lemma atom_in_intersection_normal: forall (X : atom) T,
  in_intersection X T ->
  in_intersection X (normal_form_typing T) \/
    in_intersection (typ_mut mut_readonly X) (normal_form_typing T).
Proof with eauto; simpl.
  intros * Int.
  dependent induction Int; subst...
  - destruct (IHInt X)...  
  - destruct (IHInt X)...
Qed.

Lemma atom_in_intersection_readonly_normal : forall (X : atom) T,
  in_intersection X T ->
  in_intersection X (normal_form_typing (typ_mut mut_readonly T))
    \/
  in_intersection (typ_mut mut_readonly X) (normal_form_typing (typ_mut mut_readonly T)).
Proof with eauto; simpl.
  intros * Int.
  dependent induction Int; subst...
  - destruct (IHInt X)...
  - destruct (IHInt X)...
Qed.

Lemma atom_equal_normal_form : forall (X : atom) T,
  typ_fvar X = normal_form_typing T ->
  typ_fvar X = T.
Proof with eauto; simpl.
  intros.
  destruct T; subst; simpl in *; try discriminate...

  fold merge_mutability in *.
  fold normal_form_typing in *.
  destruct (normal_form_typing T); simpl in *; try discriminate; subst...
Qed.
#[export] Hint Resolve atom_equal_normal_form : core.
#[export] Hint Resolve
  atom_in_intersection_normal atom_in_intersection_readonly_normal : core.

Lemma multiple_merge_mutability_in_normal_form : forall T,
  in_normal_form T ->
  merge_mutability (merge_mutability T mut_readonly) mut_readonly =
    merge_mutability T mut_readonly.
Proof with eauto.
  intros.
  dependent induction H; simpl;
    fold merge_mutability...
  f_equal...
Qed.

Lemma multiple_merge_mutability_normalized : forall T,
  type T ->
  merge_mutability (merge_mutability (normal_form_typing T) mut_readonly) mut_readonly 
    = merge_mutability (normal_form_typing T) mut_readonly.
Proof with eauto using multiple_merge_mutability_in_normal_form.
  intros...
Qed.

#[export] Hint Resolve multiple_merge_mutability_in_normal_form
  multiple_merge_mutability_normalized : core.
#[export] Hint Rewrite multiple_merge_mutability_in_normal_form
  multiple_merge_mutability_normalized : core.

Lemma merge_mutability_multiple : forall T m,
  (merge_mutability (merge_mutability T m) m) = merge_mutability T m.
Proof with simpl in *; eauto;
  try repeat fold merge_mutability in *; try repeat fold normal_form_typing in *.
  intros *...
  induction T...
  f_equal...
Qed.
#[export] Hint Rewrite merge_mutability_multiple : core.

Lemma normal_form_merge_mutability_exchange : forall T m,
  (normal_form_typing (merge_mutability T m)) =
    (merge_mutability (normal_form_typing T) m).
Proof with simpl in *; eauto;
  try repeat fold merge_mutability in *; try repeat fold normal_form_typing in *.
  intros *...
  induction T...
  + destruct m; destruct m0; autorewrite with core...
  + f_equal...
Qed.

(** #<a name="lemma_4.2"></a># Lemma 4.2: Normalizing is idempotent.  *)
Lemma normal_form_in_normal_form : forall T,
  (normal_form_typing (normal_form_typing T)) = (normal_form_typing T).
Proof with simpl in *; eauto;
  try repeat fold merge_mutability in *; try repeat fold normal_form_typing in *.
  intros T.
  induction T; try solve [simpl in *; f_equal; eauto]...
  + rewrite normal_form_merge_mutability_exchange...
    rewrite IHT...
Qed.
#[export] Hint Rewrite normal_form_in_normal_form : core.


Lemma readonly_atom_in_normal_to_normal : forall (X : atom) T,
  in_intersection (typ_mut mut_readonly X)
    (normal_form_typing T) ->
  type T ->
  in_intersection (typ_mut mut_readonly X)
    (normal_form_typing (typ_mut mut_readonly T)).
Proof with eauto; simpl in *;
  repeat (fold merge_mutability in *; fold normal_form_typing in *).
  intros * Int Typ...
  dependent induction T; subst;
    try solve [ inversion Int; try discriminate ]...
  - destruct m...  
    rewrite multiple_merge_mutability_normalized...
  - inversion Typ; subst...
    inversion Int; subst... discriminate.
Qed.
#[export] Hint Resolve readonly_atom_in_normal_to_normal : core.

Lemma readonly_atom_in_normal_readonly_to_normal : forall (X : atom) T,
  in_intersection (typ_mut mut_readonly X)
    (normal_form_typing (typ_mut mut_readonly T)) ->
  type T ->
  in_intersection (typ_mut mut_readonly X) (normal_form_typing T)
    \/
  in_intersection X (normal_form_typing T).
Proof with eauto; simpl in *;
  repeat (fold merge_mutability in *; fold normal_form_typing in *);
  try discriminate.
  intros * Int Typ.
  dependent induction T;
    try solve [ inversion Int; try discriminate ]...
  - inversion Int; subst...
    inversion H...
  - destruct m; rewrite multiple_merge_mutability_normalized in Int...
  - inversion Int; subst...
    destruct IHT1...
    destruct IHT2...
Qed.
#[export] Hint Resolve readonly_atom_in_normal_readonly_to_normal : core.


Lemma intersection_of_normal_is_normal : forall S T,
  in_intersection S T ->
  in_normal_form T ->
  in_normal_form S.
Proof with eauto.
  intros * Int Normal.
  induction Int; subst;
    try solve [inversion Normal; eauto]...
Qed.

Lemma readonly_arrow_is_not_normal : forall T1 T2 T,
  in_normal_form T ->
  ~ in_intersection (typ_mut mut_readonly (typ_arrow T1 T2)) T.
Proof with eauto; try discriminate.
  intros.
  induction H; intro Int; inversion Int; subst...
Qed.

Lemma readonly_all_is_not_normal : forall T1 T2 T,
  in_normal_form T ->
  ~ in_intersection (typ_mut mut_readonly (typ_all T1 T2)) T.
Proof with eauto; try discriminate.
  intros.
  induction H; intro Int; inversion Int; subst...
Qed.
#[export] Hint Resolve readonly_arrow_is_not_normal readonly_all_is_not_normal : core.

Lemma in_intersection_arrow_normal_in_merge : forall T1 T2 T,
  in_intersection (typ_arrow T1 T2) T ->
  in_normal_form T ->
  in_intersection (typ_arrow T1 T2)
    (merge_mutability T mut_readonly).
Proof with eauto; try repeat fold merge_mutability in *; try discriminate.
  intros * Int Norm.
  dependent induction Norm; try solve [inversion Int; subst; eauto; discriminate].
  - simpl; inversion Int; subst...
Qed.

Lemma in_intersection_arrow_merge_in_normal : forall T1 T2 T,
  in_intersection (typ_arrow T1 T2) (merge_mutability T mut_readonly) ->
  in_normal_form T ->
  in_intersection (typ_arrow T1 T2) T.
Proof with eauto; try repeat fold merge_mutability in *;
  try discriminate.
  intros * Int Norm.
  dependent induction Norm; try solve [inversion Int; eauto; discriminate].
Qed.

#[export] Hint Resolve in_intersection_arrow_normal_in_merge : core.
#[export] Hint Resolve in_intersection_arrow_merge_in_normal : core.

Lemma in_intersection_readonly_arrow_normal_in_merge : forall T1 T2 T,
  in_intersection (typ_mut mut_readonly (typ_arrow T1 T2)) T ->
  in_normal_form T ->
  in_intersection (typ_mut mut_readonly (typ_arrow T1 T2))
    (merge_mutability T mut_readonly).
Proof with eauto; try repeat fold merge_mutability in *;
  try discriminate.
  intros * Int Norm.
  dependent induction Norm; try solve [inversion Int; eauto; discriminate].
  - simpl; inversion Int...
Qed.

Lemma in_intersection_readonly_arrow_merge_in_normal : forall T1 T2 T,
  in_intersection (typ_mut mut_readonly (typ_arrow T1 T2))
    (merge_mutability T mut_readonly) ->
  in_normal_form T ->
  in_intersection (typ_arrow T1 T2) T.
Proof with eauto; try repeat fold merge_mutability in *;
  try discriminate.
  intros * Int Norm.
  dependent induction Norm; try solve [inversion Int; eauto; discriminate].
Qed.

#[export] Hint Resolve in_intersection_readonly_arrow_merge_in_normal : core.
#[export] Hint Resolve in_intersection_readonly_arrow_normal_in_merge : core.

Lemma arrow_argument_in_normal_form : forall T1 T2,
  in_normal_form (typ_arrow T1 T2) ->
  in_normal_form T1.
Proof with eauto.
  intros * Norm.
  inversion Norm...
Qed.

Lemma arrow_return_in_normal_form : forall T1 T2 ,
  in_normal_form (typ_arrow T1 T2) ->
  in_normal_form T2.
Proof with eauto.
  intros * Norm.
  inversion Norm...
Qed.

Lemma mut_arrow_in_normal_form : forall T1 T2,
  in_normal_form (typ_mut mut_readonly (typ_arrow T1 T2)) ->
  in_normal_form (typ_arrow T1 T2).
Proof with eauto.
  intros * Norm.
  inversion Norm...
Qed.

#[export] Hint Immediate arrow_argument_in_normal_form arrow_return_in_normal_form 
  mut_arrow_in_normal_form : core.

  Lemma in_intersection_all_normal_in_merge : forall T1 T2 T,
  in_intersection (typ_all T1 T2) T ->
  in_normal_form T ->
  in_intersection (typ_all T1 T2)
    (merge_mutability T mut_readonly).
Proof with eauto; try repeat fold merge_mutability in *; try discriminate.
  intros * Int Norm.
  dependent induction Norm; try solve
    [inversion Int; simpl in *; eauto; discriminate]...
Qed.

Lemma in_intersection_all_merge_in_normal : forall T1 T2 T,
  in_intersection (typ_all T1 T2) (merge_mutability T mut_readonly) ->
  in_normal_form T ->
  in_intersection (typ_all T1 T2) T.
Proof with eauto; try repeat fold merge_mutability in *;
  try discriminate.
  intros * Int Norm.
  dependent induction Norm;
    try solve [inversion Int; eauto; discriminate].
Qed.

#[export] Hint Resolve in_intersection_all_normal_in_merge : core.
#[export] Hint Resolve in_intersection_all_merge_in_normal : core.

Lemma in_intersection_readonly_all_normal_in_merge : forall T1 T2 T,
  in_intersection (typ_mut mut_readonly (typ_all T1 T2)) T ->
  in_normal_form T ->
  in_intersection (typ_mut mut_readonly (typ_all T1 T2))
    (merge_mutability T mut_readonly).
Proof with eauto; try repeat fold merge_mutability in *;
  try discriminate.
  intros * Int Norm.
  dependent induction Norm; try solve [inversion Int; eauto; discriminate].
  - simpl; inversion Int...
Qed.

Lemma in_intersection_readonly_all_merge_in_normal : forall T1 T2 T,
  in_intersection (typ_mut mut_readonly (typ_all T1 T2))
    (merge_mutability T mut_readonly) ->
  in_normal_form T ->
  in_intersection (typ_all T1 T2) T.
Proof with eauto; try repeat fold merge_mutability in *;
  try discriminate.
  intros * Int Norm.
  dependent induction Norm; try solve [inversion Int; eauto; discriminate].
Qed.

#[export] Hint Resolve in_intersection_readonly_all_normal_in_merge : core.
#[export] Hint Resolve in_intersection_readonly_all_merge_in_normal : core.

(** Additional lemmas about wellformedness and normal forms
    TODO: check how these proofs actually work. *)
Lemma wf_typ_merge_mutability : forall E T,
  wf_typ E T ->
  wf_typ E (merge_mutability T mut_readonly).
Proof with eauto.
  intros * WfT.
  dependent induction WfT...
Qed.
Lemma wf_typ_normal_form : forall E T,
  wf_typ E T ->
  wf_typ E (normal_form_typing T).
Proof with eauto.
  intros * WfT.
  dependent induction WfT...
Qed.
#[export] Hint Resolve wf_typ_normal_form wf_typ_merge_mutability : core.

Lemma wf_typ_all_arg_from_all : forall E T1 T2,
  wf_typ E (typ_all T1 T2) ->
  wf_typ E T1.
Proof with eauto.
  intros * WfT.
  inversion WfT...
Qed.

Lemma wf_typ_from_in_intersection : forall E S T,
  in_intersection S T ->
  wf_typ E T ->
  wf_typ E S.
Proof with eauto.
  intros * WfT IntST.
  dependent induction IntST...
Qed.

#[export] Hint Resolve wf_typ_all_arg_from_all
  wf_typ_from_in_intersection : core.


Lemma box_in_intersection_merge_inversion : forall S T,
  ~ in_intersection (typ_box S) (merge_mutability T mut_readonly).
Proof with simpl in *; eauto; repeat fold merge_mutability in *.
  intros * Int.
  induction T; inversion Int; try discriminate...
Qed.
#[export] Hint Resolve box_in_intersection_merge_inversion : core.


Lemma in_intersection_box_normal_in_merge : forall T1  T,
  in_intersection (typ_box T1) T ->
  in_normal_form T ->
  in_intersection (typ_mut mut_readonly (typ_box T1))
    (merge_mutability T mut_readonly).
Proof with  simpl in *; eauto; try repeat fold merge_mutability in *; try discriminate.
  intros * Int Norm.
  dependent induction Norm; 
    try solve [simpl in *; inversion Int; subst; try discriminate]...
  - inversion Int; subst...
    inversion H...
  - inversion Int; subst...
Qed.

Lemma in_intersection_box_merge_in_normal : forall T1 T,
  in_intersection (typ_box T1) (merge_mutability T mut_readonly) ->
  in_normal_form T ->
  in_intersection (typ_box T1) T.
Proof with eauto; try repeat fold merge_mutability in *;
  try discriminate.
  intros * Int Norm.
  dependent induction Norm; try solve [inversion Int; eauto; discriminate]...
Qed.

#[export] Hint Resolve in_intersection_box_normal_in_merge : core.
#[export] Hint Resolve in_intersection_box_merge_in_normal : core.

Lemma in_intersection_readonly_box_normal_in_merge : forall T1 T,
  in_intersection (typ_mut mut_readonly (typ_box T1)) T ->
  in_normal_form T ->
  in_intersection (typ_mut mut_readonly (typ_box T1))
    (merge_mutability T mut_readonly).
Proof with eauto; try repeat fold merge_mutability in *;
  try discriminate.
  intros * Int Norm.
  dependent induction Norm; try solve [inversion Int; eauto; discriminate]...
  - simpl; inversion Int...
Qed.

Lemma in_intersection_readonly_box_merge_in_normal : forall T1 T,
  in_intersection (typ_mut mut_readonly (typ_box T1))
    (merge_mutability T mut_readonly) ->
  in_normal_form T ->
  in_intersection (typ_box T1) T \/
  in_intersection (typ_mut mut_readonly (typ_box T1)) T.
Proof with simpl in *; eauto; try repeat fold merge_mutability in *;
  try discriminate.
  intros * Int Norm.
  dependent induction Norm; try solve [inversion Int; eauto; discriminate]...
  - inversion Int; subst...
    inversion H...
  - simpl in *; inversion Int; subst...
    + destruct (IHNorm1 H1)...
    + destruct (IHNorm2 H1)...
Qed.

#[export] Hint Resolve in_intersection_readonly_box_normal_in_merge : core.
#[export] Hint Resolve in_intersection_readonly_box_merge_in_normal : core.

Lemma in_intersection_atom_normal_in_merge : forall (X : atom) T,
  in_intersection X T ->
  in_normal_form T ->
  in_intersection (typ_mut mut_readonly X) (merge_mutability T mut_readonly).
Proof with simpl in *; eauto; repeat fold merge_mutability.
  intros * Int Norm.
  induction Norm; inversion Int; subst; try discriminate...
  rewrite H...
Qed.

Lemma in_intersection_readonly_atom_normal_in_merge : forall (X :atom) T,
  in_intersection (typ_mut mut_readonly X) T ->
  in_normal_form T ->
  in_intersection (typ_mut mut_readonly X) (merge_mutability T mut_readonly).
Proof with simpl in *; eauto; repeat fold merge_mutability.
  intros * Int Norm.
  induction Norm; inversion Int; subst; try discriminate...
Qed.

#[export] Hint Resolve in_intersection_atom_normal_in_merge
  in_intersection_readonly_atom_normal_in_merge : core.


Lemma atom_in_intersection_merge_inversion : forall (X : atom) T,
  ~ in_intersection X (merge_mutability T mut_readonly).
Proof with simpl in *; eauto; repeat fold merge_mutability in *.
  intros * Int.
  induction T; inversion Int; try discriminate...
Qed.

#[export] Hint Resolve atom_in_intersection_merge_inversion : core.


Lemma merge_mutability_inversion_top : forall T,
  merge_mutability T mut_readonly = typ_top ->
  T = typ_top.
Proof with simpl in *; eauto; try discriminate; repeat fold merge_mutability in *.
  intros * Merge.
  induction T...
Qed.

#[export] Hint Resolve merge_mutability_inversion_top : core.

Lemma merge_mutability_inversion_arrow : forall T,
  (exists T1 T2, merge_mutability T mut_readonly = typ_arrow T1 T2) ->
  exists T1 T2, T = typ_arrow T1 T2.
Proof with simpl in *; eauto; try discriminate; repeat fold merge_mutability in *.
  intros * Merge.
  destruct Merge as [T1 [T2 Eq]].
  induction T...
Qed.

#[export] Hint Resolve merge_mutability_inversion_arrow : core.

Lemma merge_mutability_inversion_box : forall T,
  ~ (exists T', merge_mutability T mut_readonly = typ_box T').
Proof with simpl in *; eauto; try discriminate; repeat fold merge_mutability in *.
  intros * Merge.
  destruct Merge as [T1 Eq].
  induction T...
Qed.

#[export] Hint Resolve merge_mutability_inversion_box : core.

Lemma merge_mutability_inversion_readonly_box : forall T,
  (exists T', merge_mutability T mut_readonly = typ_mut mut_readonly (typ_box T')) ->
  (exists T', T = typ_box T') \/ (exists T', T = typ_mut mut_readonly (typ_box T')).
Proof with simpl in *; eauto; try discriminate; repeat fold merge_mutability in *.
  intros * Merge.
  destruct Merge as [T1 Eq].
  induction T...
Qed.

#[export] Hint Resolve merge_mutability_inversion_readonly_box : core.

Lemma merge_mutability_inversion_record : forall T,
  ~ (exists a T', merge_mutability T mut_readonly = typ_record a T').
Proof with simpl in *; eauto; try discriminate; repeat fold merge_mutability in *.
  intros * Merge.
  destruct Merge as [T1 [a Eq]].
  induction T...
Qed.

#[export] Hint Resolve merge_mutability_inversion_record : core.

Lemma merge_mutability_inversion_readonly_record : forall T,
  (exists a T', merge_mutability T mut_readonly = typ_mut mut_readonly (typ_record a T')) ->
  (exists a T', T = typ_record a T') \/ (exists a T', T = typ_mut mut_readonly (typ_record a T')).
Proof with simpl in *; eauto; try discriminate; repeat fold merge_mutability in *.
  intros * Merge.
  destruct Merge as [T1 [a Eq]].
  induction T...
Qed.

#[export] Hint Resolve merge_mutability_inversion_readonly_record : core.

Lemma in_intersection_merge : forall T1 T,
  in_normal_form T ->
  ~ (exists U1 U2, T1 = typ_int U1 U2) ->
  in_intersection T1 (merge_mutability T mut_readonly) ->
  in_intersection T1 T \/
    exists T1',  T1 = typ_mut mut_readonly T1' /\ in_intersection T1' T.
Proof with simpl in *; eauto 4; try repeat fold merge_mutability in *.
  intros * NormT Form Int.
  dependent induction NormT; try solve [inversion Int; subst; eauto]...
  - inversion Int; subst...
    right...
  - inversion Int; subst...
    right...
  - inversion Int; subst...
    + exfalso. apply Form...
    + destruct IHNormT1 as [IntT1 | [T1' [EqT1' IntT1'T0]]]...
      right...
    + destruct IHNormT2 as [IntT1 | [T1' [EqT1' IntT1'T2]]]...
      right...
  - inversion Int; subst...
    right...
Qed.

#[export] Hint Resolve in_intersection_merge : core.

Lemma in_intersection_of_normal_is_normal : forall S T,
  in_normal_form T ->
  in_intersection S T ->
  in_normal_form S.
Proof with debug eauto.
  intros * NormT Int.
  dependent induction NormT; try solve [inversion Int; subst; eauto];
  inversion Int; subst; econstructor...
Qed.

#[export] Hint Resolve in_intersection_of_normal_is_normal : core.



Lemma merge_mutability_inversion_int : forall T L R,
  merge_mutability T mut_readonly = typ_int L R ->
  (exists L' R', T = typ_int L' R').
Proof with eauto; simpl in *; repeat fold merge_mutability in *.
  intros * MergeEq.
  induction T; try discriminate...
Qed.

#[export] Hint Resolve merge_mutability_inversion_int : core.

Lemma in_intersection_to_merge : forall S T,
  in_normal_form T ->
  in_intersection S T ->
  in_intersection S (merge_mutability T mut_readonly) \/
  in_intersection (merge_mutability S mut_readonly) (merge_mutability T mut_readonly).
Proof with eauto; simpl in *; repeat fold merge_mutability in *.
  intros * NormT IntT.
  induction IntT; subst; inversion NormT; subst...
  - destruct IHIntT...
  - destruct IHIntT...
Qed.

#[export] Hint Resolve in_intersection_to_merge : core.

#[export] Hint Extern 1 (~ exists L R, ?T = typ_int L R) =>
  let Bad := fresh "Bad" in intro Bad; destruct Bad as [? [? ?]]; discriminate : core.

#[export] Hint Extern 6 False =>
  match goal with
  | H : forall S', in_intersection_component S' ?T1 -> S' = typ_top |- _ =>
    eenough (T1 = typ_top) by discriminate; apply H; split; eauto
  end : core.

#[export] Hint Extern 1 (in_intersection_component ?S ?T) =>
  match goal with
  | H1 : in_intersection S T |- _ =>
    match goal with
    | H2 : ~ (exists L R, S = typ_int L R) |- _ =>
      split; assumption
    end
  end : core.

  
Lemma in_intersection_component_to_merge : forall S T,
  in_normal_form T ->
  in_intersection_component S T ->
  in_intersection_component S (merge_mutability T mut_readonly) \/
  in_intersection_component (merge_mutability S mut_readonly)
    (merge_mutability T mut_readonly).
Proof with eauto; simpl in *; repeat fold merge_mutability in *.
  intros * Norm IntComp.
  destruct IntComp as [Primitive IntST]...
  dependent induction IntST; subst; try solve [left; split; eauto];
    try solve [right; split; eauto]...
  - right... split...
    intro Bad; destruct Bad as [L [R Eq]]... 
  - destruct IHIntST; eauto; destruct H...
  - destruct IHIntST; eauto; destruct H...
Qed.

#[export] Hint Extern 1 False =>
  match goal with
  | H : forall S, in_intersection_component S (typ_mut ?m ?T) -> S = typ_top |- _ =>
    eenough (typ_mut m T = typ_top) by discriminate; eapply H; split; eauto
  end : core. 


Lemma in_intersection_component_top_merged : forall T,
  in_normal_form T ->
  (forall S, in_intersection_component S (merge_mutability T mut_readonly) -> S = typ_top) ->
  (forall S, in_intersection_component S T -> S = typ_top).
Proof with eauto 4; simpl in *; repeat fold merge_mutability in *.
  intros * NormT SMut * IntS.
  destruct IntS as [Primitive IntS]; dependent induction IntS; subst...
  * induction NormT; apply SMut; split...
    - exfalso...  
    - exfalso...
    - exfalso. apply Primitive...
    - exfalso...
  * apply IHIntS... intros S' IntS'.
    destruct IntS' as [PrimitiveS' IntS']... eapply SMut...
  * apply IHIntS... intros S' IntS'.
    destruct IntS' as [PrimitiveS' IntS']... eapply SMut...
Qed.

#[export] Hint Extern 1 False => 
  let T1 := fresh "T1" in let T2 := fresh "T2" in let BadEq := fresh "BadEq" in 
  match goal with
  | H : forall S, in_intersection_component S (typ_mut ?m ?T) -> 
        exists S1 S2, S = typ_arrow S1 S2 |- _ =>
    eenough (exists T1 T2, typ_mut m T = typ_arrow T1 T2) as [T1 [T2 BadEq]] by discriminate; eapply H; split; eauto
  end : core. 

Lemma in_intersection_component_arrow_merged : forall T,
  in_normal_form T ->
  (forall S, in_intersection_component S (merge_mutability T mut_readonly) -> exists S1 S2, S = typ_arrow S1 S2) ->
  (forall S, in_intersection_component S T -> exists S1 S2, S = typ_arrow S1 S2).
Proof with eauto; simpl in *; repeat fold merge_mutability in *.
  intros * NormT SMut * IntS.
  destruct IntS as [Primitive IntS]; dependent induction IntS; subst...
  * induction NormT; apply SMut; split...
    - exfalso...
    - exfalso...
    - exfalso. apply Primitive...
    - exfalso...
  * apply IHIntS... intros S' IntS'.
    destruct IntS' as [PrimitiveS' IntS']...
  * apply IHIntS... intros S' IntS'.
    destruct IntS' as [PrimitiveS' IntS']...
Qed.


#[export] Hint Extern 1 False => 
  let T1 := fresh "T1" in let T2 := fresh "T2" in let BadEq := fresh "BadEq" in 
  match goal with
  | H : forall S, in_intersection_component S (typ_mut ?m ?T) -> 
        S = typ_top \/ exists S1 S2, S = typ_arrow S1 S2 |- _ =>
    eenough (typ_mut m T = typ_top \/ exists T1 T2, typ_mut m T = typ_arrow T1 T2) as [Eq | [T1 [T2 BadEq]]] by discriminate; eapply H; split; eauto
  end : core. 

Lemma in_intersection_component_top_or_arrow_merged : forall T,
  in_normal_form T ->
  (forall S, in_intersection_component S (merge_mutability T mut_readonly) -> S = typ_top \/ exists S1 S2, S = typ_arrow S1 S2) ->
  (forall S, in_intersection_component S T -> S = typ_top \/ exists S1 S2, S = typ_arrow S1 S2).
Proof with eauto; simpl in *; repeat fold merge_mutability in *.
  intros * NormT SMut * IntS.
  destruct IntS as [Primitive IntS]; dependent induction IntS; subst...
  * induction NormT; apply SMut; split...
    - exfalso...
    - exfalso...
    - exfalso. apply Primitive...
    - exfalso...
  * apply IHIntS... intros S' IntS'.
    destruct IntS' as [PrimitiveS' IntS']...
  * apply IHIntS... intros S' IntS'.
    destruct IntS' as [PrimitiveS' IntS']...
Qed.


Lemma in_intersection_all_component_left : forall P T1 T2,
  (forall T, in_intersection_component T (typ_int T1 T2) -> P T) ->
  (forall T, in_intersection_component T T1 -> P T).
Proof with eauto.
  intros * PropT T IntCompT1.
  apply PropT... destruct IntCompT1 as [Prim IntT]; split...
Qed.
Lemma in_intersection_all_component_right : forall P T1 T2,
  (forall T, in_intersection_component T (typ_int T1 T2) -> P T) ->
  (forall T, in_intersection_component T T2 -> P T).
Proof with eauto.
  intros * PropT T IntCompT1.
  apply PropT... destruct IntCompT1 as [Prim IntT]; split...
Qed.

Lemma in_intersection_component_merged_top : forall T,
  in_normal_form T ->
  (forall S, in_intersection_component S T -> S = typ_top) ->
  (forall S, in_intersection_component S (merge_mutability T mut_readonly) -> S = typ_top).
Proof with eauto 4; simpl in *; repeat fold merge_mutability in *.
  intros * NormT IntCompS S IntCompSMut.
  dependent induction NormT...
  * exfalso...
  * exfalso...
  * destruct IntCompSMut as [Primitive IntS]...
    unshelve epose proof 
      (in_intersection_all_component_left _ _ _ IntCompS).
    unshelve epose proof 
      (in_intersection_all_component_right _ _ _ IntCompS).

    inversion IntS; subst...
    - exfalso. apply Primitive...
  * exfalso...
Qed.

#[export] Hint Extern 6 False => let Eq := fresh "Eq" in let _S1 := fresh "S1" in let _S2 := fresh "S2" in
  match goal with
  | H : forall S', in_intersection_component S' ?T1 -> exists S1 S2, S' = typ_arrow S1 S2 |- _ =>
    eenough (exists S1 S2, T1 = typ_arrow S1 S2) as [_S1 [_S2 Eq]] by discriminate; apply H; split; eauto
  end : core.

Lemma in_intersection_component_merged_arrow : forall T,
  in_normal_form T ->
  (forall S, in_intersection_component S T -> exists S1 S2, S = typ_arrow S1 S2) ->
  (forall S, in_intersection_component S (merge_mutability T mut_readonly) -> exists S1 S2, S = typ_arrow S1 S2).
Proof with eauto 4; simpl in *; repeat fold merge_mutability in *.
  intros * NormT IntCompS S IntCompSMut.
  dependent induction NormT...
  * exfalso...
  * exfalso...
  * destruct IntCompSMut as [Primitive IntS]...
    unshelve epose proof 
      (in_intersection_all_component_left _ _ _ IntCompS).
    unshelve epose proof 
      (in_intersection_all_component_right _ _ _ IntCompS).

    inversion IntS; subst...
    - exfalso. apply Primitive...
  * exfalso...
Qed.

#[export] Hint Extern 6 False => 
  let Eq := fresh "Eq" in let _S1 := fresh "S1" in let _S2 := fresh "S2" in
  match goal with
  | H : forall S', in_intersection_component S' ?T1 -> S' = typ_top \/ exists S1 S2, S' = typ_arrow S1 S2 |- _ =>
    eenough (T1 = typ_top \/ exists S1 S2, T1 = typ_arrow S1 S2) as [Eq | [_S1 [_S2 Eq]]] by discriminate; apply H; split; eauto
  end : core.

Lemma in_intersection_component_merged_top_or_arrow : forall T,
  in_normal_form T ->
  (forall S, in_intersection_component S T -> S = typ_top \/ exists S1 S2, S = typ_arrow S1 S2) ->
  (forall S, in_intersection_component S (merge_mutability T mut_readonly) -> S = typ_top \/ exists S1 S2, S = typ_arrow S1 S2).
Proof with eauto 4; simpl in *; repeat fold merge_mutability in *.
  intros * NormT IntCompS S IntCompSMut.  
  dependent induction NormT...
  * exfalso...
  * exfalso...
  * destruct IntCompSMut as [Primitive IntS]...
    unshelve epose proof 
      (in_intersection_all_component_left _ _ _ IntCompS).
    unshelve epose proof 
      (in_intersection_all_component_right _ _ _ IntCompS).

    inversion IntS; subst...
    - exfalso. apply Primitive...
  * exfalso...
Qed.

Lemma mut_in_intersection_is_component : forall S S' T,
  S = typ_mut mut_readonly S' ->
  in_normal_form T ->
  in_intersection S T ->
  in_intersection_component S T.
Proof with eauto.
  intros * Eq NormT IntS.
  split...
  induction NormT; inversion IntS; subst; try discriminate...
Qed.


#[export] Hint Extern 6 False => let Bad := fresh "Bad" in 
  match goal with
  | H : forall S', in_intersection_component S' ?T1 -> exists S1, S' = typ_box S1 |- _ =>
    eenough (exists S1, T1 = typ_box S1) as 
      Bad by (destruct Bad as [? ?]; discriminate); apply H; split; eauto
  end : core.

#[export] Hint Extern 6 False => 
  let Eq := fresh "Eq" in let _S1 := fresh "S1" in
  match goal with
  | H : forall S', in_intersection_component S' ?T1 -> S' = typ_top \/ exists S1, S' = typ_box S1 |- _ =>
    eenough (T1 = typ_top \/ exists S1, T1 = typ_box S1) as [Eq | [_S1 Eq]] by discriminate; apply H; split; eauto
  end : core.

Lemma in_intersection_component_top_or_box_merged : forall T,
  in_normal_form T ->
  (forall S, in_intersection_component S (merge_mutability T mut_readonly) -> S = typ_top \/ exists S1, S = typ_box S1) ->
  (forall S, in_intersection_component S T -> S = typ_top \/ exists S1, S = typ_box S1).
Proof with eauto 4; simpl in *; repeat fold merge_mutability in *.
  intros * NormT SMut * IntS.
  destruct IntS as [Primitive IntS]; dependent induction IntS; subst...
  * induction NormT; apply SMut; split...
    - exfalso...
    - exfalso...
    - exfalso. apply Primitive...
    - exfalso...
  * apply IHIntS... intros S' IntS'.
    destruct IntS' as [PrimitiveS' IntS']... eapply SMut...
  * apply IHIntS... intros S' IntS'.
    destruct IntS' as [PrimitiveS' IntS']... eapply SMut...
Qed.

Lemma in_intersection_component_merged_top_or_box : forall T,
  in_normal_form T ->
  (forall S, in_intersection_component S T -> S = typ_top \/ exists S1, S = typ_box S1) ->
  (forall S, in_intersection_component S (merge_mutability T mut_readonly) -> S = typ_top \/ exists S1, S = typ_mut mut_readonly (typ_box S1)).
Proof with eauto 4; simpl in *; repeat fold merge_mutability in *.
  intros * NormT IntCompS S IntCompSMut.  
  dependent induction NormT; 
    try solve [inversion IntCompSMut as [Prim Eq]; inversion Eq; eauto]...
  * exfalso...
  * exfalso...
  * exfalso...
  * exfalso...
  * exfalso...
  * destruct IntCompSMut as [Primitive IntS]...
    unshelve epose proof 
      (in_intersection_all_component_left _ _ _ IntCompS).
    unshelve epose proof 
      (in_intersection_all_component_right _ _ _ IntCompS).

    inversion IntS; subst...
    - exfalso. apply Primitive...
  * exfalso...
  * exfalso...
Qed.



#[export] Hint Extern 6 False => let Bad := fresh "Bad" in 
  match goal with
  | H : forall S', in_intersection_component S' ?T1 -> 
    exists S1, S' = typ_box S1 |- _ =>
    eenough (exists S1, T1 = typ_box S1) as 
      Bad by (destruct Bad as [? ?]; discriminate); apply H; split; eauto
  end : core.

#[export] Hint Extern 6 False => 
  let Eq := fresh "Eq" in let _S1 := fresh "S1" in
  match goal with
  | H : forall S', in_intersection_component S' ?T1 -> 
    S' = typ_top \/ (exists S1, S' = typ_box S1) \/ (exists S2, S' = typ_mut mut_readonly (typ_box S2)) |- _ =>
    eenough (T1 = typ_top \/ 
             (exists S1, T1 = typ_box S1) \/
             (exists S2, T1 = typ_mut mut_readonly (typ_box S2))) 
             as [Eq | [[_S1 Eq] | [_S1 Eq]]] by discriminate; apply H; split; eauto
  end : core.

Lemma in_intersection_component_top_or_box_or_readonly_box_merged : forall T,
  in_normal_form T ->
  (forall S, in_intersection_component S (merge_mutability T mut_readonly) -> 
    S = typ_top \/ (exists S1, S = typ_box S1) \/ (exists S1, S = typ_mut mut_readonly (typ_box S1))) ->
  (forall S, 
    in_intersection_component S T ->
    S = typ_top \/ (exists S1, S = typ_box S1) \/ (exists S1, S = typ_mut mut_readonly (typ_box S1))).
Proof with eauto 4; simpl in *; repeat fold merge_mutability in *.
  intros * NormT SMut * IntS.
  destruct IntS as [Primitive IntS]; dependent induction IntS; subst...
  * induction NormT...
    - exfalso...
    - exfalso...
    - exfalso...
    - exfalso...
    - right... right... destruct m...
    - exfalso. apply Primitive...
    - exfalso...
    - exfalso...
  * apply IHIntS... intros S' IntS'.
    destruct IntS' as [PrimitiveS' IntS']... eapply SMut...
  * apply IHIntS... intros S' IntS'.
    destruct IntS' as [PrimitiveS' IntS']... eapply SMut...
Qed.

Lemma in_intersection_component_merged_top_or_box_or_readonly_box : forall T,
  in_normal_form T ->
  (forall S, in_intersection_component S T -> 
    S = typ_top \/ (exists S1, S = typ_box S1) \/ (exists S1, (S = typ_mut mut_readonly (typ_box S1)))) ->
  (forall S, in_intersection_component S (merge_mutability T mut_readonly) -> 
    S = typ_top \/ (exists S1, S = typ_mut mut_readonly (typ_box S1))).
Proof with eauto 4; simpl in *; repeat fold merge_mutability in *.
  intros * NormT IntCompS S IntCompSMut.  
  dependent induction NormT; 
    try solve [inversion IntCompSMut as [Prim Eq]; inversion Eq; eauto]...
  * exfalso...
  * exfalso...
  * exfalso...
  * exfalso...
  * right... destruct m... destruct IntCompSMut as [Prim Eq]...
    inversion Eq...
  * destruct IntCompSMut as [Primitive IntS]...
    unshelve epose proof 
      (in_intersection_all_component_left _ _ _ IntCompS).
    unshelve epose proof 
      (in_intersection_all_component_right _ _ _ IntCompS).

    inversion IntS; subst...
    - exfalso. apply Primitive...
  * exfalso...
  * exfalso...
Qed.

#[export] Hint Extern 6 False => let Bad := fresh "Bad" in 
  match goal with
  | H : forall S', in_intersection_component S' ?T1 -> 
    exists S1, S' = typ_mut mut_readonly (typ_box S1) |- _ =>
    eenough (exists S1, T1 = typ_mut mut_readonly (typ_box S1)) as 
      Bad by (destruct Bad as [? ?]; discriminate); apply H; split; eauto
  end : core.

#[export] Hint Extern 6 False => 
  let Eq := fresh "Eq" in let _S1 := fresh "S1" in
  match goal with
  | H : forall S', in_intersection_component S' ?T1 -> 
    S' = typ_top \/ (exists S2, S' = typ_mut mut_readonly (typ_box S2)) |- _ =>
    eenough (T1 = typ_top \/ 
             (exists S2, T1 = typ_mut mut_readonly (typ_box S2))) 
             as [Eq | [_S1 Eq]] by discriminate; apply H; split; eauto
  end : core.

Lemma merge_mutability_inversion_box_intersection : forall S T,
  ~ (in_intersection (typ_box S) (merge_mutability T mut_readonly)).
Proof with simpl in *; eauto; repeat fold merge_mutability in *.
  intros *.
  intro Int; dependent induction Int;
   try solve [inversion Int; discriminate]...
  eapply merge_mutability_inversion_box...
  unshelve epose proof (merge_mutability_inversion_int T L R _) as [L' [R' Eq]]; subst...
  inversion x; subst...
  unshelve epose proof (merge_mutability_inversion_int T L R _) as [L' [R' Eq]]; subst...
  inversion x; subst...
Qed.

#[export] Hint Resolve merge_mutability_inversion_box_intersection : core.

Lemma merge_mutability_inversion_record_intersection : forall a S T,
  ~ (in_intersection (typ_record a S) (merge_mutability T mut_readonly)).
Proof with simpl in *; eauto; repeat fold merge_mutability in *.
  intros *.
  intro Int; dependent induction Int;
   try solve [inversion Int; discriminate]...
  eapply merge_mutability_inversion_record...
  unshelve epose proof (merge_mutability_inversion_int T L R _) as [L' [R' Eq]]; subst...
  inversion x; subst...
  unshelve epose proof (merge_mutability_inversion_int T L R _) as [L' [R' Eq]]; subst...
  inversion x; subst...
Qed.

#[export] Hint Resolve merge_mutability_inversion_record_intersection : core.

Lemma in_intersection_inversion_merge : forall T T', 
  in_intersection T' (merge_mutability T mut_readonly) ->
  exists M, in_intersection M T /\ T' = merge_mutability M mut_readonly.
Proof with simpl in *; eauto; repeat fold merge_mutability in *.
  intros * IntMerge.
  dependent induction T; inversion IntMerge; subst...
  - destruct (IHT1 T' H1) as [M [IntM Eq]]...
  - destruct (IHT2 T' H1) as [M [IntM Eq]]...
Qed.

Lemma in_intersection_component_inversion_merge : forall T T',
  in_intersection_component T' (merge_mutability T mut_readonly) ->
  exists M, in_intersection_component M T /\ T' = merge_mutability M mut_readonly.
Proof with simpl in *; eauto; repeat fold merge_mutability in *.
  intros * [Prim Int].
  unshelve epose proof (in_intersection_inversion_merge _ _ Int) as [M [IntM Eq]].
  exists M... repeat split...
  intros [L [R EqInt]]; subst...
Qed.


Lemma record_in_intersection_merge_inversion : forall a S T,
  ~ in_intersection (typ_record a S) (merge_mutability T mut_readonly).
Proof with simpl in *; eauto; repeat fold merge_mutability in *.
  intros * Int.
  induction T; inversion Int; try discriminate...
Qed.
#[export] Hint Resolve record_in_intersection_merge_inversion : core.

Lemma in_intersection_record_normal_in_merge : forall T1 a T,
  in_intersection (typ_record a T1) T ->
  in_normal_form T ->
  in_intersection (typ_mut mut_readonly (typ_record a T1))
    (merge_mutability T mut_readonly).
Proof with  simpl in *; eauto; try repeat fold merge_mutability in *; try discriminate.
  intros * Int Norm.
  dependent induction Norm; 
    try solve [simpl in *; inversion Int; subst; try discriminate]...
  - inversion Int; subst...
  - inversion Int; subst...
    inversion H...
Qed.

Lemma in_intersection_record_merge_in_normal : forall T1 a T,
  in_intersection (typ_record a T1) (merge_mutability T mut_readonly) ->
  in_normal_form T ->
  in_intersection (typ_record a T1) T.
Proof with eauto; try repeat fold merge_mutability in *;
  try discriminate.
  intros * Int Norm.
  dependent induction Norm; try solve [inversion Int; eauto; discriminate]...
Qed.

#[export] Hint Resolve in_intersection_record_normal_in_merge : core.
#[export] Hint Resolve in_intersection_record_merge_in_normal : core.



Lemma in_intersection_readonly_record_normal_in_merge : forall T1 a T,
  in_intersection (typ_mut mut_readonly (typ_record a T1)) T ->
  in_normal_form T ->
  in_intersection (typ_mut mut_readonly (typ_record a T1))
    (merge_mutability T mut_readonly).
Proof with eauto; try repeat fold merge_mutability in *;
  try discriminate.
  intros * Int Norm.
  dependent induction Norm; try solve [inversion Int; eauto; discriminate]...
  - simpl; inversion Int...
Qed.

Lemma in_intersection_readonly_record_merge_in_normal : forall T1 a T,
  in_intersection (typ_mut mut_readonly (typ_record a T1))
    (merge_mutability T mut_readonly) ->
  in_normal_form T ->
  in_intersection (typ_record a T1) T \/
  in_intersection (typ_mut mut_readonly (typ_record a T1)) T.
Proof with simpl in *; eauto; try repeat fold merge_mutability in *;
  try discriminate.
  intros * Int Norm.
  dependent induction Norm; try solve [inversion Int; eauto; discriminate]...
  - simpl in *; inversion Int; subst...
    + destruct (IHNorm1 H1)...
    + destruct (IHNorm2 H1)...
  - inversion Int; subst...
    inversion H...
Qed.

#[export] Hint Resolve in_intersection_readonly_record_normal_in_merge : core.
#[export] Hint Resolve in_intersection_readonly_record_merge_in_normal : core.


#[export] Hint Extern 6 False => let Bad := fresh "Bad" in 
  match goal with
  | H : forall S', in_intersection_component S' ?T1 -> 
    exists a S1, S' = typ_mut mut_readonly (typ_record a S1) |- _ =>
    eenough (exists a S1, T1 = typ_mut mut_readonly (typ_record a S1)) as 
      Bad by (destruct Bad as [? [? ?]]; discriminate); apply H; split; eauto
  end : core.

#[export] Hint Extern 6 False => 
  let Eq := fresh "Eq" in let _S1 := fresh "S1" in let _a := fresh "a" in
  match goal with
  | H : forall S', in_intersection_component S' ?T1 -> 
    S' = typ_top \/ (exists a S2, S' = typ_mut mut_readonly (typ_record a S2)) |- _ =>
    eenough (T1 = typ_top \/ 
             (exists a S2, T1 = typ_mut mut_readonly (typ_record a S2))) 
             as [Eq | [_a [_S1 Eq]]] by discriminate; apply H; split; eauto
  end : core.

#[export] Hint Extern 6 False => let Bad := fresh "Bad" in 
match goal with
| H : forall S', in_intersection_component S' ?T1 -> 
  exists a S1, S' = typ_record a S1 |- _ =>
  eenough (exists a S1, T1 = typ_record a S1) as 
    Bad by (destruct Bad as [? [? ?]]; discriminate); apply H; split; eauto
end : core.

#[export] Hint Extern 6 False => 
  let Eq := fresh "Eq" in let _S1 := fresh "S1" in let _a := fresh "a" in
  match goal with
  | H : forall S', in_intersection_component S' ?T1 -> 
    S' = typ_top \/ (exists b S1, S' = typ_record b S1) \/ (exists c S2, S' = typ_mut mut_readonly (typ_record c S2)) |- _ =>
    eenough (T1 = typ_top \/ 
             (exists a S1, T1 = typ_record a S1) \/
             (exists a S2, T1 = typ_mut mut_readonly (typ_record a S2))) 
             as [Eq | [[_a [_S1 Eq]] | [_a [_S1 Eq]]]] by discriminate; apply H; split; eauto
  end : core.

Lemma in_intersection_component_top_or_record_or_readonly_record_merged : forall T,
  in_normal_form T ->
  (forall S, in_intersection_component S (merge_mutability T mut_readonly) -> 
    S = typ_top \/ (exists a S1, S = typ_record a S1) \/ (exists a S1, S = typ_mut mut_readonly (typ_record a S1))) ->
  (forall S, 
    in_intersection_component S T ->
    S = typ_top \/ (exists a S1, S = typ_record a S1) \/ (exists a S1, S = typ_mut mut_readonly (typ_record a S1))).
Proof with eauto 4; simpl in *; repeat fold merge_mutability in *.
  intros * NormT SMut * IntS.
  destruct IntS as [Primitive IntS]; dependent induction IntS; subst...
  * induction NormT...
    - exfalso...
    - exfalso...
    - exfalso...
    - exfalso...
    - exfalso...
    - exfalso...
    - exfalso. apply Primitive...
    - right...
    - right... right... destruct m...
  * apply IHIntS... intros S' IntS'.
    destruct IntS' as [PrimitiveS' IntS']... eapply SMut...
  * apply IHIntS... intros S' IntS'.
    destruct IntS' as [PrimitiveS' IntS']... eapply SMut...
Qed.

Lemma in_intersection_component_merged_top_or_record_or_readonly_record : forall T,
  in_normal_form T ->
  (forall S, in_intersection_component S T -> 
    S = typ_top \/ (exists a S1, S = typ_record a S1) \/ (exists a S1, (S = typ_mut mut_readonly (typ_record a S1)))) ->
  (forall S, in_intersection_component S (merge_mutability T mut_readonly) -> 
    S = typ_top \/ (exists a S1, S = typ_mut mut_readonly (typ_record a S1))).
Proof with eauto 4; simpl in *; repeat fold merge_mutability in *.
  intros * NormT IntCompS S IntCompSMut.  
  dependent induction NormT; 
    try solve [inversion IntCompSMut as [Prim Eq]; inversion Eq; eauto]...
  * exfalso...
  * exfalso...
  * exfalso...
  * exfalso...
  * exfalso...
  * exfalso...
  * destruct IntCompSMut as [Primitive IntS]...
    unshelve epose proof 
      (in_intersection_all_component_left _ _ _ IntCompS).
    unshelve epose proof 
      (in_intersection_all_component_right _ _ _ IntCompS).

    inversion IntS; subst...
    - exfalso. apply Primitive...
  * right... destruct m... destruct IntCompSMut as [Prim Eq]...
    inversion Eq...
Qed.

Lemma in_intersection_component_top_inversion : forall T',
  in_intersection_component T' typ_top ->
  T' = typ_top.
Proof with eauto.
  intros * [Prim Int]...
  dependent induction Int; subst...
Qed.
#[export] Hint Resolve in_intersection_component_top_inversion : core.

Lemma always_has_component : forall T,
  (exists T', in_intersection_component T' T).
Proof with eauto.
  intros.
  induction T; subst...
  + exists typ_top...
  + exists n...
  + exists a...
  + exists (typ_arrow T1 T2)...
  + exists (typ_all T1 T2)...
  + exists (typ_box T)...
  + exists (typ_mut m T)...
  + destruct IHT1 as [T1' [Prim Int]]...
  + exists (typ_record a T)...
Qed.
#[export] Hint Resolve always_has_component : core.
