(* =========================================================== *)
(**
* Considering concurrent regions in the equivalence of semantics for interaction languages.
Erwan Mahe - 2023

This is a reformulation and extension of the previous Coq proof from
#<a href="https://github.com/erwanM974/coq_hibou_label_semantics_equivalence/">Coq proof for the equivalence of three semantics defined on an interaction language</a>#.

** Context

Our aim is to prove the equivalence of two trace semantics of a modeling language for distributed system communication:
- a denotational one, which uses composition with operators on sets of traces
- an operational one, which uses successive concatenation of actions which can be executed in the model

A similar proof can be found in 
#<a href="https://github.com/erwanM974/coq_hibou_label_semantics_equivalence/">Coq proof for the equivalence of three semantics defined on an interaction language</a># 
on a subset of the language.

Here, we consider a co-region "concurrent region" operator which incidentaly covers both interleaving and weak sequencing.
As a result, we remove the "seq" and "par" operators and the associated loops "loopW" and "loopP" and replace them with "coreg" and "loopC".
We reformulate the pruning relation and the semantics so as to rely on fewer predicates (e.g. we got rid of "terminates", "avoids").
**)

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Coq.Vectors.Fin.
Require Import Psatz.
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic. 
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.

(** 
** Signature & Actions

The interaction language that I define depends on a signature that is composed of:
- a set of "lifelines" L, which elements represent the individual sub-systems that can be found in the disctributed system (or some groups of sub-systems via abstraction/refinement)
- a set of "messages" M, which elements represent the individual distinguishable messages that can be exchanged (via asynchronous communication) within (i.e. internally) or without (i.e externally) the distributed system 
Given that I consider finitely many such lifelines and messages, I use finite vectors from "Coq.Vectors.Fin."
to model those sets
**)

Parameter LCard : nat.
Parameter MCard : nat.

Definition L := Fin.t (S LCard).
Definition M := Fin.t (S MCard).


(**
** Preliminaries

This section is dedicated to enoncing some basic types and properties on which the remainder of the proof will be based.
**)

Theorem eq_img: forall {X Y:Type} (f: X->Y) (x y :X), x = y -> f x = f y.
Proof.
intros.
rewrite H. reflexivity.
Qed.

Theorem contraposition : forall p q:Prop, (p->q)->(~q->~p).
Proof. 
intros. intro.
apply H0. apply H.
assumption.
Qed.

(**
*** Lifeline manipulation
We model lifelines as elements of "L".
Below are some basic properties to manipulate lifelines.
**)

Lemma L_not_neq :
  forall (l l':L),  
    (~ (l <> l'))
    -> (l = l').
Proof. 
intros.
pose proof (Fin.eq_dec l l').
destruct H0.
- assumption.
- contradiction.
Qed.

Lemma L_neq_or_not_neq (x y:L) :
  (x <> y) \/ (not(x<>y)).
Proof.
pose proof (Fin.eq_dec x y).
destruct H.
- right. intro. contradiction.
- left. assumption.
Qed.

Lemma L_eqb_neq (l1 l2:L) :
  (Fin.eqb l1 l2) = false <-> l1<>l2.
Proof.
split ; intros.
- pose proof (L_neq_or_not_neq l1 l2). destruct H0.
  + assumption.
  + apply L_not_neq in H0. 
    apply Fin.eqb_eq in H0.
    rewrite H0 in H. pose proof diff_true_false .
    contradiction.
-
Admitted.

Lemma lifeline_neq_symmetry (l1 l2:L) :
  (l1<>l2) <-> (l2<>l1).
Proof.
Admitted.

(**
*** Selection of lifelines
We represent a selection of lifelines in "L" with a function "L->bool".
**)

Lemma coreg_choice (p:L-> bool) (l:L) :
  (p l = true) \/ (p l = false).
Proof.
pose proof (bool_dec (p l) true). destruct H.
- left. assumption.
- right. apply not_true_iff_false. assumption.
Qed.

Theorem coreg_eq (p1 p2:L-> bool) :
  (p1 = p2)
  <-> (forall (l:L), p1 l = p2 l).
Proof.
split ; intros.
- rewrite H. reflexivity.
- 
Admitted.

Lemma coreg_discriminate (p:L-> bool) (l1 l2 : L) :
  ~ (is_true (p l1)) /\ (is_true (p l2)) -> (l1<>l2).
Proof.
intros. destruct H. unfold is_true in *.
pose proof (eq_img p l1 l2).
apply contraposition in H1.
- assumption.
- rewrite H0. assumption.
Qed.


(**
** Actions and traces

We denote by "l!m" the emission of message "m" (element of "M") from lifeline "l" (element of "L").
We denote by "l?m" the reception of message "m" (element of "M") by lifeline "l" (element of "L").
To distinguish between emissions and receptions I encode the kind of action
({!,?}) with an inductive type "ActKind".
**)

Inductive ActKind : Set :=
  |ak_snd:ActKind
  |ak_rcv:ActKind.

(**
I can now define actions with the "Action" type via a cartesian product of types L, ActKind and M.

A utility function "lifeline" returns, for any action, the lifeline on which it occurs.
**)

Definition Action :Set:= L*ActKind*M.

Definition lifeline: Action -> L :=
  fun '(_ as l,_,_) => l.

Lemma exists_action_on_lifeline (l:L) :
  (exists a:Action, l = (lifeline a) ).
Proof.
Admitted.

(**
The "Trace" type is defined as that of lists of actions ("Action" type).
**)

Definition Trace : Type := list Action.


(**
*** Conditional Sequencing
**)

Inductive no_condconf : (L->bool) -> Trace -> L -> Prop :=
| no_condconf_nil  : forall (p:L->bool) (l:L), (no_condconf p nil l)
| no_condconf_cons : forall (p:L->bool) (l:L) (a:Action) (t:Trace),
                        (
                          (no_condconf p t l)
                          /\ (
                                (is_true (p (lifeline a)))
                                \/ ( not ((lifeline a) = l) )
                             )
                        ) -> (no_condconf p (a::t) l).

 

Inductive is_cond_seq : (L -> bool) -> Trace -> Trace -> Trace -> Prop :=
| cond_seq_nil_left   : forall (r :  L -> bool) (t:Trace), 
                              (is_cond_seq r nil t t)
| cond_seq_nil_right  : forall (r :  L -> bool) (t:Trace), 
                              (is_cond_seq r t nil t)
| cond_seq_cons_left  : forall (r :  L -> bool) (t t1 t2:Trace) (a:Action),
                              (is_cond_seq r t1 t2 t) -> (is_cond_seq r (a::t1) t2 (a::t))
| cond_seq_cons_right : forall (r :  L -> bool) (t t1 t2:Trace) (a:Action),
                              (is_cond_seq r t1 t2 t)
                              -> (no_condconf r t1 (lifeline a)) 
                              -> (is_cond_seq r t1 (a::t2) (a::t)).

(**
Some properties of conditional sequencing
**)

Lemma is_cond_seq_nil_prop1 (r:L->bool) (t1 t2: Trace) :
  (is_cond_seq r t1 t2 nil)
  -> ( (t1 = nil) /\ (t2 = nil) ).
Proof.
intros H.
inversion H ; split ; reflexivity.
Qed.

Lemma is_cond_seq_nil_prop2 (r:L->bool) (t1 t2: Trace) :
  (is_cond_seq r nil t1 t2)
  -> (t1 = t2).
Proof.
intros H.
assert (H0:=H).
dependent induction H.
- reflexivity.
- reflexivity.
- assert (t2=t).
  { apply IHis_cond_seq.
    - trivial.
    - assumption.
  }
  destruct H2.
  reflexivity.
Qed.

Lemma is_cond_seq_nil_prop3 (r:L->bool) (t1 t2: Trace) :
  (is_cond_seq r t1 nil t2)
  -> (t1 = t2).
Proof.
intros H.
dependent induction H.
- reflexivity.
- reflexivity.
- assert (t1=t).
  { apply IHis_cond_seq.
    trivial.
  }
  destruct H0.
  reflexivity.
Qed.

Lemma is_cond_seq_existence (r:L->bool) (t1 t2:Trace) :
  exists t:Trace, is_cond_seq r t1 t2 t.
Proof.
dependent induction t1.
- exists t2. apply cond_seq_nil_left.
- specialize IHt1 with (t2:=t2).
  destruct IHt1.
  exists (a::x).
  apply cond_seq_cons_left.
  assumption.
Qed.

Lemma is_cond_seq_assoc (r:L->bool) (t1 t2 t3 tmA tmB t:Trace):
  (is_cond_seq r t1 t2 tmA)
  -> (is_cond_seq r t2 t3 tmB)
  -> ( (is_cond_seq r tmA t3 t) <-> (is_cond_seq r t1 tmB t)).
Proof.
Admitted.

Lemma is_cond_seq_cons_decomposition (r:L->bool) (t1 t2 t:Trace) (a:Action):
  (is_cond_seq r t1 t2 (a :: t))
  -> (
        (exists (t1':Trace), (t1 = a::t1') /\ (is_cond_seq r t1' t2 t))
        \/ (exists (t2':Trace), (t2 = a::t2') /\ (is_cond_seq r t1 t2' t) /\ (no_condconf r t1 (lifeline a)) )
     ).
Proof.
intros.
inversion H.
- destruct H1. symmetry in H3. destruct H3. symmetry in H2. destruct H2.
  symmetry in H0. destruct H0.
  right. exists t. split ; try split ; try assumption.
  + apply cond_seq_nil_left.
  + apply no_condconf_nil.
- destruct H2. symmetry in H3. destruct H3.
  symmetry in H1. destruct H1. symmetry in H0. destruct H0.
  left. exists t. split.
  + reflexivity.
  + apply cond_seq_nil_right.
- destruct H2. symmetry in H1. destruct H1.
  symmetry in H3. destruct H3. symmetry in H0. destruct H0.
  symmetry in H5. destruct H5.
  left. exists t3. split.
  + reflexivity.
  + assumption.
- destruct H4.
  symmetry in H1. destruct H1.
  symmetry in H3. destruct H3. 
  symmetry in H0. destruct H0.
  symmetry in H2. destruct H2.
  right. exists t4.
  split ; try split ; try assumption.
Qed.

(**
*** Verifying that conditional sequencing covers interleaving
**)

Inductive is_interleaving : Trace -> Trace -> Trace -> Prop :=
| interleaving_nil_left   : forall (t:Trace), 
                              (is_interleaving nil t t)
| interleaving_nil_right  : forall (t:Trace), 
                              (is_interleaving t nil t)
| interleaving_cons_left  : forall (t t1 t2:Trace) (a:Action),
                              (is_interleaving t1 t2 t) -> (is_interleaving (a::t1) t2 (a::t))
| interleaving_cons_right : forall (t t1 t2:Trace) (a:Action),
                              (is_interleaving t1 t2 t) -> (is_interleaving t1 (a::t2) (a::t)).

Lemma is_interleaving_nil_prop1 (t1 t2: Trace) :
  (is_interleaving t1 t2 nil)
  -> ( (t1 = nil) /\ (t2 = nil) ).
Proof.
intros H.
inversion H ; split ; reflexivity.
Qed.

Lemma is_interleaving_nil_prop2 (t t2: Trace) :
  (is_interleaving nil t2 t)
  -> (t2 = t).
Proof.
intros H.
dependent induction H.
- reflexivity.
- reflexivity.
- assert (t2=t).
  { apply IHis_interleaving.
    trivial.
  }
  destruct H0.
  reflexivity.
Qed.

Lemma is_interleaving_nil_prop3 (t1 t: Trace) :
  (is_interleaving t1 nil t)
  -> (t1 = t).
Proof.
intros H.
dependent induction H.
- reflexivity.
- reflexivity.
- assert (t1=t).
  { apply IHis_interleaving.
    trivial.
  }
  destruct H0.
  reflexivity.
Qed.

Definition all_lifelines : (L -> bool) := fun l:L => true.

Lemma no_condconf_all_lifelines_charac :
  forall (t : Trace) (l : L), no_condconf all_lifelines t l.
Proof.
intros. induction t.
- apply no_condconf_nil.
- apply no_condconf_cons.
  split.
  + assumption.
  + left. unfold all_lifelines. unfold is_true. reflexivity.
Qed.

Lemma cond_seq_covers_interleaving_1 (t1 t2 t: Trace) :
  (is_interleaving t1 t2 t) -> (is_cond_seq all_lifelines t1 t2 t).
Proof.
intros ; dependent induction t1.
- apply is_interleaving_nil_prop2 in H. destruct H.
  apply cond_seq_nil_left.
- induction H.
  + apply cond_seq_nil_left.
  + apply cond_seq_nil_right.
  + apply cond_seq_cons_left. assumption.
  + apply cond_seq_cons_right.
    * assumption.
    * apply no_condconf_all_lifelines_charac.
Qed.

Lemma cond_seq_covers_interleaving_2 (t1 t2 t: Trace) :
  (is_cond_seq all_lifelines t1 t2 t) -> (is_interleaving t1 t2 t).
Proof.
intros. dependent induction H.
- apply interleaving_nil_left.
- apply interleaving_nil_right.
- apply interleaving_cons_left. apply IHis_cond_seq.
  unfold all_lifelines. reflexivity.
- apply interleaving_cons_right. apply IHis_cond_seq.
  unfold all_lifelines. reflexivity.
Qed.

(**
Here is the proof that a certain parameterization of conditional sequencing is equivalent to the interleaving operator.
**)

Theorem cond_seq_covers_interleaving (t1 t2 t: Trace) :
  (is_interleaving t1 t2 t) <-> (is_cond_seq all_lifelines t1 t2 t).
Proof.
split.
- apply cond_seq_covers_interleaving_1.
- apply cond_seq_covers_interleaving_2.
Qed.


(**
*** Verifying that conditional sequencing covers weak sequencing
**)

Inductive no_conflict : Trace -> L -> Prop :=
| no_conflict_nil  : forall (l:L), (no_conflict nil l)
| no_conflict_cons : forall (l:L) (a:Action) (t:Trace),
                        (
                          (not ((lifeline a) = l))
                          /\ (no_conflict t l)
                        ) -> (no_conflict (a::t) l).

Inductive is_weak_seq : Trace -> Trace -> Trace -> Prop :=
| weak_seq_nil_left   : forall (t:Trace), 
                              (is_weak_seq nil t t)
| weak_seq_nil_right  : forall (t:Trace), 
                              (is_weak_seq t nil t)
| weak_seq_cons_left  : forall (t t1 t2:Trace) (a:Action),
                              (is_weak_seq t1 t2 t) -> (is_weak_seq (a::t1) t2 (a::t))
| weak_seq_cons_right : forall (t t1 t2:Trace) (a:Action),
                              (is_weak_seq t1 t2 t)
                              -> (no_conflict t1 (lifeline a)) 
                              -> (is_weak_seq t1 (a::t2) (a::t)).

Lemma is_weak_seq_nil_prop1 (t1 t2: Trace) :
  (is_weak_seq t1 t2 nil)
  -> ( (t1 = nil) /\ (t2 = nil) ).
Proof.
intros H.
inversion H ; split ; reflexivity.
Qed.

Lemma is_weak_seq_nil_prop2 (t1 t2: Trace) :
  (is_weak_seq nil t1 t2)
  -> (t1 = t2).
Proof.
intros H.
assert (H0:=H).
dependent induction H.
- reflexivity.
- reflexivity.
- assert (t2=t).
  { apply IHis_weak_seq.
    - trivial.
    - assumption.
  }
  destruct H2.
  reflexivity.
Qed.

Lemma is_weak_seq_nil_prop3 (t1 t2: Trace) :
  (is_weak_seq t1 nil t2)
  -> (t1 = t2).
Proof.
intros H.
dependent induction H.
- reflexivity.
- reflexivity.
- assert (t1=t).
  { apply IHis_weak_seq.
    trivial.
  }
  destruct H0.
  reflexivity.
Qed.


Definition no_lifelines : (L -> bool) := fun l:L => false.

Lemma no_condconf_no_lifelines_charac :
  forall (t : Trace) (l : L), (no_condconf no_lifelines t l) <-> (no_conflict t l).
Proof.
intros. split ; intros.
- dependent induction t.
  + apply no_conflict_nil.
  + inversion H.
    symmetry in H1. destruct H1. symmetry in H2. destruct H2.
    symmetry in H3. destruct H3. symmetry in H0. destruct H0.
    destruct H4. destruct H1.
    { unfold no_lifelines in H1. 
      unfold is_true in H1. discriminate.
    }
    { apply no_conflict_cons.
      split.
       - assumption.
       - apply IHt. assumption.
    }
- dependent induction t.
  + apply no_condconf_nil.
  + inversion H.
    symmetry in H1. destruct H1. symmetry in H2. destruct H2.
    symmetry in H0. destruct H0.
    destruct H3. 
    apply no_condconf_cons.
    split.
    * apply IHt. assumption.
    * right. assumption.
Qed.

Lemma cond_seq_covers_weak_seq_1 (t1 t2 t: Trace) :
  (is_weak_seq t1 t2 t) -> (is_cond_seq no_lifelines t1 t2 t).
Proof.
intros ; dependent induction t1.
- apply is_weak_seq_nil_prop2 in H. destruct H.
  apply cond_seq_nil_left.
- induction H.
  + apply cond_seq_nil_left.
  + apply cond_seq_nil_right.
  + apply cond_seq_cons_left. assumption.
  + apply cond_seq_cons_right.
    * assumption.
    * apply no_condconf_no_lifelines_charac. assumption. 
Qed.

Lemma cond_seq_covers_weak_seq_2 (t1 t2 t: Trace) :
  (is_cond_seq no_lifelines t1 t2 t) -> (is_weak_seq t1 t2 t).
Proof.
intros. dependent induction H.
- apply weak_seq_nil_left.
- apply weak_seq_nil_right.
- apply weak_seq_cons_left. apply IHis_cond_seq.
  unfold no_lifelines. reflexivity.
- apply weak_seq_cons_right.
  + apply IHis_cond_seq. unfold no_lifelines. reflexivity.
  + apply no_condconf_no_lifelines_charac. unfold no_lifelines. assumption.
Qed.

(**
Here is the proof that a certain parameterization of conditional sequencing is equivalent to the weak sequencing operator.
**)

Theorem cond_seq_covers_weak_seq (t1 t2 t: Trace) :
  (is_weak_seq t1 t2 t) <-> (is_cond_seq no_lifelines t1 t2 t).
Proof.
split.
- apply cond_seq_covers_weak_seq_1.
- apply cond_seq_covers_weak_seq_2.
Qed.

(**
*** Repetition operators
**)

Inductive merge_strict : 
  list Trace -> Trace -> Prop :=
| merge_strict_nil : (merge_strict nil nil)
| merge_strict_cons : forall (remain:list Trace) (t_first t_rep:Trace),
                    (merge_strict remain t_rep)
                    -> (merge_strict (t_first::remain) (t_first++t_rep)).

Inductive merge_coreg :
  (L -> bool) -> list Trace -> Trace -> Prop :=
| merge_coreg_nil : forall (r:L -> bool), (merge_coreg r nil nil)
| merge_coreg_cons : forall (r:L -> bool) (remain:list Trace) (t_first t_rep t_merge:Trace),
                    (merge_coreg r remain t_rep)
                    -> (is_cond_seq r t_first t_rep t_merge)
                    -> (merge_coreg r (t_first::remain) t_merge).

(**
*** Relations between conditional conflicts and operators
**)

Lemma no_condconf_charac1 (p:L-> bool) (t:Trace) (l:L) :
  ( ((p l) = true) \/ (no_condconf no_lifelines t l) )
  -> (no_condconf p t l).
Proof.
intros.
destruct H ; dependent induction t.
- apply  no_condconf_nil.
- apply no_condconf_cons.
  split.
  + apply IHt. assumption.
  + pose proof (L_neq_or_not_neq (lifeline a) l). destruct H0.
    * right. assumption.
    * apply L_not_neq in H0. destruct H0. left. auto.
- apply  no_condconf_nil.
- apply no_condconf_cons. inversion H.
  symmetry in H1. destruct H1. destruct H4.
  split. 
  + apply IHt. assumption.
  + destruct H4.
    * inversion H4.
    * right. assumption.
Qed.

Lemma no_condconf_charac2 (p:L-> bool) (t:Trace) (l:L) :
  ( ((p l) = false) /\ (no_condconf p t l) )
  -> (no_conflict t l).
Proof.
intros.
destruct H.
dependent induction t.
- apply no_conflict_nil.
- inversion H0. symmetry in H1. destruct H1.
  symmetry in H2. destruct H2.
  symmetry in H4. destruct H4.
  symmetry in H3. destruct H3.
  destruct H5. destruct H2.
  + apply no_conflict_cons. split.
    { apply lifeline_neq_symmetry. apply (coreg_discriminate p).
      split.
      - rewrite H. unfold is_true. apply diff_false_true.
      - assumption.
    }
    { apply IHt ; assumption. }
  + apply no_conflict_cons. split.
    * assumption.
    * apply IHt ; assumption.
Qed.

Definition one_lifeline (l: L) : (L -> bool) := Fin.eqb l .

Definition remove_lf_matches (l:L) (p: L -> bool) : (L -> bool) :=
fun l':L =>
  match p l' with
  | true => false
  | false => Fin.eqb l l'
 end.

Lemma no_condconf_remove_match_charac1 (l:L) (r:L->bool) :
  ((r l) = false) -> (remove_lf_matches l r) = one_lifeline l.
Proof.
intros.
unfold remove_lf_matches. unfold one_lifeline. 
apply coreg_eq. intros.
pose proof (coreg_choice r l0).
destruct H0.
- assert (l<>l0).
  { apply (coreg_discriminate r). split.
    - unfold is_true. apply not_true_iff_false. assumption.
    - unfold is_true. assumption.
  }
  rewrite H0. symmetry. apply L_eqb_neq.
  assumption.
- rewrite H0. reflexivity.
Qed.

Lemma no_condconf_remove_match_charac2 (l:L) (r:L->bool) :
  ((r l) = true) -> (remove_lf_matches l r) = no_lifelines.
Proof.
intros.
unfold remove_lf_matches. unfold no_lifelines.
apply coreg_eq. intros.
pose proof (coreg_choice r l0).
destruct H0.
- rewrite H0. reflexivity.
- rewrite H0.
  apply L_eqb_neq. apply lifeline_neq_symmetry.
  apply (coreg_discriminate r). unfold is_true.
  split.
  + apply not_true_iff_false . assumption.
  + assumption.
Qed.

Lemma no_condconf_concat (p:L->bool)(t1 t2:Trace) (l:L) :
  ( (no_condconf p t1 l) /\ (no_condconf p t2 l) )
  <-> (no_condconf p (t1++t2) l).
Proof.
split ; intros H.
- destruct H.
  dependent induction t1.
  + simpl. assumption.
  + simpl. apply no_condconf_cons.
    split.
    * apply IHt1.
      { inversion H. destruct H5. assumption. }
      { assumption. }
    * inversion H.
      destruct H5. assumption.
- dependent induction t1.
  + simpl in H.
    split.
    * apply no_condconf_nil.
    * assumption.
  + simpl in H.
    inversion H.
    symmetry in H1. destruct H1. symmetry in H0. destruct H0. symmetry in H2. destruct H2. symmetry in H3. destruct H3.
    destruct H4.
    split.
    * apply no_condconf_cons.
      split.
      { apply IHt1 in H0. destruct H0. assumption. }
      { assumption. }
    * apply IHt1 in H0. destruct H0. assumption.
Qed.

Lemma no_conflict_concat (t1 t2:Trace) (l:L) :
  ( (no_conflict t1 l) /\ (no_conflict t2 l) )
  <-> (no_conflict (t1++t2) l).
Proof.
pose proof (no_condconf_no_lifelines_charac).
pose proof (no_condconf_concat no_lifelines t1 t2 l).
split ; intros.
- apply H. apply H0. destruct H1. split ; apply H ; assumption.
- apply H in H1. apply H0 in H1. 
  destruct H1. split ; apply H ; assumption.
Qed. 

Lemma no_condconf_condseq (p r:L->bool) (t1 t2 t :Trace) (l:L) :
  (is_cond_seq r t1 t2 t)
  -> (
       ( (no_condconf p t1 l) /\ (no_condconf p t2 l) )
       <-> (no_condconf p t l)
     ).
Proof.
split ; intros H1.
- destruct H1.
  dependent induction H.
  + assumption.
  + assumption.
  + apply no_condconf_cons.
    inversion H0. destruct H6.
    split.
    * apply IHis_cond_seq ; assumption.
    * assumption.
  + apply no_condconf_cons. 
    inversion H2. destruct H7.
    split.
    * apply IHis_cond_seq ; assumption.
    * assumption.
- dependent induction H.
  + split.
    * apply no_condconf_nil.
    * assumption.
  + split.
    * assumption.
    * apply no_condconf_nil.
  + inversion H1.
    destruct H5. 
    apply IHis_cond_seq in H5.
    destruct H5.
    split.
    * apply no_condconf_cons.
      split ; assumption.
    * assumption.
  + inversion H1.
    destruct H6. 
    apply IHis_cond_seq in H6.
    destruct H6.
    split.
    * assumption.
    * apply no_condconf_cons.
      split ; assumption.
Qed.

Lemma no_conflict_condseq (r:L->bool) (t1 t2 t:Trace) (l:L) :
  (is_cond_seq r t1 t2 t)
  -> (
       ( (no_conflict t1 l) /\ (no_conflict t2 l) )
       <-> (no_conflict t l)
     ).
Proof.
pose proof (no_condconf_no_lifelines_charac).
pose proof (no_condconf_condseq no_lifelines r t1 t2 t l).
split ; intros.
- apply H. apply H0. try split ; try assumption. 
  destruct H2. split ; apply H ; assumption.
- apply H0 in H1. apply H in H2. apply H1 in H2. 
  destruct H2. split ; apply H ; assumption.
Qed. 

Lemma no_condconf_merge_strict (p:L->bool) (subs:list Trace) (t :Trace) (l:L) :
  (merge_strict subs t)
  -> (
       (no_condconf p t l) 
       <-> (forall t0:Trace, (In t0 subs) -> (no_condconf p t0 l))
     ).
Proof.
intros.
split ; intros ; dependent induction subs.
- contradiction.
- inversion H.
  symmetry in H2. destruct H2. destruct H3. destruct H4. 
  apply no_condconf_concat in H0. destruct H0.
  inversion H1.
  + symmetry in H3. destruct H3.  assumption. 
  + apply (IHsubs t_rep) ; assumption.
- inversion H. destruct H2. apply no_condconf_nil.
- inversion H.
  destruct H2. destruct H1. destruct H3.
  apply no_condconf_concat. split.
  + apply H0. simpl. left. reflexivity.
  + apply IHsubs.
    * assumption.
    * intros. apply H0. simpl. right. assumption.
Qed.

Lemma no_conflict_merge_strict (subs:list Trace) (t :Trace) (l:L) :
  (merge_strict subs t)
  -> (
       (no_conflict t l)
       <-> (forall t0:Trace, (In t0 subs) -> (no_conflict t0 l))
     ).
Proof.
pose proof (no_condconf_no_lifelines_charac).
pose proof (no_condconf_merge_strict no_lifelines subs t l).
split ; intros.
- apply H. apply H0.
  + assumption.
  + apply H. assumption.
  + assumption.
- apply H. apply H0 in H1. apply H1. intros.
  apply H. apply H2. assumption.
Qed.

Lemma no_condconf_merge_coreg (p r:L->bool) (subs:list Trace) (t :Trace) (l:L) :
  (merge_coreg r subs t)
  -> (
       (no_condconf p t l) 
       <-> (forall t0:Trace, (In t0 subs) -> (no_condconf p t0 l))
     ).
Proof.
intros.
split ; intros ; dependent induction subs.
- contradiction.
- inversion H.
  symmetry in H4. destruct H4. destruct H2. destruct H3. destruct H6. 
  apply (no_condconf_condseq p r t_first t_rep t_merge l) in H0.
  + destruct H0. inversion H1.
    * destruct H3. assumption.
    * apply (IHsubs t_rep) ; assumption.
  + assumption.
- inversion H. destruct H3. apply no_condconf_nil.
- inversion H.
  symmetry in H3. destruct H3. destruct H2. destruct H1. destruct H5.
  apply (no_condconf_condseq p r t_first t_rep t_merge l).
  + assumption.
  + split.
    * apply H0. simpl. left. reflexivity.
    * apply IHsubs.
      { assumption. }
      { intros. apply H0. simpl. right. assumption. }
Qed.

Lemma no_conflict_merge_coreg (r:L->bool) (subs:list Trace) (t :Trace) (l:L) :
  (merge_coreg r subs t)
  -> (
       (no_conflict t l)
       <-> (forall t0:Trace, (In t0 subs) -> (no_conflict t0 l))
     ).
Proof.
pose proof (no_condconf_no_lifelines_charac).
pose proof (no_condconf_merge_coreg no_lifelines r subs t l).
split ; intros.
- apply H. apply H0.
  + assumption.
  + apply H. assumption.
  + assumption.
- apply H. apply H0 in H1. apply H1. intros.
  apply H. apply H2. assumption.
Qed.

(**
*** Conflicts shortcuts
**)

Lemma conflict_at_head (t:Trace) (a:Action) :
~ no_conflict (a :: t) (lifeline a).
Proof.
Admitted.

Lemma conflict_concat_left (t1 t2:Trace) (l:L) :
~ (no_conflict t1 l) -> ~ no_conflict (t1 ++ t2) l.
Proof.
Admitted.

Lemma conflict_concat_right (t1 t2:Trace) (l:L) :
~ (no_conflict t2 l) -> ~ no_conflict (t1 ++ t2) l.
Proof.
Admitted.

Lemma conflict_cond_seq_left (t1 t2 t:Trace) (p:L->bool) (l:L) :
(is_cond_seq p t1 t2 t) /\ ~ (no_conflict t1 l) -> ~ no_conflict t l.
Proof.
Admitted.

Lemma conflict_cond_seq_right (t1 t2 t:Trace) (p:L->bool) (l:L) :
(is_cond_seq p t1 t2 t) /\ ~ (no_conflict t2 l) -> ~ no_conflict t l.
Proof.
Admitted.

(**
*** Further characterization of iteration with strict
**)

Lemma merge_strict_nil_prop2 (t_merge:Trace) :
  (merge_strict nil t_merge)
  -> (t_merge=nil).
Proof.
intros.
dependent induction t_merge.
- reflexivity.
- inversion H.
Qed.

Lemma merge_strict_existence (subs:list Trace) :
   (exists t:Trace, (merge_strict subs t)).
Proof.
dependent induction subs.
- exists nil. apply merge_strict_nil.
- destruct IHsubs as (tmerge,H).
  exists (a ++ tmerge).
  apply merge_strict_cons ; assumption.
Qed.

Lemma merge_strict_unicity
  (subs:list Trace) (t1 t2:Trace) :
    ( 
      (merge_strict subs t1)
      /\(merge_strict subs t2)
    )->(t1=t2).  
Proof.
dependent induction subs.
- intros. destruct H.
  apply merge_strict_nil_prop2 in H.
  apply merge_strict_nil_prop2 in H0.
  symmetry in H. destruct H.
  symmetry. assumption.
- intros. destruct H.
  inversion H. destruct H1. destruct H2.
  destruct H3.
  inversion H0. symmetry in H1. destruct H1.
  symmetry in H3. destruct H3.
  destruct H2.
  assert (t_rep=t_rep0).
  { apply IHsubs. split ; assumption. }
  destruct H1. reflexivity.
Qed.

Lemma merge_strict_operational_characterization
  (t0 t t_merge_remain:Trace) (remain:list Trace) (a:Action) :
(merge_strict ((a :: t0) :: remain) (a :: t))
-> (merge_strict remain t_merge_remain)
-> (t = t0 ++ t_merge_remain).
Proof.
intros.
dependent induction remain generalizing t t_merge_remain t0.
- apply merge_strict_nil_prop2 in H0.
  symmetry in H0. destruct H0.
  inversion H.
  apply merge_strict_nil_prop2 in H1.
  rewrite H1. reflexivity.
- inversion H.
  destruct H4. 
  symmetry in H1. destruct H1.
  symmetry in H3. destruct H3.
  assert (t_rep=t_merge_remain).
  { apply (merge_strict_unicity (a::remain)).
    split ; assumption.
  }  
  destruct H1. reflexivity.
Qed.

Lemma merge_strict_skip_empty (subs : list Trace) (t:Trace) :
  (merge_strict (nil :: subs) t)
  -> (merge_strict subs t).
Proof.
Admitted.

Lemma merge_strict_cons_existence (subs:list Trace) (t:Trace) (a:Action):
  (merge_strict subs (a :: t))
  -> ( exists (t0:Trace) (prev succ:list Trace),
        (subs = prev ++ ( (a::t0) :: succ))
        /\ (forall (tprev:Trace), In tprev prev -> tprev = nil)
        /\ (merge_strict ( (a::t0)::succ ) (a::t))
     ).
Proof.
Admitted.

(**
*** Further characterization of iteration with coreg
**)

Lemma merge_coreg_nil_prop2 (r:L->bool) (t_merge:Trace) :
  (merge_coreg r nil t_merge)
  -> (t_merge=nil).
Proof.
intros.
dependent induction t_merge.
- reflexivity.
- inversion H.
Qed.

Lemma merge_coreg_existence (r:L->bool) (subs:list Trace) :
   (exists t:Trace, (merge_coreg r subs t)).
Proof.
dependent induction subs.
- exists nil. apply merge_coreg_nil.
- destruct IHsubs as (tmerge,H).
  pose proof (is_cond_seq_existence r a tmerge).
  destruct H0 as (t,H0).
  exists t.
  apply (merge_coreg_cons r subs a tmerge t) ; assumption.
Qed.

Lemma merge_coreg_add_left (r:L->bool) (subs:list Trace) (t1 t:Trace) (a:Action):
  (merge_coreg r (t1 :: subs) t)
  -> (merge_coreg r ((a::t1) :: subs) (a::t)).
Proof.
Admitted.

Lemma merge_coreg_reorder_prop1 (r:L->bool) (sub1 sub3 : list Trace) (t2 t : Trace) (a:Action):
  (merge_coreg r (sub1 ++ (t2::sub3)) t)
  -> (forall t1:Trace, (In t1 sub1) -> (no_condconf r t1 (lifeline a)))
  -> (merge_coreg r (sub1 ++ ((a::t2)::sub3)) (a::t)).
Proof.
intros.
dependent induction sub1.
- simpl in *.
  apply merge_coreg_add_left. assumption.
- simpl in *. inversion H.
  destruct H1. symmetry in H3. destruct H3.
  symmetry in H5. destruct H5. symmetry in H2. destruct H2.
  apply (merge_coreg_cons r (sub1 ++ (a0::t2)::sub3) t_first (a0::t_rep)).
  + apply IHsub1.
    * assumption.
    * intros. apply H0. right. assumption.
  + apply cond_seq_cons_right.
    * assumption.
    * apply H0. simpl. left. reflexivity.
Qed.

Lemma merge_coreg_bi_assoc (r:L->bool) (sub1 sub2 : list Trace) (t1 t2 t : Trace):
  (merge_coreg r sub1 t1)
  -> (merge_coreg r sub2 t2)
  -> (is_cond_seq r t1 t2 t)
  -> (merge_coreg r (sub1++sub2) t).
Proof.
intros.
dependent induction H generalizing sub2 t2 t.
- simpl.
  apply is_cond_seq_nil_prop2 in H1.
  destruct H1. assumption.
- pose proof (is_cond_seq_existence r t_rep t2).
  destruct H3 as (t3,H3).
  apply (merge_coreg_cons r (remain++sub2) t_first t3 t).
  + apply (IHmerge_coreg sub2 t2 t3).
    * assumption.
    * assumption.
  + apply (is_cond_seq_assoc r t_first t_rep t2 t_merge) ; assumption.
Qed.

Lemma merge_coreg_sandwich (r:L->bool) (sub1 sub3 : list Trace) (t1 t2 t3 tm t : Trace):
  (merge_coreg r sub1 t1)
  -> (merge_coreg r sub3 t3)
  -> (is_cond_seq r t2 t3 tm)
  -> (is_cond_seq r t1 tm t)
  -> (merge_coreg r (sub1 ++ t2 :: sub3) t).
Proof.
intros.
apply (merge_coreg_bi_assoc r sub1 (t2::sub3) t1 tm).
- assumption.
- apply (merge_coreg_cons r sub3 t2 t3 tm).
  + assumption.
  + assumption.
- assumption.
Qed.

Lemma merge_coreg_cons_existence (r:L->bool) (subs:list Trace) (t:Trace) (a:Action):
  (merge_coreg r subs (a :: t))
  -> ( exists (t0:Trace) (prev succ:list Trace),
        (subs = prev ++ ( (a::t0) :: succ))
        /\ (forall (tprev:Trace), In tprev prev -> no_condconf r tprev (lifeline a))
        /\ (merge_coreg r ( prev ++ (t0::succ) ) t)
     ).
Proof.
Admitted.

Lemma merge_coreg_recompose (r:L->bool) (prev succ:list Trace) (t t0 tprev tsucc tright : Trace):
  (merge_coreg r prev tprev)
  -> (is_cond_seq r t0 tsucc tright)
  -> (merge_coreg r succ tsucc)
  -> (merge_coreg r (prev ++ (t0::succ)) t)
  -> (is_cond_seq r tprev tright t).
Proof.
Admitted.




(**
** Syntax of the interaction language
**)

Inductive Interaction : Set := 
  |interaction_empty:Interaction 
  |interaction_act:Action->Interaction
  |interaction_strict:Interaction->Interaction->Interaction
  |interaction_alt:Interaction->Interaction->Interaction
  |interaction_loopS:Interaction->Interaction
  |interaction_coreg:(L -> bool)->Interaction->Interaction->Interaction
  |interaction_loopC:(L -> bool)->Interaction->Interaction.
  
 
(**
** Denotational Semantics
**)

Fixpoint sem_de (i : Interaction) : (Trace -> Prop) :=
match i with
|interaction_empty          => fun t:Trace => 
                                  (t = nil)
|(interaction_act a)        => fun t:Trace => 
                                  (t = a :: nil)
|(interaction_strict i1 i2) => fun t:Trace => 
                                  (  exists (t1 t2:Trace), 
                                      (sem_de i1 t1) /\ (sem_de i2 t2) /\ (t = t1 ++ t2)
                                  )
|(interaction_alt i1 i2)    => fun t:Trace => 
                                  ( (sem_de i1 t) \/ (sem_de i2 t) )
|(interaction_loopS i1)   => fun t:Trace => 
                                  exists (subs:list Trace),
                                    (forall (t0:Trace), (In t0 subs) -> (sem_de i1 t0) )
                                    /\ (merge_strict subs t) 
|(interaction_coreg r i1 i2)    => fun t:Trace => 
                                  exists (t1 t2:Trace), 
                                    (sem_de i1 t1) /\ (sem_de i2 t2) /\ (is_cond_seq r t1 t2 t)
|(interaction_loopC r i1)   => fun t:Trace => 
                                  exists (subs:list Trace),
                                    (forall (t0:Trace), (In t0 subs) -> (sem_de i1 t0) )
                                    /\ (merge_coreg r subs t) 
end. 

Lemma loopS_accepts_nil (i : Interaction) :
  sem_de (interaction_loopS i) nil.
Proof.
simpl. exists nil. split ; intros.
- inversion H.
- apply merge_strict_nil.
Qed.

Lemma loopC_accepts_nil (i : Interaction) (r : L->bool) :
  sem_de (interaction_loopC r i) nil.
Proof.
simpl. exists nil. split ; intros.
- inversion H.
- apply merge_coreg_nil.
Qed.


(**
** Pruning
**)

Inductive cannot_prune : Interaction -> (L -> bool) -> Prop :=
| cannot_prune_act : forall (a:Action) (p : L -> bool), 
                       (is_true (p (lifeline a)))
                         -> (cannot_prune (interaction_act a) p)
| cannot_prune_alt : forall (i1 i2:Interaction) (p : L -> bool),
                       ( (cannot_prune i1 p) /\ (cannot_prune i2 p) )
                         -> (cannot_prune (interaction_alt i1 i2) p)
| cannot_prune_strict : forall (i1 i2:Interaction) (p : L -> bool),
                       ( (cannot_prune i1 p) \/ (cannot_prune i2 p) )
                         -> (cannot_prune (interaction_strict i1 i2) p)
| cannot_prune_coreg : forall (r:L->bool) (i1 i2:Interaction) (p : L -> bool),
                       ( (cannot_prune i1 p) \/ (cannot_prune i2 p) )
                         -> (cannot_prune (interaction_coreg r i1 i2) p)
.

Inductive prunes_into : Interaction -> (L -> bool) -> Interaction -> Prop :=
| prune_empty  : forall (p : L -> bool), 
                   (prunes_into interaction_empty p interaction_empty)
| prune_act    : forall (a:Action) (p : L -> bool), 
                   (not (is_true (p (lifeline a)))) 
                     -> (prunes_into (interaction_act a) p (interaction_act a))
| prune_alt_both : forall (i1 i2 i1' i2':Interaction) (p : L -> bool),
                     (prunes_into i1 p i1')
                     ->(prunes_into i2 p i2')
                     -> (prunes_into (interaction_alt i1 i2) p (interaction_alt i1' i2'))
| prune_alt_left : forall (i1 i2 i1':Interaction) (p : L -> bool),
                     (cannot_prune i2 p)
                     ->(prunes_into i1 p i1')
                     ->(prunes_into (interaction_alt i1 i2) p i1')
| prune_alt_right : forall (i1 i2 i2':Interaction) (p : L -> bool),
                     (cannot_prune i1 p)
                     ->(prunes_into i2 p i2')
                     ->(prunes_into (interaction_alt i1 i2) p i2')
| prune_strict  : forall (i1 i2 i1' i2':Interaction) (p : L -> bool),
                (prunes_into i1 p i1')
                ->(prunes_into i2 p i2')
                  -> (prunes_into (interaction_strict i1 i2) p (interaction_strict i1' i2'))
| prune_coreg  : forall (r : L -> bool) (i1 i2 i1' i2':Interaction) (p : L -> bool),
                (prunes_into i1 p i1')
                ->(prunes_into i2 p i2')
                  -> (prunes_into (interaction_coreg r i1 i2) p (interaction_coreg r i1' i2'))
| prune_loopS_select : forall (i1 i1':Interaction) (p : L -> bool),
                     (prunes_into i1 p i1')
                     -> (prunes_into (interaction_loopS i1) p (interaction_loopS i1'))
| prune_loopS_elim : forall (i1:Interaction) (p : L -> bool),
                     (cannot_prune i1 p)
                     -> (prunes_into (interaction_loopS i1) p interaction_empty)
| prune_loopC_select : forall (r : L -> bool) (i1 i1':Interaction) (p : L -> bool),
                     (prunes_into i1 p i1')
                     -> (prunes_into (interaction_loopC r i1) p (interaction_loopC r i1'))
| prune_loopC_elim : forall (r : L -> bool) (i1:Interaction) (p : L -> bool),
                     (cannot_prune i1 p)
                     -> (prunes_into (interaction_loopC r i1) p interaction_empty)
.

(**
*** Some initials lemmas on the prune and cannot prune relations
**)

Lemma cannot_prune_contradicts_prune (i i' : Interaction) (p : L -> bool) :
  (cannot_prune i p) /\ (prunes_into i p i') -> False.
Proof.
intros ; destruct H.
dependent induction i.
- inversion H.
- inversion H. inversion H0. contradiction.
- inversion H. inversion H0.
  destruct H4.
  + apply (IHi1 i1' p) ; assumption.
  + apply (IHi2 i2' p) ; assumption.
- inversion H.
  destruct H4. symmetry in H1. destruct H1. symmetry in H3. destruct H3. symmetry in H2. destruct H2.
  inversion H0.
  + apply (IHi1 i1' p) ; assumption.
  + apply (IHi1 i' p) ; assumption.
  + apply (IHi2 i' p) ; assumption.
- inversion H.
- inversion H.
  destruct H1. symmetry in H3. destruct H3. symmetry in H4. destruct H4. symmetry in H2. destruct H2.
  destruct H5.
  + inversion H0.
    apply (IHi1 i1' p) ; assumption.
  + inversion H0. 
    apply (IHi2 i2' p) ; assumption.
- inversion H.
Qed.

Lemma can_prune_or_cannot_prune (i : Interaction) (p : L -> bool) :
  (cannot_prune i p) \/ (exists (i':Interaction), prunes_into i p i').
Proof.
dependent induction i.
- right. exists interaction_empty. apply prune_empty.
- pose proof (coreg_choice p (lifeline a)).
  destruct H.
  + left. apply cannot_prune_act.
    unfold is_true. assumption.
  + right. exists (interaction_act a).
    apply prune_act. unfold is_true.
    apply not_true_iff_false. assumption.
- specialize IHi1 with (p:=p). specialize IHi2 with (p:=p).
  destruct IHi1.
  + left. apply cannot_prune_strict. left. assumption.
  + destruct IHi2.
    * left. apply cannot_prune_strict. right. assumption.
    * right. destruct H as (i1',H1).
      destruct H0 as (i2',H2).
      exists (interaction_strict i1' i2').
      apply prune_strict ; assumption.
- specialize IHi1 with (p:=p). specialize IHi2 with (p:=p).
  destruct IHi1.
  + destruct IHi2.
    * left. apply cannot_prune_alt. split ; assumption.
    * right. destruct H0 as (i2',H2).
      exists i2'. apply prune_alt_right ; assumption.
  + destruct H as (i1',H1).
    right.
    destruct IHi2.
    * exists i1'. apply prune_alt_left ; assumption.
    * destruct H as (i2',H2).
      exists (interaction_alt i1' i2').
      apply prune_alt_both ; assumption.
- right. specialize IHi with (p:=p).
  destruct IHi.
  + exists interaction_empty.
    apply prune_loopS_elim. assumption.
  + destruct H as (i', H).
    exists (interaction_loopS i').
    apply prune_loopS_select. assumption.
- specialize IHi1 with (p:=p). specialize IHi2 with (p:=p).
  destruct IHi1.
  + left. apply cannot_prune_coreg. left. assumption.
  + destruct IHi2.
    * left. apply cannot_prune_coreg. right. assumption.
    * right. destruct H as (i1',H1).
      destruct H0 as (i2',H2).
      exists (interaction_coreg b i1' i2').
      apply prune_coreg ; assumption.
- right. specialize IHi with (p:=p).
  destruct IHi.
  + exists interaction_empty.
    apply prune_loopC_elim. assumption.
  + destruct H as (i', H).
    exists (interaction_loopC b i').
    apply prune_loopC_select. assumption.
Qed.

Lemma can_always_prune_loopS (i : Interaction) (p:L->bool) :
  exists i' : Interaction, prunes_into (interaction_loopS i) p i'.
Proof.
pose proof (can_prune_or_cannot_prune i p) as Hp1.
destruct Hp1.
- exists interaction_empty.
  apply prune_loopS_elim ; assumption.
- destruct H as (i1',H).
  exists (interaction_loopS i1').
  apply prune_loopS_select ; assumption.
Qed.

Lemma can_always_prune_loopC (i : Interaction) (p r:L->bool) :
  exists i' : Interaction, prunes_into (interaction_loopC r i) p i'.
Proof.
pose proof (can_prune_or_cannot_prune i p) as Hp1.
destruct Hp1.
- exists interaction_empty.
  apply prune_loopC_elim ; assumption.
- destruct H as (i1',H).
  exists (interaction_loopC r i1').
  apply prune_loopC_select ; assumption.
Qed.


(**
Below we characterize the cannot prune relation operator w.r.t. the denotational style semantics
**)

Theorem cannot_prune_characterisation_with_sem_de (i : Interaction) (p: L -> bool) :
  (cannot_prune i p) 
  -> (
        forall (t:Trace),
            (sem_de i t)
            -> (exists (l:L), (is_true (p l)) /\ ~ (no_conflict t l) )
     ).
Proof.
intros. 
dependent induction i.
- inversion H.
- inversion H. inversion H0. exists (lifeline a).
  split.
  + assumption.
  + apply conflict_at_head. 
- specialize IHi1 with (p:=p).
  specialize IHi2 with (p:=p).
  inversion H. destruct H4.
  + inversion H0 as (t1,H5). destruct H5 as (t2,H5).
    destruct H5. destruct H6. symmetry in H7. destruct H7.
    assert (exists l : L, is_true (p l) /\ ~ no_conflict t1 l).
    { apply IHi1 ; assumption. }
    destruct H7 as (l,H7). destruct H7. exists l.
    split.
    * assumption.
    * apply conflict_concat_left. assumption.
  + inversion H0 as (t1,H5). destruct H5 as (t2,H5).
    destruct H5. destruct H6. symmetry in H7. destruct H7.
    assert (exists l : L, is_true (p l) /\ ~ no_conflict t2 l).
    { apply IHi2 ; assumption. }
    destruct H7 as (l,H7). destruct H7. exists l.
    split.
    * assumption.
    * apply conflict_concat_right. assumption.
- specialize IHi1 with (p:=p).
  specialize IHi2 with (p:=p).
  inversion H. destruct H4.
  inversion H0.
  + assert (exists l : L, is_true (p l) /\ ~ no_conflict t l).
    { apply IHi1 ; assumption. }
    destruct H7 as (l,H7). destruct H7. exists l.
    split ; assumption.
  + assert (exists l : L, is_true (p l) /\ ~ no_conflict t l).
    { apply IHi2 ; assumption. }
    destruct H7 as (l,H7). destruct H7. exists l.
    split ; assumption.
- pose proof (can_always_prune_loopS i p).
  destruct H1 as (i',Hprune).
  exfalso. apply (cannot_prune_contradicts_prune (interaction_loopS i) i' p).
  split ; assumption.
- specialize IHi1 with (p:=p).
  specialize IHi2 with (p:=p).
  inversion H. destruct H5.
  + inversion H0 as (t1,H6). destruct H6 as (t2,H6).
    destruct H6. destruct H7.
    assert (exists l : L, is_true (p l) /\ ~ no_conflict t1 l).
    { apply IHi1 ; assumption. }
    destruct H9 as (l,H9). destruct H9. exists l.
    split.
    * assumption.
    * apply (conflict_cond_seq_left t1 t2 t b l). split ; assumption.
  + inversion H0 as (t1,H6). destruct H6 as (t2,H6).
    destruct H6. destruct H7. 
    assert (exists l : L, is_true (p l) /\ ~ no_conflict t2 l).
    { apply IHi2 ; assumption. }
    destruct H9 as (l,H9). destruct H9. exists l.
    split.
    * assumption.
    * apply (conflict_cond_seq_right t1 t2 t b l). split ; assumption.
- pose proof (can_always_prune_loopC i p b).
  destruct H1 as (i',Hprune).
  exfalso. apply (cannot_prune_contradicts_prune (interaction_loopC b i) i' p).
  split ; assumption.
Qed.


(**
*** Some more advanced lemmas on the prune relation
**)

Lemma prune_all_equiv_accept_nil_1 (i i' : Interaction) :
  (prunes_into i all_lifelines i')
  -> (sem_de i nil).
Proof.
intros.
dependent induction i.
  + simpl. reflexivity.
  + inversion H. unfold all_lifelines in H1. 
    unfold is_true in H1. contradiction.
  + inversion H. simpl. exists nil. exists nil.
    split ; try split.
    * apply (IHi1 i1'). assumption.
    * apply (IHi2 i2'). assumption.
    * simpl. reflexivity.
  + inversion H.
    * simpl. left. apply (IHi1 i1'). assumption.
    * simpl. left. apply (IHi1 i1'). destruct H4. assumption.
    * simpl. right. apply (IHi2 i2'). destruct H4. assumption.
  + apply loopS_accepts_nil.
  + inversion H. simpl. exists nil. exists nil.
    split ; try split.
    * apply (IHi1 i1'). assumption.
    * apply (IHi2 i2'). assumption.
    * apply cond_seq_nil_left.
  + apply loopC_accepts_nil.
Qed.

Lemma prune_all_equiv_accept_nil_2 (i : Interaction) :
  (sem_de i nil)
  -> (exists (i':Interaction), (prunes_into i all_lifelines i')).
Proof.
intros.
- dependent induction i.
  + exists interaction_empty. apply prune_empty. 
  + inversion H.
  + inversion H as (t1,H1). destruct H1 as (t2,H1).
    destruct H1. destruct H1. symmetry in H2. apply app_eq_nil in H2. 
    destruct H2. symmetry in H2. destruct H2.
    symmetry in H3. destruct H3.
    apply IHi1 in H0. destruct H0 as (i1',H1p).
    apply IHi2 in H1. destruct H1 as (i2',H2p).
    exists (interaction_strict i1' i2'). apply prune_strict ; assumption.
  + pose proof (can_prune_or_cannot_prune i1 all_lifelines) as Hp1.
    pose proof (can_prune_or_cannot_prune i2 all_lifelines) as Hp2. 
    destruct Hp1 ; destruct Hp2 ; inversion H.
    * apply IHi1 in H2. destruct H2. exfalso.
      apply (cannot_prune_contradicts_prune i1 x all_lifelines). split ; assumption.
    * apply IHi2 in H2. destruct H2. exfalso.
      apply (cannot_prune_contradicts_prune i2 x all_lifelines). split ; assumption.
    * destruct H1 as (i2',H1). exists i2'.
      apply prune_alt_right ; assumption.
    * destruct H1 as (i2',H1). exists i2'.
      apply prune_alt_right ; assumption.
    * destruct H0 as (i1',H0). exists i1'.
      apply prune_alt_left ; assumption.
    * apply IHi2 in H2. destruct H2. exfalso.
      apply (cannot_prune_contradicts_prune i2 x all_lifelines). split ; assumption.
    * destruct H0 as (i1',Hp1). destruct H1 as (i2',Hp2).
      exists (interaction_alt i1' i2').
      apply prune_alt_both ; assumption.
    * destruct H0 as (i1',Hp1). destruct H1 as (i2',Hp2).
      exists (interaction_alt i1' i2').
      apply prune_alt_both ; assumption.
  + apply can_always_prune_loopS.
  + inversion H as (t1,H1). destruct H1 as (t2,H1).
    destruct H1. destruct H1. apply is_cond_seq_nil_prop1 in H2. 
    destruct H2. symmetry in H2. destruct H2.
    symmetry in H3. destruct H3.
    apply IHi1 in H0. destruct H0 as (i1',H1p).
    apply IHi2 in H1. destruct H1 as (i2',H2p).
    exists (interaction_coreg b i1' i2'). apply prune_coreg ; assumption.
  + apply can_always_prune_loopC.
Qed.

Lemma prune_characterisation_with_sem_de_1 (i i': Interaction) (p :L -> bool) (t:Trace) :
  (prunes_into i p i') /\ (sem_de i' t)
    -> (sem_de i t).
Proof.
intros H.
destruct H.
dependent induction i.
- inversion H. destruct H3.
  inversion H0. simpl. reflexivity.
- inversion H. destruct H4.
  inversion H0. simpl. reflexivity.
- inversion H.
  symmetry in H1. destruct H1.
  symmetry in H4. destruct H4.
  symmetry in H2. destruct H2.
  destruct H5.
  simpl.
  inversion H0 as (t1,Hd).
  destruct Hd as (t2,Hd).
  destruct Hd as (Hi1,Hd).
  destruct Hd as (Hi2,Hconc).
  exists t1. exists t2.
  split.
  { apply (IHi1 i1' p) ; assumption. }
  { split.
    { apply (IHi2 i2' p) ; assumption. }
    { assumption. }
  }
- inversion H.
  + symmetry in H1. destruct H1.
    symmetry in H4. destruct H4.
    symmetry in H2. destruct H2.
    simpl. destruct H5.
    inversion H0.
    { left. apply (IHi1 i1' p) ; assumption. }
    { right. apply (IHi2 i2' p) ; assumption. }
  + symmetry in H1. destruct H1.
    symmetry in H4. destruct H4.
    symmetry in H2. destruct H2.
    destruct H5. simpl. left. apply (IHi1 i1' p) ; assumption.
  + symmetry in H1. destruct H1.
    symmetry in H4. destruct H4.
    symmetry in H2. destruct H2.
    destruct H5. simpl. right. apply (IHi2 i2' p) ; assumption.
- inversion H.
  + symmetry in H1. destruct H1.
    symmetry in H3. destruct H3. destruct H4.
    simpl in H0. destruct H0 as (subs,H0).
    destruct H0 as (H0,HMerge).
    simpl. exists subs. split.
    { intros. apply H0 in H1. apply (IHi i1' p t0) ; assumption. }
    { assumption. }
  + symmetry in H1. destruct H1.
    symmetry in H3. destruct H3. destruct H4.
    simpl in H0. symmetry in H0. destruct H0.
    simpl. exists nil. split.
    { simpl. intros. contradiction. }
    { apply merge_strict_nil. } 
- inversion H. destruct H1.
  symmetry in H2. destruct H2.
  symmetry in H4. destruct H4.
  symmetry in H3. destruct H3.
  destruct H5. simpl in H0.
  destruct H0 as (t1,H0).
  destruct H0 as (t2,H0).
  destruct H0. destruct H1.
  simpl. exists t1. exists t2.
  split.
  + apply (IHi1 i1' p t1) ; assumption.
  + split.
    { apply (IHi2 i2' p t2) ; assumption. }
    { assumption. }
- inversion H.
  + symmetry in H1. destruct H1.
    symmetry in H2. destruct H2. 
    symmetry in H3. destruct H3. destruct H4.
    simpl in H0. destruct H0 as (subs,H0).
    destruct H0 as (H0,HMerge).
    simpl. exists subs. split.
    { intros. apply H0 in H1. apply (IHi i1' p t0) ; assumption. }
    { assumption. }
  + symmetry in H1. destruct H1.
    symmetry in H2. destruct H2. 
    symmetry in H3. destruct H3. destruct H4.
    simpl in H0. symmetry in H0. destruct H0.
    simpl. exists nil. split.
    { simpl. intros. contradiction. }
    { apply merge_coreg_nil. }
Qed. 

Lemma prune_characterisation_with_sem_de_2 (i i': Interaction) (p :L -> bool) (t:Trace) :
  (prunes_into i p i') /\ (sem_de i t) /\ (forall (l:L), (is_true (p l)) -> (no_conflict t l) )
    -> (sem_de i' t).
Proof.
intros H.
destruct H. destruct H0.
dependent induction i.
- inversion H0. inversion H. simpl. reflexivity.
- inversion H0. inversion H. simpl. reflexivity.
- inversion H0 as (t1,H3). destruct H3 as (t2,H3). destruct H3. destruct H3.
  symmetry in H4. destruct H4.
  inversion H.  simpl.
  exists t1. exists t2. 
  split ; try split.
  + apply (IHi1 i1' p t1) ; try assumption. 
    intros. assert (no_conflict (t1 ++ t2) l).
    { apply H1. assumption. } 
    apply no_conflict_concat in H11. destruct H11. assumption.
  + apply (IHi2 i2' p t2) ; try assumption. 
    intros. assert (no_conflict (t1 ++ t2) l).
    { apply H1. assumption. } 
    apply no_conflict_concat in H11. destruct H11. assumption.
  + reflexivity.
- inversion H.
  + simpl. inversion H0.
    * left. apply (IHi1 i1' p t) ; assumption.
    * right. apply (IHi2 i2' p t) ; assumption.
  + destruct H6. inversion H0.
    * apply (IHi1 i1' p t) ; assumption.
    * assert (exists (l:L), (is_true (p l)) /\ ~ (no_conflict t l) ). 
      { apply (cannot_prune_characterisation_with_sem_de i2 p) ; assumption. }
      destruct H8 as (l,H8). destruct H8. apply H1 in H8. contradiction.
  + destruct H6. inversion H0.
    * assert (exists (l:L), (is_true (p l)) /\ ~ (no_conflict t l) ). 
      { apply (cannot_prune_characterisation_with_sem_de i1 p) ; assumption. }
      destruct H8 as (l,H8). destruct H8. apply H1 in H8. contradiction.
    * apply (IHi2 i2' p t) ; assumption.
- inversion H0 as (subs,Hmerge).
  destruct Hmerge as (Hsubs,Hmerge).
  inversion H.
  + destruct H5. simpl. exists subs.
    split.
    { intros. apply (IHi i1' p t0).
      - assumption.
      - apply Hsubs. assumption.
      - intros. apply (no_conflict_merge_strict subs t l).
        + assumption.
        + apply H1. assumption.
        + assumption.
    }
    { assumption. } 
  + destruct H5. destruct H2. symmetry in H4. destruct H4. 
    induction subs.
    * apply merge_strict_nil_prop2 in Hmerge.
      symmetry in Hmerge. destruct Hmerge.
      simpl. reflexivity.
    * assert (sem_de i1 a).
      {  apply Hsubs. simpl. left. reflexivity. }
      assert (forall t : Trace, sem_de i1 t -> exists l : L, is_true (p l) /\ ~ no_conflict t l).
      { apply (cannot_prune_characterisation_with_sem_de i1 p). assumption. }
      specialize H4 with (t:=a). apply H4 in H2.
      destruct H2 as (l,H2). destruct H2. 
      assert (no_conflict a l).
      { pose proof (no_conflict_merge_strict (a::subs) t l) .
        apply H6 in Hmerge. assert (no_conflict t l).
        { apply H1. assumption. }
        rewrite Hmerge in H7.
        specialize H7 with (t0:=a). apply H7. simpl. left. reflexivity.
      }
      contradiction.
- inversion H0 as (t1,H3). destruct H3 as (t2,H3). destruct H3. destruct H3.
  inversion H.  simpl.
  exists t1. exists t2. 
  split ; try split.
  + apply (IHi1 i1' p t1) ; try assumption.  
    intros. assert (no_conflict t l). 
    { apply H1. assumption. } 
    assert (no_conflict t1 l /\ no_conflict t2 l <-> no_conflict t l).
    { apply (no_conflict_condseq b t1 t2 t l). assumption. }
    symmetry in H14. rewrite H14 in H13. destruct H13. assumption.
  + apply (IHi2 i2' p t2) ; try assumption.  
    intros. assert (no_conflict t l). 
    { apply H1. assumption. } 
    assert (no_conflict t1 l /\ no_conflict t2 l <-> no_conflict t l).
    { apply (no_conflict_condseq b t1 t2 t l). assumption. }
    symmetry in H14. rewrite H14 in H13. destruct H13. assumption.
  + assumption.
- inversion H0 as (subs,Hmerge).
  destruct Hmerge as (Hsubs,Hmerge).
  inversion H.
  + destruct H5. simpl. exists subs.
    split.
    { intros. apply (IHi i1' p t0).
      - assumption.
      - apply Hsubs. assumption.
      - intros. apply (no_conflict_merge_coreg b subs t l).
        + assumption.
        + apply H1. assumption.
        + assumption.
    }
    { assumption. } 
  + destruct H5. destruct H2. destruct H4. symmetry in H3. destruct H3. 
    induction subs.
    * apply merge_coreg_nil_prop2 in Hmerge.
      symmetry in Hmerge. destruct Hmerge.
      simpl. reflexivity.
    * assert (sem_de i1 a).
      {  apply Hsubs. simpl. left. reflexivity. }
      assert (forall t : Trace, sem_de i1 t -> exists l : L, is_true (p l) /\ ~ no_conflict t l).
      { apply (cannot_prune_characterisation_with_sem_de i1 p). assumption. }
      specialize H3 with (t:=a). apply H3 in H2.
      destruct H2 as (l,H2). destruct H2. 
      assert (no_conflict a l).
      { pose proof (no_conflict_merge_coreg r (a::subs) t l) .
        apply H5 in Hmerge. assert (no_conflict t l).
        { apply H1. assumption. }
        rewrite Hmerge in H7.
        specialize H7 with (t0:=a). apply H7. simpl. left. reflexivity.
      }
      contradiction.
Qed.

Lemma prune_removes_conflicts (i i':Interaction) (p:L->bool) (t:Trace) :
  (prunes_into i p i') 
  -> (sem_de i' t)
  -> ( forall l : L, is_true (p l) -> no_conflict t l ).
Proof.
intros H1 H2.
dependent induction H1 generalizing t.
- inversion H2. 
  intros. apply no_conflict_nil.
- inversion H2.
  intros.
  apply no_conflict_cons.
  split.
  + apply (coreg_discriminate p). split ; assumption.
  + apply no_conflict_nil.
- simpl in H2.
  destruct H2.
  + apply IHprunes_into1. assumption.
  + apply IHprunes_into2. assumption.
- apply IHprunes_into. assumption.
- apply IHprunes_into. assumption.
- simpl in H2.
  destruct H2 as (t1,H).
  destruct H as (t2,H).
  destruct H as (Hi1,H).
  destruct H as (Hi2,H).
  symmetry in H. destruct H. intros.
  apply no_conflict_concat.
  split.
  + apply IHprunes_into1 ; assumption.
  + apply IHprunes_into2 ; assumption.
- simpl in H2.
  destruct H2 as (t1,H).
  destruct H as (t2,H).
  destruct H as (Hi1,H).
  destruct H as (Hi2,H). intros.
  pose proof (no_conflict_condseq r t1 t2 t l).
  apply H1 in H. apply H.
  split.
  + apply IHprunes_into1 ; assumption.
  + apply IHprunes_into2 ; assumption.
- simpl in H2.
  destruct H2 as (subs,H2).
  destruct H2. intros.
  apply (no_conflict_merge_strict subs t l).
  + assumption.
  + intros t0 Ht0.
    apply IHprunes_into.
    * apply H. assumption.
    * assumption.
- simpl in *. symmetry in H2. destruct H2. intros.
  apply no_conflict_nil.
- simpl in H2.
  destruct H2 as (subs,H2).
  destruct H2. intros.
  apply (no_conflict_merge_coreg r subs t l).
  + assumption.
  + intros t0 Ht0.
    apply IHprunes_into.
    * apply H. assumption.
    * assumption.
- simpl in *. symmetry in H2. destruct H2. intros.
  apply no_conflict_nil.
Qed.


(**
Below we characterize the pruning operator w.r.t. the denotational style semantics
**)

Theorem prune_characterisation_with_sem_de (i i': Interaction) (p :L -> bool) :
  (prunes_into i p i')
  -> (
         forall (t:Trace),
           (sem_de i' t) <-> (
                               (sem_de i t) 
                               /\ (forall (l:L), (is_true (p l)) -> (no_conflict t l) )
                             )
     ).
Proof.
intros. split.
- intros. split.
  + apply (prune_characterisation_with_sem_de_1 i i' p t).  
    split ; assumption.
  + apply (prune_removes_conflicts i i') ; assumption.
- intros. destruct H0.
  apply (prune_characterisation_with_sem_de_2 i i' p t).
  split ; try split ; try assumption.
Qed.

(**
*** Others
**)

Lemma no_condconf_implies_coreg_prunable
  (i: Interaction) (r:L->bool) (l:L) (t:Trace) :
    (sem_de i t)
    -> (no_condconf r t l)
    -> exists (i':Interaction), 
	     (prunes_into i (remove_lf_matches l r) i').
Proof.
Admitted.

Lemma filter_loopC_preserves_prev (b:L->bool) (i1 i0':Interaction) (l:L) (prev:list Trace) (tprev:Trace) :
  ( forall tin : Trace, In tin prev -> (sem_de i1 tin) /\ (no_condconf b tin l) )
  -> (merge_coreg b prev tprev)
  -> (prunes_into (interaction_loopC b i1) (remove_lf_matches l b) i0')
  -> (sem_de i0' tprev).
Proof.
Admitted.




(**
** Execution relation
**)

Inductive executes_into : Interaction -> Action -> Interaction -> Prop :=
|execute_at_leaf : forall (a:Action), 
                 (executes_into (interaction_act a) a interaction_empty)
|execute_left_alt     : forall (a:Action) (i1 i2 i1' : Interaction),
                           (executes_into i1 a i1') 
                              -> (executes_into (interaction_alt i1 i2) a i1')
|execute_right_alt    : forall (a:Action) (i1 i2 i2' : Interaction),
                           (executes_into i2 a i2') 
                              -> (executes_into (interaction_alt i1 i2) a i2')
|execute_left_strict  : forall (a:Action) (i1 i2 i1' : Interaction),
                          (executes_into i1 a i1') 
                             -> (executes_into 
                                       (interaction_strict i1 i2)
                                       a
                                       (interaction_strict i1' i2)
                                )
|execute_right_strict : forall (a:Action) (i1 i1' i2 i2' : Interaction),
                          (executes_into i2 a i2')
                          -> (prunes_into i1 all_lifelines i1')
                          -> (executes_into (interaction_strict i1 i2) a i2')
|execute_left_coreg     : forall (r:L->bool) (a:Action) (i1 i2 i1' : Interaction),
                          (executes_into i1 a i1') 
                             -> (executes_into 
                                       (interaction_coreg r i1 i2)
                                       a
                                       (interaction_coreg r i1' i2)
                                )
|execute_right_coreg    : forall (r:L->bool) (a:Action) (i1 i2 i1' i2' : Interaction),
                          (executes_into i2 a i2')
                          -> (prunes_into i1 (remove_lf_matches (lifeline a) r) i1')
                          -> (executes_into 
                                      (interaction_coreg r i1 i2)
                                      a 
                                      (interaction_coreg r i1' i2')
                             )
|execute_loopS : forall (a:Action) (i1 i1' : Interaction),
                          (executes_into i1 a i1') 
                             -> (executes_into 
                                       (interaction_loopS i1)
                                       a
                                       (interaction_strict i1' (interaction_loopS i1))
                                )
|execute_loopC    : forall (r:L->bool) (a:Action) (i1 i1' i0': Interaction),
                          (executes_into i1 a i1')
                          -> (prunes_into (interaction_loopC r i1) (remove_lf_matches (lifeline a) r) i0')
                             -> (executes_into 
                                       (interaction_loopC r i1)
                                       a
                                       (interaction_coreg r i0' (interaction_coreg r i1' (interaction_loopC r i1)))
                                )
.

(**
*** Characterisation w.r.t. the denotational semantics
**)

Lemma execution_characterisation_with_sem_de_1 (i i': Interaction) (a:Action) (t:Trace) :
  (executes_into i a i') 
  -> (sem_de i' t)
  -> (sem_de i (a::t) ).
Proof.
intros H1 H2. 
dependent induction H1 generalizing t.
- simpl. inversion H2. reflexivity.
- simpl. left.
  apply IHexecutes_into.
  assumption.
- simpl. right.
  apply IHexecutes_into.
  assumption.
- simpl in *.
  destruct H2 as (t1,H).
  destruct H as (t2,H).
  destruct H as (Hi1,H).
  destruct H as (Hi2,H).
  exists (a::t1). exists t2.
  split.
  + apply IHexecutes_into ; assumption.
  + split.
    { assumption. }
    { simpl. rewrite H. reflexivity. } 
- simpl in *.
  exists nil. exists (a::t).
  simpl. split.
  + apply (prune_all_equiv_accept_nil_1 i1 i1'). 
    assumption.
  + split.
    { apply (IHexecutes_into t). assumption. }
    { reflexivity. }
- simpl in *.
  destruct H2 as (t1,H).
  destruct H as (t2,H).
  destruct H as (Hi1,H).
  destruct H as (Hi2,H).
  exists (a::t1). exists t2.
  split.
  + apply IHexecutes_into ; assumption.
  + split.
    { assumption. }
    { simpl. apply cond_seq_cons_left. assumption. }
- simpl in *.
  destruct H2 as (t1,H2).
  destruct H2 as (t2,H2).
  destruct H2 as (Hi1,H2).
  destruct H2 as (Hi2,H2).
  exists t1. exists (a::t2). 
  split ; try split.
  + apply (prune_characterisation_with_sem_de_1 i1 i1' (remove_lf_matches (lifeline a) r)).
    split ; assumption.
  + apply IHexecutes_into. assumption.
  + apply cond_seq_cons_right.
    { assumption. }
    { apply no_condconf_charac1.
      pose proof (coreg_choice r (lifeline a)). destruct H0.
      - left. assumption.
      - right.
        assert ((remove_lf_matches (lifeline a) r) = one_lifeline (lifeline a)).
        { apply no_condconf_remove_match_charac1. assumption. }
        symmetry in H3. destruct H3.
        apply no_condconf_no_lifelines_charac.
        apply (prune_removes_conflicts i1 i1' (one_lifeline (lifeline a)) t1).
        + assumption.
        + assumption.
        + unfold one_lifeline. apply Fin.eqb_eq. reflexivity.
    }
- simpl in H2.
  destruct H2 as (t1,H).
  destruct H as (t2,H).
  destruct H as (Hi1,H).
  destruct H as (H,Hconc).
  destruct H as (subs,H).
  destruct H as (Hin,Hrep).
  simpl.
  exists ((a::t1)::subs).
  split.
  + intros t0 Ht0.
    inversion Ht0.
    * destruct H. apply IHexecutes_into. assumption.
    * apply Hin. assumption.
  + symmetry in Hconc. destruct Hconc. 
    apply (merge_strict_cons subs (a::t1) t2).
    assumption.
- simpl in H2.
  destruct H2 as (t0,H3).
  destruct H3 as (tm,H3).
  destruct H3 as (Hi0,H3).
  destruct H3 as (H3,Hmer).
  destruct H3 as (t1,H3).
  destruct H3 as (t2,H3).
  destruct H3 as (Hi1,H3).
  destruct H3 as (H3,Hmer2).
  destruct H3 as (subs,H3).
  destruct H3 as (Hin,Hrep).
  inversion H.
  { symmetry in H0. destruct H0.
    symmetry in H2. destruct H2.
    symmetry in H3. destruct H3.
    destruct H4.
    simpl in Hi0.
    destruct Hi0 as (sub0,Hi0).
    destruct Hi0 as (H0A,H0B).
    simpl.
    exists (sub0 ++ (a::t1)::subs).
    split.
    - intros t3 Ht3.
      apply in_app_or in Ht3.
      destruct Ht3.
      + apply H0A in H0.
        apply (prune_characterisation_with_sem_de_1 i1 i1'0 (remove_lf_matches (lifeline a) r) t3).
        split ; assumption.
      + simpl in H0. destruct H0.
        * destruct H0. apply IHexecutes_into. assumption.
        * apply Hin. assumption.
    - apply merge_coreg_reorder_prop1.
      + apply (merge_coreg_sandwich r sub0 subs t0 t1 t2 tm) ; assumption.
      + intros. apply no_condconf_charac1.
        pose proof (coreg_choice r (lifeline a)). destruct H2.
        * left. assumption.
        * right.
          apply no_condconf_no_lifelines_charac.
          apply (prune_removes_conflicts i1 i1'0 (remove_lf_matches (lifeline a) r) t3).
          { assumption. }
          { apply H0A. assumption. }
          { assert ( (remove_lf_matches (lifeline a) r) = (one_lifeline (lifeline a)) ).
            { apply (no_condconf_remove_match_charac1 (lifeline a) r). assumption. }
            rewrite H3. unfold one_lifeline. apply Fin.eqb_eq. reflexivity.
          }
  }
  { destruct H4.
    symmetry in H0. destruct H0.
    symmetry in H3. destruct H3.
    symmetry in H2. destruct H2. simpl in *.
    symmetry in Hi0. destruct Hi0.
    exists ((a::t1)::subs).
    split.
    - intros. simpl in H0. destruct H0.
      + destruct H0. apply IHexecutes_into.
        assumption.
      + apply Hin. assumption.
    - apply (merge_coreg_cons r subs (a::t1) t2 (a::t)).
      + assumption.
      + apply cond_seq_cons_left. apply is_cond_seq_nil_prop2 in Hmer. destruct Hmer. assumption.
  }
Qed.

Lemma execution_characterisation_with_sem_de_2 
  (i : Interaction) (a:Action) (t:Trace) :
  (sem_de i (a::t))
    -> (exists (i':Interaction), (executes_into i a i') /\ (sem_de i' t) ).
Proof.
intros H.
dependent induction i. 
- simpl in H. inversion H.
- simpl in H. inversion H.
  symmetry in H1. destruct H1.
  symmetry in H2. destruct H2.
  exists interaction_empty. simpl.
  split.
  + apply execute_at_leaf.
  + reflexivity.
- simpl in H.
  destruct H as (t1,H).
  destruct H as (t2,H).
  destruct H.
  destruct H0.
  destruct t1.
  + simpl in H1. destruct H1.
    apply IHi2 in H0.
    destruct H0 as (i2',H0).
    destruct H0.
    exists i2'.
    split.
    * apply prune_all_equiv_accept_nil_2 in H.
      destruct H as (i1',Hi1).
      apply (execute_right_strict a i1 i1') ; assumption.
    * assumption.
  + inversion H1. 
    destruct H3.
    simpl in H1.
    apply IHi1 in H. 
    destruct H as (i1',H). 
    exists (interaction_strict i1' i2).
    destruct H.
    split.
    * apply execute_left_strict. assumption.
    * simpl. exists t1. exists t2.
      split.
      { assumption. }
      { split. 
        - assumption. 
        - reflexivity.
      }
- simpl in H. destruct H.
  + apply IHi1 in H.
    destruct H as (i1',H).
    destruct H.
    exists i1'.
    split.
    * apply execute_left_alt. assumption.
    * assumption.
  + apply IHi2 in H.
    destruct H as (i2',H).
    destruct H.
    exists i2'.
    split.
    * apply execute_right_alt. assumption.
    * assumption.
- simpl in H.
  destruct H as (subs,H).
  destruct H as (Hin,Hrep).
  assert (Hr:=Hrep).
  apply (merge_strict_cons_existence subs t a) in Hrep.
  destruct Hrep as (t0,H).
  destruct H as (prev,H).
  destruct H as (succ,H).
  destruct H. destruct H0.
  assert (exists i' : Interaction, executes_into i a i' /\ sem_de i' t0).
  { apply IHi. apply Hin. rewrite H. 
    apply in_or_app. right. simpl. left. reflexivity.
  }
  destruct H2 as (i',Hi). destruct Hi.
  exists (interaction_strict i' (interaction_loopS i)).
  split.
  + apply execute_loopS. assumption.
  + simpl. exists t0.
    pose proof (merge_strict_existence succ).
    destruct H4 as (tmsucc,Hmsucc).
    exists tmsucc.
    split.
    { assumption. }
    { split.
      - exists succ. split.
        + intros. apply Hin. rewrite H. 
          apply in_or_app. right. 
          simpl. right. assumption.
        + assumption.
      - apply (merge_strict_operational_characterization t0 t tmsucc succ a).
        + assumption.
        + assumption.
    }
- simpl in H.
  destruct H as (t1,H).
  destruct H as (t2,H).
  destruct H.
  destruct H0.
  apply is_cond_seq_cons_decomposition in H1.
  destruct H1.
  + destruct H1 as (t1',H1). destruct H1.
    symmetry in H1. destruct H1.
    apply IHi1 in H.
    destruct H as (i1',H).
    destruct H as (Hi1x,Hi1s).
    exists (interaction_coreg b i1' i2).
    split.
    * apply execute_left_coreg. assumption.
    * simpl. exists t1'. exists t2.
      split ; try split ; try assumption.
  + destruct H1 as (t2',H1). destruct H1. destruct H2.
    symmetry in H1. destruct H1.
    apply IHi2 in H0.
    destruct H0 as (i2',H0).
    destruct H0 as (Hi2x,Hi2s).
    assert (exists i1' : Interaction, prunes_into i1 (remove_lf_matches (lifeline a) b) i1').
    { apply (no_condconf_implies_coreg_prunable i1 b (lifeline a) t1) ; assumption. }
    destruct H0 as (i1',Hi1p).
    exists (interaction_coreg b i1' i2').
    split.
    { apply execute_right_coreg ; assumption. }
    { simpl. exists t1. exists t2'.
      split ; try split ; try assumption.
      pose proof (coreg_choice b (lifeline a)).
      destruct H0.
      - apply (no_condconf_remove_match_charac2 (lifeline a) b) in H0. symmetry in H0. destruct H0.
        apply (prune_characterisation_with_sem_de_2 i1 i1' no_lifelines).
        split ; try split ; try assumption.
        intros. unfold no_lifelines in H0. unfold is_true in H0. discriminate.
      - assert (Hb:=H0). apply (no_condconf_remove_match_charac1 (lifeline a) b) in H0. symmetry in H0. destruct H0.
        apply (prune_characterisation_with_sem_de_2 i1 i1' (one_lifeline (lifeline a))).
        split ; try split ; try assumption.
        intros. unfold one_lifeline in H0. apply Fin.eqb_eq in H0. destruct H0.
        apply (no_condconf_charac2 b t1). split ; assumption.
    }
- simpl in H.
  destruct H as (subs,H).
  destruct H as (Hin,Hrep).
  assert (Hr:=Hrep).
  apply (merge_coreg_cons_existence b subs t a) in Hrep.
  destruct Hrep as (t0,H).
  destruct H as (prev,H).
  destruct H as (succ,H).
  destruct H. destruct H0.
  assert (exists i' : Interaction, executes_into i a i' /\ sem_de i' t0).
  { apply IHi. apply Hin. rewrite H. 
    apply in_or_app. right. simpl. left. reflexivity.
  }
  destruct H2 as (i',Hi). destruct Hi.
  pose proof (can_always_prune_loopC i (remove_lf_matches (lifeline a) b) b).
  destruct H4 as (i0',H4).
  exists (interaction_coreg b i0' (interaction_coreg b i' (interaction_loopC b i))).
  split.
  + apply execute_loopC ; assumption.
  + simpl.
    pose proof (merge_coreg_existence b prev).
    destruct H5 as (tprev,H5).
    exists tprev.
    pose proof (merge_coreg_existence b succ).
    destruct H6 as (tsucc,H6).
    pose proof (is_cond_seq_existence b t0 tsucc).
    destruct H7 as (tright,H7).
    exists tright.
    split ; try split.
    { apply (filter_loopC_preserves_prev b i i0' (lifeline a) prev tprev).
      - intros. split.
        + apply Hin. rewrite H. apply in_app_iff. left. assumption.
        + apply H0. assumption.
      - assumption.
      - assumption.
    }
    { exists t0. exists tsucc.
      split.
      - assumption.
      - split.
        + exists succ. split.
          * intros. apply Hin.
            rewrite H. apply in_app_iff.
            right. apply in_cons . assumption.
          * assumption.
        + assumption.
    }
    { apply (merge_coreg_recompose b prev succ t t0 tprev tsucc tright) ; assumption. }
Qed.

(**
** The operational style semantics
**)

Inductive sem_op : Interaction -> Trace -> Prop :=
 | sem_op_empty  : forall (i i':Interaction),
                      (prunes_into i all_lifelines i')
                      -> (sem_op i nil)
 | sem_op_event : forall (i i':Interaction) (a:Action) (t:Trace),
                      (executes_into i a i')
                      -> (sem_op i' t)
                      -> (sem_op i (a::t) ).



Theorem op_implies_de (i : Interaction) (t : Trace) :
  (sem_op i t) -> (sem_de i t).
Proof.
intros H.
dependent induction t generalizing i.
- inversion H.
  apply (prune_all_equiv_accept_nil_1 i i').
  assumption.
- inversion H. 
  symmetry in H1. destruct H1.
  symmetry in H0. destruct H0.
  symmetry in H2. destruct H2.
  apply (execution_characterisation_with_sem_de_1 i i' a t).
  + assumption.
  + apply (IHt i').
    assumption.
Qed.

Theorem de_implies_op (i : Interaction) (t : Trace) :
  (sem_de i t) -> (sem_op i t).
Proof.
intros H.
dependent induction t generalizing i. 
- apply prune_all_equiv_accept_nil_2 in H. 
  destruct H as (i',H). apply (sem_op_empty i i').
  assumption.
- apply execution_characterisation_with_sem_de_2 in H.
  destruct H as (i',H).
  destruct H.
  apply (sem_op_event i i').
  + assumption.
  + apply IHt. assumption.
Qed.

(**
Finally we porove the equivalence of both semantics,
as stated by the "sem_equivalence_de_op" Theorem.
**)
  
Theorem sem_equivalence_de_op (i : Interaction) (t : Trace) :
  (sem_op i t) <-> (sem_de i t).
Proof.
split.
- apply op_implies_de.
- apply de_implies_op.
Qed.








