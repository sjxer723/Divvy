Require Import Basics.
Require Import ZArith.
Require Import Nat.
Require Import List.

Module Sets.

Definition Item := nat.

Definition SET : Type:= list Item.

Definition empty_set : SET:= nil.

Definition single_ton (g: Item) : SET:= cons g nil.

Definition is_empty (s: SET) := (s = nil).

Fixpoint add_item (s: SET) (g: Item) := 
    match s with
    | nil => cons g nil
    | cons n l =>
        if n =? g then s
        else cons n (add_item l g)
    end.

(* Minus s1 s2 = s1 \ s2 *)
Fixpoint minus (s1 s2 : SET) : SET :=
    match s1 with
    | nil => nil
    | h :: t => if (in_dec Nat.eq_dec h s2) then (minus t s2) else (cons h (minus t s2))
end.

Fixpoint delete_item (s: SET) (g: Item) := 
    match s with
    | nil => nil
    | cons n l =>
        if n =? g then delete_item l g
        else cons n (delete_item l g)
    end.


(* Intersect s1 s2 = s1 n s2*)
Fixpoint intersect (s1 s2 : SET) : SET :=
    match s1 with
    | nil => nil
    | h :: t => if (in_dec Nat.eq_dec h s2) then h::(intersect t s2) else (intersect t s2)
end.
(* 
Lemma in_concat : forall (l1 l2 : list Item) (x : Item),
  In x (l1 ++ l2) -> In x l1 \/ In x l2.
Proof.
  induction l1 as [| h t IH].
  - simpl.
    intros H.
    right;auto.
  - simpl.
    intros l2 x [H1 | H2].
    + left;left. apply H1.
    + apply IH in H2.
      destruct H2 as [H3 | H4];tauto.
Qed. *)

(* Lemma in_inter1 : forall (s1 s2 : SET) (x : Item),
  In x s1 -> In x s2 -> In x (intersect s1 s2).
Proof.
  intros s1 s2 x H1 H2.
  unfold intersect.
  apply in_concat.
  exists x.
  split.
  - apply in_elem.
    exact H1.
  - apply in_elem.
    exact H2.
Qed. *)

Definition member (g: Item) (s: SET) : Prop := In g s.

Definition include (s1: SET) (s2: SET): Prop:=
    forall a, (member a s1) -> (member a s2).

Definition is_equal (s1: SET) (s2: SET): Prop:=
    (include s1 s2) /\ (include s2 s2).

(* Union s1 s2 = s1 U s2 *)
Definition union (s1 s2: SET): SET:= s1 ++ s2.

(* Lemma intersect_commutativity: forall s1 s2:SET, is_equal (intersect s1 s2) (intersect s2 s1).
Proof.
    unfold is_equal;intros;split.
    + unfold include;intros.   *)


(* Fixpoint union (s1 s2: SET): SET :=
    match s2 with
    | nil => s1
    | cons n l => union (add_item s1 n) l
    end. *)

(* forall s, ∅ is included by s *) 
Lemma any_set_include_empty: forall s:SET, include empty_set s.
Proof.
    intros;unfold include;intros.
    unfold member in H;contradiction.
Qed.

(* forall s, s is included by s *) 
Lemma self_include_self: forall s:SET, include s s.
Proof.
    intros;unfold include;intros;tauto.
Qed.

(* forall s, s is equal to s *) 
Lemma self_equal_self: forall s:SET, is_equal s s.
Proof.
    intros;unfold is_equal;split;apply self_include_self.
Qed.

(* forall s1, s2, s1 is included by (s1 U s2) *)
Lemma union_include_single: forall s1 s2:SET, include s1 (union s1 s2).
Proof.
    intros;unfold include, union.
    intros;apply in_app_iff;left;tauto.
Qed.

Lemma include_rel_keep_after_new_elem: forall (s1 s2:SET) (g: Item),
    (include s1 s2) -> (include (g::s1) (g::s2)).
Proof.
    intros s1 s2 g H.
    unfold include in *.
    intros x H1.
    simpl in H1.
    destruct H1 as [H1 | H1].
    + left. rewrite H1. reflexivity.
    + right. apply H. exact H1.
Qed.
    

(* forall s1, s2, (s1 \ s2) is included by s1*)
Lemma left_includes_left_minus_right: forall s1 s2:SET, include (minus s1 s2) s1.
Proof.
    intros.
    induction s1;simpl.
    + unfold include;intros a H;tauto.
    + unfold include;intros. destruct (in_dec Nat.eq_dec a s2).
        * unfold member;right. apply IHs1;auto.
        * assert (H1: include (a::minus s1 s2) (a::s1)). 
            {apply include_rel_keep_after_new_elem;auto. } 
        apply H1;auto.
Qed.

(* forall s1, s2, (s1 n s2) is included by s1*)
Lemma left_includes_intersection: forall s1 s2:SET, include (intersect s1 s2) s1.
Proof.
    intros.
    induction s1;simpl.
    + unfold include;intros;tauto.
    + unfold include;intros. destruct (in_dec Nat.eq_dec a s2).
        * assert (H1: include (a::intersect s1 s2) (a::s1)).
            {apply include_rel_keep_after_new_elem;auto. }
        apply H1;auto.
        * right;auto.
Qed.

(* forall s1, s2, (s1 n s2) is included by s2*)
Lemma right_includes_intersection: forall s1 s2:SET, include (intersect s1 s2) s2.
Proof.
    intros.
    induction s1;simpl.
    + apply any_set_include_empty.
    + destruct (in_dec Nat.eq_dec a s2).
        * unfold include;intros a0 H1.
        unfold member in H1. destruct H1.
            ** rewrite H in i;auto.
            ** apply IHs1;apply H.
        * auto.
Qed.

Lemma in_inter : forall (s1 s2 : SET) (x : Item),
  In x (intersect s1 s2) <-> In x s1 /\ In x s2.
Proof.
  intros s1 s2 x.
  split.
  - intros H.
    split.
    + pose (left_includes_intersection s1 s2) as H1.
        unfold include in H1.
        apply H1;auto.
    + pose (right_includes_intersection s1 s2) as H1.
        unfold include in H1.
        apply H1;auto.
  - intros [H1 H2].
    induction s1 as [| h t IH].
    + simpl.
      contradiction.
    + simpl.
      destruct (in_dec Nat.eq_dec h s2) as [H3 | H3].
      * destruct H1 as [H1 | H1].
        ** rewrite H1.
           left;reflexivity.
        ** right.
           apply IH.
           exact H1.
      * apply IH.
        unfold In in H1;destruct H1.
        ** rewrite <- H in H2. contradiction.
        ** auto.
Qed.

(* Commutativity of intersection:
 *  forall s1 s2, (s1 n s2) = (s2 n s1)
*)
Lemma intersect_commutativity: forall (s1 s2 : SET),
  is_equal (intersect s1 s2)  (intersect s2 s1).
Proof.
    intros.
    unfold is_equal, include;split.
    + intros. rewrite in_inter. rewrite in_inter in H;tauto.
    + intros. rewrite in_inter. rewrite in_inter in H;tauto.
Qed.

End Sets.