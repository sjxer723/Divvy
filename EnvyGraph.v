Require Import Basics.
Require Import ZArith.
Require Import List.
Require Import Permutation.
Require Import Lia.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Logic.Classical.
Require Import Divvy.SetDomain.
Import ListNotations. 
Import Sets.

(******************************************************************************)
(*                  Basic Definitions of fair division problem                *)
(******************************************************************************)

Definition Agent :Type := nat.

(* Alloc records the current allocation *)
Definition Alloc :Type := (Agent -> SET).

(* Envy-free up one item for two bundles *)
Definition ef1_for_two_bundles (v: (SET -> SET -> Prop)) : SET -> SET -> Prop:=
  fun X Y => (v Y X) \/ (exists g, (In g Y) /\ (v (delete_item Y g) X)).

(* Envy-free up to one item*)
Definition ef1 (n: nat) (A: Alloc) (valuation: Agent -> (SET -> SET -> Prop)):Prop :=
  forall i j, (i < n) -> (j < n) -> ef1_for_two_bundles (valuation i) (A i) (A j).

Class valuation_assumptions (valuation: Agent -> (SET -> SET -> Prop)) :Prop:=
{
  v_total_order:  forall i s1 s2, (valuation i s1 s2) \/ (valuation i s2 s1);
  v_reflexivity_prop: forall i X, valuation i X X;
  v_transitivity_prop:  forall i X Y Z, 
    (valuation i X Y) -> (valuation i Y Z) -> (valuation i X Z);
  v_monotonicity_prop: forall i X Y, (include X Y) -> valuation i X Y;
}.

Class ef1_properties (valuation: Agent -> (SET -> SET -> Prop)) :Prop:=
{
  ef1_reflexivity_prop: forall i X, ef1_for_two_bundles (valuation i) X X;
  ef1_monotonicity_prop1: forall i X Y, (include X Y) -> ef1_for_two_bundles (valuation i) Y X; 
  ef1_monotonicity_prop2: forall i X Y Z, (valuation i X Z) -> 
    (ef1_for_two_bundles (valuation i) X Y) -> (ef1_for_two_bundles (valuation i) Z Y);   
}.

Lemma valuation_assumptions_to_ef_properties (valuation: Agent -> (SET -> SET -> Prop))
  (H: valuation_assumptions valuation): ef1_properties valuation.
Proof.
  intros. split;intros.
  + unfold ef1_for_two_bundles. left. apply v_reflexivity_prop.
  + unfold ef1_for_two_bundles. left. apply v_monotonicity_prop;auto.
  + unfold ef1_for_two_bundles. destruct H1.
    * left. eapply v_transitivity_prop;[apply H1| apply H0].
    * right. destruct H1. exists x. destruct H1. split;auto.
      eapply v_transitivity_prop;[apply H2|auto].
Qed.

(* Definition of envy-graph *)
Class envy_graph :Type :=
{ 
  n: nat; (* number of agents *)
  edges: (Agent -> Agent -> Prop);
}.

(* From the current allocation to a envy-graph *)
Definition current_envy_graph (n: nat) (A: Alloc) (valuation: Agent -> (SET -> SET -> Prop)) :envy_graph:=
{| n:= n; edges := (fun i j => ~ (valuation i (A j) (A i))); |}.

(* A cycle is a map from index to agent.                  *)
(* e.g., {0 !-> Agent 1; 1 !-> Agent 2; 2 !-> Agent 3}    *)
(*       represents the cycle 1 -> 2 -> 3 -> 1            *)
Definition Cycle :Type:= nat -> Agent.

Fixpoint cycle_to_list (cycle: Cycle) (length: nat): list Agent:=
  match length with 
  | 0 => []
  | S n => (cycle n) :: (cycle_to_list cycle n)
  end.

Lemma correctness_of_cycle_to_list: forall (cycle:Cycle) (length: nat) (a: Agent),
  (In a (cycle_to_list cycle length)) <-> (exists i, (i < length) /\ (cycle i = a)).
Proof.
  intros;split.
  + intro H.
    induction length as [| n IH].
    * simpl in H. contradiction.
    * simpl in H. destruct H as [H_eq | H_in].
      ** exists n. split.
        -- lia. 
        -- assumption.
      ** apply IH in H_in. destruct H_in as [i [H_lt H_eq]].
        exists i. split.
        -- lia.
        -- assumption.
  + intro H. destruct H as [i [H_lt H_eq]].
    induction length as [| n IH].
    * exfalso. apply (Nat.nlt_0_r i). auto.
    * simpl. simpl in H_lt. destruct (i =? n) eqn:H_i_eq_n.
      ** rewrite Nat.eqb_eq in H_i_eq_n. rewrite H_i_eq_n in H_eq. left;auto.
      ** rewrite Nat.eqb_neq in H_i_eq_n. right. apply IH. lia.
Qed.

Definition mod_add_one (i: Agent) (n: nat):= 
  if (S i =? n) then 0 else S i.

Lemma ub_of_mod_add_one:
  forall i n, (i < n) -> (mod_add_one i n < n).
Proof.
  intros. destruct (S i =? n0) eqn:E.
  + unfold mod_add_one. simpl. rewrite Nat.eqb_eq in E. rewrite <- E.
    rewrite Nat.eqb_refl. lia.
  + rewrite Nat.eqb_neq in E. unfold mod_add_one.
    rewrite <- Nat.eqb_neq in E.
    rewrite E. apply Nat.le_neq;split.
    * apply Nat.lt_succ_r. lia.
    * apply Nat.eqb_neq. auto. 
Qed.

Fixpoint agent_index (cycle: Cycle) (length: nat): Agent -> nat:=
  fun a =>
  match length with
  | 0 => length
  | S n => if a =? (cycle n) then n else (agent_index cycle n a)
  end.

Class is_valid_cycle `{G: envy_graph} (length: nat) (cycle: Cycle) :Prop :=
{
    positive_length: 0 < length;
    diff_elements: forall i j, (i <> j) -> (cycle i <> cycle j);
    in_bound: forall i, (i < length) -> (cycle i) < n;
    finite_cycle: 
        forall i, (i < length) -> edges (cycle i) (cycle (mod_add_one i length));
}.

Lemma agent_index_bound: forall c len a, (0 < len) -> (agent_index c len a < len).
Proof.
  intros. induction len as [| n IH].
  - inversion H.
  - simpl. destruct (a =? c n).
    + apply Nat.lt_succ_diag_r.
    + destruct (n =? 0) eqn:E. 
      * rewrite Nat.eqb_eq in E. rewrite E. simpl. lia.
      * rewrite Nat.eqb_neq in E. assert(n > 0). { lia. }
        apply IH in H0. lia.
Qed.

Lemma correctness_of_agent_index0 (cycle:Cycle) (length: nat) (a: Agent)
  (H_cycle_diff_elem: forall i j, (i <> j) -> (cycle i <> cycle j)):
  (exists i, (i < length) /\ (cycle i = a)) ->
  cycle (agent_index cycle length a) = a.
Proof.
  intros. destruct H as [i [IHi_leq IHia]].
  induction length.
  + lia.
  + simpl. destruct (i =? length) eqn:E.
  * rewrite Nat.eqb_eq in E. rewrite E in IHia.
    destruct (a =? cycle length) eqn:H_a_cycle.
    ++ auto.
    ++ rewrite Nat.eqb_neq in H_a_cycle. lia. 
  * assert(Hi_leq_len: i < length).
    { rewrite Nat.eqb_neq in E. lia. }
    pose proof IHlength Hi_leq_len.
    destruct (a =? cycle length) eqn:H_a_cycle_length.
    ** rewrite <- IHia.
      pose proof H_cycle_diff_elem length i.
      assert(cycle length <> cycle i). { lia. }
      rewrite Nat.eqb_eq in H_a_cycle_length.
      lia.
    ** apply IHlength. auto.
Qed.

Lemma correctness_of_agent_index1 (cycle:Cycle) (length: nat) (a: Agent)
  (H_cycle_diff_elem: forall i j, (i <> j) -> (cycle i <> cycle j)):
  (In a (cycle_to_list cycle length)) ->
  cycle (agent_index cycle length a) = a.
Proof.
  intros.
  apply correctness_of_agent_index0;auto.
  apply correctness_of_cycle_to_list;auto.
Qed.

Lemma correctness_of_agent_index2 (cycle:Cycle) (length: nat) (a: Agent) (i: nat)
  (H_cycle_diff_elem: forall i j, (i <> j) -> (cycle i <> cycle j)):
  ((i < length) /\ (cycle i = a)) ->
  (agent_index cycle length a) = i.
Proof.
  intros.
  pose proof Nat.eq_dec (agent_index cycle length a) i. 
  destruct H0;auto.
  pose proof correctness_of_agent_index0 cycle length a H_cycle_diff_elem.
  assert (cycle (agent_index cycle length a) = a).
  { apply H0. exists i. auto. }
  exfalso.
  eapply (H_cycle_diff_elem i (agent_index cycle length a));lia.
Qed.

Definition next_agent_along_cycle {G: envy_graph} (cycle:Cycle) (length: nat) (a: Agent): Agent:=
  cycle (mod_add_one (agent_index cycle length a) length).

Lemma agent_is_adjacent_to_next_agent_along_cycle {G: envy_graph} (cycle:Cycle) (length: nat) (a: Agent):
  is_valid_cycle length cycle -> 
  (In a (cycle_to_list cycle length)) ->
  edges a (next_agent_along_cycle cycle length a).
Proof.
  intros. destruct H.
  unfold next_agent_along_cycle.
  pose proof H0 as H_a_in_list.
  apply correctness_of_cycle_to_list in H0.
  destruct H0 as [i [H2 H3]].
  pose proof (finite_cycle0 i H2).
  rewrite H3 in H.
  pose proof correctness_of_agent_index1 cycle length a diff_elements0.
  apply H0 in H_a_in_list.
  pose proof correctness_of_agent_index2 cycle length a i diff_elements0.
  assert (agent_index cycle length a = i). {tauto. }
  rewrite H4.
  auto.
Qed.

(******************************************************************************)
(*                 Primitive Operations of Envy-cycle procedure               *)
(******************************************************************************)


(* Operation 1: shift the bundles along a cycle *)
Definition shift_bundle `{G: envy_graph} (A: Alloc) (cycle:Cycle) (length: nat) :Alloc :=
    fun a => 
      if (existsb (fun x => (x =? a)) (cycle_to_list cycle length)) then 
        A (next_agent_along_cycle cycle length a)
      else A a.

(* If an agent is not in the cycle, her bundle will not change after shifting *)
Theorem unchanged_bundle_after_shifting {G: envy_graph} (A: Alloc)(cycle:Cycle) (length: nat):
    forall a: Agent, 
      ~ (In a (cycle_to_list cycle length)) -> 
      (A a) = (shift_bundle A cycle length a).
Proof.
    intros;unfold shift_bundle.
    destruct (@existsb _  (fun x => (x =? a)) (cycle_to_list cycle length)) eqn:H1.
    + exfalso. apply H. 
      pose proof @existsb_exists _ (fun x => (x =? a)) (cycle_to_list cycle length).
      rewrite H0 in H1.
      destruct H1 as [x [H11 H12]].
      rewrite Nat.eqb_eq in H12.
      rewrite H12 in H11.
      auto.
    + auto.
Qed.

(* If an agent is in the cycle, her bundle will be changed to the next bundle *)
Lemma bundle_changed_to_next_bundle_after_shifting
    (n: nat)
    (A: Alloc)
    (valuation: Agent -> (SET -> SET -> Prop)) 
    (cycle: Cycle)
    (length: nat)
    (H_valuation_assump: valuation_assumptions valuation)
    (H: @is_valid_cycle (current_envy_graph n A valuation) length cycle): 
    let g := (current_envy_graph n A valuation) in
    forall a: Agent, (In a (cycle_to_list cycle length)) -> 
         (@shift_bundle (current_envy_graph n A valuation) A cycle length a) = (A (@next_agent_along_cycle g cycle length a)).
Proof.
  intros. unfold shift_bundle.
  destruct (existsb (fun x : nat => x =? a) (cycle_to_list cycle length)) eqn:H_in.
  + auto.
  + pose proof @existsb_exists _ (fun x => (x =? a)) (cycle_to_list cycle length).
    assert(existsb (fun x : nat => x =? a) (cycle_to_list cycle length) = true).
    { apply H1. exists a. split;auto. apply Nat.eqb_eq;auto. }
    rewrite H_in in H2.
    lia.
Qed.    

(* If an agent is in the cycle, her utility will increase *)
Theorem bundle_increased_after_shifting 
    (n: nat)
    (A: Alloc) 
    (valuation: Agent -> (SET -> SET -> Prop)) 
    (cycle: Cycle)
    (length: nat)
    (H_valuation_assump: valuation_assumptions valuation)
    (H: @is_valid_cycle (current_envy_graph n A valuation) length cycle): 
    let g := (current_envy_graph n A valuation) in
    forall a: Agent, (In a (cycle_to_list cycle length)) -> 
        valuation a (A a) (@shift_bundle g A cycle length a).
Proof.
  intros. unfold shift_bundle.
  destruct (existsb (fun x : nat => x =? a) (cycle_to_list cycle length)) eqn:H_in.
  + pose proof @agent_is_adjacent_to_next_agent_along_cycle g cycle length a H H0.
    simpl in H1.
    destruct H_valuation_assump.
    pose proof v_total_order0 a (A a) (A (@next_agent_along_cycle g cycle length a)).
    tauto.
  + pose proof @existsb_exists _ (fun x => (x =? a)) (cycle_to_list cycle length).
    assert(exists x : nat, In x (cycle_to_list cycle length) /\ (fun x0 : nat => x0 =? a) x = true).
    { exists a. split;auto. apply Nat.eqb_eq;auto. }
    apply H1 in H2.
    rewrite H_in in H2. lia.
Qed.


(* If the original allocation is EF1, the allocation after shifting bundle is still EF1 *)
Theorem ef1_during_bundle_shifting
    (n: nat) 
    (A: Alloc) 
    (valuation: Agent -> (SET -> SET -> Prop)) 
    (cycle: Cycle)
    (length: nat)
    (H_valuation_assump: valuation_assumptions valuation)
    (H: @is_valid_cycle (current_envy_graph n A valuation) length cycle):
    let g:= (current_envy_graph n A valuation) in 
      ef1 n A valuation ->
      ef1 n (@shift_bundle g A cycle length) valuation.
Proof.
  intros.
  pose proof classic.
  unfold ef1. intros.
  pose proof H1 (In i (cycle_to_list cycle length)).
  pose proof H1 (In j (cycle_to_list cycle length)).
  pose proof valuation_assumptions_to_ef_properties valuation H_valuation_assump as H_ef1_prop.
  destruct H4.
  unfold g.
  + destruct H5.
    (* Both agent i and j are in the cycle *)
    * pose proof bundle_changed_to_next_bundle_after_shifting n A valuation cycle length H_valuation_assump H i H4.      
      pose proof bundle_changed_to_next_bundle_after_shifting n A valuation cycle length H_valuation_assump H j H5.
      rewrite H6. rewrite H7.
      eapply ef1_monotonicity_prop2.
      2:{ apply H0;auto. unfold next_agent_along_cycle. apply H. apply ub_of_mod_add_one. apply agent_index_bound. apply H. }
      ** pose proof bundle_increased_after_shifting n A valuation cycle length H_valuation_assump H i H4.
        rewrite H6 in H8. auto. 
    (* Agent i is in the cycle while j is not *)
    * pose proof bundle_changed_to_next_bundle_after_shifting n A valuation cycle length H_valuation_assump H i H4.
      rewrite H6.
      eapply ef1_monotonicity_prop2.
      ** pose proof bundle_increased_after_shifting n A valuation cycle length H_valuation_assump H i H4.
        rewrite H6 in H7. apply H7.
      ** pose proof unchanged_bundle_after_shifting A cycle length j H5.
        unfold g in H7;rewrite <- H7.
        apply H0;auto.
  + destruct H5.
    (* Agent i is not in the cycle while j is *)
    * pose proof unchanged_bundle_after_shifting A cycle length i H4.
      pose proof bundle_changed_to_next_bundle_after_shifting n A valuation cycle length H_valuation_assump H j H5.
      rewrite <- H6.
      unfold g; rewrite H7. 
      apply H0;auto. 
      unfold next_agent_along_cycle. apply H. apply ub_of_mod_add_one. apply agent_index_bound. apply H.
    (* Both agent i and j are not in the cycle *)
    * pose proof unchanged_bundle_after_shifting A cycle length i H4.
      pose proof unchanged_bundle_after_shifting A cycle length j H5.
      rewrite <- H6, <- H7;auto.
Qed.


(* The following are to be continued ... *)
Section CycleElimination.

(** Assume we are given a correct DFS oracle **)
Context (DFS: envy_graph -> option (Cycle * nat))
        (DFS_correctness1: forall g c l, (DFS g = Some (c, l)) -> (@is_valid_cycle g l c))
        (DFS_correctness2: forall g c l, 
          ((DFS g = Some (c, l)))  <-> (exists c1 l1, @is_valid_cycle g l1 c1))
        (DFS_correctness3: forall g, 
          (DFS g = None) <-> ~ (exists c l, @is_valid_cycle g l c)).


End CycleElimination.