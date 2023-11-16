Require Import Basics.
Require Import ZArith.
Require Import List.
Require Import Divvy.SetDomain.
 
Import Sets.

Definition order_reflexivity (u: SET -> SET -> Prop): Prop :=
    forall A, u A A.

Definition is_total_order (u: SET -> SET -> Prop): Prop :=
    forall A B, (u A B) \/ (u B A).

Lemma total_order_symmetry: forall (u: SET -> SET -> Prop) (H: is_total_order u) A B,
    ~(u A B) -> u B A.
Proof.
    intros.
    unfold is_total_order in H.
    pose proof H A B.
    tauto.
Qed.

Definition order_monotonicity (u: SET -> SET -> Prop): Prop :=
    forall A B, (include A B) -> u A B.

Definition order_additivity (u: SET -> SET -> Prop): Prop :=
    forall A1 A2 B1 B2, (is_equal (intersect B1 B2) (empty_set)) ->
        (u A1 B1) -> (u A2 B2) -> (u (union A1 A2) (union B1 B2)).

Definition EF1_for_u (u: SET -> SET -> Prop) (A B: SET): Prop :=
    (is_empty B) \/ (u B A) \/ (exists g, (member g B) /\ u (delete_item B g) A).

(* Lemma cut_and_choose (u1 u2: SET -> SET -> Prop)
    (H_u1_mono: order_monotonicity u1)    
    (H_u2_mono: order_monotonicity u2)
    (H_u1_add: order_additivity u1)
    (H_u2_add: order_additivity u2)
    (A B: SET)
    (H_EF1_for_u1_1: EF1_for_u u1 A B)
    (H_EF1_for_u1_2: EF1_for_u u1 B A)
    (H_GE: u2 A B)
    : (EF1_for_u u1 B A) /\ (EF1_for_u u2 A B).
Proof.
    intros;split.
    + auto.
    +  unfold EF1_for_u;tauto.
Qed. *)

Definition Var := nat.

(* Inductive BExpr :=
    | BTrue                                 (* false *)
    | BFalse                                (* true *)
    | BAnd (b1: BExpr) (b2: BExpr)          (* b1 && b2 *)
    | BOr (b1: BExpr) (b2: BExpr)           (* b1 || b2 *).
     *)
Inductive Value : Type := 
    | VBool (b: bool)
    | VSet (s: SET)
    | VPair (v1 v2: Value).

Inductive Expr := 
    | EConst (v: Value)                             (* v *)
    | EAnd (e1: Expr) (e2: Expr)                    (* e1 && e2 *)
    | EOr (e1: Expr) (e2: Expr)                     (* e1 || e2 *)
    | EVar (v: Var)                                 (* v *)
    | ESetUnion (s1 s2: Expr)                       (* s1 U s2 *)
    | ESetMinus (s1 s2: Expr)                       (* s1 \ s2 *)
    | ESetIntersect (s1 s2: Expr)                   (* s1 n s2 *)
    | EPair (e1 e2: Expr)                           (* (e1, e2) *)
    | ELetIn1 (x: Var) (e1: Expr) (e2: Expr)        (* let x = e1 in e2 *)
    | ELetIn2 (x1 x2: Var) (e1: Expr) (e2: Expr)    (* let x1, x2 = e1 in e2 *)
    | EIf (b: Expr) (e1: Expr) (e2: Expr)           (* If b then e1 else e2 *)
    | ECompare (i: nat) (e1: Expr) (e2: Expr)       (* u_i(e1) <? u_i(e2) *)
    | EDivide (i: nat) (e1: Expr)                   (* Divide_i(e_1) *).

Notation "'tt'" := (EConst (VBool true)) (at level 50).
Notation "'ff'" := (EConst (VBool false)) (at level 50).
Notation "x 'and' y" := (EAnd x y) (at level 40, left associativity).
Notation "x 'or' y" := (EOr x y) (at level 40, left associativity).
Notation "'var' x" := (EVar x) (at level 50).
Notation "s1 'U' s2" := (ESetUnion s1 s2) (at level 60, right associativity).
Notation "s1 '\' s2" := (ESetMinus s1 s2) (at level 60, right associativity).
Notation "s1 'n' s2" := (ESetIntersect s1 s2) (at level 60, right associativity).
Notation "'LET' x ':=' e1 'IN' e2" := (ELetIn1 x e1 e2) (at level 80, right associativity).
Notation "'LET' x ',' y ':=' e1 'IN' e2" := (ELetIn2 x y e1 e2) (at level 80, right associativity).
Notation "'IF' b 'THEN' e1 'ELSE' e2" := (EIf b e1 e2) (at level 80, right associativity).
(* Notation " e1 '[' '(' i   e2  " := (ECompare i e1 e2) (at level 70). *)

Definition Config :Type := Var -> Value.

Definition assign_var (c: Config) (x: Var) (v: Value) :Config:= 
    fun x1 => if (x1 =? x) then v else (c x1).

Lemma multiple_assign: forall c x1 x2 v1 v2,
    ~(x1 = x2) ->
    assign_var (assign_var c x1 v1) x2 v2 x1 = v1.
Proof.
    intros c x1 x2 v1 v2 H. unfold assign_var.
    destruct (x1 =? x2) eqn:E.
    + apply Nat.eqb_eq in E;tauto.
    + destruct (x1 =? x1) eqn:E1.
        * tauto.
        * pose proof Nat.eqb_eq x1 x1.
        rewrite E1 in H0.
        assert (H1: false = true). {apply H0. reflexivity. }
        discriminate H1.
Qed.

(* Small-Step semantics of Expr *)
Inductive Estep (u1 u2: SET -> SET -> Prop): Config -> Expr -> Value -> Prop:= 
    | ES_const: forall c (v: Value), 
        Estep u1 u2 c (EConst v) v
    | ES_var: forall c x,
        Estep u1 u2 c (EVar x) (c x)
    | ES_pair: forall c e1 e2 v1 v2,
        Estep u1 u2 c e1 v1 ->
        Estep u1 u2 c e2 v2 ->
        Estep u1 u2 c (EPair e1 e2) (VPair v1 v2)
    | ES_and: forall c e1 e2 b1 b2,
        Estep u1 u2 c e1 (VBool b1) ->
        Estep u1 u2 c e2 (VBool b2) ->
        Estep u1 u2 c (EAnd e1 e2) (VBool (b1 && b2))
    | ES_or: forall c e1 e2 b1 b2,
        Estep u1 u2 c e1 (VBool b1) ->
        Estep u1 u2 c e2 (VBool b2) ->
        Estep u1 u2 c (EOr e1 e2) (VBool (b1 || b2))
    | ES_If_True: forall c b e1 e2 v1,
        Estep u1 u2 c b (VBool true) ->
        Estep u1 u2 c e1 v1 ->
        Estep u1 u2 c (EIf b e1 e2) v1
    | ES_If_False: forall c b e1 e2 v2,
        Estep u1 u2 c b (VBool false) ->
        Estep u1 u2 c e2 v2 ->
        Estep u1 u2 c (EIf b e1 e2) v2
    | ES_LetIn1: forall c x e1 e2 v1 v2,
        Estep u1 u2 c e1 v1 ->
        Estep u1 u2 (assign_var c x v1) e2 v2 ->
        Estep u1 u2 c (ELetIn1 x e1 e2) v2
    | ES_LetIn2: forall c x1 x2 e1 e2 v11 v12 v2, 
        Estep u1 u2 c e1 (VPair v11 v12) ->
        Estep u1 u2 (assign_var (assign_var c x1 v11) x2 v12) e2 v2 ->
        Estep u1 u2 c (ELetIn2 x1 x2 e1 e2) v2    
    | ES_comp_1_true: forall c e1 e2 v1 v2,
        Estep u1 u2 c e1 (VSet v1) -> 
        Estep u1 u2 c e2 (VSet v2) ->
        u1 v1 v2 -> 
        Estep u1 u2 c (ECompare 1 e1 e2) (VBool true)
    | ES_comp_1_false: forall c e1 e2 v1 v2,
        Estep u1 u2 c e1 (VSet v1) -> 
        Estep u1 u2 c e2 (VSet v2) ->
        ~(u1 v1 v2) -> 
        Estep u1 u2 c (ECompare 1 e1 e2) (VBool false)
    | ES_comp_2_true: forall c e1 e2 v1 v2,
        Estep u1 u2 c e1 (VSet v1) -> 
        Estep u1 u2 c e2 (VSet v2) ->
        u2 v1 v2 -> 
        Estep u1 u2 c (ECompare 2 e1 e2) (VBool true)
    | ES_comp_2_false: forall c e1 e2 v1 v2,
        Estep u1 u2 c e1 (VSet v1) -> 
        Estep u1 u2 c e2 (VSet v2) ->
        ~(u2 v1 v2) -> 
        Estep u1 u2 c (ECompare 2 e1 e2) (VBool false)
    | ES_divide_1: forall c x1 x2 e1 e2 v T A B,
        Estep u1 u2 c e1 (VSet T) -> 
        EF1_for_u u1 A B ->
        EF1_for_u u1 B A ->
        u1 A B ->
        Estep u1 u2 (assign_var (assign_var c x1 (VSet A)) x2 (VSet B)) e2 v ->
        Estep u1 u2 c (ELetIn2 x1 x2 (EDivide 1 e1) e2) v.

        
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "[[ e ]]( u1 , u2 , c ) := v" := (Estep u1 u2 c e v) (at level 10).


Lemma I_Cut_U_Choose: forall (u1 u2: SET -> SET -> Prop) 
    (H_u2_total: is_total_order u2) (c: Config) 
    (T: SET) v1 v2,
    [[
        LET 1, 2 := (EDivide 1 (EConst (VSet T))) IN
            (IF (ECompare 2 (var 1) (var 2)) 
                THEN (EPair (var 1) (var 2))
            ELSE (EPair (var 2) (var 1))
            )
    ]](u1, u2, c) := (VPair (VSet v1) (VSet v2)) ->
    (EF1_for_u u1 v1 v2) /\ (EF1_for_u u2 v2 v1).
Proof.
    intros u1 u2 H_u2_total c T v1 v2 H.
    split.
    + inversion H.
        * inversion H6.
        * inversion H10. 
            ** inversion H17. inversion H22. inversion H24. rewrite <- H28, <-H31. auto.
            ** inversion H17. inversion H22. inversion H24. rewrite <- H28, <-H31. auto.
    + inversion H.
        * inversion H7. 
            ** inversion H13. inversion H17. inversion H19.
            assert(H_v11_equal_v4: v11 = VSet v4). 
            { rewrite <- H22. symmetry. apply multiple_assign. discriminate. }
            assert(H_v12_equal_v5: v12 = VSet v5). 
            { rewrite <- H25. symmetry. reflexivity. }
            inversion H14.
            inversion H31.
            assert(H_v11_equal_v1: v11 = VSet v1).
            { rewrite <- H35. symmetry. apply multiple_assign. discriminate. }
            inversion H33.
            assert(H_v12_equal_v2: v12 = VSet v2).
            { rewrite <- H38. symmetry. reflexivity. }
            right. left. rewrite H_v11_equal_v1 in H_v11_equal_v4.
            rewrite H_v12_equal_v2 in H_v12_equal_v5. 
            inversion H_v11_equal_v4.
            inversion H_v12_equal_v5.
            auto.
            ** inversion H13. inversion H17. inversion H19.
            assert(H_v11_equal_v4: v11 = VSet v4). 
            { rewrite <- H22. symmetry. apply multiple_assign. discriminate. }
            assert(H_v12_equal_v5: v12 = VSet v5). 
            { rewrite <- H25. symmetry. reflexivity. }
            inversion H14.
            inversion H31.
            assert(H_v12_equal_v1: v12 = VSet v1).
            { rewrite <- H35. reflexivity. }
            inversion H33.
            assert(H_v11_equal_v2: v11 = VSet v2).
            { rewrite <- H38. symmetry. apply multiple_assign. discriminate. }
            right. left. rewrite H_v11_equal_v2 in H_v11_equal_v4.
            rewrite H_v12_equal_v1 in H_v12_equal_v5. 
            inversion H_v11_equal_v4.
            inversion H_v12_equal_v5.
            apply total_order_symmetry;auto.
        *  inversion H10.
            ** inversion H16. inversion H20. inversion H22.
            inversion H17. inversion H34. inversion H36.
            right. left. rewrite <- H40, <- H43, H27, H30. auto.
            ** inversion H16. inversion H20. inversion H22.
            inversion H17. inversion H34. inversion H36.
            right. left. rewrite <- H40, <- H43, H27, H30. 
            apply total_order_symmetry;auto.
Qed.

(* test_comp1: if {1,2} <_1 {3}, then [[Compare_1({1,2}, {3})]] = true *)
Example test_comp1: forall (u1 u2: SET -> SET -> Prop) (H_u1_total_order: is_total_order u1)
    (c: Config) (v: Value),
    (u1 [1;2] [3]) ->
    (Estep u1 u2 c (ECompare 1 (EConst (VSet [1;2])) (EConst (VSet [3])))  v) ->
    (v =  (VBool true)).
Proof.
    intros.
    inversion H0. 
    + auto.
    + inversion H3. inversion H5. rewrite <- H11 in H7. rewrite <- H14 in H7.
    contradiction.
Qed.

(* test_if: 
 * for any two sets s1, s2, [[if Compare_1(s1, s2) then s1 else s2]] <=_1 s2
 *)
Example test_if: forall (u1 u2: SET -> SET -> Prop) 
    (H: order_reflexivity u1)
    (c: Config) (s1 s2 s3: SET),
    [[
        IF (ECompare 1 (EConst (VSet s1)) (EConst (VSet s2))) 
            THEN (EConst (VSet s1)) 
        ELSE (EConst (VSet s2)) 
    ]](u1, u2, c) := (VSet s3) ->
    (u1 s3 s3).
Proof.
 intros u1 u2 H c s1 s2 s3 H1.
 inversion H1;auto.
Qed.

(* test_let_in: 
 *  if s1 <_1 s2, [[let x1 = s1 in Compare_1(x, s2)]] = true 
 *)
Example test_letin: forall (u1 u2: SET -> SET -> Prop) (H_u1_total_order: is_total_order u1)
    (c: Config) v (s1 s2: SET),
    (u1 s1 s2) ->
    [[
        LET 1 := (EConst (VSet s1)) IN 
            (ECompare 1 (var 1) (EConst (VSet s2)))
    ]](u1, u2, c) := v ->
    (v = (VBool true)).
Proof.
    intros u1 u2 H_u1_total_order c v s1 s2 H0 H1.
    inversion H1.
    inversion H7;auto.
    + inversion H6.
     assert(H_v1_set_v0: v1 = VSet v0).
    { inversion H10. rewrite <- H19. unfold assign_var. reflexivity. }
    assert(H_s1_v0: VSet s1 = VSet v0).
    { rewrite H16, <-H_v1_set_v0. reflexivity. }
    inversion H_s1_v0.
    rewrite H19 in H0.
    inversion H12.
    rewrite H22 in H0.
    contradiction.
Qed.

(* test_const: [[EConst (VBool true)]] = (VBool true) *)
Example test_const: forall (u1 u2: SET -> SET -> Prop) (c: Config) v, 
    [[EConst (VBool true)]](u1, u2, c) := v ->
    (v = (VBool true)).
Proof. 
    intros u1 u2 c v H.
    inversion H;auto.
Qed.



Example test_and: forall (u1 u2: SET -> SET -> Prop) (c: Config) v, 
    [[(EConst (VBool true)) and (EConst (VBool false))]](u1, u2, c) := v ->
    (v = (VBool false)).
Proof. 
    intros u1 u2 c v H.
    inversion H.
    inversion H3; inversion H5;auto.
Qed.