Require Import SMTC.Tactic.
Require Import SMTC.Integers.
Require Import Coq.Strings.String.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.
Set SMT Solver "z3".
Set SMT Debug.

Local Open Scope Z_scope.

Goal forall x y, x + y = y + x.
Proof.
  intros.
  smt solve.
Abort.

Goal Int64.max_unsigned + 1 = (Int.max_unsigned+1) * (Int.max_unsigned+1).
Proof.
  intros.
  smt solve.
Abort.

Goal forall x y, Int64.eq x y = true -> x = y.
Proof.
  intros.
  smt solve.
Abort.


Goal Int64.ltu (Int64.modu (Int64.repr 8) (Int64.repr Int.modulus)) Int64.iwordsize = true.
Proof.
  intros.
  smt solve.
Abort.

Goal forall x:Z, x > 0.
Proof.
  intros.
  Fail smt solve.
Abort.

Goal forall v0 v1,
   (Int64.unsigned v0 <= 255)%Z -> 
   (Int64.unsigned v1 <= 255)%Z ->
   (Int64.unsigned (Int64.add v0 (Int64.shl v1 (Int64.modu (Int64.repr 8) (Int64.repr Int.modulus)))) <=? Int.max_unsigned = true)%Z.
Proof.
  intros.
  smt solve.
Abort.

Goal 1 = 1.
Proof.
  intros.
  smt solve.
Abort.

Goal Int64.one = Int64.and Int64.one Int64.one.
Proof.
  intros.
  smt solve.
Abort.

Goal forall (n'''': int64) (x: Z), n'''' = Int64.and Int64.one Int64.one /\ x = 1 -> n'''' = Int64.one /\ x = 1.
Proof.
  intros.
  smt solve.
Abort.

Goal forall n: Z, n * 3 = 123 -> n = 41.
Proof.
  intros.
  smt solve.
Abort.

Goal forall (n: int64) (x: Z), n = Int64.and Int64.one Int64.one -> x = 1 -> x = Int64.unsigned n.
Proof.
  intros.
  smt solve.
Abort.

Goal forall (n: int64), n = Int64.repr (Int64.unsigned n).
Proof.
  intros.
  smt solve.
Abort.

Goal forall b: bool, b = b.
Proof.
  intros.
  smt solve.
Abort.

Goal true = false.
Proof.
  intros.
  Fail smt solve.
Abort.

Goal forall i0 i,
    Int64.ltu i0 i = false ->
    Int64.unsigned (Int64.add (Int64.divu (Int64.sub i0 i) (Int64.repr 2)) i) =
    (Int64.unsigned i + Int64.unsigned i0) /2. 
Proof.
  intros.
(*   smt solve. *)
Abort.

Goal forall A B : Prop, A /\ B -> B.
Proof.
  intros.
  smt solve.
Abort.

Goal forall A B : Prop, True -> False -> A /\ B.
Proof.
  intros.
  smt solve.
Abort.

Goal forall x : Z, x < 0 -> x + x < x.
Proof.
  intros.
  smt solve.
Abort.

Goal Z.neg (5) = -5.
Proof.
  intros.
  smt solve.
Abort.

Goal forall x : Z, x = -1 \/ ~(x = -1).
Proof.
  intros.
  smt solve.
Abort.

Goal forall n: int, Int.and n (Int.repr 3) = Int.zero ->
  Int.and (Int.add n (Int.repr 4)) (Int.repr 3) = Int.zero.
Proof.
  intros.
  smt solve.
Abort.

Goal forall n: int64, Int64.and n (Int64.repr 3) = Int64.zero ->
  Int64.and (Int64.add n (Int64.repr 4)) (Int64.repr 3) = Int64.zero.
Proof.
  intros.
  smt solve.
Abort.

Goal forall n:int64, Int64.or n Int64.zero = n.
Proof.
  intros.
  smt solve.
Abort.

Goal forall x y, (Int64.ltu x y = false) -> Int64.ltu y x = true \/ x = y.
Proof.
  intros.
  smt solve.
Abort.

Goal forall x y, (Int.ltu x y = false) -> Int.ltu y x = true \/ x = y.
Proof.
  intros.
  smt solve.
Abort.

Goal forall x, Int64.zero = x -> x = Int64.repr 0.
Proof.
  intros.
  smt solve.
Abort.

Goal forall x, Int.zero = x -> x = Int.repr 0.
Proof.
  intros.
  smt solve.
Abort.

Goal forall (n:int) (m:int64), Int.unsigned n = 2 * Int64.unsigned m.
Proof.
  intros.
  Fail smt solve.
Abort.

Goal forall x:Z, x >= 0 -> x = Z.of_nat (Z.to_nat x).
Proof.
  intros.
  smt solve.
Abort.

Goal  Int.signed (Int.repr(-1)) = -1.
Proof.
  intros.
  smt solve.
Abort.

Goal  Int64.signed (Int64.repr(-1)) = -1.
Proof.
  intros.
  smt solve.
Abort.

Goal Int64.signed (Int64.add (Int64.repr(2-5)) (Int64.repr(-1))) = -4.
Proof.
  intros.
  smt solve.
Abort.

Goal forall n:int8, 0 <= Byte.unsigned n < 256.
Proof.
  intros.
  smt solve.
Abort.

Goal forall z, -128 <= z < 128 -> Byte.signed (Byte.repr (z)) = z.
Proof.
  intros.
  smt solve.
Abort.

Goal Byte.signed (Byte.repr 255) = -1.
Proof.
  intros.
  smt solve.
Abort.

Goal forall n:int8, -128 <= Byte.signed n < 128.
Proof.
  intros.
  smt solve.
Abort.

Goal forall a b, a >= 0 -> b >= 0 -> Z.modulo a b = Z.rem a b.
Proof.
  intros.
  smt solve.
Abort.

Goal Z.modulo 8 3 = 2 /\ Z.modulo (-8) 3 = 1 /\ Z.modulo 8 (-3) = -1 /\ Z.modulo (-8) (-3) = (-2) /\
     Z.rem 8 3 = 2 /\ Z.rem (-8) 3 = -2 /\ Z.rem 8 (-3) = 2 /\ Z.rem (-8) (-3) = (-2).
Proof.
  intros.
  smt solve.
Abort.

Goal forall x n, n < 0 -> Z.pow x n = 0.
Proof.
  intros.
  smt solve.
Abort.

Goal Z.shiftr (Z.shiftl 1 64) 60 = 16.
Proof.
  intros.
  smt solve.
Abort.

Goal forall x, Z.pow x 1 = x.
Proof.
  intros.
  smt solve.
Abort.

Goal forall x, Z.pow x 0 = 1.
Proof.
  intros.
(*   smt solve. *) (* z3' bug *)
Abort.

Goal forall x m n, Z.shiftl m x * Z.shiftl n x = Z.shiftl (m + n) x.
Proof.
  intros.
(*   smt solve. *) (* z3' bug *)
Abort.

Goal forall x, Z.shiftl 1 x = Z.pow 2 x.
Proof.
  intros.
(*   smt solve. *) (* z3' bug *)
Abort.

Local Open Scope nat_scope.

Goal forall x y, x + y = y + x.
Proof.
  intros.
  smt solve.
Abort.

Goal 1 + 3 - 2 * 4 = 0.
Proof.
  intros.
  smt solve.
Abort.

Goal forall x:nat, x = Z.to_nat (Z.of_nat x).
Proof.
  intros.
  smt solve.
Abort.

Goal forall x:nat, x - 5 >= 0.
Proof.
  intros.
  smt solve.
Abort.

Inductive my_type:Type :=
  | my_O : my_type
  | my_S : my_type -> my_type.

Definition my_eq: my_type -> my_type -> Prop :=
  fun a b => a = b.

Goal forall A B, A /\ B -> A.
Proof.
  intros.
  smt solve.
Abort.

Goal forall B, (my_eq (my_S my_O) (my_O)) /\ B -> (my_eq (my_S my_O) (my_O)).
Proof.
  intros.
  smt solve.
Abort.

Goal forall B, (my_eq (my_S my_O) (my_O)) /\ B -> (my_eq (my_S my_O) (my_S my_O)).
Proof.
  intros.
  Fail smt solve.
Abort.


Local Open Scope R_scope. 

Goal forall x y: R, x + y = y + x.
Proof.
  intros.
  smt solve.
Abort.

Goal forall x : R, ~(x = -1).
Proof.
  intros.
  Fail smt solve.
Abort.

Goal forall x : R, x < 0 -> x + x < x.
Proof.
  intros.
  smt solve.
Abort.

Goal forall x : R, ~(x = 1).
Proof.
  intros.
  Fail smt solve.
Abort.

Goal forall x: R, 1/2 * 2/3 * 3/4 * 4/5 * 5/x = 1/x.
Proof.
  intros.
  smt solve.
Abort.



