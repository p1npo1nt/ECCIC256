From Coq Require Import ZArith.
From Coq Require Import Znumtheory. 
From Coq Require Import Field.
From Coq Require Import Field_theory.
From Coq Require Import Setoid.
From Coq Require Import Bool.Bool.

Open Scope Z_scope.

(* define a prime modulus p *)
Parameter p : Z.
Axiom p_prime : prime p.

Definition mod_add (a b : Z) : Z := Z.modulo (a + b) p.

Definition mod_sub (a b : Z) : Z := Z.modulo (a - b + p) p.

Definition mod_mul (a b : Z) : Z := Z.modulo (a * b) p.

(* modular inverse *)
Definition mod_inv (a : Z) : option Z :=
  if Z.gcd a p =? 1 then Some (Z.modulo (Z.pow a (p - 2)) p) else None.

(* definition of the EC and its properties, following this: *)

(* elliptic curve parameters *)
Parameter a b : Z.

(* non-singularity condition: 4a^3 + 27b^2 ≠ 0 mod p *)
Axiom non_singular : mod_add (mod_mul 4 (mod_mul a (mod_mul a a))) (mod_mul 27 (mod_mul b b)) <> 0.

(* define a point on the curve or the point at infinity *)
Inductive ECPoint :=
  | Infinity : ECPoint
  | Point : Z -> Z -> ECPoint.  (* Point x y *)

(* add two points P Q on the elliptic curve *)
Definition point_add (P Q : ECPoint) : ECPoint :=
  match P, Q with
  | Infinity, _ => Q
  | _, Infinity => P
  | Point x1 y1, Point x2 y2 =>
      if (x1 =? x2) && (y1 =? (p - y2) mod p) then Infinity  (* P + (-P) = Infinity *)
      else if x1 =? x2 then
        (* Point doubling *)
        match mod_inv (mod_mul 2 y1) with
        | Some inv_denom =>
            let lambda := mod_mul (mod_add (mod_mul 3 (mod_mul x1 x1)) a) inv_denom in
            let x3 := mod_sub (mod_sub (mod_mul lambda lambda) x1) x2 in
            let y3 := mod_sub (mod_mul lambda (mod_sub x1 x3)) y1 in
            Point x3 y3
        | None => Infinity
        end
      else
        (* Point addition *)
        match mod_inv (mod_sub x2 x1) with
        | Some inv_denom =>
            let lambda := mod_mul (mod_sub y2 y1) inv_denom in
            let x3 := mod_sub (mod_sub (mod_mul lambda lambda) x1) x2 in
            let y3 := mod_sub (mod_mul lambda (mod_sub x1 x3)) y1 in
            Point x3 y3
        | None => Infinity
        end
  end.

(* scalar multiplication with nat *)
Fixpoint scalar_mult (k : nat) (P : ECPoint) : ECPoint :=
  match k with
  | O => Infinity
  | S k' => point_add P (scalar_mult k' P)
  end.

(* !TEST! *)

(* Example point G on the curve: G = (5, 1) *)
Definition G : ECPoint := Point 5 1.

(* ======================================================= *)

Example point_doubling_test : point_add G G = Point 6 3.
Proof.
  compute.
  reflexivity.
Qed.


Example scalar_mult_test : scalar_mult 3 G = Point 10 6.
Proof.
  compute.
  reflexivity.
Qed.
