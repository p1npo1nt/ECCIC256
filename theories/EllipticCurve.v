From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssralg ssrnum.
(* opam install coq-mathcomp-ssreflect coq-mathcomp-algebra coq-mathcomp-field coq-mathcomp-fingroup *)

Variable K : fieldType.
(* Definition of an elliptic curve type *)
Definition four := (4 : K).
Definition twenty_seven := (27 : K).

(* Definition of an elliptic curve type *)
Record ecuType := { 
  A : K; 
  B : K; 
  _ : four * A^3 + twenty_seven * B^2 != 0 
}.

(* Representation of points on the elliptic curve *)
Inductive point := 
  | EC_Inf  (* Point at infinity *)
  | EC_In of K & K.

Notation "(x, y)" := (EC_In x y).

(* Predicate to check if a point lies on the elliptic curve *)
Definition oncurve (p : point) : bool :=
  match p with
  | (x, y) => y^2 == x^3 + A * x + B
  | EC_Inf => true
  end.

(* Definition of the elliptic curve type *)
Inductive ec : Type := 
  | EC of { p : point | oncurve p }.
