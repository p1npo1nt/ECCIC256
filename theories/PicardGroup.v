(* Definition of a divisor on an elliptic curve *)
Record divisor := {
  coeff : point -> int;
  finite_support : exists p, coeff p <> 0
}.

(* Definition of principal divisors *)
Definition principal_div (f : {fraction ecring}) : divisor :=
  fun p => order f p.

(* Definition of the Picard group *)
Definition PicardGroup := quotient divisor principal_div.

(* proof that Pic(E) is a group *)
Lemma PicardGroup_law : group_law PicardGroup.
Proof.
  split.
  - (* Closure: If D1 and D2 are in Pic(E), then D1 + D2 is also in Pic(E) *)
    move=> D1 D2.
    exists (lr (D1 + D2)).
    apply ecdeqv_lr.
  
  - (* Associativity: (D1 + D2) + D3 = D1 + (D2 + D3) *)
    move=> D1 D2 D3.
    apply eq_class_eq.
    rewrite /class_of.
    rewrite add_assoc.
    reflexivity.

  - (* Identity element: There exists D0 such that D + D0 = D *)
    exists (class_of (<<EC_Inf>> - <<EC_Inf>>)).
    move=> D.
    apply eq_class_eq.
    rewrite /class_of.
    by rewrite add0g.

  - (* Inverse element: For each D, there exists -D such that D + (-D) = D0 *)
    move=> D.
    exists (class_of (- D)).
    apply eq_class_eq.
    rewrite /class_of.
    by rewrite subrr.
Qed.

