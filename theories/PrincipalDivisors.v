(* Definition of a principal divisor *)
Definition ecdiv (f : {fraction ecring}) : divisor :=
  fun p => order f p.

Lemma deg_ecdiv_eq0 (f : {fraction ecring}) : 
  sum (fun p => order f p) = 0.
Proof.
  (* Proof that the sum of orders is zero *)
Admitted.
