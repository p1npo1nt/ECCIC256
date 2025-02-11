(* Representation of rational functions on the curve *)
Inductive ecring := 
  | ECRing of {poly K} * {poly K}.

Notation "[ecp p1 *Y + p2]" := (ECRing p1 p2).

(* Multiplication in the field of rational functions *)
Definition mul (p q : ecring) :=
  let xs := (p.1 * q.2 + p.2 * q.1) in
  [ecp xs *Y + (p.2 * q.2)].
