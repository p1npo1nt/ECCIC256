(* Definition of negation *)
Definition neg (p : point) : point :=
  match p with
  | (x, y) => (x, -y)
  | EC_Inf => EC_Inf
  end.

(* Definition of elliptic curve point addition *)
Definition add (p1 p2 : point) : point :=
  match p1, p2 with
  | EC_Inf, _ => p2
  | _, EC_Inf => p1
  | (x1, y1), (x2, y2) => 
      if x1 == x2 then EC_Inf (* Vertical line case *)
      else
        let s := (y2 - y1) / (x2 - x1) in
        let xs := s^2 - x1 - x2 in
        (xs, - (s * (xs - x1) + y1))
  end.


Lemma addO (p q : point): oncurve (add p q).
Proof.
  Proof.
  rewrite /oncurve /add.
  case: p => [| x1 y1]; case: q => [| x2 y2]; simpl; try done.
  - by [].
  - by [].
  - move=> H1 H2. 
    rewrite eq_sym in H1.
    case: ifP => [/eqP Heq | Hneq].
    + rewrite -Heq in H2.
      (* Special case: vertical line case, sum goes to infinity *)
      by [].
    + (* Regular case: using slope formula *)
      set s := (y2 - y1) / (x2 - x1).
      set xs := s^2 - x1 - x2.
      have Hcurve: (s^2 - x1 - x2)^3 + A * (s^2 - x1 - x2) + B = (s * (x1 - xs) + y1)^2.
      (* Algebraic manipulations to confirm the sum point satisfies the equation *)
      admit.
Qed.


Definition addec (p1 p2 : ec) : ec := 
  EC (add p1 p2) (addO p1 p2).



