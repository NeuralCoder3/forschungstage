Example lia1b (x:nat)(H: x <= 3):
  x <= 7.
Proof.
  (* ohne Taktik *)
  apply le_S. (* Per Definition x <= S n falls x <= n *)
  constructor. (* Diese Taktik macht das gleiche *)
  do 2 constructor. (* noch zwei mal das gleiche *)
  assumption.
Qed.



Lemma le_alt (x y:nat) :
  x <= y <-> exists k, x + k = y.
Proof.
Admitted.

Example lia2 (x y z:nat) (H1: x <= y)(H2: y <= z) :
  x <= z.
Proof.
  rewrite le_alt in *.
  destruct H1 as [k1 H1].
  destruct H2 as [k2 H2].
  exists (k1 + k2).
  rewrite <- H2, <- H1.
  rewrite Nat.add_assoc.
  reflexivity.