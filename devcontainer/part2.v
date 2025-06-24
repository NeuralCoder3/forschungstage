(* Wir initialisieren Rocq und widerholen die Definition of Listen. *)
Require Import PeanoNat Arith.
Local Open Scope nat_scope.
Require Import Lia. 
Import Compare_dec.

Inductive list  : Type :=
|nil : list
|cons (x:nat) (xs:list): list.

Infix "::" := cons (at level 60, right associativity).

Notation is_leq := le_gt_dec.
Tactic Notation "case_analysis_is_leq" ident(x) ident(y) := (destruct (le_gt_dec x y)).


(* In Rocq stellt x <= y die Aussage "x ist kleiner oder gleich y" dar. 
Wenn numerische Aussagen zu beweisen sind, z.B. kleiner-gleich-Aussagen, 
können wir die Taktik lia benutzen. 
Diese Taktik versucht die zu zeigende numerische Aussage aus den Annahmen zu beweisen. 
Für unsere Fälle reicht diese Taktik aus. *)
Example lia1 (x:nat)(H: x <= 3):
  x <= 7.
Proof.
  lia.
Qed.

Example lia2 (x y z:nat) (H1: x <= y)(H2: y <= z) :
  x <= z.
Proof.
  lia. 
Qed.

Example lia_fail (x y:nat) :
  x <= y.
Proof.
  (* lia *)
  Fail lia.
  (*lia kann diese Aussage nicht beweisen*)
Abort.

(* Später werden wir Funktionen schreiben, 
in denen wir eine Fallunterscheidung machen müssen, 
ob eine Zahl keiner als eine andere ist. 
Dies können wir mit dem folgenden if-then-else Konstrukt machen. 
is_leq ist eine Funktion, die entscheidet ob x <= y. 
Wir gehen hier nicht darauf ein, wie das funktioniert und warum das nötig ist.

Um in einem Beweis diese Fallunterscheidung dann durchzuführen, 
verwenden wir die Taktik case_analysis_is_leq x y.
 *)
Example smaller (x y:nat) :
  (if (is_leq x y) then x else y) <= y.
Proof.
  case_analysis_is_leq x y.
  - lia.
  - lia.
Qed.

(* Wenn wir eine Aussage X zu zeigen wollen und ein Lemma lem haben, 
dass X aussagt, können wir mit der Taktik apply lem dieses Lemma anwenden. 
Die Taktik erzeugt dann Goals für alle Annahmen, die lem aufführt um X zu zeigen. *)
Example apply_lemma (x:nat): 
   (if (is_leq x 3) then x else 3) <= 7.
Proof.
  apply lia1.
  apply smaller.
Qed.

(* Jetzt geht's an das Beweisen eines "richtigen" Algorithmus! 
Wir beweisen die Korrektheit von Insertion Sort. *)

(* Definiere eine Funktion sort vom Typ list -> list, die Insertion Sort implementiert! *)

(* Fügt ein Element x in eine Liste ys ein. 
Wenn ys schon sortiert ist, soll auch insert x ys sortiert sein. *)
Fixpoint insert (x:nat) (ys:list) :=
  (* TODO *)
  .

(* Insertion sort. *)
Fixpoint sort (xs:list) : list :=
  (* TODO *)
  .

(* Keine Idee oder Probleme? Fragt uns um Hilfe, wenn ihr nicht weiterkommt! *)

(* Bevor wir beweisen können, dass unsere Implementierung von Insertion Sort korrekt ist, 
müssen wir definieren, was Korrektheit eines Sortieralgorithmus überhaupt bedeutet. *)

(* Definiere ein Funktion sorted vom Typ list -> Prop, die eine Aussage erzeugt, 
die Sortiertheit einer Liste ausdrückt. *)

 (* Überprüft ob z kleiner ist als das erste Element von xs. 
Wenn xs leer ist, wird True zurückgegeben. *)
Definition smaller_fst (z: nat) (xs: list) :=
  (* TODO *) .

(* Überprüft ob eine Liste von natürlichen Zahlen sortiert ist. *)
Fixpoint sorted (xs : list) : Prop :=
  (* TODO *) .
 

(* Beweise, dass die Implementierung von Insertion Sort eine sortierte Liste zurück gibt. 
Noch ein paar Hinweise:

- Wenn ihr simpl nicht in der zu beweisenden Aussage sondern in einer Annahme H benutzen möchtet, 
  könnt ihr dies mit simpl in H tun.
- Es ist sehr hilfreich, den Beweis in mehrere Lemmas zu trennen und 
  diese dann mit apply anzuwenden.
- Die Induktionen hier werden etwas komplizierter. 
  Vermutlich werdet ihr eine Induktionshypothese der Form IH: X -> Y bekommen. 
  Dies stellt eine Implikation da: wenn X gilt, dann gilt auch Y. 
  Wenn ihr nun Y zeigen sollt, könnt ihr mit apply IH die Induktionshypothese (wie ein Lemma) anwenden. 
  Nun müsst ihr X zeigen.
- Für Verschachtelungen von Untergoals benutzt ihr erst '-', dann '+', dann '*'. 
  Solltest ihr mehr brauchen müsst ihr mit { und } arbeiten um wieder mit '-' beginnen zu können. 
  Fragt in diesem Fall am besten nach.
- Wenn ihr Fragen habt, nicht weiter kommt, oder etwas nicht versteht, meldet euch und wir helfen. *)

 (* Kompatibiltät von smaller_fst und > *)
Lemma smaller_first_insert (z y:nat) (xs:list) (A: y > z) (B : smaller_fst z xs):
     smaller_fst z (insert y xs). 
Proof.
  (* TODO *)
Admitted.

(* Insert erhält Sortiertheit. *)
Lemma insert_pres (ys:list) (H: sorted ys) (x:nat):
  sorted (insert x ys). 
Proof.
  (* TODO *)
Admitted.

(* Korrektheit von Sort. *)
Lemma correctness_sort (xs: list) :
  sorted (sort xs). 
Proof.
  (* TODO *)
Admitted.




(* Im vorherigen Abschnitte haben wir bewiesen, dass Insertion Sort sortierte Liste erzeugt. 
Jedoch fehlt hier noch was! Diese Aufgabe bearbeiten wir aus Zeitgründen nicht in Rocq. *)

(* 
Aufgabe 4.1
Gebt ein Beispiel für einen "Sortieralgorithmus", der immer eine sortierte Liste zurück gibt, aber offensichtlich nicht das tut, was wir von einem Sortieralgorithmus erwarten.

Aufgabe 4.2
Formulierteine weitere Eigenschaft von sort, die der "Sortieralgorithmus" aus Aufgabe 4.1 nicht erfüllt.

Aufgabe 4.3
Überleget, ob eine Funktion, die eine sortierte Liste zurück gibt und eure Eigenschaft aus 4.2 erfüllt, schon eindeutig spezifiziert ist. Falls nein, wie könnte eine Funktion aussehen, die dies alles erfüllt, aber andere Ergebnisse als sort liefert? Ihr müsst diese nicht unbedingt in Rocq implementieren.

Aufgabe 4.4
Versucht eine weitere Aussage zu definieren, die unseren Sortieralgorithmus eindeutig spezifiziert. Jeder andere Algorithmus, der diese Spezifikation erfüllt, muss immer die selben Ergebnisse wie sort liefern. Es kann sein, dass ihr Hilfsfunktionen definieren müsst. Auch diese Aufgabe müsst ihr nicht in Rocq lösen.
 *)
