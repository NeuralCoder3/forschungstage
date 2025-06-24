(**
Man kann über Strg+J weiter im Code runter gehen und mit Strg+K wieder hoch.
(Vielleicht auch Alt+Pfeiltasten)
*)

(**
Wir beginnen mit einfachen Aussagen in Rocq und Taktiken um mit Aussagen umzugehen.
In Rocq heißen Aussagen Prop und mit (X:Prop) legen wir fest, dass X eine Aussage ist. 
Wenn X eine Aussage ist, schreiben wir (H:X) um X anzunehmen und diese Annahme bekommt den Namen H.
Mit der Taktik assumption beweisen wir eine Aussage, die wir bereits als Annahme gegeben haben.
*)

Example Assumption (X: Prop) (H: X) :
(* Hier stehen unsere Annahmen. 'Assumption' ist lediglich der Name des Beispiels. *)
     X.
    (* Hier steht die Aussage, die wir beweisen wollen. *)
Proof.
(* Mit Proof beginnen wir den Beweis. *)
  assumption.                           
Qed.
(* Mit Qed schließen wir einen Beweis ab.*) 


(* Die Aussage True ist immer wahr und kann mit der Taktik trivial bewiesen werden. *)
Example Truth :
  True.
Proof.
  trivial.
Qed. 


(* Wenn X und Y Aussagen sind ist X/\Y die Konjunktion von X und Y. 
Um eine Konjunktion zu beweisen, müssen beide Teile der Konjunktion bewiesen werden. 
Die Taktik split teilt eine zu beweisende Konjunktion in ihre beiden Teilaussagen auf 
und erzeugt für jede ein neues Goal. 
Mit dem Strich '-' deuten wir an, dass wir eines dieser Goals beweisen. *)
Example Conj_Split (X Y: Prop) (H1 : X)(H2: Y) :
  X /\ Y.
Proof.
  split.
  - assumption.
  - assumption.
Qed. 

(* Wenn wir eine Konjunktion als Annahme haben, zerlegt die Taktik destruct die Konjunktion in ihre beiden Teilaussagen. 
In den rechteckigen Klammern werden die Namen für die Teilannahmen angegeben. *)
Example Conj_Destruct (X Y: Prop) (H: X /\ Y) :
	X.
Proof.
  destruct H as [H1 H2].
  assumption.
Qed. 

(* Die Aussage x = y besagt dass x und y gleich sind. 
Die Aussage x = x kann mit der Taktik reflexivity bewiesen werden. 
Mit (x:nat) legen wir fest, dass x eine natürliche Zahl ist. *)
Example Equality_Reflexivity (x : nat) : x = x.
Proof.
  reflexivity.
Qed. 


(* Hat man H: x = y als Annahme, ersetzt die Taktik rewrite H alle Vorkommen von x in der zu beweisenden Aussage durch y. *)
Example Eq_Rewrite (x y : nat) (H: x = y): y = x.
Proof.
  rewrite H.
  reflexivity.
Qed.



(* Übungseinheit 1: Aussagen in Rocq *)
(* Jetzt seid ihr dran! In dieser Übung sollt ihr euch mit oben vorgestellten Taktiken vertraut machen. *)

(* Aufgabe 1.1 *)
Example Conj_Swap (X Y: Prop) (H: X /\ Y) :
	Y /\ X.
Proof.
  (* TODO *)
Admitted. 

(* Aufgabe 1.2 *)
Example Conj_True (X: Prop) (H: X):
  X /\ True.
Proof.
  (* TODO *)
Admitted. 

(* Aufgabe 1.3 *)
Example Equality_Symmetric (x y : nat) (H: x = y) : y = x.
Proof.
  (* TODO *)
Admitted. 

(* Aufgabe 1.4 *)
Example Equality_Transitive (x y z : nat) (H1: x = y) (H2: y = z): x = z.
Proof.
  (* TODO *)
Admitted. 


(* Abschnitt 2: Listen in Rocq *)
(* In diesem Abschnitt betrachten wir Listen. 
Zur Einfachheit beschränken wir und auf Listen von natürlichen Zahlen. 
Wir definieren Listen wie folgt: *)
Inductive list : Type :=
|nil :list                     (* nil ist die leere List *)
|cons (x:nat) (xs:list): list. (* cons erzeugt eine Liste mit x an erster Stelle gefolgt von der List xs *) 

(* Üblicherweise schreibt man nicht cons x xs sondern x :: xs. 
Folgendes Kommando aktiviert diese Notation in Rocq. *)
Infix "::" := cons (at level 60, right associativity).

(* Wir beginnen mit einfachen Funktionen auf Listen. 
Mit match implementieren wir eine Fallunterscheidung, 
ob eine Liste durch nil oder durch cons erzeugt wurde. 
Im Fall für cons geben die beiden folgenden Namen die Variable für die Zahl und die restliche Liste an. 
Funktionen können in Rocq auch Aussagen erzeugen. 
Folgende Funktion erzeugt eine Aussage, die gültig ist, wenn die gegebene Liste nicht leer ist: *)
Definition nonempty (xs : list) : Prop :=
  match xs with        (* Fallunterscheidung für xs *)
  | nil => False       (* xs wurde durch nil erzeugt *)
  | x :: xs' => True (*xs wurde durch cons x xs' erzeugt *)
  end.

(* Diese Funktion berechnet die Länge einer Liste. 
Die Funktion inc erhöht eine gegebene Zahl um eins. 
Das Schlüsselwort Fixpoint ist wichtig um Rocq mitzuteilen,
dass es sich um eine rekursive Funktion handelt. *)
Fixpoint length (xs : list) : nat :=
  match xs with
  | nil => 0
  | x :: xs' => S (length xs')
  end.

(* Mit compute können wir in Rocq einen Ausdruck auswerten, z.B. die Länge einer konkreten Liste berechnen: *)
Compute (length (0 :: 1 :: 2 :: nil)).
Compute (length nil). 

(* Die Funktion app hängt eine Liste an eine andere an. 
Wir benutzen ++ als Notation für diese Funktion. *)
Fixpoint app (xs ys : list) :=
  match xs with
   | nil => ys
   | x :: xs' => x :: app xs' ys
  end.
 
Infix  "++" := app (at level 60, right associativity).

(* In Rocq können wir Ausdrücke teilweise auswerten, 
wenn nicht alle Parameter einer Funktion bekannt sind. 
Mit Section und Variable können wir festlegen, dass xs eine Variable ist. *)
Section Eval.
  Variable (xs : list).
  Compute (nil ++ xs). 
  Compute ((1 :: 2 :: nil) ++ xs).
  Compute ((1 :: 2 :: xs) ++ (3::nil)).
  Compute (xs ++ nil).
End Eval. 


(* Übungseinheit 2: Listen in Rocq *)

(* Aufgabe 2.1 *)
(* Definiert eine Funktion map, die eine Funktion f: nat -> nat  
auf die Elemente einer Liste anwendet. *)
Fixpoint map (f : nat -> nat) (l : list) : list :=
 (* TODO *) .


Compute (map S (1 :: 3 :: 4 :: nil)).


(* Bisher haben wir nur Funktionen auf Listen definiert. 
Nun wollen wir Eigenschaften dieser Funktionen beweisen. 
Wir haben bereits gesehen dass nil ++ xs zu xs evaluiert. 
Allerdings evaluiert xs ++ nil nicht zu xs, da xs nicht bekannt ist. 
Um zu beweisen dass xs ++ nil = xs benötigen wir strukturelle Induktion.
Die Taktik induction xs as [|x xs'] führt eine Induktion über die Liste xs aus. 
In den eckigen Klammern werden die Namen angegeben. 
Im Fall für nil müssen keine Variablen vergeben werden, 
im Fall für cons wird die Zahl x und die restliche Liste xs' genannt. 
Die Induktionshypothese bekommt den Namen IHxs'. 
Mit der Taktik simpl wird ein Ausdruck vereinfacht. 
Das ist ähnlich zu der Evaluierung mit Eval. *)
Lemma app_nil (xs : list) :
  xs ++ nil = xs.
Proof.
  induction xs as [|x xs'].
  - simpl. reflexivity.
  - simpl. rewrite IHxs'. reflexivity.
Qed.

(* Aufgabe 3.1 *)
(* Beweist, dass |xs ++ ys| = |xs| + |ys|. *)
Lemma length_app (xs ys : list) : 
  length (xs ++ ys) = length xs + length ys.
Proof.
  (* TODO *)
Admitted.

(* Aufgabe 3.2 *)
(* Beweist, dass map mit app verträglich ist: *)
Lemma map_app (f :nat -> nat) (xs ys : list) :
  map f (xs ++ ys) = (map f xs) ++ (map f ys).
Proof.
  (* TODO *)
Admitted.