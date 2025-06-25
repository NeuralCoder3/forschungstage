-- Lean 4 translation of the Rocq tutorial – **step-wise proofs**
-- Each proof is given in tactic style with explanatory comments so you can
-- follow the individual proof steps, similar to Coq scripts.

-- Abschnitt 1: Aussagen in Lean

example (X : Prop) (h : X) : X := by
  -- Goal: prove X from hypothesis h : X
  exact h

example : True := by
  -- `trivial` closes any goal that is `True`.
  trivial

example (X Y : Prop) (h₁ : X) (h₂ : Y) : X ∧ Y := by
  -- To prove a conjunction we use `constructor`.
  constructor
  -- left conjunct
  exact h₁
  -- right conjunct
  exact h₂

example (X Y : Prop) (h : X ∧ Y) : X := by
  -- Break the conjunction into its two parts.
  cases h with
  | intro hX hY =>
    -- Now we have hX : X, hY : Y. Goal is X.
    exact hX

example (x : Nat) : x = x := by
  -- Reflexivity (`rfl`) solves equalities of the form t = t.
  rfl

example (x y : Nat) (h : x = y) : y = x := by
  -- `symm` turns goal `y = x` into `x = y`, which is exactly h.
  rewrite [h]
  rfl

-- Übungseinheit 1

example (X Y : Prop) (h : X ∧ Y) : Y ∧ X := by
  -- TODO
  cases h with
  | intro hX hY =>
    constructor
    exact hY
    exact hX

example (X : Prop) (h : X) : X ∧ True := by
  -- TODO
  constructor
  exact h
  trivial

example (x y : Nat) (h : x = y) : y = x := by
  -- TODO
  rw [h]

example (x y z : Nat) (h₁ : x = y) (h₂ : y = z) : x = z := by
  -- TODO
  rw [h₁]
  rw [h₂]

-- Abschnitt 2: Listen in Lean

#print Nat

inductive List' : Type
| nil : List'
| cons : Nat → List' → List'

namespace List'

infixr:60 " :: " => List'.cons

-- Folgende Funktion erzeugt eine Aussage, die gültig ist, wenn die gegebene Liste nicht leer ist:
def nonempty : List' → Prop
| nil => False
| _ :: _ => True

-- Diese Funktion berechnet die Länge einer Liste.
def length : List' → Nat
| nil => 0
| _ :: xs => Nat.succ (length xs)

-- Compute (in Coq) entspricht `#eval` in Lean
#eval length (0 :: 1 :: 2 :: nil)
#eval length nil

-- Die Funktion app hängt eine Liste an eine andere an.
def append : List' → List' → List'
| nil, ys => ys
| x :: xs, ys => x :: append xs ys

infixr:60 " ++ " => append

section Eval
  variable (xs : List')
  #eval (nil ++ xs)
  #eval ((1 :: 2 :: nil) ++ xs)
  #eval ((1 :: 2 :: xs) ++ (3 :: nil))
  #eval (xs ++ nil)
end Eval

-- Aufgabe 2.1
-- Definiert eine Funktion map, die eine Funktion f: nat -> nat  auf die Elemente einer Liste anwendet.
def map (f : Nat → Nat) : List' → List'
| nil => nil
| x :: xs => f x :: map f xs


#eval (map Nat.succ (1 :: 3 :: 4 :: nil))

-- Beweist, dass xs ++ nil = xs
lemma append_nil (xs : List') : xs ++ nil = xs := by
  induction xs with
  | nil =>
    simp
  | cons x xs ih =>
    simp [append, ih]

-- Aufgabe 3.1
-- Beweist, dass |xs ++ ys| = |xs| + |ys|.
lemma length_append (xs ys : List') : length (xs ++ ys) = length xs + length ys := by
  induction xs with
  | nil =>
    simp
  | cons x xs ih =>
    simp [length, append, ih]

-- Aufgabe 3.2
-- Beweist, dass map mit app verträglich ist:
lemma map_append (f : Nat → Nat) (xs ys : List') :
  map f (xs ++ ys) = (map f xs) ++ (map f ys) := by
  induction xs with
  | nil =>
    simp [map, append]
  | cons x xs ih =>
    simp [map, append, ih]

end List'
