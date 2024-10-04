-- This module serves as the root of the `Brownian` library.
-- Import modules here that should be built as part of the library.
import mathlib
import «Brownian».Basic

def lean : String := "Lean"

#eval String.append hello (String.append " " lean)

def HHaskell {α : Type} [LinearOrderedField α] (n : ℕ) (k : ℕ) (_ : 2 * k - 1 ≤ 2^n -1) (s : α) : ℤ :=
  let k':= 2 * k + 1
  if (k' - 1) * 2^(-n : ℤ) < s ∧ s <= k' * 2^(-n : ℤ)
  then 2^((n - 1) / 2)
  else if k' * 2^(-n : ℤ) < s && s <= (k' + 1) * 2^(-n : ℤ)
       then -2^((n - 1) / 2)
       else 0

def HHaskell {α : Type} [LinearOrderedField α] (n : ℕ) (k : ℕ) (_ : 2 * k - 1 ≤ 2^n - 1) (s : α) : ℤ :=
  let k' := 2 * k + 1
  match true with
  | (k' - 1) * 2^(-n : ℤ) < s ∧ s <= k'       * 2^(-n : ℤ) =>  2^((n - 1) / 2)
  | k'       * 2^(-n : ℤ) < s ∧ s <= (k' + 1) * 2^(-n : ℤ) => -2^((n - 1) / 2)
  | _                                                      => 0

#eval HHaskell 1 1 (by decide) (3/4 : ℚ)

def HPollard {α : Type} [LinearOrderedField α] (i : ℕ) (k : ℕ) (s : α) : Nat :=
  if (i * 2^(-k : ℤ) : α) < s ∧ s <= ((i + 1 / 2) * 2^(-k : ℤ))
    then 1
    else 0

def HPollard1 {α : Type} [LinearOrderedField α] (i : ℕ) (k : ℕ) (s : α) : Nat :=
  if (i * 2^(-k : ℤ) : α) < s ∧ s <= ((i + 1 / 2) * 2^(-k : ℤ))
    then 1
    else 0

def HPollard2 {α : Type} [LinearOrderedField α] (i : ℕ) (k : ℕ) (s : α) : Nat :=
  if (i * 2^(-k : ℤ) : α) < s ∧ s <= ((i + 1 / 2) * 2^(-k : ℤ))
    then 1
    else 0

#synth LinearOrderedField ℚ

#eval HPollard 0 0 (2 : ℚ)

#synth LinearOrderedField Float

#eval HPollard 0 0 (2 : ℝ)
