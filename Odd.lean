import Mathlib.Data.List.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.Ring.Parity

def D (n : ℕ) : List ℚ :=
  List.range (2^n + 1) |>.map (λ k => k / (2^n : ℕ))

def complement {α : Type} [DecidableEq α] (l1 l2 : List α) : List α :=
  l1.filter (λ x => if x ∈ l2 then false else true)

#eval Odd 3
#eval D 0

lemma even_in_D_n_minus_one {k n : ℕ} (hk : Even k) :
  (k : ℚ) / (2^n : ℕ) ∈ D (n - 1) := by
  rcases hk with ⟨m, rfl⟩
  sorry

lemma OddNumD {k n : ℕ} 
  (h : (k : ℚ) / (2^n : ℕ) ∈ (complement (D n) (D (n - 1)))) : Odd k := by
  sorry

#print Nat.Coprime
