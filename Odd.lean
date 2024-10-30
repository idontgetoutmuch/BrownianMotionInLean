import Mathlib.Data.List.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Rat

example {l n : ℕ} : (2 * l) / (2^n * 2) = 2 * (l / (2^n * 2 )) := by
  let j : ℚ := l
  let m : ℚ := (2^n : ℕ)
  have h3 : (2 : ℚ) * j / (m * (2 : ℚ)) = (2 : ℚ) * (j / (m * (2 : ℚ))) := by rw [mul_div_assoc]
  sorry

#synth DivInvMonoid ℚ

example (n : ℕ) (h : n > 0) : n = n - 1 + 1 := by
  cases n with
  | zero => contradiction
  | succ m => rfl

example (n : ℕ) (h : n > 0) : n = n - 1 + 1 := by
  cases h with
  | _ => rfl

def D (n : ℕ) : List ℚ :=
  List.range (2^n + 1) |>.map (λ k => k / (2^n : ℕ))

def complement {α : Type} [DecidableEq α] (l1 l2 : List α) : List α :=
  l1.filter (λ x => if x ∈ l2 then false else true)

#eval Odd 3
#eval D 0

#check (2 : ℚ) / (2^3 : ℕ)

example (l : ℚ) : 2 * l / 2 = l := by
  have h2 : 2 * l / 2 = l := by simp
  exact h2

lemma even_in_D_n_minus_one {k n : ℕ} (h : n > 0) (hk : Even k) :
  (k : ℚ) / ((2 ^ n : ℕ) : ℚ) ∈ D (n - 1) := by
  rcases hk with ⟨l, rfl⟩
  have h5a : ((2 * l : ℚ) / 2) = (l : ℚ) := by simp
  sorry

lemma even_in_D_n_minus_one {k n : ℕ} (h : n > 0) (hk : Even k) :
  (k : ℚ) / ((2 ^ n : ℕ) : ℚ) ∈ D (n - 1) := by
  rcases hk with ⟨l, rfl⟩
  -- have h1 : 2^(n + 1) = 2^n * 2 := by rw [pow_succ]
  -- have h2 : (2 * l) / 2^(n + 1) = (2 * l) / (2^n * 2 ) := by rw [h1]
  -- have h3 : (2 * l) / ((2^n      * 2) : ℚ) = 2 * l / (2^n * 2 ) := by rw [mul_div_assoc]
  -- have h4 : (2 * l) / ((2^n : ℚ) * 2)      = (2 * l / 2) / 2^n := by rw [div_mul_eq_div_div_swap]
  have h5a : ((2 * l : ℚ) / 2) = (l : ℚ) := by simp -- [mul_div_cancel_left]
  -- have h5b : ((2 * l : ℚ) / 2) / 2^n = l / 2^n := by rw [mul_div_cancel_left]
  sorry

lemma even_in_D_n_minus_one {k n : ℕ} (h : n > 0) (hk : Even k) :
  (k : ℚ) / ((2 ^ n : ℕ) : ℚ) ∈ D (n - 1) := by
  cases n with
  | zero => contradiction
  | succ m =>
      rw [pow_succ]
      rcases hk with ⟨l, rfl⟩
      have h_div : (2 * l : ℚ) / (2^(m + 1) : ℕ) = l / (2^m : ℕ)
      sorry -- replace this with the remaining proof steps

lemma even_in_D_n_minus_one {k n : ℕ} (h : n > 0) (hk : Even k) :
  (k : ℚ) / ((2 ^ n : ℕ) : ℚ) ∈ D (n - 1) := by
  cases n with
  | zero => contradiction
  | succ m =>
    have h_pow : ((2 ^ (m + 1) : ℕ)) = ((2 ^ m : ℕ)) * 2 := by
      rw [pow_succ]
    rw [h_pow]
    rcases hk with ⟨l, rfl⟩
    -- Continue with further steps to show `(k : ℚ) / ((2 ^ m : ℕ) * 2 : ℚ) ∈ D (m)`
    sorry -- replace this with the remaining proof steps

lemma foo (n : ℕ) (h : n > 0) : 2 ^ n = 2 ^ (n - 1 + 1) := by
  cases n with
  | zero => contradiction
  | succ m => rfl

lemma OddNumD {k n : ℕ}
  (h : (k : ℚ) / (2^n : ℕ) ∈ (complement (D n) (D (n - 1)))) : Odd k := by
  sorry

#print Nat.Coprime

#min_imports
