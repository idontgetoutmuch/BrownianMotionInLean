import «Brownian».Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian

-- The dyadic points
def D {α : Type} [LinearOrderedField α] (n : ℕ) : List α :=
  List.range (2^n + 1) |>.map (λ k => k / (2^n : α))

-- FIXME: The list should be sorted
def binarySearch {α : Type} [LinearOrderedField α] [Inhabited α] (vec : List α) (x : α) : Nat :=
  let rec loop (l u : Nat) : Nat :=
    if u <= l then l
     else
      let k := l + (u - l) / 2
      if x <= vec.get! k then loop l k else loop (k + 1) u
  termination_by u - l
  loop 0 (vec.length - 1)

def testBinarySearch : Nat :=
  let vec : List ℚ := [1 / 2, 2 / 2, 3 / 2, 4 / 2, 5 / 2, 6 / 2, 7 / 2, 8 / 2, 9 / 2, 10 / 2]
  let x := 9 / 4
  binarySearch vec x

#eval testBinarySearch

def linearInterpolation (xzs : List (ℚ × ℚ)) : ℚ → ℚ :=
  let xs := xzs.map Prod.fst
  let zs := xzs.map Prod.snd
  λ t => if t < xs.head! || t > xs.last! then panic! "Cannot interpolate"
         else let ys := xs.map Rat.cast
              let i := binarySearch ys t
              let m := (t - ys.get! (i - 1)) / (ys.get! i - ys.get! (i - 1))
              m * zs.get! i + (1 - m) * zs.get! (i - 1)

open MeasureTheory ProbabilityTheory NNReal Real

variable {Ω : Type} [MeasureSpace Ω]
variable {μ : ℝ} {v : ℝ≥0}
variable {X : Ω → ℝ} (hX : Measure.map X ℙ = gaussianReal μ v)
#check X

variable {_ : MeasurableSpace Ω} {μ : Measure Ω}

def I : Set ℝ := {x | 0 ≤ x ∧ x ≤ 1}
variable {_ : MeasurableSpace I} {ν : Measure I}

theorem BrowianExistence
    {m : ∀ x, MeasurableSpace ℝ}
    {f : ∀ i, Ω → ℝ} (hf_Indep : iIndepFun m f μ) (h_Normal : Measure.map (f i) μ = gaussianReal 0 1)
    {i j : Ω -> ℝ} (hij : i ≠ j) :
    IndepFun (f i) (f j) μ := sorry

-- FIXME: I may have used the wrong spaces (ℝ instead of I or vice versa)
def Browian
    {m : ∀ x, MeasurableSpace ℝ}
    -- A supply of normally distributed random variables
    {Z : ∀ i : ℕ, I → ℝ} (hZ_Indep : iIndepFun m Z ν) (h_Normal : Measure.map (Z i) ν = gaussianReal 0 1)
    -- A supply of random values so that we can sample from the random variables
    {ω : ℕ -> I} :
    I -> ℝ -> ℝ :=
      -- To a first approximation, BM is the linear interpolation of 0 and a random sample from Z 0
      let F d t := if d == 1
                   then t * Z 1 (ω 1)
                   -- Do the ever better approximations once we know how to pattern match and recurse
                   else pi
      sorry

def HHaskell {α : Type} [LinearOrderedField α] (n : ℕ) (k : ℕ) (_ : 2 * k - 1 ≤ 2^n -1) (s : α) : ℤ :=
  let k':= 2 * k + 1
  if (k' - 1) * 2^(-n : ℤ) < s ∧ s <= k' * 2^(-n : ℤ)
  then 2^((n - 1) / 2)
  else if k' * 2^(-n : ℤ) < s && s <= (k' + 1) * 2^(-n : ℤ)
       then -2^((n - 1) / 2)
       else 0

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
