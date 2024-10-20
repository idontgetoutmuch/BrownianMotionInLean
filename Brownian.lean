import Mathlib
import «Brownian».Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.MeasureTheory.Constructions.UnitInterval

-- The dyadic points
def D {α : Type} [LinearOrderedField α] (n : ℕ) : List α :=
  List.range (2^n + 1) |>.map (λ k => k / (2^n : α))

def complement {α : Type} [DecidableEq α] (l1 l2 : List α) : List α :=
  l1.filter (λ x => if _ : x ∈ l2 then false else true)

def roundDiv2 {α : Type} [LinearOrderedField α] [FloorRing α] (x : α) : Nat :=
  Nat.div (Int.toNat (⌊x + 1⌋)) 2

partial def g {α : Type} [LinearOrderedField α] [FloorRing α] [Ord α] (p : α) (n : Nat) : ℕ :=
  if p ∈ (complement (D n) (D (n - 1))) then
    2^(n - 1) + roundDiv2 (2^n * p)
  else g p (n + 1)

def unD {α : Type} [LinearOrderedField α] [FloorRing α] [Ord α] (p : α) : ℕ :=
  if p ∈ D 0 then
    roundDiv2 (2^0 * p)
  else g p 1

#eval ((D 4) : List ℚ)
#eval (complement ((D 3) : List ℚ) (D 2))
#eval ((D 0) : List ℚ)
#eval unD (7/8 : ℚ)
#eval unD (0 : ℚ)

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

def linearInterpolation {α : Type} [LinearOrderedField α] [Inhabited α] (xzs : List (α × α)) : α → α :=
  let xs := xzs.map Prod.fst
  let zs := xzs.map Prod.snd
  λ t => if t < xs.head! || t > xs.getLast! then panic! "Cannot interpolate"
         else let i := binarySearch xs t
              let m := (t - xs.get! (i - 1)) / (xs.get! i - xs.get! (i - 1))
              m * zs.get! i + (1 - m) * zs.get! (i - 1)

open MeasureTheory ProbabilityTheory NNReal Real

class HasApproxSqrt2 (k) where sqrt2 : k
instance               : HasApproxSqrt2 ℚ where sqrt2 := 886731088897 / 627013566048
noncomputable instance : HasApproxSqrt2 ℝ where sqrt2 := Real.sqrt 2

def F {k : Type} [LinearOrderedField k] [FloorRing k] [Inhabited k] [HasApproxSqrt2 k]
         (Z : ℕ → k → k) (ω : ℕ → k) (n : ℕ) (t : k) : k :=
  if n == 0 then
    t * Z 0 (ω 0)
  else if t ∈ D (n - 1) then
    0
  else if t ∈ D n then
    Z (unD t) (ω (unD t))
  else let xys := D n |>.map (λ d => if d ∈ D (n - 1) then (d, 0) else (d, g d))
       linearInterpolation xys t
  where g (d : k) := let m := (n + 1) / 2
                     let s := if Odd n
                              then 1 / 2^m
                              else 1 / 2^m / HasApproxSqrt2.sqrt2
                     s * Z (unD d) (ω n)

def F1 {k : Type} [LinearOrderedField k] [FloorRing k] [Inhabited k] [HasApproxSqrt2 k]
         (Z : ℕ → k → k) (ω : ℕ → k) (n : ℕ) (t : k) : k -> k :=
  if n == 0 then
    λ x => t * Z 0 x
  else if t ∈ D (n - 1) then
    0
  else if t ∈ D n then
    λ x => Z (unD t) x
  else let xys := D n |>.map (λ d => if d ∈ D (n - 1) then (d, 0) else (d, g d))
       linearInterpolation xys
  where g (d : k) := let m := (n + 1) / 2
                     let s := if Odd n
                              then 1 / 2^m
                              else 1 / 2^m / HasApproxSqrt2.sqrt2
                     s * Z (unD d) (ω n)


open scoped unitInterval

#check volume I
#check volume ∅
#check volume (Set.Icc (1/2 : ℝ) (3/4 : ℝ))

noncomputable
def ν : (Measure I) := volume

#check volume.restrict I

#check ν ∅
#check ν (Set.Icc (0 : I) (1 : I))

variable {Ω : Type} [MeasureSpace Ω]
variable {μ : ℝ} {v : ℝ≥0}
variable {X : Ω → ℝ} (hX : Measure.map X ℙ = gaussianReal μ v)
#check X

def Y : I → ℝ := λ x => x^2
-- FIXME: Of course this isn't true but we could define a function via
-- Box-Müller that we could prove to satisfy this.
variable (hYY : Measure.map Y ν = gaussianReal 0 1)

noncomputable
def F4 [LinearOrderedField I] [FloorRing I]
       (Z : ℕ → Ω → ℝ) (n : ℕ) : Ω → (I → ℝ) :=
  if n == 0 then
    λ ω => λ t => t * Z 0 ω
  else λ ω => λ t =>
    if t ∈ D (n - 1) then
      0
    else if t ∈ D n then
      Z (unD t) ω
    else let xys := D n |>.map (λ d => if d ∈ D (n - 1) then (d, 0) else (d, g ω d))
         linearInterpolation xys t
    where g ω (d : ℝ) := let m := (n + 1) / 2
                         let s := if Odd n
                                  then 1 / 2^m
                                  else 1 / 2^m / HasApproxSqrt2.sqrt2
                         s * Z (unD d) ω

def J := Set.Icc (0 : ℚ) (1 : ℚ)

def F5 [LinearOrderedField J] [FloorRing J]
       (Z : ℕ → I → ℚ) (n : ℕ) : I → (J → ℚ) :=
  if n == 0 then
    λ ω => λ t => t * Z 0 ω
  else λ ω => λ t =>
    if t ∈ D (n - 1) then
      0
    else if t ∈ D n then
      Z (unD t) ω
    else let xys := D n |>.map (λ d => if d ∈ D (n - 1) then (d, 0) else (d, g ω d))
         linearInterpolation xys t
    where g ω (d : ℚ) := let m := (n + 1) / 2
                         let s := if Odd n
                                  then 1 / 2^m
                                  else 1 / 2^m / HasApproxSqrt2.sqrt2
                         s * Z (unD d) ω


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
