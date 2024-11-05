import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau
import Batteries.Data.Rat.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Integrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.FloorPow
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Probability.Variance
import Mathlib.Topology.Basic
import Mathlib.Topology.Filter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.NotNormal
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.BoxIntegral.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable

open MeasureTheory ProbabilityTheory NNReal Real Filter Finset Asymptotics
open Set Filter TopologicalSpace
open Topology Filter Cardinal MeasureSpace  MeasureTheory.Measure BoundedContinuousFunction BoxIntegral


def ConvergenceInDistribution1 {Ω : Type*} [MeasureSpace Ω]
                               {μ : ProbabilityMeasure Ω}
                               {X_i : ℕ → Ω → ℝ}
                               {X_lim : Ω → ℝ}: Prop :=
  ∀ x : ℝ, Tendsto (fun i => rnDeriv (Measure.map (X_i i) μ) volume x) atTop (𝓝 (rnDeriv (Measure.map X_lim μ) volume x))

def AlmostSureConvergence {Ω : Type*} [MeasureSpace Ω]
                          (μ : ProbabilityMeasure Ω)
                          (X_i : ℕ → Ω → ℝ)
                          (X_lim : Ω → ℝ): Prop :=
  ∀ᵐ ω ∂μ.toMeasure, Tendsto (fun i => X_i i ω) atTop (𝓝 (X_lim ω))

def ConvergenceInDistribution2  {Ω : Type*} [MeasureSpace Ω]
                                (X_i : ℕ → Ω → ℝ)
                                (X_lim : Ω → ℝ)
                                (μ : ProbabilityMeasure Ω)
                                (f : ℝ →ᵇ ℝ): Prop :=
    Tendsto (fun i =>  ∫ a, f ((X_i i) a) ∂μ) atTop (𝓝 (∫ a, f (X_lim a) ∂μ))

theorem pointwise_convergence_of_f  {Ω : Type*} [MeasureSpace Ω]
                                    (μ : ProbabilityMeasure Ω)
                                    (X_i : ℕ → Ω → ℝ)
                                    (X_lim : Ω → ℝ)
                                    (f : ℝ →ᵇ ℝ)
                                    (h_as_conv: AlmostSureConvergence μ X_i X_lim):
  ∀ᵐ ω ∂μ.toMeasure, Tendsto (fun n => f (X_i n ω)) atTop (𝓝 (f (X_lim ω))) := by
  filter_upwards [h_as_conv] with ω h_ω
  exact Tendsto.comp ( f.continuous.tendsto (X_lim ω)) h_ω

variable {CC : ℝ}


theorem as_convergence_is_convergence_in_distribution
  {Ω : Type*} [MeasureSpace Ω]
  (X_i : ℕ → Ω → ℝ)
  (X_lim : Ω → ℝ)
  (μ : ProbabilityMeasure Ω)
  (h_mu : IsFiniteMeasure μ.toMeasure)
  (f : ℝ →ᵇ ℝ) -- f is bounded continuous
  (h_as_conv: AlmostSureConvergence μ X_i X_lim)
  (X_i_measurable : ∀ i, Measurable (X_i i)) -- New measurability assumption for each X_i n
 :
  ConvergenceInDistribution2 X_i X_lim μ f := by

  -- Step 3: Prove `F n` is almost everywhere strongly measurable
  let F := fun i ω => f (X_i i ω)
  have X_i_meas : ∀ i, AEStronglyMeasurable (X_i i) μ := by
    intro i
    exact Measurable.aestronglyMeasurable (X_i_measurable i)

  have F_measurable : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro i
    exact f.continuous.comp_aestronglyMeasurable (X_i_meas i)  --aestronglyMeasurable_id

  obtain ⟨M, hM⟩ := f.bounded
  let someBound : Ω -> ℝ  := (fun ω => M + dist (F 0 ω) 0)
  let F0_dist : Ω -> ℝ  := (fun ω => dist (F 0 ω) 0)
  let F0 : Ω -> ℝ  := (fun ω => F 0 ω)

  have h_bound2 : ∀ i, ∀ᵐ ω ∂μ.toMeasure, ‖F i ω‖ ≤ someBound ω := by
    intro i
    apply Filter.Eventually.of_forall
    intro ω
    -- Step 1: Rewrite `‖F i ω‖` as `dist (F i ω, 0)`
    have h_norm_is_dist : ‖F i ω‖ = dist (F i ω) 0 := by
      rw [Real.norm_eq_abs, Real.dist_eq, sub_zero]

    -- Step 2: Apply the triangle inequality to `dist (F i ω, 0)`
    have h_triangle : dist (F i ω) 0 ≤ dist (F i ω) (F 0 ω) + dist (F 0 ω) 0 :=
      dist_triangle _ _ _

    -- Step 3: Use `hM` to bound `dist (F i ω, F 0 ω) ≤ M`
    have h_dist_bound : dist (F i ω) (F 0 ω) ≤ M := hM (X_i i ω) (X_i 0 ω)

    -- Step 4: Conclude that `‖F i ω‖ ≤ M + dist (F 0 ω, 0)`
    rw [h_norm_is_dist]
    exact le_trans h_triangle (add_le_add h_dist_bound (le_refl (dist (F 0 ω) 0)))




  -- Step 1: Prove that `F0` is integrable
  have F0_integrable : Integrable F0 μ := by
    -- Show that `F0` is almost everywhere strongly measurable
    have F0_aemeasurable : AEStronglyMeasurable F0 μ := by
      exact F_measurable 0

    -- Step 2: Use the triangle inequality to bound `‖F 0 ω‖` with the help of `hM`
    obtain ⟨M, hM⟩ := f.bounded

    let limFn : Ω -> ℝ  := (fun ω => M + ‖f 0‖)
    have h_bound : ∀ ω, ‖F0 ω‖ ≤ limFn ω := by
      intro ω
      -- Step 1: Rewrite `‖F i ω‖` as `dist (F i ω) 0`
      have h_norm_is_dist : ‖F0 ω‖ = dist (F0 ω) 0 := by
        rw [Real.norm_eq_abs, Real.dist_eq, sub_zero]

      -- Step 2: Apply the triangle inequality to `dist (F i ω) 0`
      have h_triangle : dist (F0 ω) 0 ≤ dist (F0 ω) (f 0) + dist (f 0) 0 :=
        dist_triangle _ _ _

      -- Step 3: Simplify `dist (f 0) 0` as `‖f 0‖`
      have h_dist_f0 : dist (f 0) 0 = ‖f 0‖ := by
        rw [Real.norm_eq_abs, Real.dist_eq, sub_zero]

      -- Step 4: Use `hM` to bound `dist (F i ω) (f 0) ≤ M`
      have h_dist_bound : dist (F 0 ω) (f 0) ≤ M := hM (X_i 0 ω) 0

      -- Step 5: Substitute and finalize the bound
      rw [h_norm_is_dist]  -- Substitute `‖F i ω‖` with `dist (F i ω) 0`
      apply le_trans h_triangle
      rw [h_dist_f0]       -- Substitute `dist (f 0) 0` with `‖f 0‖`
      exact add_le_add h_dist_bound (le_refl ‖f 0‖)

    -- Convert `h_bound` to an almost-everywhere bound
    have h_bound_ae : ∀ᵐ ω ∂μ.toMeasure, ‖F0 ω‖ ≤ limFn ω := Filter.Eventually.of_forall h_bound

    have M_ge_0 : 0 < M ∨ 0 = M := by
      have hM_nonneg : 0 ≤ M := by
        -- Use that `M` bounds the distance between any two values of `f`
        specialize hM (f 0) (f 0)
        -- Since `dist (f 0) (f 0) = 0`, we have `0 ≤ M`
        rw [dist_self] at hM
        exact hM

      -- Conclude `0 < M ∨ 0 = M` by comparing with `0`
      exact hM_nonneg.lt_or_eq

    have h_bound_ae_norm : ∀ᵐ ω ∂μ.toMeasure, ‖F0 ω‖ ≤ ‖limFn ω‖ :=  by
      have h_limFn_eq : ∀ ω, ‖limFn ω‖ = limFn ω := by
        intro ω
        -- Since `limFn ω = M + ‖f 0‖`, which is non-negative, we have `‖limFn ω‖ = limFn ω`
        rw [Real.norm_eq_abs]
        exact abs_of_nonneg (add_nonneg (le_of_lt_or_eq M_ge_0) (norm_nonneg (f 0)))

      -- Now apply `h_bound_ae` using the equality `‖limFn ω‖ = limFn ω`
      filter_upwards [h_bound_ae] with ω h_bound_ae_ω
      rw [h_limFn_eq ω]
      exact h_bound_ae_ω


    have integrable_bound : Integrable limFn μ := by
      exact integrable_const (M + ‖f 0‖)

    exact ⟨F0_aemeasurable, integrable_bound.2.mono h_bound_ae_norm⟩


  have F0_dist_integrable : Integrable F0_dist μ := by
    have h_norm_is_dist : ∀ ω,  dist (F 0 ω) 0 = ‖F 0 ω‖ := by
      intro ω
      rw [Real.norm_eq_abs, Real.dist_eq, sub_zero]
    have : F0_dist = (fun ω => ‖F 0 ω‖) := funext h_norm_is_dist
    rw [this]
    exact F0_integrable.norm


  have some_bound_integrable : Integrable someBound μ := by
    apply MeasureTheory.Integrable.add
    exact integrable_const M
    exact F0_dist_integrable

  -- Step 6: Apply the Dominated Convergence Theorem
  apply MeasureTheory.tendsto_integral_of_dominated_convergence someBound F_measurable some_bound_integrable h_bound2 (pointwise_convergence_of_f μ X_i X_lim f h_as_conv)
