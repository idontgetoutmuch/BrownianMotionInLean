import Mathlib

open MeasureTheory ProbabilityTheory NNReal Real Filter Finset Asymptotics
open Set Filter TopologicalSpace
open Topology Filter Cardinal MeasureSpace  MeasureTheory.Measure
open BoundedContinuousFunction BoxIntegral PMF
open ENNReal ProbabilityMeasure ClosedIicTopology

variable  {Ω : Type*} [MeasureSpace Ω] (μ : ProbabilityMeasure Ω)
variable {M : ℝ} {V : ℝ≥0}

noncomputable
def gaussian_cdf (μ : ℝ) (v : ℝ≥0) (x : ℝ) := --: ℝ≥0 :=
  ∫ t in (Iic x), gaussianPDFReal μ v t ∂volume

#check cdf_nonneg
#check MeasureTheory.withDensity_apply sorry sorry

variable
(m : ℝ)
(v : ℝ≥0)
(hv : v ≠ 0)

#check m

#check ∫⁻ (a : ℝ) in (Iic (0 : ℝ)), ENNReal.ofReal (gaussianPDFReal m v a) ∂volume

noncomputable
def f := (λ x => ENNReal.ofReal (gaussianPDFReal m v x))

noncomputable
def ν : Measure ℝ := volume.withDensity (f m v)

noncomputable
def my_gaussian_cdf (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  cdf (ν μ v) x

#check ν m v (Iic (0 : ℝ))

open MeasureTheory

#check ∞
#check MeasureTheory.withDensity_apply (f m v)  measurableSet_Iic
#check ((Iic (∞ : ℝ≥0∞)) : Set  (ℝ≥0∞))

instance foo (hv : v ≠ 0) : IsProbabilityMeasure (ν m v) := by
  have h1 : (volume.withDensity (f m v)) = ν m v := rfl
  have h2 : (volume.withDensity (f m v)) Set.univ = ∫⁻ (a : ℝ), ENNReal.ofReal (gaussianPDFReal m v a) ∂volume := by
    rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ]
    rw [MeasureTheory.Measure.restrict_univ]
    congr
  have h7 : ν m v Set.univ =  ∫⁻ (a : ℝ), ENNReal.ofReal (gaussianPDFReal m v a) ∂volume := by
    rw [<-h1]
    exact h2

  have h7z : 0 ≤ᶠ[ae ℙ] gaussianPDFReal m v := by
    apply Eventually.of_forall
    exact gaussianPDFReal_nonneg m v

  have h8 : ENNReal.ofReal (∫ (a : ℝ), gaussianPDFReal m v a ∂volume) =
            ∫⁻ (a : ℝ), ENNReal.ofReal (gaussianPDFReal m v a) ∂volume := by
    apply MeasureTheory.ofReal_integral_eq_lintegral_ofReal (ProbabilityTheory.integrable_gaussianPDFReal m v) h7z

  have h9 : ∫ (a : ℝ), gaussianPDFReal m v a ∂volume = 1 := integral_gaussianPDFReal_eq_one m hv

  have h10 : ∫⁻ (a : ℝ), ENNReal.ofReal (gaussianPDFReal m v a) ∂volume = 1 := by
    rw [← h8]
    rw [h9]
    rw [ENNReal.ofReal_one]

  apply IsProbabilityMeasure.mk
  show (ν m v) Set.univ = 1
  rw [h7]
  exact h10

lemma gaussian_cdf_eq_my_gaussian_cdf (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
  gaussian_cdf μ v x = my_gaussian_cdf μ v x := by
  have h1 : gaussian_cdf μ v x =  ∫ t in (Iic x), gaussianPDFReal μ v t ∂volume := by
    rfl
  have h2 : my_gaussian_cdf μ v x = cdf (ν μ v) x := by
    rfl
  have h3 : IsProbabilityMeasure (ν μ v) := by
    apply foo μ v hv
  have h4 : cdf (ν μ v) x = ((ν μ v) (Iic x)).toReal := by
    apply ProbabilityTheory.cdf_eq_toReal (ν μ v) x

  have h5 : ν μ v (Iic (x : ℝ)) = ∫⁻ (a : ℝ) in (Iic (x : ℝ)), ENNReal.ofReal (gaussianPDFReal μ v a) ∂volume := by
    apply MeasureTheory.withDensity_apply (f μ v) measurableSet_Iic

  have h_nonneg_ae : 0 ≤ᶠ[ae ℙ] gaussianPDFReal μ v := by
    apply Eventually.of_forall
    exact gaussianPDFReal_nonneg μ v

  have h6 : ENNReal.ofReal (∫ (x : ℝ), (gaussianPDFReal μ v) x ∂volume) =
            ∫⁻ (x : ℝ), ENNReal.ofReal (gaussianPDFReal μ v x) ∂volume := by
            apply ofReal_integral_eq_lintegral_ofReal (ProbabilityTheory.integrable_gaussianPDFReal μ v) h_nonneg_ae

  have h7 : my_gaussian_cdf μ v x = (∫⁻ (a : ℝ) in (Iic (x : ℝ)), ENNReal.ofReal (gaussianPDFReal μ v a) ∂volume).toReal :=
    calc my_gaussian_cdf μ v x = cdf (ν μ v) x := by exact h2
      _ = ((ν μ v) (Iic x)).toReal := by exact h4
      _ = (∫⁻ (a : ℝ) in (Iic (x : ℝ)), ENNReal.ofReal (gaussianPDFReal μ v a) ∂volume).toReal := by rw[h5]

  have h8 : (∫⁻ (a : ℝ) in (Iic (x : ℝ)), ENNReal.ofReal (gaussianPDFReal μ v a) ∂volume).toReal =
            (ENNReal.ofReal (∫ (a : ℝ) in (Iic (x : ℝ)), (gaussianPDFReal μ v) a ∂volume)).toReal := by

    have h_indicator : ∫ (a : ℝ) in (Iic x), gaussianPDFReal μ v a ∂volume =
                      ∫ (a : ℝ), (Set.indicator (Iic x) (gaussianPDFReal μ v)) a ∂volume := by
      rw [MeasureTheory.integral_indicator measurableSet_Iic]

    have h_lintegral_indicator : ∫⁻ (a : ℝ) in (Iic x), ENNReal.ofReal (gaussianPDFReal μ v a) ∂volume =
                                 ∫⁻ (a : ℝ), ENNReal.ofReal ((Set.indicator (Iic x) (gaussianPDFReal μ v)) a) ∂volume := by
      rw [MeasureTheory.lintegral_indicator _ measurableSet_Iic]

    have h8a : ENNReal.ofReal (∫ (a : ℝ), (Set.indicator (Iic x) (gaussianPDFReal μ v)) a ∂volume) =
               ∫⁻ (a : ℝ), ENNReal.ofReal ((Set.indicator (Iic x) (gaussianPDFReal μ v)) a) ∂volume := by
               apply ofReal_integral_eq_lintegral_ofReal sorry sorry

    rw [h8a]

  sorry
