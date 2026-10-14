import Submission.DifferentialGeometry.Analysis.Integration.Measure.BoundedDensity
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.InnerProductSpace.PiL2

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.ContinuousLinearMap
open scoped _root_.Convolution _root_.ENNReal

namespace Convex
open _root_.Convex

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

open _root_.Convex in
theorem integral_smul_mem_of_nonneg_of_integral_eq_one
    {K : Set F} (hK : Convex ℝ K) (hKclosed : IsClosed K)
    {k : X → ℝ} (hk : AEMeasurable k μ) (hk0 : 0 ≤ᵐ[μ] k)
    (hk1 : ∫ x, k x ∂μ = 1) {f : X → F}
    (hfK : ∀ᵐ x ∂μ, f x ∈ K) (hfi : _root_.MeasureTheory.Integrable (fun x => k x • f x) μ) :
    (∫ x, k x • f x ∂μ) ∈ K := by
  let ν : _root_.MeasureTheory.Measure X := μ.withDensity (fun x => ENNReal.ofReal (k x))
  let : _root_.MeasureTheory.IsProbabilityMeasure ν := isProbabilityMeasure_withDensity_ofReal hk0 hk1
  have hfν : ∀ᵐ x ∂ν, f x ∈ K := (_root_.MeasureTheory.withDensity_absolutelyContinuous μ _).ae_le hfK
  have hiν : _root_.MeasureTheory.Integrable f ν := by
    apply (_root_.MeasureTheory.integrable_withDensity_iff_integrable_smul₀' hk.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
    apply hfi.congr
    filter_upwards [hk0] with x hx
    rw [ENNReal.toReal_ofReal hx]
  have hm := hK.integral_mem hKclosed hfν hiν
  have heq : (∫ x, f x ∂ν) = ∫ x, k x • f x ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hk.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hk0] with x hx
    rw [ENNReal.toReal_ofReal hx]
  rwa [heq] at hm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Convex.integral_smul_mem_of_nonneg_of_integral_eq_one then
    throwError "Refusing to shadow existing declaration Convex.integral_smul_mem_of_nonneg_of_integral_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Convex.integral_smul_mem_of_nonneg_of_integral_eq_one ``Submission.Convex.integral_smul_mem_of_nonneg_of_integral_eq_one

end Convex

namespace ContDiffBump
open _root_.ContDiffBump

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

open _root_.ContDiffBump in
local notation "V" => EuclideanSpace ℝ (Fin d)

open _root_.ContDiffBump in
theorem normed_convolution_mem_of_ae_mem_closed_convex
    (φ : ContDiffBump (0 : V)) {f : V → F} (hf : _root_.MeasureTheory.LocallyIntegrable f _root_.MeasureTheory.MeasureSpace.volume)
    {K : Set F} (hK : Convex ℝ K) (hKclosed : IsClosed K)
    (hfK : ∀ᵐ x ∂volume, f x ∈ K) (x : V) :
    (φ.normed _root_.MeasureTheory.MeasureSpace.volume ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] f) x ∈ K := by
  rw [_root_.MeasureTheory.convolution_def]
  apply hK.integral_smul_mem_of_nonneg_of_integral_eq_one hKclosed
    φ.continuous_normed.measurable.aemeasurable
    (Eventually.of_forall φ.nonneg_normed) φ.integral_normed
  · exact (Measure.measurePreserving_sub_left (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V) x).quasiMeasurePreserving.ae hfK
  · exact φ.hasCompactSupport_normed.convolutionExists_left (_root_.ContinuousLinearMap.lsmul ℝ ℝ)
      φ.continuous_normed hf x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffBump.normed_convolution_mem_of_ae_mem_closed_convex then
    throwError "Refusing to shadow existing declaration ContDiffBump.normed_convolution_mem_of_ae_mem_closed_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffBump.normed_convolution_mem_of_ae_mem_closed_convex ``Submission.ContDiffBump.normed_convolution_mem_of_ae_mem_closed_convex

open _root_.ContDiffBump in
theorem normed_convolution_indicator_mem_of_ae_mem_closed_convex
    (φ : ContDiffBump (0 : V)) {Ω : Set V} (hΩ : MeasurableSet Ω) {f : V → F}
    (hf : _root_.MeasureTheory.LocallyIntegrable (Ω.indicator f) _root_.MeasureTheory.MeasureSpace.volume)
    {K : Set F} (hK : Convex ℝ K) (hKclosed : IsClosed K) (h0 : (0 : F) ∈ K)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K) (x : V) :
    (φ.normed _root_.MeasureTheory.MeasureSpace.volume ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] (Ω.indicator f)) x ∈ K := by
  apply φ.normed_convolution_mem_of_ae_mem_closed_convex hf hK hKclosed
  filter_upwards [(_root_.MeasureTheory.ae_restrict_iff' hΩ).mp hfK] with y hy
  by_cases hyΩ : y ∈ Ω
  · rw [_root_.Set.indicator_of_mem hyΩ]
    exact hy hyΩ
  · rw [_root_.Set.indicator_of_notMem hyΩ]
    exact h0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffBump.normed_convolution_indicator_mem_of_ae_mem_closed_convex then
    throwError "Refusing to shadow existing declaration ContDiffBump.normed_convolution_indicator_mem_of_ae_mem_closed_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffBump.normed_convolution_indicator_mem_of_ae_mem_closed_convex ``Submission.ContDiffBump.normed_convolution_indicator_mem_of_ae_mem_closed_convex

end ContDiffBump

end

end
