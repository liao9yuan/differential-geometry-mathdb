import Submission.DifferentialGeometry.Topology.LocalHomeomorph.Univalent
import Submission.DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Comp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Topology
open scoped _root_.ContDiff

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_smooth_openPartialHomeomorph_of_injOn_det_ne_zero
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → E} (hf : ContDiffOn ℝ ∞ f Ω)
    (hi : _root_.Set.InjOn f Ω) (hd : ∀ z ∈ Ω, (fderiv ℝ f z).toLinearMap.det ≠ 0) :
    ∃ e : OpenPartialHomeomorph E E, e.source = Ω ∧ e.target = f '' Ω ∧
      (e : E → E) = f ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hlocal : IsLocalHomeomorphOn f Ω := by
    intro z hz
    let K := ((fderiv ℝ f z).toLinearMap.equivOfIsUnitDet
      (isUnit_iff_ne_zero.mpr (hd z hz))).toContinuousLinearEquiv
    have hK : K.toContinuousLinearMap = fderiv ℝ f z := by
      ext v
      exact LinearMap.equivOfIsUnitDet_apply _ v
    have hdf : HasFDerivAt f K.toContinuousLinearMap z := by
      rw [hK]
      exact ((hf.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hz)).hasFDerivAt
    obtain ⟨e, hez, _, _, _, heq⟩ := exists_localInverse_of_hasFDerivAt_equiv hf hΩ hz hdf
    exact ⟨e, hez, (funext heq).symm⟩
  obtain ⟨e, hes, het, hef⟩ := hlocal.exists_openPartialHomeomorph_of_injOn hΩ hi
  have he : ContDiffOn ℝ ∞ e e.source := by simpa only [hef, hes] using hf
  refine ⟨e, hes, het, hef, he, ?_⟩
  intro z hz
  have hx := e.map_target hz
  have hdx : (fderiv ℝ e (e.symm z)).toLinearMap.det ≠ 0 := by
    rw [hef]
    exact hd _ (hes ▸ hx)
  let K := ((fderiv ℝ e (e.symm z)).toLinearMap.equivOfIsUnitDet
    (isUnit_iff_ne_zero.mpr hdx)).toContinuousLinearEquiv
  have hK : K.toContinuousLinearMap = fderiv ℝ e (e.symm z) := by
    ext v
    exact LinearMap.equivOfIsUnitDet_apply _ v
  have hec := he.contDiffAt (e.open_source.mem_nhds hx)
  have hdf : HasFDerivAt e K.toContinuousLinearMap (e.symm z) := by
    rw [hK]
    exact (hec.differentiableAt (by simp)).hasFDerivAt
  exact (e.contDiffAt_symm hz hdf hec).contDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_smooth_openPartialHomeomorph_of_injOn_det_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_smooth_openPartialHomeomorph_of_injOn_det_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_smooth_openPartialHomeomorph_of_injOn_det_ne_zero ``Submission.DifferentialGeometry.Analysis.exists_smooth_openPartialHomeomorph_of_injOn_det_ne_zero

end DifferentialGeometry.Analysis

end

end

section

open _root_.Set _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis

theorem exists_open_det_fderiv_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {x : E} {s : Set E}
    (hf : ContDiffAt ℝ 1 f x) (hs : s ∈ 𝓝 x)
    (hpos : 0 < (fderiv ℝ f x).det) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ s ∧
      ∀ y ∈ U, 0 < (fderiv ℝ f y).det := by
  have hc : ContinuousAt (fun y => (fderiv ℝ f y).det) x :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      (hf.continuousAt_fderiv one_ne_zero)
  have hp : {y : E | 0 < (fderiv ℝ f y).det} ∈ 𝓝 x :=
    hc.preimage_mem_nhds (Ioi_mem_nhds hpos)
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp (_root_.Filter.inter_mem hs hp)
  exact ⟨U, hUopen, hxU, fun y hy => (hUsub hy).1,
    fun y hy => (hUsub hy).2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_open_det_fderiv_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_open_det_fderiv_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_open_det_fderiv_pos ``Submission.DifferentialGeometry.Analysis.exists_open_det_fderiv_pos

end DifferentialGeometry.Analysis

end
