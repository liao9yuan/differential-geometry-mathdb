import Submission.DifferentialGeometry.Topology.LoopSpace.RadialHomeomorphism
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Submission.DifferentialGeometry.Tensor.LinearAlgebra.ComplexDeterminant
import Submission.DifferentialGeometry.Analysis.Integration.Measure.ComplexSlitPlane

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

private theorem radialDirection_eq_exp_arg {z : ℂ} (hz : z ≠ 0) :
    (radialDirection z : ℂ) = Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
  have he := radialDirection_reconstruct z
  rw [Complex.real_smul] at he
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  exact mul_left_cancel₀ hn (he.trans (Complex.norm_mul_exp_arg_mul_I z).symm)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.radialDirection_eq_exp_arg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.radialDirection_eq_exp_arg target :: scope.openDecls } }

theorem radialExtension_geometricCircleHomeomorph_eq_exp_log
    (δ : loopCircle ≃ₜ loopCircle) {f : ℝ → ℝ}
    (hδ : ∀ s : ℝ, δ (s : loopCircle) = (f s : loopCircle))
    {z : ℂ} (hz : z ≠ 0) :
    radialExtension (geometricCircleHomeomorph δ) z =
      Complex.exp ((Complex.log z).re +
        (2 * Real.pi * f ((Complex.log z).im / (2 * Real.pi)) : ℝ) * Complex.I) := by
  have hz0 := hz
  have hdir : radialDirection z = AddCircle.toCircle ((Complex.arg z / (2 * Real.pi) : ℝ) : loopCircle) := by
    apply Subtype.ext
    rw [radialDirection_eq_exp_arg hz0]
    simp only [AddCircle.toCircle_apply_mk, Circle.coe_exp, div_one]
    congr 1
    push_cast
    field_simp
  rw [radialExtension, hdir, geometricCircleHomeomorph_boundary, hδ]
  simp only [AddCircle.toCircle_apply_mk, Circle.coe_exp, div_one,
    Complex.real_smul, Complex.log_im]
  rw [Complex.exp_add]
  congr 1
  rw [Complex.log_re, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr hz0)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialExtension_geometricCircleHomeomorph_eq_exp_log then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialExtension_geometricCircleHomeomorph_eq_exp_log"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialExtension_geometricCircleHomeomorph_eq_exp_log ``Submission.DifferentialGeometry.Topology.radialExtension_geometricCircleHomeomorph_eq_exp_log

def radialStretchLinearMap (a : ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp Complex.reCLM +
    Complex.I • (Complex.ofRealCLM.comp (a • Complex.imCLM))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialStretchLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialStretchLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialStretchLinearMap ``Submission.DifferentialGeometry.Topology.radialStretchLinearMap

theorem radialStretchLinearMap_apply (a : ℝ) (w : ℂ) :
    radialStretchLinearMap a w = (w.re : ℂ) + (a * w.im : ℝ) * Complex.I := by
  simp only [radialStretchLinearMap, _root_.add_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, _root_.smul_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    smul_eq_mul, mul_comm Complex.I]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialStretchLinearMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialStretchLinearMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialStretchLinearMap_apply ``Submission.DifferentialGeometry.Topology.radialStretchLinearMap_apply

theorem hasFDerivAt_radialExtension_geometricCircleHomeomorph
    (δ : loopCircle ≃ₜ loopCircle) {f : ℝ → ℝ}
    (hδ : ∀ s : ℝ, δ (s : loopCircle) = (f s : loopCircle))
    {z : ℂ} (hz : z ∈ Complex.slitPlane)
    (hf : DifferentiableAt ℝ f (Complex.arg z / (2 * Real.pi))) :
    HasFDerivAt (radialExtension (geometricCircleHomeomorph δ))
      ((Complex.exp ((Complex.log z).re +
          (2 * Real.pi * f ((Complex.log z).im / (2 * Real.pi)) : ℝ) * Complex.I)) •
        (radialStretchLinearMap (deriv f (Complex.arg z / (2 * Real.pi)))).comp
          (z⁻¹ • (1 : ℂ →L[ℝ] ℂ))) z := by
  let p := Complex.log z
  have hlog := (Complex.hasStrictFDerivAt_log_real hz).hasFDerivAt
  have hr := Complex.reCLM.hasFDerivAt.comp z hlog
  have hi := Complex.imCLM.hasFDerivAt.comp z hlog
  have hf' : HasDerivAt f (deriv f (p.im / (2 * Real.pi))) (p.im / (2 * Real.pi)) := by
    simpa only [p, Complex.log_im] using hf.hasDerivAt
  have hangle := hf'.comp_hasFDerivAt z (hi.mul_const (2 * Real.pi)⁻¹)
  have hangle' := Complex.ofRealCLM.hasFDerivAt.comp z (hangle.const_smul (2 * Real.pi))
  have hreal := Complex.ofRealCLM.hasFDerivAt.comp z hr
  have hsum := hreal.add (hangle'.mul_const Complex.I)
  have hexp := (Complex.hasDerivAt_exp _).comp_hasFDerivAt z hsum
  have heq : (radialExtension (geometricCircleHomeomorph δ)) =ᶠ[𝓝 z]
      (fun w : ℂ => Complex.exp ((Complex.log w).re +
        (2 * Real.pi * f ((Complex.log w).im / (2 * Real.pi)) : ℝ) * Complex.I)) :=
    Filter.eventuallyEq_of_mem (Complex.isOpen_slitPlane.mem_nhds hz)
      (fun w hw => radialExtension_geometricCircleHomeomorph_eq_exp_log δ hδ (Complex.slitPlane_ne_zero hw))
  apply (hexp.congr_of_eventuallyEq heq).congr_fderiv
  ext w
  simp only [ContinuousLinearMap.comp_apply, _root_.add_apply, _root_.smul_apply,
    Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    radialStretchLinearMap_apply, p, Complex.log_im, div_eq_mul_inv]
  push_cast
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hasFDerivAt_radialExtension_geometricCircleHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hasFDerivAt_radialExtension_geometricCircleHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hasFDerivAt_radialExtension_geometricCircleHomeomorph ``Submission.DifferentialGeometry.Topology.hasFDerivAt_radialExtension_geometricCircleHomeomorph


theorem det_radialStretchLinearMap (a : ℝ) :
    (radialStretchLinearMap a).toLinearMap.det = a := by
  rw [DifferentialGeometry.Geometry.complex_linearMap_det]
  simp [radialStretchLinearMap_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.det_radialStretchLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.det_radialStretchLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.det_radialStretchLinearMap ``Submission.DifferentialGeometry.Topology.det_radialStretchLinearMap

private theorem complex_smul_det (c : ℂ) (A : ℂ →L[ℝ] ℂ) :
    (c • A).toLinearMap.det = Complex.normSq c * A.toLinearMap.det := by
  rw [DifferentialGeometry.Geometry.complex_linearMap_det,
    DifferentialGeometry.Geometry.complex_linearMap_det]
  simp only [ContinuousLinearMap.coe_coe, _root_.smul_apply, smul_eq_mul,
    Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.complex_smul_det
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.complex_smul_det target :: scope.openDecls } }

theorem det_fderiv_radialExtension_geometricCircleHomeomorph
    (δ : loopCircle ≃ₜ loopCircle) {f : ℝ → ℝ}
    (hδ : ∀ s : ℝ, δ (s : loopCircle) = (f s : loopCircle))
    {z : ℂ} (hz : z ∈ Complex.slitPlane)
    (hf : DifferentiableAt ℝ f (Complex.arg z / (2 * Real.pi))) :
    (fderiv ℝ (radialExtension (geometricCircleHomeomorph δ)) z).toLinearMap.det =
      deriv f (Complex.arg z / (2 * Real.pi)) := by
  rw [(hasFDerivAt_radialExtension_geometricCircleHomeomorph δ hδ hz hf).fderiv,
    complex_smul_det]
  rw [show ((radialStretchLinearMap (deriv f (Complex.arg z / (2 * Real.pi)))).comp
      (z⁻¹ • (1 : ℂ →L[ℝ] ℂ))).toLinearMap =
        (radialStretchLinearMap (deriv f (Complex.arg z / (2 * Real.pi)))).toLinearMap.comp
          (z⁻¹ • (1 : ℂ →L[ℝ] ℂ)).toLinearMap from rfl,
    LinearMap.det_comp, det_radialStretchLinearMap, complex_smul_det]
  have hnorm : Complex.normSq
      (Complex.exp ((Complex.log z).re +
        (2 * Real.pi * f ((Complex.log z).im / (2 * Real.pi)) : ℝ) * Complex.I)) =
      Complex.normSq z := by
    rw [← radialExtension_geometricCircleHomeomorph_eq_exp_log δ hδ (Complex.slitPlane_ne_zero hz),
      Complex.normSq_eq_norm_sq, radialExtension_norm, Complex.normSq_eq_norm_sq]
  rw [hnorm, Complex.normSq_inv]
  have hz0 : Complex.normSq z ≠ 0 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (Complex.slitPlane_ne_zero hz))
  have hid : (1 : ℂ →L[ℝ] ℂ).toLinearMap.det = 1 := LinearMap.det_id
  rw [hid]
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.det_fderiv_radialExtension_geometricCircleHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.det_fderiv_radialExtension_geometricCircleHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.det_fderiv_radialExtension_geometricCircleHomeomorph ``Submission.DifferentialGeometry.Topology.det_fderiv_radialExtension_geometricCircleHomeomorph

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Topology


theorem fderiv_radialExtension_radialDirection
    (δ : loopCircle ≃ₜ loopCircle) {f : ℝ → ℝ}
    (hδ : ∀ s : ℝ, δ (s : loopCircle) = (f s : loopCircle))
    {z : ℂ} (hz : z ∈ Complex.slitPlane)
    (hf : DifferentiableAt ℝ f (Complex.arg z / (2 * Real.pi))) :
    fderiv ℝ (radialExtension (geometricCircleHomeomorph δ)) z (radialDirection z) =
      (geometricCircleHomeomorph δ (radialDirection z) : ℂ) := by
  have hz0 := Complex.slitPlane_ne_zero hz
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  have hnC : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [(hasFDerivAt_radialExtension_geometricCircleHomeomorph δ hδ hz hf).fderiv,
    ← radialExtension_geometricCircleHomeomorph_eq_exp_log δ hδ hz0]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    one_apply_eq_self, radialDirection_coe hz0, NormedSpace.normalize,
    Complex.real_smul, Complex.ofReal_inv]
  have hi : z⁻¹ * ((↑‖z‖)⁻¹ * z) = (↑‖z‖)⁻¹ := by field_simp
  rw [hi, radialStretchLinearMap_apply]
  simp only [← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_im, _root_.MulZeroClass.mul_zero,
    Complex.ofReal_zero, _root_.MulZeroClass.zero_mul, add_zero]
  rw [radialExtension, Complex.real_smul]
  push_cast
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fderiv_radialExtension_radialDirection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fderiv_radialExtension_radialDirection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fderiv_radialExtension_radialDirection ``Submission.DifferentialGeometry.Topology.fderiv_radialExtension_radialDirection

theorem fderiv_radialExtension_tangentDirection
    (δ : loopCircle ≃ₜ loopCircle) {f : ℝ → ℝ}
    (hδ : ∀ s : ℝ, δ (s : loopCircle) = (f s : loopCircle))
    {z : ℂ} (hz : z ∈ Complex.slitPlane)
    (hf : DifferentiableAt ℝ f (Complex.arg z / (2 * Real.pi))) :
    fderiv ℝ (radialExtension (geometricCircleHomeomorph δ)) z
        (Complex.I * (radialDirection z : ℂ)) =
      deriv f (Complex.arg z / (2 * Real.pi)) •
        (Complex.I * (geometricCircleHomeomorph δ (radialDirection z) : ℂ)) := by
  have hz0 := Complex.slitPlane_ne_zero hz
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  have hnC : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [(hasFDerivAt_radialExtension_geometricCircleHomeomorph δ hδ hz hf).fderiv,
    ← radialExtension_geometricCircleHomeomorph_eq_exp_log δ hδ hz0]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    one_apply_eq_self, radialDirection_coe hz0, NormedSpace.normalize,
    Complex.real_smul, Complex.ofReal_inv]
  have hi : z⁻¹ * (Complex.I * ((↑‖z‖)⁻¹ * z)) = (↑‖z‖)⁻¹ * Complex.I := by field_simp
  rw [hi, radialStretchLinearMap_apply]
  simp only [← Complex.ofReal_inv, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, _root_.MulZeroClass.mul_zero, sub_zero,
    mul_one, zero_add, Complex.ofReal_zero]
  rw [radialExtension, Complex.real_smul]
  push_cast
  field_simp
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fderiv_radialExtension_tangentDirection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fderiv_radialExtension_tangentDirection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fderiv_radialExtension_tangentDirection ``Submission.DifferentialGeometry.Topology.fderiv_radialExtension_tangentDirection

end DifferentialGeometry.Topology

end
