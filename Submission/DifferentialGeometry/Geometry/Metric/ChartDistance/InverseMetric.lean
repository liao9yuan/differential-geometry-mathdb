import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry

variable {V E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

private theorem mfderiv_apply_mfderiv_symm
    (ψ : OpenPartialHomeomorph V M)
    (hψ : ContMDiffOn 𝓘(ℝ, V) I 1 ψ ψ.source)
    (hψsymm : ContMDiffOn I 𝓘(ℝ, V) 1 ψ.symm ψ.target)
    {y : V} (hy : y ∈ ψ.source) (v : TangentSpace I (ψ y)) :
    mfderiv 𝓘(ℝ, V) I ψ y (mfderiv I 𝓘(ℝ, V) ψ.symm (ψ y) v) = v := by
  have hforward : MDifferentiableAt 𝓘(ℝ, V) I ψ y :=
    (hψ.contMDiffAt (ψ.open_source.mem_nhds hy)).mdifferentiableAt one_ne_zero
  have hbackward : MDifferentiableAt I 𝓘(ℝ, V) ψ.symm (ψ y) :=
    (hψsymm.contMDiffAt (ψ.open_target.mem_nhds (ψ.map_source hy))).mdifferentiableAt
      one_ne_zero
  have heq : (ψ : V → M) ∘ (ψ.symm : M → V) =ᶠ[𝓝 (ψ y)] id := by
    filter_upwards [ψ.open_target.mem_nhds (ψ.map_source hy)] with p hp
    exact ψ.right_inv hp
  have hchain := mfderiv_comp_apply_of_eq (I := I) (I' := 𝓘(ℝ, V)) (I'' := I)
    (x := ψ y) hforward hbackward (ψ.left_inv hy) v
  rw [heq.mfderiv_eq, mfderiv_id] at hchain
  exact hchain.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.mfderiv_apply_mfderiv_symm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.mfderiv_apply_mfderiv_symm target :: scope.openDecls } }

variable [IsManifold I ∞ M]

theorem mul_norm_mfderiv_symm_sq_le
    (g : SmoothRiemannianMetric I M) (ψ : OpenPartialHomeomorph V M)
    (hψ : ContMDiffOn 𝓘(ℝ, V) I 1 ψ ψ.source)
    (hψsymm : ContMDiffOn I 𝓘(ℝ, V) 1 ψ.symm ψ.target)
    {y : V} (hy : y ∈ ψ.source) {m : ℝ}
    (hbound : ∀ ξ : V, m * ‖ξ‖ ^ 2 ≤
      g.inner (ψ y) (mfderiv 𝓘(ℝ, V) I ψ y ξ) (mfderiv 𝓘(ℝ, V) I ψ y ξ))
    (v : TangentSpace I (ψ y)) :
    m * @_root_.Norm.norm V _ (mfderiv I 𝓘(ℝ, V) ψ.symm (ψ y) v) ^ 2 ≤ g.inner (ψ y) v v := by
  have h := hbound (mfderiv I 𝓘(ℝ, V) ψ.symm (ψ y) v)
  rwa [mfderiv_apply_mfderiv_symm ψ hψ hψsymm hy v] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.mul_norm_mfderiv_symm_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.mul_norm_mfderiv_symm_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.mul_norm_mfderiv_symm_sq_le ``Submission.DifferentialGeometry.Geometry.mul_norm_mfderiv_symm_sq_le

theorem norm_mfderiv_symm_le_inv_sqrt_mul
    (g : SmoothRiemannianMetric I M) (ψ : OpenPartialHomeomorph V M)
    (hψ : ContMDiffOn 𝓘(ℝ, V) I 1 ψ ψ.source)
    (hψsymm : ContMDiffOn I 𝓘(ℝ, V) 1 ψ.symm ψ.target)
    {y : V} (hy : y ∈ ψ.source) {m : ℝ} (hm : 0 < m)
    (hbound : ∀ ξ : V, m * ‖ξ‖ ^ 2 ≤
      g.inner (ψ y) (mfderiv 𝓘(ℝ, V) I ψ y ξ) (mfderiv 𝓘(ℝ, V) I ψ y ξ))
    (v : TangentSpace I (ψ y)) :
    @_root_.Norm.norm V _ (mfderiv I 𝓘(ℝ, V) ψ.symm (ψ y) v) ≤
      (Real.sqrt m)⁻¹ * Real.sqrt (g.inner (ψ y) v v) := by
  let w : V := mfderiv I 𝓘(ℝ, V) ψ.symm (ψ y) v
  change ‖w‖ ≤ (Real.sqrt m)⁻¹ * Real.sqrt (g.inner (ψ y) v v)
  have hsq : m * ‖w‖ ^ 2 ≤ g.inner (ψ y) v v :=
    mul_norm_mfderiv_symm_sq_le g ψ hψ hψsymm hy hbound v
  have hs := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul hm.le, Real.sqrt_sq_eq_abs, abs_norm] at hs
  calc
    ‖w‖ ≤ Real.sqrt (g.inner (ψ y) v v) / Real.sqrt m :=
      (le_div_iff₀ (Real.sqrt_pos.mpr hm)).mpr (by simpa only [mul_comm] using hs)
    _ = (Real.sqrt m)⁻¹ * Real.sqrt (g.inner (ψ y) v v) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.norm_mfderiv_symm_le_inv_sqrt_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.norm_mfderiv_symm_le_inv_sqrt_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.norm_mfderiv_symm_le_inv_sqrt_mul ``Submission.DifferentialGeometry.Geometry.norm_mfderiv_symm_le_inv_sqrt_mul

end DifferentialGeometry.Geometry

end

end
