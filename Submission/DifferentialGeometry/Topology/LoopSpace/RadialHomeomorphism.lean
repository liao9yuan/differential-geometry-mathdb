import Submission.DifferentialGeometry.Topology.LoopSpace.RadialExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.NNReal

namespace DifferentialGeometry.Topology



def radialDiskHomeomorph (F : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hF : LipschitzWith K F) (hF' : LipschitzWith L F.symm) : closedDisk ≃ₜ closedDisk where
  toFun z := ⟨radialExtension F z, by
    simpa only [_root_.Metric.mem_closedBall, dist_zero_right, radialExtension_norm] using z.property⟩
  invFun z := ⟨radialExtension F.symm z, by
    simpa only [_root_.Metric.mem_closedBall, dist_zero_right, radialExtension_norm] using z.property⟩
  left_inv z := by
    apply Subtype.ext
    change radialExtension F.symm (radialExtension F z) = (z : ℂ)
    rw [← radialExtension_comp]
    have heq : (F.symm ∘ F : Circle → Circle) = id := funext F.symm_apply_apply
    rw [heq, radialExtension_id]
  right_inv z := by
    apply Subtype.ext
    change radialExtension F (radialExtension F.symm z) = (z : ℂ)
    rw [← radialExtension_comp]
    have heq : (F ∘ F.symm : Circle → Circle) = id := funext F.apply_symm_apply
    rw [heq, radialExtension_id]
  continuous_toFun := ((radialExtension_lipschitz hF).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((radialExtension_lipschitz hF').continuous.comp continuous_subtype_val).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialDiskHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialDiskHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialDiskHomeomorph ``Submission.DifferentialGeometry.Topology.radialDiskHomeomorph

theorem radialDiskHomeomorph_lipschitz (F : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hF : LipschitzWith K F) (hF' : LipschitzWith L F.symm) :
    LipschitzWith (2 * K + 1) (radialDiskHomeomorph F hF hF') := by
  intro z w
  exact radialExtension_lipschitz hF z w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialDiskHomeomorph_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialDiskHomeomorph_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialDiskHomeomorph_lipschitz ``Submission.DifferentialGeometry.Topology.radialDiskHomeomorph_lipschitz

theorem radialDiskHomeomorph_symm_lipschitz (F : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hF : LipschitzWith K F) (hF' : LipschitzWith L F.symm) :
    LipschitzWith (2 * L + 1) (radialDiskHomeomorph F hF hF').symm := by
  intro z w
  exact radialExtension_lipschitz hF' z w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialDiskHomeomorph_symm_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialDiskHomeomorph_symm_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialDiskHomeomorph_symm_lipschitz ``Submission.DifferentialGeometry.Topology.radialDiskHomeomorph_symm_lipschitz



def geometricCircleHomeomorph (ψ : loopCircle ≃ₜ loopCircle) : Circle ≃ₜ Circle :=
  ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.trans ψ).trans
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.geometricCircleHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.geometricCircleHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.geometricCircleHomeomorph ``Submission.DifferentialGeometry.Topology.geometricCircleHomeomorph

theorem geometricCircleHomeomorph_boundary (ψ : loopCircle ≃ₜ loopCircle) (θ : loopCircle) :
    geometricCircleHomeomorph ψ (AddCircle.toCircle θ) = AddCircle.toCircle (ψ θ) := by
  have hleft : (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
      (AddCircle.toCircle θ) = θ := by
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact (AddCircle.homeomorphCircle one_ne_zero).symm_apply_apply θ
  change (AddCircle.homeomorphCircle one_ne_zero)
    (ψ ((AddCircle.homeomorphCircle one_ne_zero).symm (AddCircle.toCircle θ))) = _
  rw [hleft, AddCircle.homeomorphCircle_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.geometricCircleHomeomorph_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.geometricCircleHomeomorph_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.geometricCircleHomeomorph_boundary ``Submission.DifferentialGeometry.Topology.geometricCircleHomeomorph_boundary

theorem geometricCircleHomeomorph_symm (ψ : loopCircle ≃ₜ loopCircle) :
    (geometricCircleHomeomorph ψ).symm = geometricCircleHomeomorph ψ.symm := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.geometricCircleHomeomorph_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.geometricCircleHomeomorph_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.geometricCircleHomeomorph_symm ``Submission.DifferentialGeometry.Topology.geometricCircleHomeomorph_symm



theorem geometricCircleHomeomorph_lipschitz (ψ : loopCircle ≃ₜ loopCircle) {K : ℝ≥0}
    (hψ : LipschitzWith K ψ) : ∃ C : ℝ≥0, LipschitzWith C (geometricCircleHomeomorph ψ) := by
  have hb : LipschitzWith ⟨2 * Real.pi, by positivity⟩ (fun θ : loopCircle => AddCircle.toCircle θ) :=
    fun x y => circle_boundary_lipschitz x y
  have h := hb.comp (hψ.comp circle_parameter_lipschitz)
  refine ⟨⟨2 * Real.pi, by positivity⟩ * (K * 1), ?_⟩
  intro z w
  change _root_.EDist.edist ((AddCircle.homeomorphCircle one_ne_zero)
      (ψ ((AddCircle.homeomorphCircle one_ne_zero).symm z)))
    ((AddCircle.homeomorphCircle one_ne_zero)
      (ψ ((AddCircle.homeomorphCircle one_ne_zero).symm w))) ≤ _
  rw [AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply]
  exact h z w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.geometricCircleHomeomorph_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.geometricCircleHomeomorph_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.geometricCircleHomeomorph_lipschitz ``Submission.DifferentialGeometry.Topology.geometricCircleHomeomorph_lipschitz



theorem exists_radial_disk_reparametrization (ψ : loopCircle ≃ₜ loopCircle) {K L : ℝ≥0}
    (hψ : LipschitzWith K ψ) (hψ' : LipschitzWith L ψ.symm) :
    ∃ φ : closedDisk ≃ₜ closedDisk,
      (∀ θ, φ (diskBoundary θ) = diskBoundary (ψ θ)) ∧
      ∃ K' L' : ℝ≥0, LipschitzWith K' φ ∧ LipschitzWith L' φ.symm := by
  obtain ⟨Cf, hf⟩ := geometricCircleHomeomorph_lipschitz ψ hψ
  obtain ⟨Ci, hi⟩ := geometricCircleHomeomorph_lipschitz ψ.symm hψ'
  rw [← geometricCircleHomeomorph_symm] at hi
  let φ := radialDiskHomeomorph (geometricCircleHomeomorph ψ) hf hi
  refine ⟨φ, ?_, _, _, radialDiskHomeomorph_lipschitz _ hf hi,
    radialDiskHomeomorph_symm_lipschitz _ hf hi⟩
  intro θ
  apply Subtype.ext
  change radialExtension (geometricCircleHomeomorph ψ) (AddCircle.toCircle θ : ℂ) =
    (AddCircle.toCircle (ψ θ) : ℂ)
  rw [radialExtension_circle, geometricCircleHomeomorph_boundary]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_radial_disk_reparametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_radial_disk_reparametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_radial_disk_reparametrization ``Submission.DifferentialGeometry.Topology.exists_radial_disk_reparametrization

end DifferentialGeometry.Topology
