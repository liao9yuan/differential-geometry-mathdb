import Submission.DifferentialGeometry.Topology.Manifold.SphereRadialExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Manifold _root_.Module
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

section Basic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sphereDirection (v : _root_.Metric.sphere (0 : E) 1) (x : E) : _root_.Metric.sphere (0 : E) 1 := by
  classical
  exact if hx : x = 0 then v else
    ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hx)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereDirection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereDirection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereDirection ``Submission.DifferentialGeometry.Topology.Manifold.sphereDirection

theorem coe_sphereDirection (v : _root_.Metric.sphere (0 : E) 1) {x : E} (hx : x ≠ 0) :
    (sphereDirection v x : E) = ‖x‖⁻¹ • x := by
  rw [sphereDirection, dif_neg hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.coe_sphereDirection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.coe_sphereDirection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.coe_sphereDirection ``Submission.DifferentialGeometry.Topology.Manifold.coe_sphereDirection

theorem sphereDirection_pos_smul (v w : _root_.Metric.sphere (0 : E) 1) {r : ℝ} (hr : 0 < r) :
    sphereDirection v (r • (w : E)) = w := by
  apply Subtype.ext
  rw [coe_sphereDirection v (smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere w))]
  simp [norm_smul, norm_eq_of_mem_sphere, abs_of_pos hr, smul_smul, hr.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereDirection_pos_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereDirection_pos_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereDirection_pos_smul ``Submission.DifferentialGeometry.Topology.Manifold.sphereDirection_pos_smul

theorem norm_smul_sphereDirection (v : _root_.Metric.sphere (0 : E) 1) {x : E} (hx : x ≠ 0) :
    ‖x‖ • (sphereDirection v x : E) = x := by
  rw [coe_sphereDirection v hx, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.norm_smul_sphereDirection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.norm_smul_sphereDirection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.norm_smul_sphereDirection ``Submission.DifferentialGeometry.Topology.Manifold.norm_smul_sphereDirection

end Basic

theorem contMDiffOn_sphereDirection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (_root_.Module.finrank ℝ E = n + 1)] (v : _root_.Metric.sphere (0 : E) 1) :
    ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (sphereDirection v) ({0}ᶜ : Set E) := by
  let U : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun x : U ↦ (x : E)) := contMDiff_subtype_val
  have hn : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun x : U ↦ ‖(x : E)‖) :=
    fun x ↦ (contDiffAt_norm ℝ x.2).contMDiffAt.comp x (hv x)
  have hni : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun x : U ↦ ‖(x : E)‖⁻¹) :=
    hn.inv₀ (fun x ↦ norm_ne_zero_iff.mpr x.2)
  have hd : ContMDiff 𝓘(ℝ, E) (𝓡 n) ∞ (fun x : U ↦ sphereDirection v x) := by
    let d : U → _root_.Metric.sphere (0 : E) 1 := fun x ↦
      ⟨‖(x : E)‖⁻¹ • (x : E), mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm x.2)⟩
    have h : ContMDiff 𝓘(ℝ, E) (𝓡 n) ∞ d := (hni.smul hv).codRestrict_sphere _
    have heq : (fun x : U ↦ sphereDirection v x) = d := by
      funext x
      apply Subtype.ext
      exact coe_sphereDirection v x.2
    rw [heq]
    exact h
  intro x hx
  exact (contMDiffAt_subtype_iff (U := U) (f := sphereDirection v) |>.mp (hd ⟨x, hx⟩)).contMDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.contMDiffOn_sphereDirection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.contMDiffOn_sphereDirection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.contMDiffOn_sphereDirection ``Submission.DifferentialGeometry.Topology.Manifold.contMDiffOn_sphereDirection

end DifferentialGeometry.Topology.Manifold
