import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Calculus

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

def sphereRadialExtension (f : _root_.Metric.sphere (0 : E) 1 → _root_.Metric.sphere (0 : E) 1) (x : E) : E := by
  classical
  exact if hx : x = 0 then 0 else
    ‖x‖ • (f ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hx)⟩ : E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereRadialExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereRadialExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereRadialExtension ``Submission.DifferentialGeometry.Topology.Manifold.sphereRadialExtension

theorem sphereRadialExtension_of_ne_zero
    (f : _root_.Metric.sphere (0 : E) 1 → _root_.Metric.sphere (0 : E) 1) {x : E} (hx : x ≠ 0) :
    sphereRadialExtension f x =
      ‖x‖ • (f ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hx)⟩ : E) :=
  dif_neg hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereRadialExtension_of_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereRadialExtension_of_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereRadialExtension_of_ne_zero ``Submission.DifferentialGeometry.Topology.Manifold.sphereRadialExtension_of_ne_zero

theorem sphereRadialExtension_pos_smul
    (f : _root_.Metric.sphere (0 : E) 1 → _root_.Metric.sphere (0 : E) 1) (v : _root_.Metric.sphere (0 : E) 1)
    {r : ℝ} (hr : 0 < r) :
    sphereRadialExtension f (r • (v : E)) = r • (f v : E) := by
  have hx := smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere v)
  rw [sphereRadialExtension_of_ne_zero _ hx]
  have hn : ‖r • (v : E)‖ = r := by
    simp [norm_smul, norm_eq_of_mem_sphere, abs_of_pos hr]
  have hd : (⟨‖r • (v : E)‖⁻¹ • (r • (v : E)),
      mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hx)⟩ : _root_.Metric.sphere (0 : E) 1) = v := by
    apply Subtype.ext
    change ‖r • (v : E)‖⁻¹ • (r • (v : E)) = (v : E)
    rw [hn]
    simp [smul_smul, hr.ne']
  rw [hd, hn]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereRadialExtension_pos_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereRadialExtension_pos_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereRadialExtension_pos_smul ``Submission.DifferentialGeometry.Topology.Manifold.sphereRadialExtension_pos_smul

theorem norm_sphereRadialExtension (f : _root_.Metric.sphere (0 : E) 1 → _root_.Metric.sphere (0 : E) 1) (x : E) :
    ‖sphereRadialExtension f x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [sphereRadialExtension, hx]
  · simp [sphereRadialExtension, hx, norm_smul, norm_eq_of_mem_sphere]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.norm_sphereRadialExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.norm_sphereRadialExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.norm_sphereRadialExtension ``Submission.DifferentialGeometry.Topology.Manifold.norm_sphereRadialExtension

theorem sphereRadialExtension_id : sphereRadialExtension (id : _root_.Metric.sphere (0 : E) 1 → _) = id := by
  funext x
  by_cases hx : x = 0
  · simp [sphereRadialExtension, hx]
  · simp [sphereRadialExtension, hx, smul_smul, norm_ne_zero_iff.mpr hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereRadialExtension_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereRadialExtension_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereRadialExtension_id ``Submission.DifferentialGeometry.Topology.Manifold.sphereRadialExtension_id

theorem sphereRadialExtension_comp (f g : _root_.Metric.sphere (0 : E) 1 → _root_.Metric.sphere (0 : E) 1) :
    sphereRadialExtension (g ∘ f) = sphereRadialExtension g ∘ sphereRadialExtension f := by
  funext x
  by_cases hx : x = 0
  · simp [sphereRadialExtension, hx]
  · have hy : sphereRadialExtension f x ≠ 0 := by
      intro h
      have hn := norm_sphereRadialExtension f x
      rw [h, norm_zero] at hn
      exact hx (norm_eq_zero.mp hn.symm)
    have hdir :
        (⟨‖sphereRadialExtension f x‖⁻¹ • sphereRadialExtension f x,
          mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hy)⟩ : _root_.Metric.sphere (0 : E) 1) =
        f ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hx)⟩ := by
      apply Subtype.ext
      change ‖sphereRadialExtension f x‖⁻¹ • sphereRadialExtension f x = _
      rw [norm_sphereRadialExtension]
      simp [sphereRadialExtension, hx, smul_smul, norm_ne_zero_iff.mpr hx]
    change sphereRadialExtension (g ∘ f) x = sphereRadialExtension g (sphereRadialExtension f x)
    rw [sphereRadialExtension_of_ne_zero _ hx, sphereRadialExtension_of_ne_zero _ hy,
      hdir, norm_sphereRadialExtension]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereRadialExtension_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereRadialExtension_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereRadialExtension_comp ``Submission.DifferentialGeometry.Topology.Manifold.sphereRadialExtension_comp

end Basic
section Smooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

theorem contDiffOn_sphereRadialExtension_family
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (f : P → _root_.Metric.sphere (0 : E) 1 → _root_.Metric.sphere (0 : E) 1)
    (hf : ContMDiff (𝓘(ℝ, P).prod (𝓡 n)) (𝓡 n) ∞
      (fun q : P × _root_.Metric.sphere (0 : E) 1 ↦ f q.1 q.2)) :
    ContDiffOn ℝ ∞ (fun q : P × E ↦ sphereRadialExtension (f q.1) q.2)
      {q | q.2 ≠ 0} := by
  let U : TopologicalSpace.Opens (P × E) :=
    ⟨{q | q.2 ≠ 0}, isOpen_compl_singleton.preimage continuous_snd⟩
  have hp : ContMDiff 𝓘(ℝ, P × E) 𝓘(ℝ, P) ∞ (fun q : U ↦ q.1.1) :=
    contDiff_fst.contMDiff.comp contMDiff_subtype_val
  have hx : ContMDiff 𝓘(ℝ, P × E) 𝓘(ℝ, E) ∞ (fun q : U ↦ q.1.2) :=
    contDiff_snd.contMDiff.comp contMDiff_subtype_val
  have hn : ContMDiff 𝓘(ℝ, P × E) 𝓘(ℝ) ∞ (fun q : U ↦ ‖q.1.2‖) := by
    intro q
    exact (contDiffAt_norm ℝ q.2).contMDiffAt.comp q (hx q)
  have hni : ContMDiff 𝓘(ℝ, P × E) 𝓘(ℝ) ∞ (fun q : U ↦ ‖q.1.2‖⁻¹) :=
    fun q ↦ (contDiffAt_inv ℝ (norm_ne_zero_iff.mpr q.2)).contMDiffAt.comp q (hn q)
  let d : U → _root_.Metric.sphere (0 : E) 1 := fun q ↦
    ⟨‖q.1.2‖⁻¹ • q.1.2, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm q.2)⟩
  have hd : ContMDiff 𝓘(ℝ, P × E) (𝓡 n) ∞ d :=
    (hni.smul hx).codRestrict_sphere _
  have hval : ContMDiff 𝓘(ℝ, P × E) 𝓘(ℝ, E) ∞
      (fun q : U ↦ sphereRadialExtension (f q.1.1) q.1.2) := by
    have hs := hn.smul (contMDiff_coe_sphere.comp (hf.comp (hp.prodMk hd)))
    have heq : (fun q : U ↦ sphereRadialExtension (f q.1.1) q.1.2) =
        (fun q : U ↦ ‖q.1.2‖ • (f q.1.1 (d q) : E)) := by
      funext q
      exact dif_neg q.2
    rw [heq]
    exact hs
  intro q hq
  exact (contMDiffAt_subtype_iff (U := U)
    (f := fun q : P × E ↦ sphereRadialExtension (f q.1) q.2) |>.mp
    (hval ⟨q, hq⟩)).contDiffAt.contDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.contDiffOn_sphereRadialExtension_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.contDiffOn_sphereRadialExtension_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.contDiffOn_sphereRadialExtension_family ``Submission.DifferentialGeometry.Topology.Manifold.contDiffOn_sphereRadialExtension_family

theorem contDiffOn_sphereRadialExtension
    (f : _root_.Metric.sphere (0 : E) 1 → _root_.Metric.sphere (0 : E) 1)
    (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f) :
    ContDiffOn ℝ ∞ (sphereRadialExtension f) ({0}ᶜ : Set E) := by
  have h := contDiffOn_sphereRadialExtension_family (fun _ : ℝ ↦ f)
    (hf.comp contMDiff_snd)
  exact h.comp (show ContDiff ℝ ∞ (fun x : E ↦ ((0 : ℝ), x)) from
    contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hx ↦ hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.contDiffOn_sphereRadialExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.contDiffOn_sphereRadialExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.contDiffOn_sphereRadialExtension ``Submission.DifferentialGeometry.Topology.Manifold.contDiffOn_sphereRadialExtension

end Smooth
end DifferentialGeometry.Topology.Manifold
