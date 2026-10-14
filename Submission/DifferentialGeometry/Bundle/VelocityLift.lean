import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

noncomputable def velocityLift (γ : 𝕜 → M) (t : 𝕜) : TangentBundle I M :=
  tangentMap 𝓘(𝕜, 𝕜) I γ ⟨t, (1 : 𝕜)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.velocityLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.velocityLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.velocityLift ``Submission.DifferentialGeometry.velocityLift

@[simp] theorem velocityLift_proj (γ : 𝕜 → M) (t : 𝕜) :
    (velocityLift (I := I) γ t).proj = γ t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.velocityLift_proj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.velocityLift_proj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.velocityLift_proj ``Submission.DifferentialGeometry.velocityLift_proj

@[simp] theorem velocityLift_snd (γ : 𝕜 → M) (t : 𝕜) :
    (velocityLift (I := I) γ t).snd = mfderiv 𝓘(𝕜, 𝕜) I γ t (1 : 𝕜) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.velocityLift_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.velocityLift_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.velocityLift_snd ``Submission.DifferentialGeometry.velocityLift_snd

theorem velocityLift_eq_tangentMap (γ : 𝕜 → M) (t : 𝕜) :
    velocityLift (I := I) γ t = tangentMap 𝓘(𝕜, 𝕜) I γ ⟨t, (1 : 𝕜)⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.velocityLift_eq_tangentMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.velocityLift_eq_tangentMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.velocityLift_eq_tangentMap ``Submission.DifferentialGeometry.velocityLift_eq_tangentMap

variable [IsManifold I 1 M] {m n : ℕ∞ω}

open _root_.ContMDiffAt in
theorem _root_.Submission.ContMDiffAt.velocityLift {γ : 𝕜 → M} {t : 𝕜}
    (hγ : ContMDiffAt 𝓘(𝕜, 𝕜) I n γ t) (hmn : m + 1 ≤ n) :
    ContMDiffAt 𝓘(𝕜, 𝕜) I.tangent m (velocityLift (I := I) γ) t := by
  have hv : ContMDiffAt 𝓘(𝕜, 𝕜) (𝓘(𝕜, 𝕜)).tangent m
      (fun s : 𝕜 => (⟨s, (1 : 𝕜)⟩ : TangentBundle 𝓘(𝕜, 𝕜) 𝕜)) t := by
    rw [_root_.Bundle.contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    simpa using (contMDiffAt_const (I := 𝓘(𝕜, 𝕜)) (I' := 𝓘(𝕜, 𝕜))
      (n := m) (c := (1 : 𝕜)) (x := t))
  exact (hγ.mfderiv_const hmn).clm_apply_of_inCoordinates hv
    (hγ.of_le (le_self_add.trans hmn))

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffAt
  let env ← Lean.getEnv
  if env.contains `ContMDiffAt.velocityLift then
    throwError "Refusing to shadow existing declaration ContMDiffAt.velocityLift"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffAt.velocityLift ``Submission.ContMDiffAt.velocityLift

end DifferentialGeometry
