import Mathlib.Analysis.Normed.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter
open scoped _root_.Topology

universe u v w x

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {X : Type x} [TopologicalSpace X]

open _root_.ContinuousWithinAt in
theorem ContinuousWithinAt.eventually_finrank_range_ge
    [FiniteDimensional 𝕜 E]
    {A : X → E →L[𝕜] F} {s : Set X} {x : X}
    (hA : ContinuousWithinAt A s x) :
    ∀ᶠ y in 𝓝[s] x,
      Module.finrank 𝕜 (A x).range ≤ Module.finrank 𝕜 (A y).range := by
  have hopen := isOpen_setOfPred_nat_le_rank (𝕜 := 𝕜) (E := E) (F := F)
    (Module.finrank 𝕜 (A x).range)
  have hmem : A x ∈ {f : E →L[𝕜] F |
      (Module.finrank 𝕜 (A x).range : Cardinal) ≤ (f : E →ₗ[𝕜] F).rank} := by
    change (Module.finrank 𝕜 (A x).range : Cardinal) ≤ Module.rank 𝕜 (A x).range
    rw [Module.finrank_eq_rank']
  have hev := hA.eventually (hopen.mem_nhds hmem)
  filter_upwards [hev] with y hy
  change (Module.finrank 𝕜 (A x).range : Cardinal) ≤ Module.rank 𝕜 (A y).range at hy
  rw [← Module.finrank_eq_rank'] at hy
  exact_mod_cast hy

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContinuousWithinAt
  let env ← Lean.getEnv
  if env.contains `ContinuousWithinAt.eventually_finrank_range_ge then
    throwError "Refusing to shadow existing declaration ContinuousWithinAt.eventually_finrank_range_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousWithinAt.eventually_finrank_range_ge ``Submission.ContinuousWithinAt.eventually_finrank_range_ge

open _root_.ContinuousAt in
theorem ContinuousAt.eventually_finrank_range_ge
    [FiniteDimensional 𝕜 E]
    {A : X → E →L[𝕜] F} {x : X} (hA : ContinuousAt A x) :
    ∀ᶠ y in 𝓝 x,
      Module.finrank 𝕜 (A x).range ≤ Module.finrank 𝕜 (A y).range := by
  simpa only [nhdsWithin_univ] using
    hA.continuousWithinAt.eventually_finrank_range_ge (s := Set.univ)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContinuousAt
  let env ← Lean.getEnv
  if env.contains `ContinuousAt.eventually_finrank_range_ge then
    throwError "Refusing to shadow existing declaration ContinuousAt.eventually_finrank_range_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAt.eventually_finrank_range_ge ``Submission.ContinuousAt.eventually_finrank_range_ge
