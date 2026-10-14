import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {k : WithTop ℕ∞} {s : Set M} {f : M → ℝ}

open _root_.ContMDiffOn in
theorem ContMDiffOn.log (hf : ContMDiffOn I 𝓘(ℝ, ℝ) k f s)
    (hzero : ∀ x ∈ s, f x ≠ 0) :
    ContMDiffOn I 𝓘(ℝ, ℝ) k (fun x => Real.log (f x)) s := by
  intro x hx
  exact (Real.contDiffAt_log.2 (hzero x hx)).comp_contMDiffWithinAt (hf x hx)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffOn
  let env ← Lean.getEnv
  if env.contains `ContMDiffOn.log then
    throwError "Refusing to shadow existing declaration ContMDiffOn.log"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffOn.log ``Submission.ContMDiffOn.log
