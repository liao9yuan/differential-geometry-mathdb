import Mathlib.Analysis.Calculus.ContDiff.RCLike

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.ContDiffOn in
theorem ContDiffOn.locallyLipschitzOn_of_isOpen
    {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {s : Set E}
    (hf : ContDiffOn 𝕜 1 f s) (hs : IsOpen s) : LocallyLipschitzOn s f := by
  intro x hx
  obtain ⟨K, t, ht, hK⟩ := ((hf x hx).contDiffAt (hs.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContDiffOn
  let env ← Lean.getEnv
  if env.contains `ContDiffOn.locallyLipschitzOn_of_isOpen then
    throwError "Refusing to shadow existing declaration ContDiffOn.locallyLipschitzOn_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffOn.locallyLipschitzOn_of_isOpen ``Submission.ContDiffOn.locallyLipschitzOn_of_isOpen
