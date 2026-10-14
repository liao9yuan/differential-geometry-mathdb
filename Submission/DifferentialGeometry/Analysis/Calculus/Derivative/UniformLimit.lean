import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.UniformSpace.CompactConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter
open scoped _root_.Topology

namespace ContinuousMap
open _root_.ContinuousMap

variable {X F ι : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open _root_.ContinuousMap in
theorem hasDerivAt_comp_of_tendsto {l : Filter ι} [_root_.Filter.NeBot l]
    {f g : ι → C(X, F)} {u v : C(X, F)} {q : ℝ → X}
    (hf : _root_.Filter.Tendsto f l (𝓝 u)) (hg : _root_.Filter.Tendsto g l (𝓝 v))
    (hd : ∀ᶠ i in l, ∀ x : ℝ, HasDerivAt (fun t => f i (q t)) (g i (q x)) x)
    (x : ℝ) : HasDerivAt (fun t => u (q t)) (v (q x)) x := by
  apply hasDerivAt_of_tendstoUniformly
    ((_root_.ContinuousMap.tendsto_iff_tendstoUniformly.mp hg).comp q) hd
  intro t
  exact (_root_.ContinuousMap.tendsto_iff_tendstoUniformly.mp hf).tendsto_at (q t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMap.hasDerivAt_comp_of_tendsto then
    throwError "Refusing to shadow existing declaration ContinuousMap.hasDerivAt_comp_of_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMap.hasDerivAt_comp_of_tendsto ``Submission.ContinuousMap.hasDerivAt_comp_of_tendsto

end ContinuousMap
