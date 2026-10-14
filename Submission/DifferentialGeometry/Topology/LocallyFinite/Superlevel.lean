import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.AtTopBot.Tendsto

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter _root_.Topology

namespace UpperSemicontinuous
open _root_.UpperSemicontinuous

open _root_.UpperSemicontinuous in
theorem locallyFinite_of_tendsto_lower_bound
    {X L ι : Type*} [TopologicalSpace X] [Preorder L] [NoMaxOrder L]
    {f : X → L} (hf : UpperSemicontinuous f) {a : ι → L}
    (ha : _root_.Filter.Tendsto a _root_.Filter.cofinite _root_.Filter.atTop) (s : ι → Set X)
    (hbound : ∀ i, ∀ x ∈ s i, a i ≤ f x) : LocallyFinite s := by
  intro x
  obtain ⟨b, hb⟩ := _root_.NoMaxOrder.exists_gt (f x)
  refine ⟨{y | f y < b}, hf x b hb, ?_⟩
  apply (Filter.eventually_cofinite.mp (ha.eventually_ge_atTop b)).subset
  rintro i ⟨y, hy, hyb⟩ hi
  exact (not_lt_of_ge (hi.trans (hbound i y hy))) hyb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `UpperSemicontinuous.locallyFinite_of_tendsto_lower_bound then
    throwError "Refusing to shadow existing declaration UpperSemicontinuous.locallyFinite_of_tendsto_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `UpperSemicontinuous.locallyFinite_of_tendsto_lower_bound ``Submission.UpperSemicontinuous.locallyFinite_of_tendsto_lower_bound

end UpperSemicontinuous
