import Submission.DifferentialGeometry.Topology.Compactness.Cocompact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter

theorem tendsto_atTop_of_isCompact_sublevel
    {X L : Type*} [TopologicalSpace X] [LinearOrder L] {f : X → L}
    (hcompact : ∀ b : L, IsCompact {x | f x ≤ b}) :
    Tendsto f (_root_.Filter.cocompact X) atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [(hcompact b).compl_mem_cocompact] with x hx
  exact le_of_not_ge hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `tendsto_atTop_of_isCompact_sublevel then
    throwError "Refusing to shadow existing declaration tendsto_atTop_of_isCompact_sublevel"
  Lean.modifyEnv fun env => Lean.addAlias env `tendsto_atTop_of_isCompact_sublevel ``Submission.tendsto_atTop_of_isCompact_sublevel
