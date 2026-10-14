import Submission.DifferentialGeometry.Topology.PartialHomeomorph.CompactNeighborhood
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Set
open scoped _root_.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem exists_open_extChartAt_image_isCompact_closure
    (α : M) {C : Set M} (hC : IsCompact C)
    (hCs : C ⊆ (extChartAt I α).source) :
    ∃ W : Set E, IsOpen W ∧ extChartAt I α '' C ⊆ W ∧
      closure W ⊆ (extChartAt I α).target ∧ IsCompact (closure W) ∧
      IsCompact ((extChartAt I α).symm '' closure W) ∧
      (extChartAt I α).symm '' closure W ⊆ (extChartAt I α).source ∧
      MapsTo (extChartAt I α).symm W ((extChartAt I α).symm '' closure W) := by
  let e : PartialHomeomorph M E := {
    toPartialEquiv := extChartAt I α
    continuousOn_toFun := continuousOn_extChartAt α
    continuousOn_invFun := continuousOn_extChartAt_symm α }
  exact e.exists_open_image_isCompact_closure
    (isOpen_extChartAt_target α) hC hCs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exists_open_extChartAt_image_isCompact_closure then
    throwError "Refusing to shadow existing declaration exists_open_extChartAt_image_isCompact_closure"
  Lean.modifyEnv fun env => Lean.addAlias env `exists_open_extChartAt_image_isCompact_closure ``Submission.exists_open_extChartAt_image_isCompact_closure
