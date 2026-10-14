import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



open _root_.Set _root_.Metric

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]



theorem exists_compact_cthickening_subset {S U : Set F} (hS : IsCompact S)
    (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ IsCompact (_root_.Metric.cthickening ρ S) ∧ _root_.Metric.cthickening ρ S ⊆ U := by
  obtain ⟨a, ha, haU⟩ := hS.exists_cthickening_subset_open hU hSU
  obtain ⟨b, hb, hbK⟩ := hS.exists_isCompact_cthickening
  exact ⟨min a b, lt_min ha hb,
    hbK.of_isClosed_subset _root_.Metric.isClosed_cthickening (_root_.Metric.cthickening_mono (min_le_right _ _) _),
    (_root_.Metric.cthickening_mono (min_le_left _ _) _).trans haU⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_compact_cthickening_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_compact_cthickening_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_compact_cthickening_subset ``Submission.DifferentialGeometry.Analysis.exists_compact_cthickening_subset

end DifferentialGeometry.Analysis
