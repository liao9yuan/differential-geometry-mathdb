import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.EMetricSpace.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



open _root_.Set _root_.Metric
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis



theorem edist_ne_top_of_preconnected {X : Type*} [PseudoEMetricSpace X] [PreconnectedSpace X]
    (x y : X) : _root_.EDist.edist x y ≠ ⊤ := by
  have h : _root_.Metric.eball x (⊤ : ℝ≥0∞) = univ :=
    (show IsClopen (_root_.Metric.eball x (⊤ : ℝ≥0∞)) from ⟨isClosed_eball_top, isOpen_eball⟩).eq_univ
      ⟨x, _root_.Metric.mem_eball_self (by simp)⟩
  have hy : y ∈ _root_.Metric.eball x (⊤ : ℝ≥0∞) := h ▸ _root_.Set.mem_univ y
  exact ne_top_of_lt (by simpa only [_root_.Metric.mem_eball, _root_.PseudoEMetricSpace.edist_comm] using hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.edist_ne_top_of_preconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.edist_ne_top_of_preconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.edist_ne_top_of_preconnected ``Submission.DifferentialGeometry.Analysis.edist_ne_top_of_preconnected

end DifferentialGeometry.Analysis
