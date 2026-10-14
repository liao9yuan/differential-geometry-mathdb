import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Operations
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false

open scoped _root_.ENNReal _root_.NNReal

namespace EMetric

variable {X : Type*} [PseudoEMetricSpace X]

theorem abs_toReal_edist_sub_le_of_edist_ne_top
    {x y p : X} (hxp : _root_.EDist.edist x p ≠ ⊤) (hyp : _root_.EDist.edist y p ≠ ⊤) :
    |(_root_.EDist.edist x p).toReal - (_root_.EDist.edist y p).toReal| ≤ (_root_.EDist.edist x y).toReal := by
  have hxy : _root_.EDist.edist x y ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
      ⟨hxp, by simpa only [_root_.PseudoEMetricSpace.edist_comm p y] using hyp⟩) (_root_.PseudoEMetricSpace.edist_triangle x p y)
  have hfirst := ENNReal.toReal_le_add (_root_.PseudoEMetricSpace.edist_triangle x y p) hxy hyp
  have hsecond := ENNReal.toReal_le_add (_root_.PseudoEMetricSpace.edist_triangle y x p)
    (by simpa only [_root_.PseudoEMetricSpace.edist_comm y x] using hxy) hxp
  rw [_root_.PseudoEMetricSpace.edist_comm y x] at hsecond
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EMetric.abs_toReal_edist_sub_le_of_edist_ne_top then
    throwError "Refusing to shadow existing declaration EMetric.abs_toReal_edist_sub_le_of_edist_ne_top"
  Lean.modifyEnv fun env => Lean.addAlias env `EMetric.abs_toReal_edist_sub_le_of_edist_ne_top ``Submission.EMetric.abs_toReal_edist_sub_le_of_edist_ne_top

theorem ofReal_abs_toReal_edist_sub_le_of_edist_ne_top
    {x y p : X} (hxp : _root_.EDist.edist x p ≠ ⊤) (hyp : _root_.EDist.edist y p ≠ ⊤) :
    ENNReal.ofReal |(_root_.EDist.edist x p).toReal - (_root_.EDist.edist y p).toReal| ≤ _root_.EDist.edist x y :=
  (ENNReal.ofReal_le_ofReal
    (abs_toReal_edist_sub_le_of_edist_ne_top hxp hyp)).trans ENNReal.ofReal_toReal_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EMetric.ofReal_abs_toReal_edist_sub_le_of_edist_ne_top then
    throwError "Refusing to shadow existing declaration EMetric.ofReal_abs_toReal_edist_sub_le_of_edist_ne_top"
  Lean.modifyEnv fun env => Lean.addAlias env `EMetric.ofReal_abs_toReal_edist_sub_le_of_edist_ne_top ``Submission.EMetric.ofReal_abs_toReal_edist_sub_le_of_edist_ne_top

theorem ofReal_abs_toReal_edist_excess_sub_le_of_edist_ne_top
    {x y p : X} (hxp : _root_.EDist.edist x p ≠ ⊤) (hyp : _root_.EDist.edist y p ≠ ⊤) (R : ℝ) :
    ENNReal.ofReal |_root_.Max.max ((_root_.EDist.edist x p).toReal - R) 0 -
      max ((_root_.EDist.edist y p).toReal - R) 0| ≤ _root_.EDist.edist x y := by
  have hmax := abs_max_sub_max_le_abs ((_root_.EDist.edist x p).toReal - R)
    ((_root_.EDist.edist y p).toReal - R) 0
  have heq : ((_root_.EDist.edist x p).toReal - R) - ((_root_.EDist.edist y p).toReal - R) =
      (_root_.EDist.edist x p).toReal - (_root_.EDist.edist y p).toReal := by ring
  rw [heq] at hmax
  exact (ENNReal.ofReal_le_ofReal hmax).trans
    (ofReal_abs_toReal_edist_sub_le_of_edist_ne_top hxp hyp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EMetric.ofReal_abs_toReal_edist_excess_sub_le_of_edist_ne_top then
    throwError "Refusing to shadow existing declaration EMetric.ofReal_abs_toReal_edist_excess_sub_le_of_edist_ne_top"
  Lean.modifyEnv fun env => Lean.addAlias env `EMetric.ofReal_abs_toReal_edist_excess_sub_le_of_edist_ne_top ``Submission.EMetric.ofReal_abs_toReal_edist_excess_sub_le_of_edist_ne_top

theorem lipschitzWith_toReal_edist_comp
    {Z : Type*} [PseudoEMetricSpace Z] {U : Z → X} {L : ℝ≥0}
    (hU : LipschitzWith L U) (p : X) (hfin : ∀ z, _root_.EDist.edist (U z) p ≠ ⊤) :
    LipschitzWith L (fun z => (_root_.EDist.edist (U z) p).toReal) := by
  intro z w
  rw [edist_dist, Real.dist_eq]
  exact (ofReal_abs_toReal_edist_sub_le_of_edist_ne_top (hfin z) (hfin w)).trans
    (hU z w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EMetric.lipschitzWith_toReal_edist_comp then
    throwError "Refusing to shadow existing declaration EMetric.lipschitzWith_toReal_edist_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `EMetric.lipschitzWith_toReal_edist_comp ``Submission.EMetric.lipschitzWith_toReal_edist_comp

theorem lipschitzWith_toReal_edist_excess_comp
    {Z : Type*} [PseudoEMetricSpace Z] {U : Z → X} {L : ℝ≥0}
    (hU : LipschitzWith L U) (p : X) (hfin : ∀ z, _root_.EDist.edist (U z) p ≠ ⊤) (R : ℝ) :
    LipschitzWith L (fun z => _root_.Max.max ((_root_.EDist.edist (U z) p).toReal - R) 0) := by
  intro z w
  rw [edist_dist, Real.dist_eq]
  exact (ofReal_abs_toReal_edist_excess_sub_le_of_edist_ne_top
    (hfin z) (hfin w) R).trans (hU z w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EMetric.lipschitzWith_toReal_edist_excess_comp then
    throwError "Refusing to shadow existing declaration EMetric.lipschitzWith_toReal_edist_excess_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `EMetric.lipschitzWith_toReal_edist_excess_comp ``Submission.EMetric.lipschitzWith_toReal_edist_excess_comp

end EMetric


end
