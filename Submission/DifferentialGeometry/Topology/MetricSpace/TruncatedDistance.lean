import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Group.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open scoped _root_.ENNReal _root_.NNReal

namespace EMetric

variable {X : Type*} [PseudoEMetricSpace X]

theorem lipschitzWith_truncated_edist (p : X) :
    LipschitzWith 1 (fun x => (_root_.Min.min (_root_.EDist.edist x p) 1).toReal) := by
  intro x y
  rw [ENNReal.coe_one, one_mul]
  change _root_.EDist.edist ((_root_.Min.min (_root_.EDist.edist x p) 1).toReal) ((_root_.Min.min (_root_.EDist.edist y p) 1).toReal) ≤ _root_.EDist.edist x y
  by_cases hxy : _root_.EDist.edist x y = ⊤
  · rw [hxy]
    exact le_top
  by_cases hxp : _root_.EDist.edist x p = ⊤
  · have hyp : _root_.EDist.edist y p = ⊤ := by
      by_contra hyp
      have hfin := ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hxy, hyp⟩)
        (_root_.PseudoEMetricSpace.edist_triangle x y p)
      exact hfin hxp
    rw [hxp, hyp, _root_.PseudoEMetricSpace.edist_self]
    exact zero_le
  · have hyp : _root_.EDist.edist y p ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
        ⟨by simpa only [_root_.PseudoEMetricSpace.edist_comm y x] using hxy, hxp⟩) (_root_.PseudoEMetricSpace.edist_triangle y x p)
    have hmin := (LipschitzWith.id (α := ℝ)).min_const 1
    have h := hmin (_root_.EDist.edist x p).toReal (_root_.EDist.edist y p).toReal
    simp only [ENNReal.coe_one, one_mul] at h
    rw [ENNReal.toReal_min hxp (by simp), ENNReal.toReal_min hyp (by simp),
      ENNReal.toReal_one]
    apply h.trans
    rw [edist_dist, Real.dist_eq]
    have hx := ENNReal.toReal_le_add (_root_.PseudoEMetricSpace.edist_triangle x y p) hxy hyp
    have hy := ENNReal.toReal_le_add (_root_.PseudoEMetricSpace.edist_triangle y x p)
      (by simpa only [_root_.PseudoEMetricSpace.edist_comm y x] using hxy) hxp
    rw [_root_.PseudoEMetricSpace.edist_comm y x] at hy
    have habs : |(_root_.EDist.edist x p).toReal - (_root_.EDist.edist y p).toReal| ≤ (_root_.EDist.edist x y).toReal :=
      abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    exact (ENNReal.ofReal_le_ofReal habs).trans ENNReal.ofReal_toReal_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EMetric.lipschitzWith_truncated_edist then
    throwError "Refusing to shadow existing declaration EMetric.lipschitzWith_truncated_edist"
  Lean.modifyEnv fun env => Lean.addAlias env `EMetric.lipschitzWith_truncated_edist ``Submission.EMetric.lipschitzWith_truncated_edist

theorem norm_truncated_edist_le_one (x p : X) : ‖(_root_.Min.min (_root_.EDist.edist x p) 1).toReal‖ ≤ (1 : ℝ) := by
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  have h : (_root_.Min.min (_root_.EDist.edist x p) 1).toReal ≤ (1 : ℝ≥0∞).toReal :=
    ENNReal.toReal_mono (by simp) (min_le_right _ _)
  simpa only [ENNReal.toReal_one] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EMetric.norm_truncated_edist_le_one then
    throwError "Refusing to shadow existing declaration EMetric.norm_truncated_edist_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `EMetric.norm_truncated_edist_le_one ``Submission.EMetric.norm_truncated_edist_le_one

end EMetric

end

end
