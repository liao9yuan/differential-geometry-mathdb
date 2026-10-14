import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Interval.Set.Infinite

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Filter _root_.Set
open scoped _root_.Topology

theorem exists_tendsto_forall_notMem_of_finite_diff_Icc {E : ℕ → Set ℝ} {ζ : ℕ → ℝ}
    (hζ : _root_.Filter.Tendsto ζ _root_.Filter.atTop (𝓝 0)) (hE : ∀ n, (E n \ _root_.Set.Icc (-(ζ n)) 0).Finite) {s : ℝ}
    (hs : s ≤ 0) :
    ∃ σ : ℕ → ℝ, _root_.Filter.Tendsto σ _root_.Filter.atTop (𝓝 s) ∧ ∀ n, σ n ≤ s ∧ σ n ∉ E n := by
  have hpick (n : ℕ) : ∃ x ∈ _root_.Set.Ioo (_root_.Min.min s (-ζ n) - 1 / ((n : ℝ) + 1)) (_root_.Min.min s (-ζ n)),
      x ∉ E n \ _root_.Set.Icc (-(ζ n)) 0 := by
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact ((_root_.Set.Ioo_infinite (by linarith)).sdiff (hE n)).nonempty
  choose σ hσ hσE using hpick
  have hmin : _root_.Filter.Tendsto (fun n => _root_.Min.min s (-ζ n)) _root_.Filter.atTop (𝓝 s) := by
    simpa [min_eq_left hs] using (tendsto_const_nhds (x := s)).min hζ.neg
  refine ⟨σ, ?_, fun n => ⟨(hσ n).2.le.trans (min_le_left _ _), fun hn => ?_⟩⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ hmin (fun n => (hσ n).1.le)
      (fun n => (hσ n).2.le)
    simpa using hmin.sub tendsto_one_div_add_atTop_nhds_zero_nat
  · exact hσE n ⟨hn, fun h => ((hσ n).2.trans_le (min_le_right _ _)).not_ge h.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exists_tendsto_forall_notMem_of_finite_diff_Icc then
    throwError "Refusing to shadow existing declaration exists_tendsto_forall_notMem_of_finite_diff_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `exists_tendsto_forall_notMem_of_finite_diff_Icc ``Submission.exists_tendsto_forall_notMem_of_finite_diff_Icc
