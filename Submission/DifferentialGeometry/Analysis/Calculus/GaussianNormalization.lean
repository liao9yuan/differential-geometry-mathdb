import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {X : Type*} [PseudoMetricSpace X]

theorem locallyLipschitzOn_exp_neg_add
    {a b : ℝ} {Ω : Set X} {f : ℝ × X → ℝ}
    (hf : LocallyLipschitzOn (_root_.Set.Icc a b ×ˢ Ω) f)
    {c : ℝ → ℝ} (hc : LocallyLipschitzOn (_root_.Set.Icc a b) c) :
    LocallyLipschitzOn (_root_.Set.Icc a b ×ˢ Ω)
      (fun q : ℝ × X => Real.exp (-f q + c q.1)) := by
  obtain ⟨C, hC⟩ := hc.exists_lipschitzOnWith_of_compact _root_.CompactIccSpace.isCompact_Icc
  have hp : LipschitzOnWith 1 (Prod.fst : ℝ × X → ℝ) (_root_.Set.Icc a b ×ˢ Ω) :=
    LipschitzWith.prod_fst.lipschitzOnWith
  have hcp : LipschitzOnWith C (fun q : ℝ × X => c q.1) (_root_.Set.Icc a b ×ˢ Ω) := by
    simpa only [mul_one, Function.comp_def] using hC.comp hp (fun _ hq => hq.1)
  have hcl : LocallyLipschitzOn (_root_.Set.Icc a b ×ˢ Ω) (fun q : ℝ × X => c q.1) := by
    intro q hq
    exact ⟨C, _root_.Set.Icc a b ×ˢ Ω, self_mem_nhdsWithin, hcp⟩
  apply locallyLipschitzOn_iff_restrict.mpr
  exact (Real.contDiff_exp : ContDiff ℝ 1 Real.exp).locallyLipschitz.comp
    (hf.neg.add hcl).restrict

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.locallyLipschitzOn_exp_neg_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.locallyLipschitzOn_exp_neg_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.locallyLipschitzOn_exp_neg_add ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.locallyLipschitzOn_exp_neg_add

theorem locallyLipschitzOn_exp_gaussian_normalization
    {a b : ℝ} (ha : 0 < a) {Ω : Set X} {f : ℝ × X → ℝ}
    (hf : LocallyLipschitzOn (_root_.Set.Icc a b ×ˢ Ω) f) (n : ℝ) :
    LocallyLipschitzOn (_root_.Set.Icc a b ×ˢ Ω) (fun q : ℝ × X =>
      Real.exp (-f q - n / 2 * Real.log q.1 - n / 2 * Real.log (4 * Real.pi))) := by
  have hc : LocallyLipschitzOn (_root_.Set.Icc a b)
      (fun t : ℝ => -n / 2 * Real.log t - n / 2 * Real.log (4 * Real.pi)) := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have hd : ContDiffAt ℝ 1
        (fun t : ℝ => -n / 2 * Real.log t - n / 2 * Real.log (4 * Real.pi)) t :=
      (contDiffAt_const.mul (Real.contDiffAt_log.mpr ht0.ne')).sub contDiffAt_const
    obtain ⟨C, V, hV, hLip⟩ := hd.exists_lipschitzOnWith
    exact ⟨C, V, mem_nhdsWithin_of_mem_nhds hV, hLip⟩
  simpa only [sub_eq_add_neg, neg_div, neg_mul, add_assoc] using
    locallyLipschitzOn_exp_neg_add hf hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.locallyLipschitzOn_exp_gaussian_normalization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.locallyLipschitzOn_exp_gaussian_normalization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.locallyLipschitzOn_exp_gaussian_normalization ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.locallyLipschitzOn_exp_gaussian_normalization

end DifferentialGeometry.Analysis.Sobolev.Euclidean
