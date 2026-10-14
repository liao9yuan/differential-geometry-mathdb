import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Set _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open scoped _root_.Topology
namespace DifferentialGeometry.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem timeH1_tendstoUniformly {L : ℝ}
    (u : ℕ → timeH1 E L) (uLim : timeH1 E L)
    (hu : _root_.Filter.Tendsto u _root_.Filter.atTop (𝓝 uLim)) :
    TendstoUniformly
      (fun n (r : _root_.Set.Icc (0 : ℝ) L) ↦ (u n).toFun r.1)
      (fun r ↦ uLim.toFun r.1) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro epsilon hepsilon
  let C : ℝ := 1 + Real.sqrt L
  have hC : 0 < C := by dsimp only [C]; positivity
  have hnorm : _root_.Filter.Tendsto (fun n ↦ ‖uLim - u n‖) _root_.Filter.atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (tendsto_const_nhds.sub hu :
        _root_.Filter.Tendsto (fun n ↦ uLim - u n) _root_.Filter.atTop (𝓝 (uLim - uLim))).norm
  filter_upwards [hnorm.eventually (Iio_mem_nhds (div_pos hepsilon hC))] with n hn
  intro r
  have hfun : (uLim - u n).toFun r.1 = uLim.toFun r.1 - (u n).toFun r.1 := by
    rw [sub_eq_add_neg, timeH1.toFun_add uLim (-u n) r.2]
    have hneg := timeH1.toFun_smul (-1 : ℝ) (u n) r.2
    simpa only [neg_one_smul, sub_eq_add_neg] using
      congrArg (uLim.toFun r.1 + ·) hneg
  rw [dist_eq_norm, ← hfun]
  calc
    ‖(uLim - u n).toFun r.1‖ ≤ C * ‖uLim - u n‖ :=
      (uLim - u n).norm_toFun_le_norm r.2
    _ < C * (epsilon / C) := mul_lt_mul_of_pos_left hn hC
    _ = epsilon := by field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.timeH1_tendstoUniformly then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.timeH1_tendstoUniformly"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.timeH1_tendstoUniformly ``Submission.DifferentialGeometry.Analysis.timeH1_tendstoUniformly

end DifferentialGeometry.Analysis
end
