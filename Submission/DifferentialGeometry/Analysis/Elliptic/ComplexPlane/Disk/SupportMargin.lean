import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Disk.ImagePotential

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis




theorem exists_disk_support_radii {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ)
    (hs : tsupport κ ⊆ Metric.ball (0 : ℂ) 1) :
    ∃ ρ R : ℝ, 0 < ρ ∧ ρ < 1 ∧ 1 < R ∧ ρ * R < 1 ∧
      ∀ w ∈ tsupport κ, ‖w‖ ≤ ρ := by
  by_cases hn : (tsupport κ).Nonempty
  · obtain ⟨w, hw, hmax⟩ := hc.exists_isMaxOn hn continuous_norm.continuousOn
    have hwlt : ‖w‖ < 1 := by
      simpa only [mem_ball_zero_iff] using hs hw
    let ρ : ℝ := (‖w‖ + 1) / 2
    have hρpos : 0 < ρ := by
      dsimp [ρ]
      linarith [norm_nonneg w]
    have hρlt : ρ < 1 := by
      dsimp [ρ]
      linarith
    obtain ⟨R, hR1, hRinv⟩ := exists_between ((one_lt_inv₀ hρpos).2 hρlt)
    refine ⟨ρ, R, hρpos, hρlt, hR1, ?_, ?_⟩
    · calc
        ρ * R < ρ * ρ⁻¹ := mul_lt_mul_of_pos_left hRinv hρpos
        _ = 1 := mul_inv_cancel₀ (ne_of_gt hρpos)
    · intro v hv
      have hwρ : ‖w‖ ≤ ρ := by
        dsimp [ρ]
        linarith
      exact (hmax hv).trans hwρ
  · refine ⟨1 / 2, 3 / 2, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    intro w hw
    exact (hn ⟨w, hw⟩).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_disk_support_radii then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_disk_support_radii"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_disk_support_radii ``Submission.DifferentialGeometry.Analysis.exists_disk_support_radii



theorem exists_contDiffOn_diskRegularizerPotential {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    (hs : tsupport κ ⊆ Metric.ball (0 : ℂ) 1) :
    ∃ R : ℝ, 1 < R ∧
      ContDiffOn ℝ ∞ (diskRegularizerPotential κ) (Metric.ball (0 : ℂ) R) := by
  obtain ⟨ρ, R, hρ, _, hR, hρR, hsρ⟩ := exists_disk_support_radii hc hs
  exact ⟨R, hR, contDiffOn_diskRegularizerPotential hc hκ hρ hρR hsρ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_contDiffOn_diskRegularizerPotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_contDiffOn_diskRegularizerPotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_contDiffOn_diskRegularizerPotential ``Submission.DifferentialGeometry.Analysis.exists_contDiffOn_diskRegularizerPotential

end DifferentialGeometry.Analysis
