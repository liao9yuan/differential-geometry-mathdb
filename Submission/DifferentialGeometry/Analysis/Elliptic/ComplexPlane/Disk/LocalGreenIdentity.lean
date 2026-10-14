import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Disk.GreenIdentity
import Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.Ball
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Filter
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis


theorem contDiffOn_complexDivergence {F G : ℂ → ℝ} {s : Set ℂ}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) (hG : ContDiffOn ℝ ∞ G s) :
    ContDiffOn ℝ ∞ (complexDivergence F G) s := by
  intro z hz
  have hFz := (hF z hz).contDiffAt (hs.mem_nhds hz)
  have hGz := (hG z hz).contDiffAt (hs.mem_nhds hz)
  exact (((hFz.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).add
    ((hGz.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const)).contDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiffOn_complexDivergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiffOn_complexDivergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiffOn_complexDivergence ``Submission.DifferentialGeometry.Analysis.contDiffOn_complexDivergence



theorem exists_contDiff_eq_near_closedBall_of_open
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {f : V → ℝ} {s : Set V} {R : ℝ} (hR : 0 ≤ R) (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (hDs : Metric.closedBall (0 : V) R ⊆ s) :
    ∃ F : V → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      ∀ z ∈ Metric.closedBall (0 : V) R, F =ᶠ[𝓝 z] f := by
  obtain ⟨δ, hδ, hδs⟩ := (_root_.ProperSpace.isCompact_closedBall (0 : V) R).exists_cthickening_subset_open hs hDs
  rw [cthickening_closedBall hδ.le hR] at hδs
  exact exists_contDiff_compactSupport_eq_near_closedBall hR (by linarith : R < δ + R)
    (hf.mono (Metric.ball_subset_closedBall.trans hδs))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_contDiff_eq_near_closedBall_of_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_contDiff_eq_near_closedBall_of_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_contDiff_eq_near_closedBall_of_open ``Submission.DifferentialGeometry.Analysis.exists_contDiff_eq_near_closedBall_of_open




theorem integral_complexDivergence_closedBall_of_open {F G : ℂ → ℝ} {s : Set ℂ}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) (hG : ContDiffOn ℝ ∞ G s)
    {R : ℝ} (hR : 0 < R) (hDs : Metric.closedBall (0 : ℂ) R ⊆ s) :
    (∫ z in Metric.closedBall (0 : ℂ) R, complexDivergence F G z) =
      ∫ θ in -Real.pi..Real.pi, R *
        (F (Complex.polarCoord.symm (R, θ)) * Real.cos θ +
          G (Complex.polarCoord.symm (R, θ)) * Real.sin θ) := by
  obtain ⟨F', hF', _, heF⟩ := exists_contDiff_eq_near_closedBall_of_open hR.le hs hF hDs
  obtain ⟨G', hG', _, heG⟩ := exists_contDiff_eq_near_closedBall_of_open hR.le hs hG hDs
  calc
    _ = ∫ z in Metric.closedBall (0 : ℂ) R, complexDivergence F' G' z := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_closedBall] with z hz
      unfold complexDivergence
      rw [(heF z hz).fderiv_eq, (heG z hz).fderiv_eq]
    _ = _ := integral_complexDivergence_closedBall (hF'.of_le (by simp))
      (hG'.of_le (by simp)) hR
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro θ _
      have hz : Complex.polarCoord.symm (R, θ) ∈ Metric.closedBall (0 : ℂ) R := by
        simp [Complex.polarCoord_symm_apply, abs_of_pos hR]
      dsimp only
      rw [(heF _ hz).eq_of_nhds, (heG _ hz).eq_of_nhds]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_complexDivergence_closedBall_of_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_complexDivergence_closedBall_of_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_complexDivergence_closedBall_of_open ``Submission.DifferentialGeometry.Analysis.integral_complexDivergence_closedBall_of_open

end DifferentialGeometry.Analysis
