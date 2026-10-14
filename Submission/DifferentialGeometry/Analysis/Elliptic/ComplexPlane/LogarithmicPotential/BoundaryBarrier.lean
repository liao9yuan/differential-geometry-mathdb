import Submission.DifferentialGeometry.Analysis.Elliptic.Euclidean.MaximumPrinciple
import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LogarithmicPotential.FundamentalSolution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Filter _root_.Metric _root_.InnerProductSpace _root_.Submission.InnerProductSpace
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis

private theorem abs_le_of_harmonic_boundary_comparison
    {s : Set ℂ} (hs : IsCompact (closure s)) {u v : ℂ → ℝ}
    (huc : ContinuousOn u (closure s)) (hvc : ContinuousOn v (closure s))
    (hu : _root_.InnerProductSpace.HarmonicOnNhd u (interior s)) (hv : _root_.InnerProductSpace.HarmonicOnNhd v (interior s))
    (hb : ∀ z ∈ frontier s, |u z| ≤ v z) :
    ∀ z ∈ closure s, |u z| ≤ v z := by
  have hup : ∀ z ∈ closure s, u z - v z ≤ 0 :=
    le_of_laplacian_nonneg_of_le_frontier hs (huc.sub hvc).upperSemicontinuousOn
      (fun z hz => ((hu z hz).sub (hv z hz)).1)
      (fun z hz => by
        have h := ((hu z hz).sub (hv z hz)).2.self_of_nhds
        change Laplacian.laplacian (fun y => u y - v y) z = 0 at h
        exact h.ge)
      (fun z hz => sub_nonpos.mpr ((le_abs_self (u z)).trans (hb z hz)))
  have hlo : ∀ z ∈ closure s, -u z - v z ≤ 0 :=
    le_of_laplacian_nonneg_of_le_frontier hs (huc.neg.sub hvc).upperSemicontinuousOn
      (fun z hz => ((hu z hz).neg.sub (hv z hz)).1)
      (fun z hz => by
        have h := ((hu z hz).neg.sub (hv z hz)).2.self_of_nhds
        change Laplacian.laplacian (fun y => -u y - v y) z = 0 at h
        exact h.ge)
      (fun z hz => sub_nonpos.mpr ((neg_le_abs (u z)).trans (hb z hz)))
  intro z hz
  exact abs_le.mpr ⟨by linarith [hlo z hz], by linarith [hup z hz]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.abs_le_of_harmonic_boundary_comparison
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.abs_le_of_harmonic_boundary_comparison target :: scope.openDecls } }

theorem abs_le_logarithmic_boundary_barrier
    {D : Set ℂ} (hD : IsOpen D) {p a : ℂ} {δ ρ gap M : ℝ}
    (hρ : 0 < ρ) (hgap : 0 < gap) (hM : 0 ≤ M) {u : ℂ → ℝ}
    (huc : ContinuousOn u (closure (D ∩ _root_.Metric.ball p δ)))
    (hu : _root_.InnerProductSpace.HarmonicOnNhd u (D ∩ _root_.Metric.ball p δ))
    (hzero : ∀ z ∈ frontier D ∩ _root_.Metric.closedBall p δ, u z = 0)
    (hbound : ∀ z ∈ closure D ∩ _root_.Metric.sphere p δ, |u z| ≤ M)
    (hexterior : ∀ z ∈ closure D ∩ _root_.Metric.closedBall p δ, ρ ≤ ‖z - a‖)
    (hrim : ∀ z ∈ closure D ∩ _root_.Metric.sphere p δ, ρ + gap ≤ ‖z - a‖) :
    ∀ z ∈ closure (D ∩ _root_.Metric.ball p δ),
      |u z| ≤ M / Real.log ((ρ + gap) / ρ) * Real.log (‖z - a‖ / ρ) := by
  let s := D ∩ _root_.Metric.ball p δ
  let L := Real.log ((ρ + gap) / ρ)
  let C := M / L
  let B : ℂ → ℝ := fun z => C * (Real.log ‖z - a‖ - Real.log ρ)
  have hL : 0 < L := Real.log_pos ((one_lt_div hρ).mpr (by linarith))
  have hC : 0 ≤ C := div_nonneg hM hL.le
  have hsopen : IsOpen s := hD.inter _root_.Metric.isOpen_ball
  have hscl : closure s ⊆ closure D ∩ _root_.Metric.closedBall p δ := by
    intro z hz
    exact ⟨closure_mono _root_.Set.inter_subset_left hz,
      closure_minimal (inter_subset_right.trans _root_.Metric.ball_subset_closedBall) _root_.Metric.isClosed_closedBall hz⟩
  have hscompact : IsCompact (closure s) :=
    (_root_.ProperSpace.isCompact_closedBall p δ).of_isClosed_subset isClosed_closure
      (fun z hz => (hscl hz).2)
  have hnorm (z : ℂ) (hz : z ∈ closure s) : 0 < ‖z - a‖ :=
    hρ.trans_le (hexterior z (hscl hz))
  have hB : _root_.InnerProductSpace.HarmonicOnNhd B (closure s) := by
    intro z hz
    have hh : _root_.InnerProductSpace.HarmonicAt (fun y : ℂ => Real.log ‖y - a‖) z :=
      (show AnalyticAt ℂ (fun y : ℂ => y - a) z by fun_prop).harmonicAt_log_norm
        (norm_ne_zero_iff.mp (hnorm z hz).ne')
    exact (hh.sub (_root_.InnerProductSpace.harmonicAt_const (Real.log ρ))).const_smul (c := C)
  have hBnonneg (z : ℂ) (hz : z ∈ closure s) : 0 ≤ B z := by
    exact mul_nonneg hC (sub_nonneg.mpr
      (Real.log_le_log hρ (hexterior z (hscl hz))))
  have hfront (z : ℂ) (hz : z ∈ frontier s) :
      z ∈ frontier D ∨ z ∈ _root_.Metric.sphere p δ := by
    rcases frontier_inter_subset D (_root_.Metric.ball p δ) hz with hzD | hzB
    · exact Or.inl hzD.1
    · exact Or.inr (_root_.Metric.frontier_ball_subset_sphere hzB.2)
  have hboundary (z : ℂ) (hz : z ∈ frontier s) : |u z| ≤ B z := by
    have hzcl : z ∈ closure s := frontier_subset_closure hz
    rcases hfront z hz with hzD | hzR
    · rw [hzero z ⟨hzD, (hscl hzcl).2⟩, abs_zero]
      exact hBnonneg z hzcl
    · have hzrim : z ∈ closure D ∩ _root_.Metric.sphere p δ := ⟨(hscl hzcl).1, hzR⟩
      have hlog : L ≤ Real.log ‖z - a‖ - Real.log ρ := by
        dsimp only [L]
        rw [Real.log_div (by positivity : ρ + gap ≠ 0) hρ.ne']
        exact sub_le_sub_right (Real.log_le_log (by linarith) (hrim z hzrim)) _
      have hML : M = C * L := by dsimp [C]; rw [div_mul_cancel₀ _ hL.ne']
      exact (hbound z hzrim).trans (by rw [hML]; exact mul_le_mul_of_nonneg_left hlog hC)
  have hcmp := abs_le_of_harmonic_boundary_comparison hscompact huc hB.continuousOn
    (by simpa only [hsopen.interior_eq] using hu)
    (hB.mono interior_subset_closure) hboundary
  intro z hz
  have hh := hcmp z hz
  simpa only [B, C, L, Real.log_div (hnorm z hz).ne' hρ.ne'] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.abs_le_logarithmic_boundary_barrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.abs_le_logarithmic_boundary_barrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.abs_le_logarithmic_boundary_barrier ``Submission.DifferentialGeometry.Analysis.abs_le_logarithmic_boundary_barrier

end DifferentialGeometry.Analysis

end

end
