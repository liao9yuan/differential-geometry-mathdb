import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardDistanceComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardExteriorVolume
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardUniformCurvatureBlowup

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

theorem standard_uniform_high_scalar_ball_volume_lower
    {T : ℝ} (hT : 0 < T) (hT1 : T < 1)
    (hTLife : ENNReal.ofReal T ≤ uniformStandardLifetime) :
    ∃ R Q D v : ℝ, 0 < R ∧ 0 < Q ∧ 0 < D ∧ 0 < v ∧
      ∀ (S : StandardSolution) (t : ℝ) (x : E3), t ∈ _root_.Set.Ico 0 T →
        Q < metricScalarAt (S.val.metric t) x →
        ‖x‖ < R ∧ ENNReal.ofReal v ≤
          riemannianVolumeMeasure (𝓡 3) E3 (S.val.metric t)
            (riemannianBallOf (S.val.metric t) x D) := by
  obtain ⟨R, Q, hR, hQ, hexterior⟩ := standard_uniform_exterior_scalar_bound hT hT1 hTLife
  obtain ⟨p, v, hv, hvolume⟩ := exists_standard_uniform_fixed_ball_volume_lower hT hT1 hTLife
  let D := R + ‖p‖ + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨R, Q, D, v, hR, hQ, hD, hv, ?_⟩
  intro S t x ht hscalar
  have hx : ‖x‖ < R := by
    by_contra h
    exact hscalar.not_ge (hexterior S t ht x (le_of_not_gt h))
  have htdom : t ∈ S.val.domain := by
    exact (mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos t).mpr
      ⟨ht.1, ((ENNReal.ofReal_lt_ofReal_iff hT).mpr ht.2).trans_le
        (hTLife.trans (uniformStandardLifetime_le_lifetime S))⟩
  refine ⟨hx, (hvolume S t ht).trans ?_⟩
  exact _root_.MeasureTheory.measure_mono (S.val.euclidean_ball_subset_riemannianBallOf htdom p x hx.le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_uniform_high_scalar_ball_volume_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_uniform_high_scalar_ball_volume_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_uniform_high_scalar_ball_volume_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_uniform_high_scalar_ball_volume_lower

theorem exists_standard_family_scalar_blowup_sequence_with_positive_ball_volume
    {T : ℝ} (hT : 0 < T) (hT1 : T < 1)
    (hLifetime : uniformStandardLifetime = ENNReal.ofReal T) :
    ∃ (S : ℕ → StandardSolution) (t : ℕ → ℝ) (x : ℕ → E3) (R D v : ℝ),
      0 < R ∧ 0 < D ∧ 0 < v ∧ (∀ n, t n ∈ _root_.Set.Ioo 0 T) ∧
      (∀ n, t n ∈ (S n).val.domain) ∧ _root_.Filter.Tendsto t _root_.Filter.atTop (𝓝[<] T) ∧
      _root_.Filter.Tendsto (fun n => metricScalarAt ((S n).val.metric (t n)) (x n)) _root_.Filter.atTop _root_.Filter.atTop ∧
      ∀ᶠ n in _root_.Filter.atTop, ‖x n‖ < R ∧ ENNReal.ofReal v ≤
        riemannianVolumeMeasure (𝓡 3) E3 ((S n).val.metric (t n))
          (riemannianBallOf ((S n).val.metric (t n)) (x n) D) := by
  obtain ⟨S, t, x, hmem, hdomain, htime, hscalar⟩ :=
    standard_family_scalar_blowup_sequence hT hT1 hLifetime
  obtain ⟨R, Q, D, v, hR, _, hD, hv, hvolume⟩ :=
    standard_uniform_high_scalar_ball_volume_lower hT hT1 hLifetime.symm.le
  refine ⟨S, t, x, R, D, v, hR, hD, hv, hmem, hdomain, htime, hscalar, ?_⟩
  filter_upwards [hscalar.eventually (_root_.Filter.eventually_gt_atTop Q)] with n hn
  exact hvolume (S n) (t n) (x n) ⟨(hmem n).1.le, (hmem n).2⟩ hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_standard_family_scalar_blowup_sequence_with_positive_ball_volume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_standard_family_scalar_blowup_sequence_with_positive_ball_volume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_standard_family_scalar_blowup_sequence_with_positive_ball_volume ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_standard_family_scalar_blowup_sequence_with_positive_ball_volume

end DifferentialGeometry.PDE.RicciFlow
