import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialRoundComponentVolume
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Bishop.LocalBallRatio
import Submission.DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciPointwise
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import Submission.DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instNeZeroNatFinrankRealThreeSpace : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instNeZeroNatFinrankRealThreeSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instNeZeroNatFinrankRealThreeSpace target :: scope.openDecls } }

theorem sqrt_scalarAt_mul_le_three_of_rm_le {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] (g : SmoothRiemannianMetric I3 M)
    (x : M)
    {r : ℝ} (hcurv : r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1) :
    Real.sqrt (metricScalarAt g x) * r ≤ 3 := by
  rcases lt_or_ge r 0 with hr | hr
  · nlinarith [Real.sqrt_nonneg (metricScalarAt g x)]
  set N := normSq0S g x 4 (metricRm04At g x) with hNdef
  have hN : 0 ≤ N := normSq0S_nonneg _ _ _ _
  have hscalar : metricScalarAt g x ≤ 9 * Real.sqrt N := by
    have hh := (le_abs_self (metricScalarAt g x)).trans (scalar_abs_le_rm g x)
    change metricScalarAt g x ≤ (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * _ at hh
    norm_num [ThreeSpace] at hh
    exact hh
  have hsN : Real.sqrt N * r ^ 2 ≤ 1 := by
    have hsq : (r ^ 2 * Real.sqrt N) ^ 2 ≤ 1 := by
      rw [mul_pow, ← pow_mul, Real.sq_sqrt hN]
      exact hcurv
    have hnn : 0 ≤ r ^ 2 * Real.sqrt N := by positivity
    nlinarith
  rcases le_or_gt (metricScalarAt g x) 0 with hQ | hQ
  · rw [Real.sqrt_eq_zero'.mpr hQ, _root_.MulZeroClass.zero_mul]
    norm_num
  have hQr : (Real.sqrt (metricScalarAt g x) * r) ^ 2 ≤ 3 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hQ.le]
    nlinarith [sq_nonneg r]
  exact abs_le_of_sq_le_sq' hQr (by norm_num) |>.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.sqrt_scalarAt_mul_le_three_of_rm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.sqrt_scalarAt_mul_le_three_of_rm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.sqrt_scalarAt_mul_le_three_of_rm_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.sqrt_scalarAt_mul_le_three_of_rm_le

theorem exists_ball_volume_of_spatialRoundComponent (C1 C2 : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {x : P.Carrier} {eps : ℝ}
      (W : SpatialCanonicalWitness g eps C1 C2 x), W.domain.carrier = connectedComponent x →
      SpatialRoundComponent g eps x W.domain.carrier →
      SimplyConnectedSpace (connectedComponent x) → ∀ r : ℝ, 0 < r →
      r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1 →
      ENNReal.ofReal (κ * r ^ 3) ≤
        riemannianVolumeMeasure I3 P.Carrier g (riemannianBallOf g x r) := by
  set A := _root_.Max.max C1 1 with hAdef
  set B := _root_.Max.max C2 1 with hBdef
  have hA : 1 ≤ A := le_max_right _ _
  have hB : 1 ≤ B := le_max_right _ _
  refine ⟨Real.exp (-(18 * A * Real.sqrt B)) * (4 * Real.sqrt 3 * Real.pi) / (216 * A ^ 3),
    by positivity, ?_⟩
  intro P g x eps W whole D hsc r hr hcurv
  set Q := metricScalarAt g x with hQdef
  have hQ : 0 < Q := W.Q_pos
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hsQsq : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ.le
  set L := 3 * A / Real.sqrt Q with hLdef
  have hL : 0 < L := by positivity
  have hrL : r ≤ L := by
    have h3 := sqrt_scalarAt_mul_le_three_of_rm_le g x hcurv
    rw [hLdef, le_div_iff₀ hsQ]
    nlinarith
  have hball : riemannianBallOf g x L ⊆ W.domain.carrier := by
    rw [whole]
    exact DifferentialGeometry.Geometry.Metric.edistOf_ball_subset_connCompOpen
      (I := I3) g x L
  have hdomain : W.domain.carrier ⊆ riemannianBallOf g x L := by
    refine W.inside_ball.trans (riemannianBallOf_mono g x ?_)
    have hrad : W.radius ≤ A / Real.sqrt Q :=
      W.radius_upper.trans (div_le_div_of_nonneg_right (le_max_left _ _) hsQ.le)
    have hApos : 0 ≤ A / Real.sqrt Q := by positivity
    rw [hLdef, mul_div_assoc]
    linarith
  set q := 3 * Real.sqrt (B * Q) with hqdef
  have hq : 0 ≤ q := by positivity
  have hRic : ∀ y ∈ riemannianBallOf g x L, ∀ v : TangentSpace I3 y,
      -(((Module.finrank ℝ ThreeSpace - 1 : ℕ) : ℝ) * q ^ 2) * g.inner y v v ≤
        ricciTensor (I := I3) g y v v := by
    intro y hy v
    have hrm : Real.sqrt (normSq0S g y 4 (metricRm04At g y)) ≤ B * Q :=
      (W.rm_bound y (hball hy)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hQ.le)
    have hlow := Geometry.Riemannian.BonnetMyers.ricciLowerAt_of_rm (I := I3) g hrm v
    have hinner : 0 ≤ g.inner y v v := by
      rcases eq_or_ne v 0 with hv | hv
      · subst v
        simp
      · exact (g.pos y v hv).le
    have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
    rw [hdim] at hlow ⊢
    have hq2 : q ^ 2 = 9 * (B * Q) := by
      rw [hqdef, mul_pow, Real.sq_sqrt (by positivity)]
      norm_num
    have hcoef : -(((3 - 1 : ℕ) : ℝ) * q ^ 2) ≤ -(((3 : ℕ) : ℝ) ^ 2 * (B * Q)) := by
      rw [hq2]
      norm_num
      nlinarith [mul_pos (zero_lt_one.trans_le hB) hQ]
    exact (mul_le_mul_of_nonneg_right hcoef hinner).trans hlow
  have hmain :=
    Geometry.Riemannian.VolumeComparison.riemannianBallOf_volume_ratio_ge_of_ricci_lower g
      (RiemannianMetricComplete.of_compact g) x hq hr hrL hRic
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  rw [hdim] at hmain
  have hU : ENNReal.ofReal (4 * Real.sqrt 3 * Real.pi / (Q * Real.sqrt Q)) ≤
      riemannianVolumeMeasure I3 P.Carrier g (riemannianBallOf g x L) := by
    rw [← whole] at hsc
    exact (D.volume_lower_of_simplyConnected).trans (_root_.MeasureTheory.measure_mono hdomain)
  have hexp : q * ((3 - 1 : ℕ) : ℝ) * L = 18 * A * Real.sqrt B := by
    rw [hqdef, hLdef, Real.sqrt_mul (by positivity)]
    field_simp
    norm_num
  rw [hexp] at hmain
  have hcoef : Real.exp (-(18 * A * Real.sqrt B)) * (4 * Real.sqrt 3 * Real.pi) /
        (216 * A ^ 3) * r ^ 3 =
      Real.exp (-(18 * A * Real.sqrt B)) * (r / (2 * L)) ^ 3 *
        (4 * Real.sqrt 3 * Real.pi / (Q * Real.sqrt Q)) := by
    rw [hLdef]
    have hQ3 : Q * Real.sqrt Q = Real.sqrt Q ^ 3 := by rw [pow_succ, hsQsq]
    rw [hQ3]
    field_simp
    ring
  rw [hcoef, ENNReal.ofReal_mul (by positivity)]
  exact (mul_le_mul' le_rfl hU).trans hmain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_ball_volume_of_spatialRoundComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_ball_volume_of_spatialRoundComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_ball_volume_of_spatialRoundComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_ball_volume_of_spatialRoundComponent

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
