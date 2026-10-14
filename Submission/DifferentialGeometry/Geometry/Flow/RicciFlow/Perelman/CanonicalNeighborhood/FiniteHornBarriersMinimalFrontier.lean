import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BoundedAtDistanceFromRmBallBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EndChartTipSideDiameterRefutation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBarriersRadialNesting
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornConstruction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  RealizedFiniteHorn.metric_space RealizedFiniteHorn.charted RealizedFiniteHorn.smooth
  RealizedFiniteHorn.sigmaCompact

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

theorem not_endChartTipSideDiameterBound {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop) :
    ¬ EndChartTipSideDiameterBound g H ray d := by
  rintro ⟨L, hL, hbound⟩
  obtain ⟨i, hrest⟩ :=
    ((((endChart_tipSide_pair_height_and_dist H ray d hd hzero hlarge (3 / 4)
        (by norm_num) (by norm_num)).and hbound).and
      (eventually_mem_tail g H ray d hd hzero)).and
      (hlarge.eventually_ge_atTop (_root_.Max.max 1 ((L / (3 / 4)) ^ 2 + 1)))).exists
  obtain ⟨⟨⟨hpair, hb⟩, hgood⟩, hbig⟩ := hrest
  obtain ⟨hxle, hyeq, hdist⟩ := hpair hgood (endChart g H (ray.point (d i)) hgood)
  have hle := hb hgood (endChart g H (ray.point (d i)) hgood)
    (ray.point ((1 - 3 / 4) * d i)) (ray.point (d i)) hxle hyeq.le
  have hdpos : 0 < d i := (hd i).1
  have hs_pos : 0 < metricScalarAt g (ray.point (d i)) := by
    have hone : 1 ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 :=
      le_trans (le_max_left _ _) hbig
    nlinarith [hone, sq_nonneg (d i), sq_pos_of_pos hdpos]
  have hchain : (3 / 4) * d i ≤ L / Real.sqrt (metricScalarAt g (ray.point (d i))) :=
    le_trans hdist hle
  have hmul : (3 / 4) * (d i * Real.sqrt (metricScalarAt g (ray.point (d i)))) ≤ L := by
    have h := (le_div_iff₀ (Real.sqrt_pos.mpr hs_pos)).mp hchain
    nlinarith [h]
  have hroot : L / (3 / 4) < Real.sqrt (metricScalarAt g (ray.point (d i))) * d i := by
    have hsqrt : Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) =
        Real.sqrt (metricScalarAt g (ray.point (d i))) * d i := by
      rw [Real.sqrt_mul hs_pos.le, Real.sqrt_sq hdpos.le]
    rw [← hsqrt]
    rw [Real.lt_sqrt (by positivity)]
    have hsq : (L / (3 / 4)) ^ 2 + 1 ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 :=
      le_trans (le_max_right _ _) hbig
    linarith
  have hgt : L < (3 / 4) * (d i * Real.sqrt (metricScalarAt g (ray.point (d i)))) := by
    have h := mul_lt_mul_of_pos_left hroot (by norm_num : (0 : ℝ) < 3 / 4)
    calc L = (3 / 4) * (L / (3 / 4)) := by field_simp
      _ < (3 / 4) * (Real.sqrt (metricScalarAt g (ray.point (d i))) * d i) := h
      _ = (3 / 4) * (d i * Real.sqrt (metricScalarAt g (ray.point (d i)))) := by ring
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_endChartTipSideDiameterBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_endChartTipSideDiameterBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_endChartTipSideDiameterBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_endChartTipSideDiameterBound

omit [SigmaCompactSpace W] in
theorem finite_horn_barriers_of_neckEndScale {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (_endData : EndGeometry H) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hscale : NeckEndScale g H ray d) : Nonempty (HornBarriers H ray d) :=
  nonempty_hornBarriers_of_neckEndScale g H ray d hd hzero hlarge hscale

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_neckEndScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_neckEndScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_neckEndScale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_neckEndScale

theorem boundedAtDistanceShell_of_terminalDerivativeBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : TerminalDerivativeBoundProducer.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi := by
  obtain ⟨e, he, hb⟩ := h
  obtain ⟨e', he', hb'⟩ := bounded_curvature_at_distance_of_terminalDerivativeBoundProducer
    ⟨e, he, fun eps' hp' hle' X' => hb eps' hp' hle' X'⟩
  exact ⟨e', he', fun eps hp hle X => (hb' eps hp hle X).1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_terminalDerivativeBoundProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_terminalDerivativeBoundProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_terminalDerivativeBoundProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_terminalDerivativeBoundProducer

theorem finite_horn_construction_of_terminalDerivativeBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (h : TerminalDerivativeBoundProducer.{u} kappa sigma Phi) :
    ∃ alphaMax collarMin : ℝ, 0 < alphaMax ∧ alphaMax < 1 / 11 ∧ 0 < collarMin ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaMax → ∀ collar : ℝ, collarMin ≤ collar →
        ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            FiniteControlledRadius X → ∃ H : RealizedFiniteHorn X.toFlowSequence,
              H.horn.neck_precision = alpha ∧ collar ≤ H.horn.collar_depth :=
  finite_horn_construction_of_boundedAtDistanceShell hkappa hsigma hPhi
    (boundedAtDistanceShell_of_terminalDerivativeBoundProducer h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_of_terminalDerivativeBoundProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_of_terminalDerivativeBoundProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_of_terminalDerivativeBoundProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_of_terminalDerivativeBoundProducer

theorem not_nonempty_finiteControlledRadius_of_boundedAtDistance
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (h : BoundedAtDistance X) : ¬ Nonempty (FiniteControlledRadius X) :=
  fun hc => finiteControlledRadius_false_of_boundedAtDistance X h hc.some

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_nonempty_finiteControlledRadius_of_boundedAtDistance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_nonempty_finiteControlledRadius_of_boundedAtDistance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_nonempty_finiteControlledRadius_of_boundedAtDistance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_nonempty_finiteControlledRadius_of_boundedAtDistance

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
