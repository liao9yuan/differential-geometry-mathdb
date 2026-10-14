import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BoundedAtDistanceFromRmBallBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DistanceCurvatureEscape
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBarrierFrontierWeb
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBarriersMinimalFrontier
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBarriersRadialNesting
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBoundedCurvatureFrontier

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
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact
  RealizedFiniteHorn.metric_space RealizedFiniteHorn.charted RealizedFiniteHorn.smooth
  RealizedFiniteHorn.sigmaCompact

theorem not_nonempty_finiteControlledRadius_of_boundedAtDistanceShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (h : BoundedAtDistanceShell.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ¬ Nonempty (FiniteControlledRadius X) := by
  obtain ⟨e, he, hb⟩ := h
  exact ⟨e, he, fun eps hp hle X =>
    not_nonempty_finiteControlledRadius_of_boundedAtDistance X (hb eps hp hle X)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_nonempty_finiteControlledRadius_of_boundedAtDistanceShell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_nonempty_finiteControlledRadius_of_boundedAtDistanceShell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_nonempty_finiteControlledRadius_of_boundedAtDistanceShell ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_nonempty_finiteControlledRadius_of_boundedAtDistanceShell

theorem finite_horn_construction_of_realizedDistanceCurvatureEscapeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (h : ∃ alphaMax collarMin : ℝ, 0 < alphaMax ∧ alphaMax < 1 / 11 ∧ 0 < collarMin ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaMax → ∀ collar : ℝ, collarMin ≤ collar →
        ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            RealizedDistanceCurvatureEscape X → ∃ H : RealizedFiniteHorn X.toFlowSequence,
              H.horn.neck_precision = alpha ∧ collar ≤ H.horn.collar_depth) :
    ∃ alphaMax collarMin : ℝ, 0 < alphaMax ∧ alphaMax < 1 / 11 ∧ 0 < collarMin ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaMax → ∀ collar : ℝ, collarMin ≤ collar →
        ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            FiniteControlledRadius X → ∃ H : RealizedFiniteHorn X.toFlowSequence,
              H.horn.neck_precision = alpha ∧ collar ≤ H.horn.collar_depth := by
  let _ := hkappa
  let _ := hsigma
  let _ := hPhi
  obtain ⟨a, c, ha, ha', hc, hmain⟩ := h
  refine ⟨a, c, ha, ha', hc, fun alpha halpha hle collar hcol => ?_⟩
  obtain ⟨e, he, hstep⟩ := hmain alpha halpha hle collar hcol
  exact ⟨e, he, fun eps hp hlep X hX =>
    hstep eps hp hlep X (realizedDistanceCurvatureEscape_of_finiteControlledRadius hX)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_of_realizedDistanceCurvatureEscapeShell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_of_realizedDistanceCurvatureEscapeShell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_of_realizedDistanceCurvatureEscapeShell ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_of_realizedDistanceCurvatureEscapeShell

theorem finite_horn_construction_iff_realizedDistanceCurvatureEscapeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    (∃ alphaMax collarMin : ℝ, 0 < alphaMax ∧ alphaMax < 1 / 11 ∧ 0 < collarMin ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaMax → ∀ collar : ℝ, collarMin ≤ collar →
        ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            RealizedDistanceCurvatureEscape X → ∃ H : RealizedFiniteHorn X.toFlowSequence,
              H.horn.neck_precision = alpha ∧ collar ≤ H.horn.collar_depth) ↔
    (∃ alphaMax collarMin : ℝ, 0 < alphaMax ∧ alphaMax < 1 / 11 ∧ 0 < collarMin ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaMax → ∀ collar : ℝ, collarMin ≤ collar →
        ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            FiniteControlledRadius X → ∃ H : RealizedFiniteHorn X.toFlowSequence,
              H.horn.neck_precision = alpha ∧ collar ≤ H.horn.collar_depth) := by
  constructor
  · rintro ⟨a, c, ha, ha', hc, hmain⟩
    exact ⟨a, c, ha, ha', hc, fun alpha halpha hle collar hcol =>
      (hmain alpha halpha hle collar hcol).imp fun e he =>
        ⟨he.1, fun eps hp hlep X hX =>
          he.2 eps hp hlep X (realizedDistanceCurvatureEscape_of_finiteControlledRadius hX)⟩⟩
  · rintro ⟨a, c, ha, ha', hc, hmain⟩
    refine ⟨a, c, ha, ha', hc, fun alpha halpha hle collar hcol => ?_⟩
    obtain ⟨e, he, hstep⟩ := hmain alpha halpha hle collar hcol
    refine ⟨e, he, fun eps hp hlep X hX => ?_⟩
    obtain ⟨F⟩ :=
      (nonempty_finiteControlledRadius_iff_realizedDistanceCurvatureEscape X).mpr hX
    exact hstep eps hp hlep X F

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_iff_realizedDistanceCurvatureEscapeShell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_iff_realizedDistanceCurvatureEscapeShell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_iff_realizedDistanceCurvatureEscapeShell ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_iff_realizedDistanceCurvatureEscapeShell

def NoSubsequenceCurvatureEscapeShell (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ¬ SubsequenceCurvatureEscape X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NoSubsequenceCurvatureEscapeShell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NoSubsequenceCurvatureEscapeShell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NoSubsequenceCurvatureEscapeShell ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NoSubsequenceCurvatureEscapeShell

theorem subsequenceCurvatureEscape_of_finiteControlledRadius
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} {X : NormalizedSequence.{u} eps kappa sigma Phi}
    (h : FiniteControlledRadius X) : SubsequenceCurvatureEscape X :=
  (subsequenceCurvatureEscape_iff_not_boundedAtDistance_of_curvatureBoundedWithin X
    (half_pos h.radius_pos)
    (h.inner_bound (h.radius / 2) (half_pos h.radius_pos)
      (by linarith [h.radius_pos]))).mpr
    (not_boundedAtDistance_of_distanceCurvatureEscape X
      (distanceCurvatureEscape_of_finiteControlledRadius h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.subsequenceCurvatureEscape_of_finiteControlledRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.subsequenceCurvatureEscape_of_finiteControlledRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.subsequenceCurvatureEscape_of_finiteControlledRadius ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.subsequenceCurvatureEscape_of_finiteControlledRadius

theorem noSubsequenceCurvatureEscapeShell_of_boundedAtDistanceShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (h : BoundedAtDistanceShell.{u} kappa sigma Phi) :
    NoSubsequenceCurvatureEscapeShell.{u} kappa sigma Phi := by
  obtain ⟨e, he, hb⟩ := h
  exact ⟨e, he, fun eps hp hle X hs =>
    not_boundedAtDistance_of_subsequenceCurvatureEscape hs (hb eps hp hle X)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.noSubsequenceCurvatureEscapeShell_of_boundedAtDistanceShell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.noSubsequenceCurvatureEscapeShell_of_boundedAtDistanceShell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.noSubsequenceCurvatureEscapeShell_of_boundedAtDistanceShell ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.noSubsequenceCurvatureEscapeShell_of_boundedAtDistanceShell

theorem boundedAtDistanceShell_of_noSubsequenceCurvatureEscapeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsmall : ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, CurvatureBoundedWithin X r)
    (h : NoSubsequenceCurvatureEscapeShell.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi := by
  obtain ⟨e₁, r, he₁, hr, hs⟩ := hsmall
  obtain ⟨e₂, he₂, hn⟩ := h
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps hp hle X => ?_⟩
  by_contra hf
  exact hn eps hp (le_trans hle (min_le_right e₁ e₂)) X
    ((subsequenceCurvatureEscape_iff_not_boundedAtDistance_of_curvatureBoundedWithin X hr
      (hs eps hp (le_trans hle (min_le_left e₁ e₂)) X)).mpr hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_noSubsequenceCurvatureEscapeShell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_noSubsequenceCurvatureEscapeShell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_noSubsequenceCurvatureEscapeShell ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistanceShell_of_noSubsequenceCurvatureEscapeShell

theorem noSubsequenceCurvatureEscapeShell_iff_boundedAtDistanceShell_of_smallScale
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsmall : ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, CurvatureBoundedWithin X r) :
    NoSubsequenceCurvatureEscapeShell.{u} kappa sigma Phi ↔
      BoundedAtDistanceShell.{u} kappa sigma Phi :=
  ⟨boundedAtDistanceShell_of_noSubsequenceCurvatureEscapeShell hsmall,
    noSubsequenceCurvatureEscapeShell_of_boundedAtDistanceShell⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.noSubsequenceCurvatureEscapeShell_iff_boundedAtDistanceShell_of_smallScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.noSubsequenceCurvatureEscapeShell_iff_boundedAtDistanceShell_of_smallScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.noSubsequenceCurvatureEscapeShell_iff_boundedAtDistanceShell_of_smallScale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.noSubsequenceCurvatureEscapeShell_iff_boundedAtDistanceShell_of_smallScale

theorem bounded_curvature_at_distance_of_noSubsequenceCurvatureEscapeShell_and_terminalDerivativeBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsmall : ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, CurvatureBoundedWithin X r)
    (hesc : NoSubsequenceCurvatureEscapeShell.{u} kappa sigma Phi)
    (hder : TerminalDerivativeBoundProducer.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X := by
  obtain ⟨e₁, he₁, hb⟩ := boundedAtDistanceShell_of_noSubsequenceCurvatureEscapeShell hsmall hesc
  obtain ⟨e₂, he₂, hd⟩ := hder
  exact ⟨min e₁ e₂, lt_min he₁ he₂, fun eps hp hle X =>
    ⟨hb eps hp (le_trans hle (min_le_left e₁ e₂)) X,
      hd eps hp (le_trans hle (min_le_right e₁ e₂)) X⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_noSubsequenceCurvatureEscapeShell_and_terminalDerivativeBoundProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_noSubsequenceCurvatureEscapeShell_and_terminalDerivativeBoundProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_noSubsequenceCurvatureEscapeShell_and_terminalDerivativeBoundProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_noSubsequenceCurvatureEscapeShell_and_terminalDerivativeBoundProducer

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

def EndChartSectionSubendCapture (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop, ∃ j : ℕ,
    H.subend j ⊆ {x : W | _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint < (1 + e) * d i} ∧
    ∀ (hx : ray.point (d i) ∈ H.subend (tailIndex g H)) (p : Sphere 2),
      (endChart g H (ray.point (d i)) hx).F (p, 0) ∈ H.subend j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndChartSectionSubendCapture then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndChartSectionSubendCapture"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndChartSectionSubendCapture ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndChartSectionSubendCapture

omit [SigmaCompactSpace W] in
theorem hornRadialExitPositionAtEndChart_of_endChartSectionSubendCapture
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (h : EndChartSectionSubendCapture g H ray d) :
    HornRadialExitPositionAtEndChart g H ray d := by
  intro e he he10
  filter_upwards [h (e / 2) (by linarith) (by linarith)] with i hi
  intro hx x hxfar
  obtain ⟨j, hjball, hjsec⟩ := hi
  by_contra hcon
  have hmem : x ∈ H.subend j := by
    by_contra hnot
    exact absurd (GlobalNeckCrossSection.outer_side_of_center_in_subend g H
      (endChart g H (ray.point (d i)) hx).cross j (hjsec hx) x hnot) hcon
  have hlt : _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint < (1 + e / 2) * d i := hjball hmem
  have hmul : (1 + e / 2) * d i < (1 + e) * d i :=
    mul_lt_mul_of_pos_right (by linarith) (hd i).1
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_of_endChartSectionSubendCapture then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_of_endChartSectionSubendCapture"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_of_endChartSectionSubendCapture ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_of_endChartSectionSubendCapture

theorem finite_horn_barriers_of_endChartSectionSubendCapture
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (endData : EndGeometry H)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (h : EndChartSectionSubendCapture g H ray d) : Nonempty (HornBarriers H ray d) :=
  finite_horn_barriers_of_hornRadialExitPositionAtEndChart H endData ray d hd hzero hlarge
    (hornRadialExitPositionAtEndChart_of_endChartSectionSubendCapture H ray d hd h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_endChartSectionSubendCapture then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_endChartSectionSubendCapture"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_endChartSectionSubendCapture ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_endChartSectionSubendCapture

theorem not_endChartTipSide_le_transverseScale {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop) :
    ¬ (∀ᶠ i in Filter.atTop, ∀ (hx : ray.point (d i) ∈ H.subend (tailIndex g H))
        (E : EndChart g H (ray.point (d i)) hx), ∀ x : W,
        E.cross.tube.height x ≤ 1 / 2 →
          _root_.Dist.dist x (ray.point (d i)) ≤
            transverseShortcutConstant W / Real.sqrt (metricScalarAt g (ray.point (d i)))) := by
  intro hcont
  obtain ⟨i, ⟨⟨⟨hpair, hbound⟩, hbig⟩, hgood⟩⟩ :=
    ((((endChart_tipSide_pair_height_and_dist H ray d hd hzero hlarge (3 / 4)
        (by norm_num) (by norm_num)).and hcont).and
      (hlarge.eventually_ge_atTop (_root_.Max.max 1 ((transverseShortcutConstant W / (3 / 4)) ^ 2 + 1)))).and
      (eventually_mem_tail g H ray d hd hzero)).exists
  obtain ⟨hxle, _hyeq, hdist⟩ := hpair hgood (endChart g H (ray.point (d i)) hgood)
  have hle := hbound hgood (endChart g H (ray.point (d i)) hgood)
    (ray.point ((1 - 3 / 4) * d i)) hxle
  have hdpos : 0 < d i := (hd i).1
  have hs_pos : 0 < metricScalarAt g (ray.point (d i)) := by
    have hone : 1 ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 :=
      le_trans (le_max_left _ _) hbig
    nlinarith [hone, sq_nonneg (d i), sq_pos_of_pos hdpos]
  have hchain : (3 / 4) * d i ≤
      transverseShortcutConstant W / Real.sqrt (metricScalarAt g (ray.point (d i))) :=
    le_trans hdist hle
  have hmul : (3 / 4) * (d i * Real.sqrt (metricScalarAt g (ray.point (d i)))) ≤
      transverseShortcutConstant W := by
    have h := (le_div_iff₀ (Real.sqrt_pos.mpr hs_pos)).mp hchain
    nlinarith [h]
  have hroot : transverseShortcutConstant W / (3 / 4) <
      Real.sqrt (metricScalarAt g (ray.point (d i))) * d i := by
    have hsqrt : Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) =
        Real.sqrt (metricScalarAt g (ray.point (d i))) * d i := by
      rw [Real.sqrt_mul hs_pos.le, Real.sqrt_sq hdpos.le]
    rw [← hsqrt, Real.lt_sqrt (div_nonneg (transverseShortcutConstant_pos W).le (by norm_num))]
    have hsq : (transverseShortcutConstant W / (3 / 4)) ^ 2 + 1 ≤
        metricScalarAt g (ray.point (d i)) * d i ^ 2 := le_trans (le_max_right _ _) hbig
    linarith
  have hgt : transverseShortcutConstant W <
      (3 / 4) * (d i * Real.sqrt (metricScalarAt g (ray.point (d i)))) := by
    have h := mul_lt_mul_of_pos_left hroot (by norm_num : (0 : ℝ) < 3 / 4)
    calc transverseShortcutConstant W = (3 / 4) * (transverseShortcutConstant W / (3 / 4)) := by
          field_simp
      _ < (3 / 4) * (Real.sqrt (metricScalarAt g (ray.point (d i))) * d i) := h
      _ = (3 / 4) * (d i * Real.sqrt (metricScalarAt g (ray.point (d i)))) := by ring
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_endChartTipSide_le_transverseScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_endChartTipSide_le_transverseScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_endChartTipSide_le_transverseScale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_endChartTipSide_le_transverseScale

private theorem div_sqrt_lt_mul_of_scaled {L eta s d : ℝ} (hs : 0 < s) (hd : 0 < d)
    (h : L / Real.sqrt (s * d ^ 2) < eta) : L / Real.sqrt s < d * eta := by
  have hsqrt : Real.sqrt (s * d ^ 2) = Real.sqrt s * d := by
    rw [Real.sqrt_mul hs.le, Real.sqrt_sq hd.le]
  rw [hsqrt] at h
  have hne : Real.sqrt s ≠ 0 := by positivity
  calc L / Real.sqrt s = d * (L / (Real.sqrt s * d)) := by field_simp
    _ < d * eta := mul_lt_mul_of_pos_left h hd

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.div_sqrt_lt_mul_of_scaled
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.div_sqrt_lt_mul_of_scaled target :: scope.openDecls } }

omit [SigmaCompactSpace W] in
theorem endChartSectionSubendCapture_of_subendRadialNesting
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hnest : SubendRadialNesting g H d) : EndChartSectionSubendCapture g H ray d := by
  intro e he he10
  filter_upwards [hnest (e / 2) (by linarith) (by linarith),
    hlarge.eventually_ge_atTop (_root_.Max.max 1 ((4 * transverseShortcutConstant W / e) ^ 2 + 1))]
    with i hnest_i hbig
  obtain ⟨j, hjsub, hjout⟩ := hnest_i
  have hdpos : 0 < d i := (hd i).1
  have hsmul : 1 ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 :=
    le_trans (le_max_left _ _) hbig
  have hspos : 0 < metricScalarAt g (ray.point (d i)) := by
    nlinarith [hsmul, sq_nonneg (d i), sq_pos_of_pos hdpos]
  have hspread : transverseShortcutConstant W /
      Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) < e / 4 := by
    have hT : 0 < transverseShortcutConstant W := transverseShortcutConstant_pos W
    have hpos : 0 < 4 * transverseShortcutConstant W / e := div_pos (by linarith) he
    have hlt : 4 * transverseShortcutConstant W / e <
        Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) := by
      rw [Real.lt_sqrt hpos.le]
      have h2 : (4 * transverseShortcutConstant W / e) ^ 2 + 1 ≤
          metricScalarAt g (ray.point (d i)) * d i ^ 2 := le_trans (le_max_right _ _) hbig
      linarith
    have hdiv := div_lt_div_of_pos_left hT hpos hlt
    have heq : transverseShortcutConstant W / (4 * transverseShortcutConstant W / e) = e / 4 := by
      field_simp
    rwa [heq] at hdiv
  have hdiam : transverseShortcutConstant W /
      Real.sqrt (metricScalarAt g (ray.point (d i))) < d i * (e / 4) :=
    div_sqrt_lt_mul_of_scaled hspos hdpos hspread
  have hjout' : ∀ x : W, x ∈ H.subend j →
      dist (x : UniformSpace.Completion W) H.endpoint < (1 + e / 2) * d i := hjout
  refine ⟨j, fun x hx => ?_, fun hx p => ?_⟩
  · exact lt_of_lt_of_le (hjout' x hx) (mul_le_mul_of_nonneg_right (by linarith) hdpos.le)
  · refine hjsub ?_
    set E := endChart g H (ray.point (d i)) hx with hE
    have hsec : E.F (p, 0) ∈ E.cross.tube.sectionSet (1 / 2) := by
      rw [← GlobalNeckTube.range_sectionMap E.cross.tube (1 / 2)]
      exact ⟨p, E.cross.center_eq p⟩
    have hbound := EndChart.section_diameter_le E _ hsec
    have htri := dist_triangle ((E.F (p, 0)) : UniformSpace.Completion W)
      ((ray.point (d i)) : UniformSpace.Completion W) H.endpoint
    rw [UniformSpace.Completion.dist_eq, dist_comm (E.F (p, 0)) (ray.point (d i)),
      ray.radial (d i) (hd i)] at htri
    have hspread' : _root_.Dist.dist (ray.point (d i)) (E.F (p, 0)) < d i * (e / 4) :=
      lt_of_le_of_lt hbound hdiam
    have hrew : d i * (e / 4) + d i = (1 + e / 2 / 2) * d i := by ring
    have hgoal : _root_.Dist.dist ((E.F (p, 0) : UniformSpace.Completion W)) H.endpoint <
        (1 + e / 2 / 2) * d i := by
      rw [← hrew]
      linarith
    exact hgoal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endChartSectionSubendCapture_of_subendRadialNesting then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endChartSectionSubendCapture_of_subendRadialNesting"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endChartSectionSubendCapture_of_subendRadialNesting ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endChartSectionSubendCapture_of_subendRadialNesting

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
