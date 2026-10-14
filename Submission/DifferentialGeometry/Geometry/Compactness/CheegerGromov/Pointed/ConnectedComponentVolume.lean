import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.ConnectedComponent
import Submission.DifferentialGeometry.Geometry.Metric.Restriction.Ball
import Submission.DifferentialGeometry.Analysis.Integration.Measure.OpenSubtypeBall
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.LocalJetBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem PointedRiemannianManifold.connectedComponent_closedBall
    (X : PointedRiemannianManifold.{u, uE, uH} I) (r : ℝ) :
    riemannianClosedBallOf X.connectedComponent.metric X.connectedComponent.basepoint r =
      (Subtype.val : connectedComponentOpen (I := I) X.basepoint → X.M) ⁻¹'
        riemannianClosedBallOf X.metric X.basepoint r := by
  ext y
  change riemannianEDistOf (X.metric.restrictOpen (connectedComponentOpen (I := I) X.basepoint))
      ⟨X.basepoint, mem_connectedComponent⟩ y ≤ ENNReal.ofReal r ↔
    riemannianEDistOf X.metric X.basepoint y.val ≤ ENNReal.ofReal r
  exact (congrArg (fun t : ℝ≥0∞ => t ≤ ENNReal.ofReal r)
    (riemannianEDistOf_restrictOpen_of_isClosed X.metric
    (connectedComponentOpen (I := I) X.basepoint) isClosed_connectedComponent
    ⟨X.basepoint, mem_connectedComponent⟩ y)).to_iff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.connectedComponent_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.connectedComponent_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.connectedComponent_closedBall ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.connectedComponent_closedBall


theorem PointedRiemannianManifold.connectedComponent_ball_volume
    (X : PointedRiemannianManifold.{u, uE, uH} I) (x : X.connectedComponent.M) (r : ℝ) :
    Integral.Measure.riemannianVolumeMeasure I X.connectedComponent.M X.connectedComponent.metric
        (riemannianBallOf X.connectedComponent.metric x r) =
      Integral.Measure.riemannianVolumeMeasure I X.M X.metric
        (riemannianBallOf X.metric x.val r) :=
  Integral.Measure.riemannianVolumeMeasure_ball_restrictOpen_of_isClosed
    X.metric (connectedComponentOpen (I := I) X.basepoint) isClosed_connectedComponent x r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.connectedComponent_ball_volume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.connectedComponent_ball_volume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.connectedComponent_ball_volume ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.connectedComponent_ball_volume

theorem PointedRiemannianSeq.inner_ball_volume_lower_bound_connectedComponent
    (X : PointedRiemannianSeq.{u, uE, uH} I) (rho : ℝ)
    (hvol : ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in _root_.Filter.atTop, ∀ x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
          Integral.Measure.riemannianVolumeMeasure I (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric x a)) :
    ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in _root_.Filter.atTop,
        ∀ x ∈ riemannianClosedBallOf (X.connectedComponent.obj n).metric
            (X.connectedComponent.obj n).basepoint r,
          ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
            Integral.Measure.riemannianVolumeMeasure I (X.connectedComponent.obj n).M
              (X.connectedComponent.obj n).metric
              (riemannianBallOf (X.connectedComponent.obj n).metric x a) := by
  intro r R hr hrR hR C hC
  obtain ⟨a,κ,ha,hκ,hra,hac,hv⟩ := hvol r R hr hrR hR C hC
  refine ⟨a,κ,ha,hκ,hra,hac,?_⟩
  filter_upwards [hv] with n hn x hx
  have hcenter : x.val ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r := by
    exact (Set.ext_iff.mp ((X.obj n).connectedComponent_closedBall r) x).mp hx
  have heq := (X.obj n).connectedComponent_ball_volume x a
  exact (hn x.val hcenter).trans_eq heq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.inner_ball_volume_lower_bound_connectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.inner_ball_volume_lower_bound_connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.inner_ball_volume_lower_bound_connectedComponent ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.inner_ball_volume_lower_bound_connectedComponent

end DifferentialGeometry.CheegerGromovCompactness

end

noncomputable section
open _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal
namespace DifferentialGeometry.CheegerGromovCompactness
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem PointedRiemannianManifold.isCompact_closedBall_connectedComponent
    (X : PointedRiemannianManifold.{u, uE, uH} I) (R : ℝ)
    (hcompact : IsCompact (riemannianClosedBallOf X.metric X.basepoint R)) :
    IsCompact (riemannianClosedBallOf X.connectedComponent.metric X.connectedComponent.basepoint R) := by
  rw [X.connectedComponent_closedBall R]
  have hsubset : riemannianClosedBallOf X.metric X.basepoint R ⊆
      (connectedComponentOpen (I := I) X.basepoint : Set X.M) := by
    intro y hy
    apply Geometry.Metric.edistOf_ball_subset_connCompOpen
      (I := I) X.metric X.basepoint (_root_.Max.max R 0 + 1)
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (by linarith [le_max_left R 0]))
  change IsCompact ((Subtype.val : connectedComponentOpen (I := I) X.basepoint →
    X.M) ⁻¹' riemannianClosedBallOf X.metric X.basepoint R)
  exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hcompact
    (fun y hy => ⟨⟨y, hsubset hy⟩, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.isCompact_closedBall_connectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.isCompact_closedBall_connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.isCompact_closedBall_connectedComponent ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.isCompact_closedBall_connectedComponent

end DifferentialGeometry.CheegerGromovCompactness

end

noncomputable section
open _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal
namespace DifferentialGeometry.CheegerGromovCompactness
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem HasLocalCurvDerivBound.connectedComponent
    {X : PointedRiemannianManifold.{u, uE, uH} I} {R C : ℝ} {p : ℕ}
    (h : HasLocalCurvDerivBound (I := I) X X.basepoint R p C) :
    HasLocalCurvDerivBound (I := I) X.connectedComponent X.connectedComponent.basepoint R p C := by
  intro y hy
  have hy' : y.val ∈ riemannianClosedBallOf X.metric X.basepoint R :=
    (Set.ext_iff.mp (X.connectedComponent_closedBall R) y).mp hy
  exact (curvDerivNorm_restrictOpen X.metric
    (connectedComponentOpen (I := I) X.basepoint) p y).trans_le (h y.val hy')

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.HasLocalCurvDerivBound
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HasLocalCurvDerivBound.connectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HasLocalCurvDerivBound.connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HasLocalCurvDerivBound.connectedComponent ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasLocalCurvDerivBound.connectedComponent

end DifferentialGeometry.CheegerGromovCompactness

end
