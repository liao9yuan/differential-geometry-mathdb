import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.BoundedGeometry
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.InjectivityRadius
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Restriction
import Submission.DifferentialGeometry.Geometry.Metric.Restriction
import Submission.DifferentialGeometry.Topology.SigmaCompactOpen
import Submission.DifferentialGeometry.Bundle.FiberBundleHausdorff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (X : PointedRiemannianManifold I)

local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM : TopologicalSpace X.M := X.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM ``Submission.DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM
local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM : ChartedSpace H X.M := X.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM ``Submission.DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM
local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM : IsManifold I ∞ X.M := X.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM ``Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM
local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM : SigmaCompactSpace X.M := X.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM ``Submission.DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM
local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM : T2Space X.M := X.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM ``Submission.DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM

def PointedRiemannianManifold.restrictOpen
    (U : TopologicalSpace.Opens X.M) (hp : X.basepoint ∈ U) : PointedRiemannianManifold I := by
  let : SigmaCompactSpace U :=
    isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  exact { M := U, basepoint := ⟨X.basepoint, hp⟩, metric := X.metric.restrictOpen U }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.restrictOpen ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.restrictOpen

theorem PointedRiemannianManifold.restrictOpen_metric
    (U : TopologicalSpace.Opens X.M) (hp : X.basepoint ∈ U) :
    (X.restrictOpen U hp).metric = X.metric.restrictOpen U := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.restrictOpen_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.restrictOpen_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.restrictOpen_metric ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.restrictOpen_metric

theorem PointedRiemannianManifold.restrictOpen_basepoint_coe
    (U : TopologicalSpace.Opens X.M) (hp : X.basepoint ∈ U) :
    ((show U from (X.restrictOpen U hp).basepoint) : X.M) = X.basepoint := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.restrictOpen_basepoint_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.restrictOpen_basepoint_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.restrictOpen_basepoint_coe ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.restrictOpen_basepoint_coe

theorem metricComplete_restrictOpen
    (U : TopologicalSpace.Opens X.M) (hp : X.basepoint ∈ U)
    (hU : IsClosed (U : Set X.M)) (hX : MetricComplete X) :
    MetricComplete (X.restrictOpen U hp) := by
  let : SigmaCompactSpace U := hU.sigmaCompactSpace
  have hg : RiemannianMetricComplete X.metric := ⟨MetricComplete.complete X hX⟩
  exact (hg.restrictOpen U hU).complete

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricComplete_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricComplete_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricComplete_restrictOpen ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricComplete_restrictOpen

theorem PointedRiemannianManifold.emetricSpace_restrictOpen_of_isClosed
    (U : TopologicalSpace.Opens X.M) (hp : X.basepoint ∈ U) (hU : IsClosed (U : Set X.M)) :
    letI : EMetricSpace X.M := X.emetricSpace
    (X.restrictOpen U hp).emetricSpace = (inferInstance : EMetricSpace U) := by
  let : EMetricSpace X.M := X.emetricSpace
  apply EMetricSpace.ext
  ext x y
  change riemannianEDistOf (X.metric.restrictOpen U) x y =
    riemannianEDistOf X.metric (Subtype.val (show U from x)) (Subtype.val (show U from y))
  exact riemannianEDistOf_restrictOpen_of_isClosed X.metric U hU x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.emetricSpace_restrictOpen_of_isClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.emetricSpace_restrictOpen_of_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.emetricSpace_restrictOpen_of_isClosed ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.emetricSpace_restrictOpen_of_isClosed

theorem hasCurvDerivBound_restrictOpen
    (U : TopologicalSpace.Opens X.M) (hp : X.basepoint ∈ U) (k : ℕ) (C : ℝ)
    (hX : HasCurvDerivBound X k C) : HasCurvDerivBound (X.restrictOpen U hp) k C := by
  change ∀ x : U, curvDerivNorm k (X.metric.restrictOpen U) x ≤ C
  intro x
  exact (curvDerivNorm_restrictOpen X.metric U k x).trans_le (hX (x : X.M))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.hasCurvDerivBound_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.hasCurvDerivBound_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.hasCurvDerivBound_restrictOpen ``Submission.DifferentialGeometry.CheegerGromovCompactness.hasCurvDerivBound_restrictOpen

end Normed

section InnerProduct

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (X : PointedRiemannianManifold I)

local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_1 : TopologicalSpace X.M := X.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_1 ``Submission.DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_1
local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_1 : ChartedSpace H X.M := X.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_1 ``Submission.DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_1
local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_1 : IsManifold I ∞ X.M := X.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_1 ``Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_1
local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealOfNatWithTopENatM : IsManifold I 1 X.M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealOfNatWithTopENatM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealOfNatWithTopENatM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealOfNatWithTopENatM ``Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealOfNatWithTopENatM
local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_1 : SigmaCompactSpace X.M := X.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_1 ``Submission.DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_1
local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_1 : T2Space X.M := X.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_1 ``Submission.DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_1

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem PointedRiemannianManifold.intrinsicInjRadius_restrictOpen_of_isClosed
    (U : TopologicalSpace.Opens X.M) (hp : X.basepoint ∈ U)
    (hU : IsClosed (U : Set X.M)) (hX : MetricComplete X)
    (hR : MetricComplete (X.restrictOpen U hp)) (x : U) :
    (X.restrictOpen U hp).intrinsicInjRadius hR x = X.intrinsicInjRadius hX (x : X.M) := by
  let : _root_.Bundle.RiemannianBundle (fun y : X.M => TangentSpace I y) := X.riemBundle
  let : IsContinuousRiemannianBundle E (fun y : X.M => TangentSpace I y) := X.riemBundle_cont
  let : EMetricSpace X.M := X.emetricSpace
  let : CompleteSpace X.M := MetricComplete.complete X hX
  let : SigmaCompactSpace U := hU.sigmaCompactSpace
  let : _root_.Bundle.RiemannianBundle (fun y : U => TangentSpace I y) :=
    ⟨(X.metric.restrictOpen U).toRiemannianMetric⟩
  let hN : IsMetricNorm X.metric := isMetricNorm_of_riemannianBundle X.metric
  let hNU : IsMetricNorm (X.metric.restrictOpen U) :=
    isMetricNorm_of_riemannianBundle (X.metric.restrictOpen U)
  let : IsContinuousRiemannianBundle E (fun y : U => TangentSpace I y) :=
    hNU.isContinuousRiemannianBundle
  let : CompleteSpace U := hU.isComplete.completeSpace_coe
  let : IsRiemannianManifold I U := by
    constructor
    intro a b
    change Manifold.riemannianEDist I (a : X.M) (b : X.M) = _
    rw [← riemannianEDistOf_eq_riemannianEDist X.metric hN,
      ← riemannianEDistOf_eq_riemannianEDist (X.metric.restrictOpen U) hNU]
    exact (riemannianEDistOf_restrictOpen_of_isClosed X.metric U hU a b).symm
  unfold PointedRiemannianManifold.intrinsicInjRadius
  dsimp only
  exact intrinsicInjRadius_restrictOpen X.metric hN U hNU x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.intrinsicInjRadius_restrictOpen_of_isClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.intrinsicInjRadius_restrictOpen_of_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.intrinsicInjRadius_restrictOpen_of_isClosed ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.intrinsicInjRadius_restrictOpen_of_isClosed

theorem hasInjRadiusAt_restrictOpen_iff
    (U : TopologicalSpace.Opens X.M) (hp : X.basepoint ∈ U)
    (hU : IsClosed (U : Set X.M)) (hX : MetricComplete X) (x : U) (ρ : ℝ) :
    HasInjRadiusAt (X.restrictOpen U hp) x ρ ↔ HasInjRadiusAt X (x : X.M) ρ := by
  constructor
  · intro hρ
    refine ⟨hρ.1, fun hM => ?_⟩
    have hr := hρ.2 (metricComplete_restrictOpen X U hp hU hX)
    rwa [PointedRiemannianManifold.intrinsicInjRadius_restrictOpen_of_isClosed
      X U hp hU hM] at hr
  · intro hρ
    refine ⟨hρ.1, fun hR => ?_⟩
    rw [PointedRiemannianManifold.intrinsicInjRadius_restrictOpen_of_isClosed
      X U hp hU hX hR x]
    exact hρ.2 hX

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.hasInjRadiusAt_restrictOpen_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.hasInjRadiusAt_restrictOpen_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.hasInjRadiusAt_restrictOpen_iff ``Submission.DifferentialGeometry.CheegerGromovCompactness.hasInjRadiusAt_restrictOpen_iff

end InnerProduct

namespace PointedRiemannianSeq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (S : PointedRiemannianSeq I)

local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.instTopologicalSpaceMObj (i : ℕ) : TopologicalSpace (S.obj i).M := (S.obj i).topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.instTopologicalSpaceMObj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.instTopologicalSpaceMObj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.instTopologicalSpaceMObj ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.instTopologicalSpaceMObj

def restrictOpen (U : ∀ i, TopologicalSpace.Opens (S.obj i).M)
    (hp : ∀ i, (S.obj i).basepoint ∈ U i) : PointedRiemannianSeq I where
  obj i := (S.obj i).restrictOpen (U i) (hp i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.restrictOpen ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.restrictOpen

end PointedRiemannianSeq

end DifferentialGeometry.CheegerGromovCompactness
