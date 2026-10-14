import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Restriction
import Submission.DifferentialGeometry.Topology.Manifold.ConnectedComponent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

namespace PointedRiemannianManifold

variable (X : PointedRiemannianManifold I)

local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.instTopologicalSpaceM : TopologicalSpace X.M := X.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.instTopologicalSpaceM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.instTopologicalSpaceM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.instTopologicalSpaceM ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.instTopologicalSpaceM
local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.instChartedSpaceM : ChartedSpace H X.M := X.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.instChartedSpaceM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.instChartedSpaceM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.instChartedSpaceM ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.instChartedSpaceM

def connectedComponent : PointedRiemannianManifold I :=
  X.restrictOpen (connectedComponentOpen (I := I) X.basepoint) mem_connectedComponent

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.connectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.connectedComponent ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.connectedComponent

theorem connectedComponent_connected :
    letI : TopologicalSpace X.connectedComponent.M := X.connectedComponent.topology
    ConnectedSpace X.connectedComponent.M := by
  change ConnectedSpace (connectedComponentOpen (I := I) X.basepoint)
  exact connectedComponentOpen_connectedSpace X.basepoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.connectedComponent_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.connectedComponent_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.connectedComponent_connected ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.connectedComponent_connected

end PointedRiemannianManifold

theorem MetricComplete.connectedComponent
    {X : PointedRiemannianManifold I} (hX : MetricComplete X) :
    MetricComplete X.connectedComponent := by
  let : TopologicalSpace X.M := X.topology
  let : ChartedSpace H X.M := X.charted
  exact metricComplete_restrictOpen X _ mem_connectedComponent isClosed_connectedComponent hX

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricComplete.connectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricComplete.connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricComplete.connectedComponent ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricComplete.connectedComponent

theorem HasCurvDerivBound.connectedComponent
    {X : PointedRiemannianManifold I} {k : ℕ} {C : ℝ}
    (hX : HasCurvDerivBound X k C) : HasCurvDerivBound X.connectedComponent k C := by
  let : TopologicalSpace X.M := X.topology
  let : ChartedSpace H X.M := X.charted
  exact hasCurvDerivBound_restrictOpen X _ mem_connectedComponent k C hX

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.connectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.connectedComponent ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.connectedComponent

namespace PointedRiemannianSeq

variable (S : PointedRiemannianSeq I)

local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.instTopologicalSpaceMObj_1 (i : ℕ) : TopologicalSpace (S.obj i).M := (S.obj i).topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.instTopologicalSpaceMObj_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.instTopologicalSpaceMObj_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.instTopologicalSpaceMObj_1 ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.instTopologicalSpaceMObj_1
local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.instChartedSpaceMObj (i : ℕ) : ChartedSpace H (S.obj i).M := (S.obj i).charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.instChartedSpaceMObj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.instChartedSpaceMObj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.instChartedSpaceMObj ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.instChartedSpaceMObj

def connectedComponent : PointedRiemannianSeq I :=
  S.restrictOpen (fun i => connectedComponentOpen (I := I) (S.obj i).basepoint)
    (fun _ => mem_connectedComponent)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.connectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.connectedComponent ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.connectedComponent

end PointedRiemannianSeq

theorem SeqMetricComplete.connectedComponent
    {S : PointedRiemannianSeq I} (hS : SeqMetricComplete S) :
    SeqMetricComplete S.connectedComponent where
  complete i := (hS.complete i).connectedComponent

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SeqMetricComplete.connectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SeqMetricComplete.connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SeqMetricComplete.connectedComponent ``Submission.DifferentialGeometry.CheegerGromovCompactness.SeqMetricComplete.connectedComponent

def SeqBoundedGeometry.connectedComponent
    {S : PointedRiemannianSeq I} (hS : SeqBoundedGeometry S) :
    SeqBoundedGeometry S.connectedComponent where
  C := hS.C
  nonneg := hS.nonneg
  bound i k := (hS.bound i k).connectedComponent

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SeqBoundedGeometry.connectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SeqBoundedGeometry.connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SeqBoundedGeometry.connectedComponent ``Submission.DifferentialGeometry.CheegerGromovCompactness.SeqBoundedGeometry.connectedComponent

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

def BaseInjBound.connectedComponent
    {S : PointedRiemannianSeq I} (hρ : BaseInjBound S) (hS : SeqMetricComplete S) :
    BaseInjBound S.connectedComponent where
  ρ := hρ.ρ
  pos := hρ.pos
  bound i := by
    let : TopologicalSpace (S.obj i).M := (S.obj i).topology
    let : ChartedSpace H (S.obj i).M := (S.obj i).charted
    exact (hasInjRadiusAt_restrictOpen_iff (S.obj i) _ mem_connectedComponent
      isClosed_connectedComponent (hS.complete i) _ hρ.ρ).mpr (hρ.bound i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.BaseInjBound.connectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.BaseInjBound.connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.BaseInjBound.connectedComponent ``Submission.DifferentialGeometry.CheegerGromovCompactness.BaseInjBound.connectedComponent

end InnerProduct

end DifferentialGeometry.CheegerGromovCompactness
