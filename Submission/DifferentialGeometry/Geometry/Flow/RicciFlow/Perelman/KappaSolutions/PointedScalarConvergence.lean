import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scalar
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackPointSelection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Topology _root_.Submission.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
attribute [local instance] pointedScalarManifoldOne pointedScalarLimitTopology
  pointedScalarLimitCharted pointedScalarLimitSmooth pointedScalarLimitT2 pointedScalarLimitSigma
section NormalizedTerminalSequence

variable {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance pointedScalarFlowTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowTopology
local instance pointedScalarFlowCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowCharted
local instance pointedScalarFlowSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowSmooth
local instance pointedScalarFlowT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowT2
local instance pointedScalarFlowSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarFlowSigma

theorem terminalCurvatureNormalizedFlowSeq_limit_scalar_base_one
    {kappa : ℝ} (hK : KLim kappa F) (x : ℕ → F.M)
    (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (Phi : PointedRiemannianConvergenceMaps (I := I)
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)) L subseq)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k) :
    metricScalarAt (I := I) L.metric L.basepoint = 1 := by
  apply pointedScalar_base_eq_of_metricCG_canonical_domains C hcanonical
  intro k
  exact terminalCurvatureNormalizedFlowSeq_scalar_base F hK x hQ (subseq k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCurvatureNormalizedFlowSeq_limit_scalar_base_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCurvatureNormalizedFlowSeq_limit_scalar_base_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCurvatureNormalizedFlowSeq_limit_scalar_base_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCurvatureNormalizedFlowSeq_limit_scalar_base_one

theorem terminalCurvatureNormalizedFlowSeq_canonical_limit_scalar_base_one
    {kappa : ℝ} (hK : KLim kappa F) (x : ℕ → F.M)
    (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (C : CanonicalMetricCompactness (I := I)
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I))) :
    let P := C.compactness.limit
    let _ : TopologicalSpace P.M := P.topology
    let _ : ChartedSpace H P.M := P.charted
    let _ : IsManifold I ∞ P.M := P.smooth
    let _ : T2Space P.M := P.t2
    metricScalarAt (I := I) P.metric P.basepoint = 1 :=
  scalar_base_eq_in_canonicalMetricCompactness C
    (terminalCurvatureNormalizedFlowSeq_scalar_base F hK x hQ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCurvatureNormalizedFlowSeq_canonical_limit_scalar_base_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCurvatureNormalizedFlowSeq_canonical_limit_scalar_base_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCurvatureNormalizedFlowSeq_canonical_limit_scalar_base_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCurvatureNormalizedFlowSeq_canonical_limit_scalar_base_one

end NormalizedTerminalSequence

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
