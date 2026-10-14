import Submission.DifferentialGeometry.Bundle.FiberBundleHausdorff
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.Defs
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness.PointedFlowData

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u v uE uH uE' uH'
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [CompleteSpace E']
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {H' : Type uH'} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {D : RealTimeInterval}
  (F : PointedFlowData.{v, uE', uH'} (I := J) D)
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

local instance pullbackTargetTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetTopology ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetTopology
local instance pullbackTargetCharted : ChartedSpace H' F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetCharted ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetCharted
local instance pullbackTargetSmooth : IsManifold J ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetSmooth ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetSmooth
local instance pullbackTargetT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetT2 ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetT2
local instance pullbackTargetSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetSigmaCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetSigmaCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetSigmaCompact ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullbackTargetSigmaCompact

def pullback (Phi : M ≃ₘ⟮I, J⟯ F.M) : PointedFlowData.{u, uE, uH} (I := I) D where
  M := M
  topology := inferInstance
  charted := inferInstance
  smooth := inferInstance
  sigmaCompact := inferInstance
  t2 := inferInstance
  t2TangentBundle := inferInstance
  basepoint := Phi.symm F.basepoint
  S := F.S.pullback Phi
  isSolution := F.isSolution.pullback F.S Phi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullback ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullback

theorem pullback_rmNormSq (Phi : M ≃ₘ⟮I, J⟯ F.M) (t : ℝ) (x : M) :
    (F.pullback Phi).rmNormSq t x = F.rmNormSq t (Phi x) := by
  exact riemannNormSq_cross (F.S.base.metric t) Phi x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullback_rmNormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullback_rmNormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullback_rmNormSq ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullback_rmNormSq

theorem pullback_complete (Phi : M ≃ₘ⟮I, J⟯ F.M) (t : ℝ)
    (hF : MetricComplete (F.atTime t)) :
    MetricComplete ((F.pullback Phi).atTime t) := by
  have hg : RiemannianMetricComplete (F.S.base.metric t) := ⟨hF⟩
  exact (RiemannianMetricComplete.pullbackCross (F.S.base.metric t) Phi hg).complete

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullback_complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullback_complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullback_complete ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.pullback_complete

end DifferentialGeometry.CheegerGromovCompactness.PointedFlowData
