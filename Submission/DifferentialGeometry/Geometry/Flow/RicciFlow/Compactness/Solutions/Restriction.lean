import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.Defs
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.CheegerGromovCompactness.PointedFlowData

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {D D' D'' : RealTimeInterval}

def timeRestrict (F : PointedFlowData.{u, uE, uH} I D)
    (D' : RealTimeInterval) (hcarrier : D'.carrier ⊆ D.carrier)
    (hregular : D'.regular ⊆ D.regular) : PointedFlowData.{u, uE, uH} I D' := by
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  letI : T2Space (TangentBundle I F.M) := F.t2TangentBundle
  exact {
    M := F.M
    topology := F.topology
    charted := F.charted
    smooth := F.smooth
    sigmaCompact := F.sigmaCompact
    t2 := F.t2
    t2TangentBundle := F.t2TangentBundle
    basepoint := F.basepoint
    S := F.S.timeRestrict D'
    isSolution := isSolutionOn_timeRestrict F.isSolution hcarrier hregular }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.timeRestrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.timeRestrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.timeRestrict ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.timeRestrict

@[simp]
theorem timeRestrict_atTime (F : PointedFlowData.{u, uE, uH} I D)
    (hcarrier : D'.carrier ⊆ D.carrier) (hregular : D'.regular ⊆ D.regular)
    (t : Real) :
    (F.timeRestrict D' hcarrier hregular).atTime t = F.atTime t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.timeRestrict_atTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.timeRestrict_atTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.timeRestrict_atTime ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.timeRestrict_atTime

@[simp]
theorem timeRestrict_self (F : PointedFlowData.{u, uE, uH} I D)
    (hcarrier : D.carrier ⊆ D.carrier) (hregular : D.regular ⊆ D.regular) :
    F.timeRestrict D hcarrier hregular = F := by
  cases F
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.timeRestrict_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.timeRestrict_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.timeRestrict_self ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.timeRestrict_self

@[simp]
theorem timeRestrict_timeRestrict (F : PointedFlowData.{u, uE, uH} I D)
    (hcarrier : D'.carrier ⊆ D.carrier) (hregular : D'.regular ⊆ D.regular)
    (hcarrier' : D''.carrier ⊆ D'.carrier) (hregular' : D''.regular ⊆ D'.regular) :
    (F.timeRestrict D' hcarrier hregular).timeRestrict D'' hcarrier' hregular' =
      F.timeRestrict D'' (hcarrier'.trans hcarrier) (hregular'.trans hregular) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.timeRestrict_timeRestrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.timeRestrict_timeRestrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.timeRestrict_timeRestrict ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.timeRestrict_timeRestrict

end DifferentialGeometry.CheegerGromovCompactness.PointedFlowData
