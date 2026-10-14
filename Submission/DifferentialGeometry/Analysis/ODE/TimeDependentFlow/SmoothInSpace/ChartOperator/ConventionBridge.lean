import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ChartDictionary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section

namespace DifferentialGeometry.Analysis.ODE

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

open _root_.Submission.DifferentialGeometry.Integral.Measure

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def chartRawRepr (α : M) (X : Π y : M, TangentSpace I y) (z : E) : E :=
  (X ((extChartAt I α).symm z) : E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.chartRawRepr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.chartRawRepr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.chartRawRepr ``Submission.DifferentialGeometry.Analysis.ODE.chartRawRepr

def chartTrivRepr (α : M) (X : Π y : M, TangentSpace I y) (z : E) : E :=
  chartESectionRepr (I := I) α X ((extChartAt I α).symm z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.chartTrivRepr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.chartTrivRepr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.chartTrivRepr ``Submission.DifferentialGeometry.Analysis.ODE.chartTrivRepr

def chartMovingTriv (α : M) (z : E) : E →L[ℝ] E :=
  trivToE (I := I) α ((extChartAt I α).symm z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.chartMovingTriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.chartMovingTriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.chartMovingTriv ``Submission.DifferentialGeometry.Analysis.ODE.chartMovingTriv

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
lemma chartTrivRepr_eq_movingTriv_rawRepr
    (α : M) (X : Π y : M, TangentSpace I y) (z : E) :
    chartTrivRepr (I := I) α X z
      = chartMovingTriv (I := I) α z (chartRawRepr (I := I) α X z) := by
  unfold chartTrivRepr chartMovingTriv chartRawRepr
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.chartTrivRepr_eq_movingTriv_rawRepr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.chartTrivRepr_eq_movingTriv_rawRepr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.chartTrivRepr_eq_movingTriv_rawRepr ``Submission.DifferentialGeometry.Analysis.ODE.chartTrivRepr_eq_movingTriv_rawRepr

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
lemma chartMovingTriv_basepoint
    (α : M) (v : E) :
    chartMovingTriv (I := I) α (extChartAt I α α) v = v := by
  unfold chartMovingTriv
  have hself : (extChartAt I α).symm (extChartAt I α α) = α :=
    (extChartAt I α).left_inv (mem_extChartAt_source (I := I) α)
  rw [hself]
  have hcore : trivToE (I := I) α α
      = (tangentBundleCore I M).coordChange (achart H α) (achart H α) α :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) (M := M)
      (b₀ := α) (b := α) (mem_chart_source H α)
  rw [hcore]
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet]; exact mem_chart_source H α) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.chartMovingTriv_basepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.chartMovingTriv_basepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.chartMovingTriv_basepoint ``Submission.DifferentialGeometry.Analysis.ODE.chartMovingTriv_basepoint

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
theorem chartTrivRepr_fderiv_eq
    (α : M) (X : Π y : M, TangentSpace I y) (h : E)
    (hR : DifferentiableAt ℝ (chartRawRepr (I := I) α X) (extChartAt I α α))
    (hC : DifferentiableAt ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α)) :
    fderiv ℝ (chartTrivRepr (I := I) α X) (extChartAt I α α) h
      = fderiv ℝ (chartRawRepr (I := I) α X) (extChartAt I α α) h
        + (fderiv ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α) h)
            (chartRawRepr (I := I) α X (extChartAt I α α)) := by
  classical
  set z₀ : E := extChartAt I α α with hz₀
  have hTeq : chartTrivRepr (I := I) α X
      = fun z => chartMovingTriv (I := I) α z (chartRawRepr (I := I) α X z) :=
    funext (fun z => chartTrivRepr_eq_movingTriv_rawRepr (I := I) α X z)
  rw [hTeq]
  rw [fderiv_clm_apply hC hR]
  rw [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  rw [chartMovingTriv_basepoint (I := I) α (fderiv ℝ (chartRawRepr (I := I) α X) z₀ h)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.chartTrivRepr_fderiv_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.chartTrivRepr_fderiv_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.chartTrivRepr_fderiv_eq ``Submission.DifferentialGeometry.Analysis.ODE.chartTrivRepr_fderiv_eq

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
theorem chartLeviCivita_flat_summand_eq_rawRepr
    (α : M) (X : Π y : M, TangentSpace I y) (w : E)
    (hR : DifferentiableAt ℝ (chartRawRepr (I := I) α X) (extChartAt I α α))
    (hC : DifferentiableAt ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α)) :
    fderiv ℝ (chartESectionRepr (I := I) α X ∘ (extChartAt I α).symm)
        (extChartAt I α α) w
      = fderiv ℝ (chartRawRepr (I := I) α X) (extChartAt I α α) w
        + (fderiv ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α) w)
            (chartRawRepr (I := I) α X (extChartAt I α α)) := by
  have hcomp : (chartESectionRepr (I := I) α X ∘ (extChartAt I α).symm)
      = chartTrivRepr (I := I) α X := rfl
  rw [hcomp]
  exact chartTrivRepr_fderiv_eq (I := I) α X w hR hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.chartLeviCivita_flat_summand_eq_rawRepr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.chartLeviCivita_flat_summand_eq_rawRepr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.chartLeviCivita_flat_summand_eq_rawRepr ``Submission.DifferentialGeometry.Analysis.ODE.chartLeviCivita_flat_summand_eq_rawRepr

end Bridge

end DifferentialGeometry.Analysis.ODE
