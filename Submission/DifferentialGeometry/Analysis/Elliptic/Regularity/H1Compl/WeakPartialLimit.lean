import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.H1Compl.GradientLipschitzBound
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.H1ComplFromDom
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.L2
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.LpSpace.Complete

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace H1ComplWeakPartialLimit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientLipschitz
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientLipschitzBound
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplToLpChartBridge
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

structure ChartPushedPartialLipschitz
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound : ∀ v : SmoothScalar g,
    ‖chartPushedPartialLpLin (I := I) (M := M) g α j v‖ ≤ C * ‖v‖

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.ChartPushedPartialLipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.ChartPushedPartialLipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.ChartPushedPartialLipschitz ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.ChartPushedPartialLipschitz

noncomputable def chartPushedPartialCLM
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j) :
    SmoothScalar g →L[ℝ]
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  (chartPushedPartialLpLin (I := I) (M := M) g α j).mkContinuous hLip.C
    hLip.bound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedPartialCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedPartialCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedPartialCLM ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedPartialCLM

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartPushedPartialCLM_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    chartPushedPartialCLM (I := I) (M := M) g α j hLip v =
      chartPushedPartialLpLin (I := I) (M := M) g α j v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedPartialCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedPartialCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedPartialCLM_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedPartialCLM_apply

omit [NeZero (Module.finrank ℝ E)] in
private lemma denseRange_smoothToH1Compl_local
    (g : SmoothRiemannianMetric I M) :
    DenseRange (smoothToH1Compl (I := I) (M := M) g) := by
  unfold smoothToH1Compl
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.denseRange_smoothToH1Compl_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.denseRange_smoothToH1Compl_local target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma isUniformInducing_smoothToH1Compl_local
    (g : SmoothRiemannianMetric I M) :
    IsUniformInducing (smoothToH1Compl (I := I) (M := M) g) := by
  unfold smoothToH1Compl
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothScalar g)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.isUniformInducing_smoothToH1Compl_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.isUniformInducing_smoothToH1Compl_local target :: scope.openDecls } }

noncomputable def H1ComplPartialCLM
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j) :
    H1Compl g →L[ℝ]
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  ContinuousLinearMap.extend
    (chartPushedPartialCLM (I := I) (M := M) g α j hLip)
    (smoothToH1Compl (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.H1ComplPartialCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.H1ComplPartialCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.H1ComplPartialCLM ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.H1ComplPartialCLM

omit [NeZero (Module.finrank ℝ E)] in
lemma H1ComplPartialCLM_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    H1ComplPartialCLM (I := I) (M := M) g α j hLip
        (smoothToH1Compl (I := I) (M := M) g v) =
      chartPushedPartialCLM (I := I) (M := M) g α j hLip v := by
  unfold H1ComplPartialCLM
  exact ContinuousLinearMap.extend_eq
    (chartPushedPartialCLM (I := I) (M := M) g α j hLip)
    (e := smoothToH1Compl (I := I) (M := M) g)
    (denseRange_smoothToH1Compl_local (I := I) (M := M) g)
    (isUniformInducing_smoothToH1Compl_local (I := I) (M := M) g) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.H1ComplPartialCLM_smoothToH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.H1ComplPartialCLM_smoothToH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.H1ComplPartialCLM_smoothToH1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.H1ComplPartialCLM_smoothToH1Compl

noncomputable def chartPushedWeakPartialLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j)
    (u_h : H1Compl g) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) :=
  H1ComplPartialCLM (I := I) (M := M) g α j hLip u_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedWeakPartialLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedWeakPartialLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedWeakPartialLp ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedWeakPartialLp

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushedWeakPartialLp_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    chartPushedWeakPartialLp (I := I) (M := M) g α j hLip
        (smoothToH1Compl (I := I) (M := M) g v) =
      chartPushedPartialLp (I := I) (M := M) g α j v
        (chartPushedPartial_memLp (I := I) (M := M) g α j v) := by
  unfold chartPushedWeakPartialLp
  rw [H1ComplPartialCLM_smoothToH1Compl]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedWeakPartialLp_smoothToH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedWeakPartialLp_smoothToH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedWeakPartialLp_smoothToH1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedWeakPartialLp_smoothToH1Compl

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushedWeakPartialLp_continuous
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j) :
    Continuous (chartPushedWeakPartialLp (I := I) (M := M) g α j hLip) := by
  unfold chartPushedWeakPartialLp
  exact (H1ComplPartialCLM (I := I) (M := M) g α j hLip).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedWeakPartialLp_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedWeakPartialLp_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedWeakPartialLp_continuous ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit.chartPushedWeakPartialLp_continuous

end H1ComplWeakPartialLimit
end Laplacian
end Analysis
end DifferentialGeometry

end
