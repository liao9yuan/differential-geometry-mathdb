import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.Chart.Lp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function _root_.FiberBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianChartAlphaChristoffelDischarge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianLpClass
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianBridge
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartInvariance
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaFrobenius
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

def christoffelDischargeSmoothCase
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    Prop :=
  ∀ x : M,
    ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothPairingChristoffelDiff (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) = 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.christoffelDischargeSmoothCase then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.christoffelDischargeSmoothCase"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.christoffelDischargeSmoothCase ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.christoffelDischargeSmoothCase

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] lemma christoffelDischargeSmoothCase_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    christoffelDischargeSmoothCase (I := I) (M := M) g φ v ↔
      ∀ x : M,
        ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
            (chartAtlasPOU I M α : M → ℝ) x *
              smoothPairingChristoffelDiff (I := I) (M := M) g α φ v
                ((toEuclidean (E := E)) (extChartAt I α x)) = 0 := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.christoffelDischargeSmoothCase_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.christoffelDischargeSmoothCase_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.christoffelDischargeSmoothCase_def ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.christoffelDischargeSmoothCase_def

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem smoothEuclidHessianPairingChart_at_chartAt_eq_tensor_plus_diff
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (α : M) (x : M) :
    smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
        ((toEuclidean (E := E)) (extChartAt I α x)) =
      smoothTensorPairingChart (I := I) (M := M) g α φ v
          ((toEuclidean (E := E)) (extChartAt I α x)) +
        smoothPairingChristoffelDiff (I := I) (M := M) g α φ v
          ((toEuclidean (E := E)) (extChartAt I α x)) :=
  smoothEuclidHessianPairingChart_eq_tensor_plus_diff
    (I := I) (M := M) g α φ v ((toEuclidean (E := E)) (extChartAt I α x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.smoothEuclidHessianPairingChart_at_chartAt_eq_tensor_plus_diff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.smoothEuclidHessianPairingChart_at_chartAt_eq_tensor_plus_diff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.smoothEuclidHessianPairingChart_at_chartAt_eq_tensor_plus_diff ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.smoothEuclidHessianPairingChart_at_chartAt_eq_tensor_plus_diff

theorem pou_weighted_euclid_pairing_decompose
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (x : M) :
    ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) x +
      ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothPairingChristoffelDiff (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) := by
  classical
  have h_per_term : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      (chartAtlasPOU I M α : M → ℝ) x *
          smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) =
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothTensorPairingChart (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) +
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothPairingChristoffelDiff (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) := by
    intro α _
    rw [smoothEuclidHessianPairingChart_at_chartAt_eq_tensor_plus_diff
      (I := I) (M := M) g φ v α x]
    ring
  rw [Finset.sum_congr rfl h_per_term]
  rw [Finset.sum_add_distrib]
  rw [pou_weighted_tensor_pairing_eq_hessPairingChart_pointwise
    (I := I) (M := M) g φ v x]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.pou_weighted_euclid_pairing_decompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.pou_weighted_euclid_pairing_decompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.pou_weighted_euclid_pairing_decompose ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.pou_weighted_euclid_pairing_decompose

theorem pou_weighted_euclid_pairing_eq_hessPairingChart_pointwise_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v)
    (x : M) :
    ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
  classical
  rw [pou_weighted_euclid_pairing_decompose (I := I) (M := M) g φ v x]
  rw [h_discharge x]
  rw [add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.pou_weighted_euclid_pairing_eq_hessPairingChart_pointwise_of_discharge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.pou_weighted_euclid_pairing_eq_hessPairingChart_pointwise_of_discharge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.pou_weighted_euclid_pairing_eq_hessPairingChart_pointwise_of_discharge ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.pou_weighted_euclid_pairing_eq_hessPairingChart_pointwise_of_discharge

omit [NeZero (Module.finrank ℝ E)] in
theorem hessPairingMChartContribution_smoothCase_eq_weighted_chartLocal
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (α : M) (x : M) :
    hessPairingMChartContribution (I := I) (M := M) g φ α
        (u_h := smoothToH1Compl (I := I) (M := M) g v) x =
      (chartAtlasPOU I M α : M → ℝ) x *
        hessPairingChartLocal (I := I) (M := M) g α φ
          (u_h := smoothToH1Compl (I := I) (M := M) g v)
          ((toEuclidean (E := E)) (extChartAt I α x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.hessPairingMChartContribution_smoothCase_eq_weighted_chartLocal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.hessPairingMChartContribution_smoothCase_eq_weighted_chartLocal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.hessPairingMChartContribution_smoothCase_eq_weighted_chartLocal ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge.hessPairingMChartContribution_smoothCase_eq_weighted_chartLocal

end HessianChartAlphaChristoffelDischarge
end Laplacian
end Analysis
end DifferentialGeometry

end
