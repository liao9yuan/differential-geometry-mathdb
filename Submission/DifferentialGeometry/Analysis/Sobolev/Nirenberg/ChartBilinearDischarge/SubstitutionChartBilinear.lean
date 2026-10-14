import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.SubstitutionNonSmoothChartBilinear
import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.Basic
import Submission.DifferentialGeometry.Analysis.Sobolev.Approximation.WeakSolution.H1

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal Pointwise

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace SubstitutionDischargeChartBilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTranslatedCutoffDiffQuot
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergSubstitution
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionNonSmoothChartBilinear

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma diffQuot_mul_apply
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) (f g : EuclN → ℝ) (x : EuclN) :
    DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (fun y => f y * g y) x =
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h f x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h g x +
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h f x * g x :=
  DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.diffQuot_coeff_apply
    (d := Module.finrank ℝ E) k h f g x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.diffQuot_mul_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.diffQuot_mul_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.diffQuot_mul_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.diffQuot_mul_apply

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma integral_mul_diffQuot_neg_eq_neg_integral_diffQuot_mul
    {F G : EuclN → ℝ} (k : Fin (Module.finrank ℝ E)) {h : ℝ} (hh : h ≠ 0)
    (hF_cont : Continuous F) (hG_smooth : ContDiff ℝ (⊤ : ℕ∞) G)
    (hG_support : HasCompactSupport G) :
    ∫ x, F x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h) G x ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      -∫ x, DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h F x * G x
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  have h_ibp :=
    integral_diffQuot_mul_eq_neg_integral_mul_diffQuot_locally_supported
      (d := Module.finrank ℝ E) (k := k) (f := F) (g := G) hh hF_cont
      hG_smooth hG_support
  linarith [h_ibp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.integral_mul_diffQuot_neg_eq_neg_integral_diffQuot_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.integral_mul_diffQuot_neg_eq_neg_integral_diffQuot_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.integral_mul_diffQuot_neg_eq_neg_integral_diffQuot_mul ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeChartBilinear.integral_mul_diffQuot_neg_eq_neg_integral_diffQuot_mul

end SubstitutionDischargeChartBilinear
end Sobolev
end Analysis
end DifferentialGeometry
