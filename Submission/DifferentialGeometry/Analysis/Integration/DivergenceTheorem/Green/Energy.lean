import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.Identities
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Integral.DivergenceTheorem

open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem integral_normGradSqFun_eq_integral_neg_laplacian_mul
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (hsupport : HasCompactSupport u) :
    (∫ x, normGradSqFun (I := I) g u x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, (-laplacian (I := I) (LeviCivita (I := I) g) g u x) * u x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hgreen := green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
    (I := I) g hu hu hsupport
  change (∫ x, normGradSqFun (I := I) g u x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
    -∫ x, u x * ΔG (I := I) g ⟨u, hu⟩ x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) at hgreen
  calc
    _ = -∫ x, u x * ΔG (I := I) g ⟨u, hu⟩ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := hgreen
    _ = -∫ x, u x * laplacian (I := I) (LeviCivita (I := I) g) g u x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      congr 1
      apply _root_.MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        congrArg (fun z => u x * z) (laplacian_levi_eq g hu x).symm
    _ = _ := by
      rw [← _root_.MeasureTheory.integral_neg]
      apply _root_.MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.integral_normGradSqFun_eq_integral_neg_laplacian_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.integral_normGradSqFun_eq_integral_neg_laplacian_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.integral_normGradSqFun_eq_integral_neg_laplacian_mul ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.integral_normGradSqFun_eq_integral_neg_laplacian_mul

end DifferentialGeometry.Integral.DivergenceTheorem
