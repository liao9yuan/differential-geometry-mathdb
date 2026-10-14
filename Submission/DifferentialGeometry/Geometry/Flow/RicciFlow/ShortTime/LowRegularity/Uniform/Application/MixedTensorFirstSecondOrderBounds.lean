import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Sobolev.H1L6
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Sobolev.FiberLpThreeSixComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Sobolev.Morrey
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.OperatorField.H1H2Composition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem operatorFieldComposition_h1_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
        ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r) (A B : ℝ),
          0 ≤ A → 0 ≤ B →
          (∑ j ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) ≤ A ^ 2 →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) ≤ B ^ 2 →
          ‖(⟨ccOperatorFieldComp (I := I) (M := M) g p r c Φ W⟩ :
              SmoothCcTensorH1 g p c)‖ ≤ C * A * B := by
  classical
  obtain ⟨Cpt, hCpt, hpt⟩ :=
    DifferentialGeometry.PDE.RicciFlow.morreyRS_uniform
      (I := I) (M := M) hDim gBase hΛ p r
  obtain ⟨CΦ, hCΦ, hΦ6⟩ :=
    DifferentialGeometry.PDE.RicciFlow.h1Lp6RS_uniform
      (I := I) (M := M) hDim gBase hΛ r c
  obtain ⟨CG6, hCG6, hG6⟩ :=
    DifferentialGeometry.PDE.RicciFlow.h1Lp6RS_uniform
      (I := I) (M := M) hDim gBase hΛ p (r + 1)
  obtain ⟨CV, hCV, h63⟩ :=
    DifferentialGeometry.PDE.RicciFlow.fiber_lp_three_le_uniform_constant_mul_lp_six
      (I := I) (M := M) gBase Λ
  let CG3 : ℝ := CV * CG6
  let C : ℝ :=
    Cpt + (Cpt + Real.sqrt (Module.finrank ℝ E) * CΦ * CG3)
  have hCG3 : 0 ≤ CG3 := by
    dsimp [CG3]
    exact mul_nonneg hCV hCG6
  refine ⟨C, by
    dsimp [C]
    positivity, ?_⟩
  intro g hEq hjet1 hjet2 Φ W A B hA hB hΦjet hWjet
  have hΦ6' : ∀ S : SmoothCcTensorH1 g r c,
      _root_.MeasureTheory.lpNorm (fiberLpFun g r c S.toCcTensor) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CΦ * ‖S‖ := by
    intro S
    change _root_.MeasureTheory.lpNorm (fun x => Real.sqrt
        (riemannianFiberNormSq (I := I) (M := M) g r c x
          (S.toCcTensor.toSection x))) 6
      (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CΦ * ‖S‖
    exact hΦ6 g hEq hjet1 S
  have hG3 : ∀ S : SmoothCcTensorH1 g p (r + 1),
      _root_.MeasureTheory.lpNorm (fiberLpFun g p (r + 1) S.toCcTensor) 3
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CG3 * ‖S‖ := by
    intro S
    calc
      _ ≤ CV * _root_.MeasureTheory.lpNorm (fiberLpFun g p (r + 1) S.toCcTensor) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) :=
        h63 g hEq p (r + 1) S.toCcTensor
      _ ≤ CV * (CG6 * ‖S‖) := by
        apply mul_le_mul_of_nonneg_left _ hCV
        change _root_.MeasureTheory.lpNorm (fun x => Real.sqrt
            (riemannianFiberNormSq (I := I) (M := M) g p (r + 1) x
              (S.toCcTensor.toSection x))) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CG6 * ‖S‖
        exact hG6 g hEq hjet1 S
      _ = CG3 * ‖S‖ := by
        dsimp [CG3]
        ring
  have hlocal := operator_field_composition_h1_bound_of_embedding_bounds (I := I) (M := M) g p r c
    Cpt CΦ CG3 hCpt hCΦ hCG3 (hpt g hEq hjet1 hjet2) hΦ6' hG3
    Φ W A B hA hB hΦjet hWjet
  simpa only [C] using hlocal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.operatorFieldComposition_h1_uniform_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.operatorFieldComposition_h1_uniform_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.operatorFieldComposition_h1_uniform_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.operatorFieldComposition_h1_uniform_bound

theorem operatorFieldComposition_h2_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
        ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r) (A B : ℝ),
          0 ≤ A → 0 ≤ B →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) ≤ A ^ 2 →
          (∑ j ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) ≤ B ^ 2 →
          ‖(⟨ccOperatorFieldComp (I := I) (M := M) g p r c Φ W⟩ :
              SmoothCcTensorH1 g p c)‖ ≤ C * A * B := by
  classical
  obtain ⟨Cpt, hCpt, hpt⟩ :=
    DifferentialGeometry.PDE.RicciFlow.morreyRS_uniform
      (I := I) (M := M) hDim gBase hΛ r c
  obtain ⟨CG, hCG, hG6⟩ :=
    DifferentialGeometry.PDE.RicciFlow.h1Lp6RS_uniform
      (I := I) (M := M) hDim gBase hΛ r (c + 1)
  obtain ⟨CW, hCW, hW6⟩ :=
    DifferentialGeometry.PDE.RicciFlow.h1Lp6RS_uniform
      (I := I) (M := M) hDim gBase hΛ p r
  obtain ⟨CV, hCV, h63⟩ :=
    DifferentialGeometry.PDE.RicciFlow.fiber_lp_three_le_uniform_constant_mul_lp_six
      (I := I) (M := M) gBase Λ
  let CW3 : ℝ := CV * CW
  let C : ℝ :=
    Cpt + (CG * CW3 + Real.sqrt (Module.finrank ℝ E) * Cpt)
  have hCW3 : 0 ≤ CW3 := by
    dsimp only [CW3]
    exact mul_nonneg hCV hCW
  refine ⟨C, by
    dsimp only [C]
    positivity, ?_⟩
  intro g hEq hjet1 hjet2 Φ W A B hA hB hΦjet hWjet
  have hG6' : ∀ S : SmoothCcTensorH1 g r (c + 1),
      _root_.MeasureTheory.lpNorm (fiberLpFun g r (c + 1) S.toCcTensor) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CG * ‖S‖ := by
    intro S
    change _root_.MeasureTheory.lpNorm (fun x => Real.sqrt
        (riemannianFiberNormSq (I := I) (M := M) g r (c + 1) x
          (S.toCcTensor.toSection x))) 6
      (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CG * ‖S‖
    exact hG6 g hEq hjet1 S
  have hW3 : ∀ S : SmoothCcTensorH1 g p r,
      _root_.MeasureTheory.lpNorm (fiberLpFun g p r S.toCcTensor) 3
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CW3 * ‖S‖ := by
    intro S
    calc
      _ ≤ CV * _root_.MeasureTheory.lpNorm (fiberLpFun g p r S.toCcTensor) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) :=
        h63 g hEq p r S.toCcTensor
      _ ≤ CV * (CW * ‖S‖) := by
        apply mul_le_mul_of_nonneg_left _ hCV
        change _root_.MeasureTheory.lpNorm (fun x => Real.sqrt
            (riemannianFiberNormSq (I := I) (M := M) g p r x
              (S.toCcTensor.toSection x))) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CW * ‖S‖
        exact hW6 g hEq hjet1 S
      _ = CW3 * ‖S‖ := by
        dsimp only [CW3]
        ring
  have hlocal := operator_field_composition_h2_bound_of_embedding_bounds (I := I) (M := M) g p r c
    Cpt CG CW3 hCpt hCG hCW3 (hpt g hEq hjet1 hjet2) hG6' hW3
    Φ W A B hA hB hΦjet hWjet
  simpa only [C] using hlocal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.operatorFieldComposition_h2_uniform_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.operatorFieldComposition_h2_uniform_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.operatorFieldComposition_h2_uniform_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.operatorFieldComposition_h2_uniform_bound

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
