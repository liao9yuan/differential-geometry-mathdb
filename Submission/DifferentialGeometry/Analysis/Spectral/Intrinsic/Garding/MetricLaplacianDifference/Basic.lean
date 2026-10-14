import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Scalar.HessianBound
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Curvature.LaplacianDifference

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

theorem lapDiff_energy_le
    (g : SmoothRiemannianMetric I M) :
    exists C : Real, 0 <= C ∧
      forall (h : SmoothRiemannianMetric I M)
        (v : TensorHs (I := I) (M := M) g 0 0 2)
        (hv : (Function.support v.coeff).Finite),
        (Module.finrank Real E : Real) *
            DifferentialGeometry.CheegerGromovCompactness.metricDerivNormSupOn
              (I := I) Set.univ 1 h g g <= (1 / 2 : Real) ->
        ∫ x, (ΔG (I := I) h ⟨_, (reprScalar0_smooth (I := I) (M := M) v hv)⟩ x -
            ΔG (I := I) g ⟨_, (reprScalar0_smooth (I := I) (M := M) v hv)⟩ x) ^ 2
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) <=
          C *
            (DifferentialGeometry.CheegerGromovCompactness.metricDerivNormSupOn
              (I := I) Set.univ 1 h g g) ^ 2 * ‖v‖ ^ 2 := by
  obtain ⟨CH, hCH, hHess⟩ := hess_energy_le (I := I) (M := M) g
  let n : Real := Module.finrank Real E
  let C : Real := 8 * n ^ 2 * CH + 72 * n
  refine ⟨C, ?_, ?_⟩
  · dsimp only [C, n]
    positivity
  intro h v hv hsmall
  let f : M -> Real := reprScalar0 (I := I) (M := M) v hv
  let hf : ContMDiff I 𝓘(Real, Real) ∞ f :=
    reprScalar0_smooth (I := I) (M := M) v hv
  let rho : Real :=
    DifferentialGeometry.CheegerGromovCompactness.metricDerivNormSupOn
      (I := I) Set.univ 1 h g g
  let A : Real := 8 * n ^ 2 * rho ^ 2
  let B : Real := 72 * n * rho ^ 2
  let HessNorm : M -> Real := fun x =>
    Tensor0SBundle.normSq0S (I := I) g x 2
      (leviHessSec (I := I) g f hf x)
  let duNorm : M -> Real := fun x =>
    Tensor0SBundle.normSq0S (I := I) g x 1
      (duSec (I := I) f hf x)
  let lhs : M -> Real := fun x =>
    (ΔG (I := I) h ⟨_, hf⟩ x - ΔG (I := I) g ⟨_, hf⟩ x) ^ 2
  let rhs : M -> Real := fun x => A * HessNorm x + B * duNorm x
  have hHessEq : HessNorm = chartHessFrobeniusSq (I := I) g f := by
    funext x
    exact hessSec_normSq (I := I) g hf x
  have hHessCont : Continuous HessNorm := by
    rw [hHessEq]
    exact chartHessFrobeniusSq_continuous (I := I) g hf
  have hduEq : duNorm = normGradSqFun (I := I) g f := by
    funext x
    simp only [duNorm, duSec_apply, normSq0S_eq_inner,
      inner0S_differential1FormFun_pair_eq_grad_inner,
      normGradSqFun_def]
    rfl
  have hduCont : Continuous duNorm := by
    rw [hduEq]
    exact normGradSqFun_continuous (I := I) g hf
  have hlhsCont : Continuous lhs := by
    exact (((Δ_g_contMDiff (I := I) h ⟨_, hf⟩).continuous.sub
      (Δ_g_contMDiff (I := I) g ⟨_, hf⟩).continuous).pow 2)
  have hrhsCont : Continuous rhs := by
    exact (continuous_const.mul hHessCont).add
      (continuous_const.mul hduCont)
  have hlhsInt : _root_.MeasureTheory.Integrable lhs
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_of_continuous_compactSpace (I := I) (M := M) g hlhsCont
  have hHessInt : _root_.MeasureTheory.Integrable HessNorm
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_of_continuous_compactSpace (I := I) (M := M) g hHessCont
  have hduInt : _root_.MeasureTheory.Integrable duNorm
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_of_continuous_compactSpace (I := I) (M := M) g hduCont
  have hrhsInt : _root_.MeasureTheory.Integrable rhs
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_of_continuous_compactSpace (I := I) (M := M) g hrhsCont
  have hpoint : forall x : M, lhs x <= rhs x := by
    intro x
    simpa only [lhs, rhs, A, B, n, rho, HessNorm, duNorm, f, hf] using
      DifferentialGeometry.CheegerGromovCompactness.lapDiff_sq_le
        (I := I) g h hf x hsmall
  have hint :
      (∫ x, lhs x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) <=
        ∫ x, rhs x ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    _root_.MeasureTheory.integral_mono_ae hlhsInt hrhsInt (Filter.Eventually.of_forall hpoint)
  have hrhsEq :
      (∫ x, rhs x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        A * (∫ x, HessNorm x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
          B * (∫ x, duNorm x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    rw [show rhs = fun x => A * HessNorm x + B * duNorm x from rfl]
    rw [_root_.MeasureTheory.integral_add (hHessInt.const_mul A) (hduInt.const_mul B)]
    rw [_root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul]
  have hH :
      (∫ x, HessNorm x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) <=
        CH * ‖v‖ ^ 2 := by
    rw [hHessEq]
    simpa only [f] using hHess v hv
  have hdu :
      (∫ x, duNorm x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) <=
        ‖v‖ ^ 2 := by
    rw [hduEq]
    simpa only [f] using grad_energy_le (I := I) (M := M) g v hv
  have hA : 0 <= A := by dsimp only [A, n]; positivity
  have hB : 0 <= B := by dsimp only [B, n]; positivity
  calc
    ∫ x, (ΔG (I := I) h ⟨_, (reprScalar0_smooth (I := I) (M := M) v hv)⟩ x -
        ΔG (I := I) g ⟨_, (reprScalar0_smooth (I := I) (M := M) v hv)⟩ x) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, lhs x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      rfl
    _ <= ∫ x, rhs x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := hint
    _ = A * (∫ x, HessNorm x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        B * (∫ x, duNorm x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := hrhsEq
    _ <= A * (CH * ‖v‖ ^ 2) + B * ‖v‖ ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hH hA)
        (mul_le_mul_of_nonneg_left hdu hB)
    _ = C * rho ^ 2 * ‖v‖ ^ 2 := by
      simp only [A, B, C]
      ring
    _ = C *
        (DifferentialGeometry.CheegerGromovCompactness.metricDerivNormSupOn
          (I := I) Set.univ 1 h g g) ^ 2 * ‖v‖ ^ 2 := by rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiff_energy_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiff_energy_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiff_energy_le ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiff_energy_le

end Spectral
end Analysis
end DifferentialGeometry

end
