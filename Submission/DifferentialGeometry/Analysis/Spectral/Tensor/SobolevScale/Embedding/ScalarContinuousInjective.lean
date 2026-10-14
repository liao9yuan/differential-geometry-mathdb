import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.ScalarContinuous
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothCoreL2
import Submission.DifferentialGeometry.Analysis.Heat.Smoothing.Scalar.HeatFlow
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Spectral

open _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.HeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instIsFiniteMeasureRiemannianVolumeMeasure (g : SmoothRiemannianMetric I M) :
    IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let := riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instIsFiniteMeasureRiemannianVolumeMeasure
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instIsFiniteMeasureRiemannianVolumeMeasure target :: scope.openDecls } }

theorem scalarHsToContinuous_toLp (g : SmoothRiemannianMetric I M)
    (u : TensorHs (I := I) (M := M) g 0 0
      ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ)) :
    ContinuousMap.toLp 2 (riemannianVolumeMeasure (I := I) (M := M) g) ℝ
      (scalarHsToContinuous g u) =
    tensor00ToScalarL2LI g
      (tensorHsToL2 (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
        (by positivity : (0 : ℝ) ≤ ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ)) u) := by
  let hσ : (0 : ℝ) ≤ ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ) := by positivity
  let lhs := (ContinuousMap.toLp 2 (riemannianVolumeMeasure (I := I) (M := M) g) ℝ).comp
    (scalarHsToContinuous g)
  let rhs := (tensor00ToScalarL2LI g).toContinuousLinearMap.comp
    (tensorHsToL2 (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) hσ)
  have heq : (lhs : _ → _) = rhs := by
    apply (ccToHsLin_dense (I := I) (M := M) g 0 hσ).equalizer lhs.continuous rhs.continuous
    funext S
    change ContinuousMap.toLp 2 (riemannianVolumeMeasure (I := I) (M := M) g) ℝ
      (scalarHsToContinuous g (ccTensorToHs g 0 _ S)) =
      tensor00ToScalarL2 g (tensorHsToL2 _ hσ (ccTensorToHs g 0 _ S))
    rw [tensorHsToL2_ccTensorToHs, tensor00ToScalarL2_toL2]
    apply Lp.ext
    refine (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) _ _).trans ?_
    have hpoint : (scalarHsToContinuous g (ccTensorToHs g 0 _ S) : M → ℝ) =
        (scalar0Cc g S).toFun := by
      funext x
      exact scalarHsToContinuous_apply_ccTensorToHs g S x
    rw [hpoint]
    exact (MemLp.coeFn_toLp (scalar0Cc g S).memLp_two).symm
  exact congrFun heq u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarHsToContinuous_toLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarHsToContinuous_toLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarHsToContinuous_toLp ``Submission.DifferentialGeometry.Analysis.Spectral.scalarHsToContinuous_toLp

end DifferentialGeometry.Analysis.Spectral
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Analysis.HeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

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

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instIsFiniteMeasureRiemannianVolumeMeasure_1 (g : SmoothRiemannianMetric I M) :
    MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let := riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instIsFiniteMeasureRiemannianVolumeMeasure_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instIsFiniteMeasureRiemannianVolumeMeasure_1 target :: scope.openDecls } }

theorem scalarHsToContinuous_injective (g : SmoothRiemannianMetric I M) :
    Function.Injective (scalarHsToContinuous (I := I) (M := M) g) := by
  intro u v huv
  apply tensorHsToL2_injective
    (h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
    (by positivity : (0 : ℝ) ≤ ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ))
  apply (tensor00ToScalarL2LI g).injective
  rw [← scalarHsToContinuous_toLp, ← scalarHsToContinuous_toLp, huv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarHsToContinuous_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarHsToContinuous_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarHsToContinuous_injective ``Submission.DifferentialGeometry.Analysis.Spectral.scalarHsToContinuous_injective

end DifferentialGeometry.Analysis.Spectral

namespace DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

theorem scalarH1ToContinuous_injective
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) : Function.Injective (scalarH1ToContinuous g) := by
  intro u v huv
  apply (tensorHsCongr g 0 0 (by norm_num : (1 : ℝ) = ((Module.finrank ℝ ℝ / 2 + 1 : ℕ) : ℝ))).injective
  exact scalarHsToContinuous_injective g huv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous_injective ``Submission.DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous_injective

theorem scalarH1PiToContinuous_injective {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) :
    Function.Injective (scalarH1PiToContinuous (ι := ι) g) := by
  intro u v huv
  apply PiLp.ext
  intro i
  apply scalarH1ToContinuous_injective g
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun f : C(M, ι → ℝ) => f x i) huv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarH1PiToContinuous_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarH1PiToContinuous_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarH1PiToContinuous_injective ``Submission.DifferentialGeometry.Analysis.Spectral.scalarH1PiToContinuous_injective

end DifferentialGeometry.Analysis.Spectral
