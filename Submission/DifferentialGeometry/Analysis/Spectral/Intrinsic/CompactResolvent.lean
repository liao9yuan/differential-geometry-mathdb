import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.Hilbert.CompactInclusion
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Rellich.Resolvent
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.Resolvent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

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

omit [CompleteSpace E] in
theorem tensorResolventL2_isCompactOperator
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) :=
  tensorResolventL2_isCompactOperator_of_isCompactOperator
    (I := I) (M := M) g r s
    (tensorH1ComplToTensorL2_isCompactOperator_intrinsic
      (I := I) (M := M) g r s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator ``Submission.DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator

omit [CompleteSpace E] in
theorem tensorResolventL2_isCompactOperator_and_isSelfAdjoint
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) ∧
      IsSelfAdjoint (tensorResolventL2 (I := I) (M := M) g r s) :=
  ⟨tensorResolventL2_isCompactOperator (I := I) (M := M) g r s,
   tensorResolventL2_isSelfAdjoint (I := I) (M := M) g r s⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator_and_isSelfAdjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator_and_isSelfAdjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator_and_isSelfAdjoint ``Submission.DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator_and_isSelfAdjoint

end Spectral
end Analysis
end DifferentialGeometry

end
