import Submission.DifferentialGeometry.Geometry.Connection.Laplacian.TensorConnLaplacian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Filter
open _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

noncomputable def rawTensorConnLapSmooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    SmoothCcTensor g r s :=
  tensorConnLaplacianOfContMDiff (I := I) g r s T
    (rawTensorConnLap_contMDiff (I := I) g r s (fun z : M => T.toSection z)
      T.toSection.contMDiff_toFun)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth ``Submission.DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth

end NormedSpaceModel

section NormedSpaceModelLemmas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] lemma rawTensorConnLapSmooth_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (x : M) :
    (rawTensorConnLapSmooth (I := I) g r s T).toSection x =
      rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) x := by
  unfold rawTensorConnLapSmooth
  exact tensorConnLaplacian_of_contMDiff_toFun (I := I) g r s T _ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth_toSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth_toSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth_toSection_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth_toSection_apply

noncomputable def rawTensorConnLapIter
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ℕ → SmoothCcTensor g r s → SmoothCcTensor g r s
  | 0,     T => T
  | k + 1, T => rawTensorConnLapSmooth (I := I) g r s
                  (rawTensorConnLapIter g r s k T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapIter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapIter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapIter ``Submission.DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapIter

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem rawTensorConnLapIter_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    rawTensorConnLapIter (I := I) g r s 0 T = T := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapIter_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapIter_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapIter_zero ``Submission.DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapIter_zero

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem rawTensorConnLapIter_succ
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (T : SmoothCcTensor g r s) :
    rawTensorConnLapIter (I := I) g r s (k + 1) T =
      rawTensorConnLapSmooth (I := I) g r s
        (rawTensorConnLapIter (I := I) g r s k T) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapIter_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapIter_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapIter_succ ``Submission.DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapIter_succ

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
lemma rawTensorConnLapIter_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    rawTensorConnLapIter (I := I) g r s 1 T =
      rawTensorConnLapSmooth (I := I) g r s T := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapIter_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapIter_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapIter_one ``Submission.DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapIter_one

end NormedSpaceModelLemmas

end Elliptic
end Analysis
end DifferentialGeometry

end
