import Submission.DifferentialGeometry.Geometry.Curvature.SecondOrderDefect.PartialMetricTrace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
    CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Tensor0SNabla
open _root_.Submission.DifferentialGeometry.TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
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

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem firstSlotHessMap_eq_secondCovDeriv_field
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (y : M) :
    firstSlotHessMap (I := I) g r s Y T y (X y) =
      tensorSecondCovDeriv (I := I) g r s X Y T y := by
  rw [tensorSecondCovDeriv_eq_firstSlotHessMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.firstSlotHessMap_eq_secondCovDeriv_field then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.firstSlotHessMap_eq_secondCovDeriv_field"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.firstSlotHessMap_eq_secondCovDeriv_field ``Submission.DifferentialGeometry.Analysis.Elliptic.firstSlotHessMap_eq_secondCovDeriv_field

noncomputable def frozenFrameTrace
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x y : M) :
    TensorRSSpace r s I y :=
  ∑ i : Fin (Module.finrank ℝ E),
    tensorSecondCovDeriv (I := I) g r s
      (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.frozenFrameTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.frozenFrameTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.frozenFrameTrace ``Submission.DifferentialGeometry.Analysis.Elliptic.frozenFrameTrace

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma frozenFrameTrace_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x y : M) :
    frozenFrameTrace (I := I) g r s T x y =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g r s
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.frozenFrameTrace_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.frozenFrameTrace_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.frozenFrameTrace_def ``Submission.DifferentialGeometry.Analysis.Elliptic.frozenFrameTrace_def

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem frozenFrameTrace_self_eq_metricTrace2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    frozenFrameTrace (I := I) g r s T x x =
      metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s) T x := by
  rw [frozenFrameTrace_def, metricTrace2_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.frozenFrameTrace_self_eq_metricTrace2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.frozenFrameTrace_self_eq_metricTrace2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.frozenFrameTrace_self_eq_metricTrace2 ``Submission.DifferentialGeometry.Analysis.Elliptic.frozenFrameTrace_self_eq_metricTrace2

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem frozenFrameTrace_eq_gWeighted_of_mem_neighborhood
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNeighborhood (I := I) (M := M) x) :
    frozenFrameTrace (I := I) g r s T x y =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        g.inner y (smoothOrthoFrame (I := I) g x i y)
            (smoothOrthoFrame (I := I) g x j y) •
          firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T y
            (smoothOrthoFrame (I := I) g x j y) := by
  classical
  rw [frozenFrameTrace_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tensorSecondCovDeriv_eq_firstSlotHessMap]
  rw [show (∑ j : Fin (Module.finrank ℝ E),
        g.inner y (smoothOrthoFrame (I := I) g x i y)
            (smoothOrthoFrame (I := I) g x j y) •
          firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T y
            (smoothOrthoFrame (I := I) g x j y)) =
      ∑ j : Fin (Module.finrank ℝ E),
        (if i = j then
          firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T y
            (smoothOrthoFrame (I := I) g x j y)
          else 0) from by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smoothOrthoFrame_orthonormal (I := I) g x hy i j]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij, one_smul]
    · rw [if_neg hij, if_neg hij, zero_smul]]
  rw [Finset.sum_ite_eq (Finset.univ) i
    (fun j => firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T y
      (smoothOrthoFrame (I := I) g x j y))]
  rw [if_pos (Finset.mem_univ i)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.frozenFrameTrace_eq_gWeighted_of_mem_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.frozenFrameTrace_eq_gWeighted_of_mem_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.frozenFrameTrace_eq_gWeighted_of_mem_neighborhood ``Submission.DifferentialGeometry.Analysis.Elliptic.frozenFrameTrace_eq_gWeighted_of_mem_neighborhood

end Elliptic
end Analysis
end DifferentialGeometry

end
