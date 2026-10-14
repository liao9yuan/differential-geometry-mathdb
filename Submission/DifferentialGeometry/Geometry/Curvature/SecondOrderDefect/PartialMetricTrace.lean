import Submission.DifferentialGeometry.Geometry.Curvature.SecondOrderDefect.OffDiagonalCurvatureCore
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.CovariantCompatibility

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
    CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

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

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

noncomputable def metricTrace2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (H : (Π b : M, TangentSpace I b) → (Π b : M, TangentSpace I b) →
      (Π b : M, TensorRSSpace r s I b) → (z : M) → TensorRSSpace r s I z)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    H (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricTrace2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricTrace2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricTrace2 ``Submission.DifferentialGeometry.Geometry.Curvature.metricTrace2

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
lemma metricTrace2_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (H : (Π b : M, TangentSpace I b) → (Π b : M, TangentSpace I b) →
      (Π b : M, TensorRSSpace r s I b) → (z : M) → TensorRSSpace r s I z)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    metricTrace2 (I := I) g r s H T x =
      ∑ i : Fin (Module.finrank ℝ E),
        H (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricTrace2_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricTrace2_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricTrace2_def ``Submission.DifferentialGeometry.Geometry.Curvature.metricTrace2_def

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem metricTrace2_secondCovDeriv_eq_metricTraceHessian
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s) T x =
      metricTraceHessian (I := I) g r s T x := by
  rw [metricTrace2_def, metricTraceHessian_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricTrace2_secondCovDeriv_eq_metricTraceHessian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricTrace2_secondCovDeriv_eq_metricTraceHessian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricTrace2_secondCovDeriv_eq_metricTraceHessian ``Submission.DifferentialGeometry.Geometry.Curvature.metricTrace2_secondCovDeriv_eq_metricTraceHessian

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem rawTensorConnLap_eq_metricTrace2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    rawTensorConnLap (I := I) g r s T x =
      metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s) T x := by
  rw [metricTrace2_secondCovDeriv_eq_metricTraceHessian]
  exact rawTensorConnLap_eq_metricTraceHessian (I := I) g r s T x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_eq_metricTrace2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_eq_metricTrace2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_eq_metricTrace2 ``Submission.DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_eq_metricTrace2

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem metricTrace2_eq_gWeighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s) T x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        g.inner x (smoothOrthoFrame (I := I) g x i x)
            (smoothOrthoFrame (I := I) g x j x) •
          firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T x
            (smoothOrthoFrame (I := I) g x j x) := by
  rw [metricTrace2_secondCovDeriv_eq_metricTraceHessian]
  exact metricTraceHessian_eq_gWeighted_firstSlot (I := I) g r s T x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricTrace2_eq_gWeighted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricTrace2_eq_gWeighted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricTrace2_eq_gWeighted ``Submission.DifferentialGeometry.Geometry.Curvature.metricTrace2_eq_gWeighted

omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem frame_pairing_locally_const
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    (fun y : M => g.inner y
        (smoothOrthoFrame (I := I) g x i y)
        (smoothOrthoFrame (I := I) g x j y)) =ᶠ[nhds x]
      (fun _ : M => (if i = j then (1 : ℝ) else 0)) := by
  filter_upwards [smoothOrthoFrameNeighborhood_mem_nhds (I := I) (M := M) x] with y hy
  exact smoothOrthoFrame_orthonormal (I := I) g x hy i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.frame_pairing_locally_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.frame_pairing_locally_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.frame_pairing_locally_const ``Submission.DifferentialGeometry.Geometry.Curvature.frame_pairing_locally_const

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem connection_smoothOrthoFrame_inner_add_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) (w : TangentSpace I x) :
    g.inner x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x w)
        (smoothOrthoFrame (I := I) g x j x)
      + g.inner x
        (smoothOrthoFrame (I := I) g x i x)
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x j) x w) = 0 := by
  classical
  have hEi : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y
        (smoothOrthoFrame (I := I) g x i y)) x :=
    (smoothOrthoFrame_smooth (I := I) g x i).contMDiffAt.mdifferentiableAt (by simp)
  have hEj : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y
        (smoothOrthoFrame (I := I) g x j y)) x :=
    (smoothOrthoFrame_smooth (I := I) g x j).contMDiffAt.mdifferentiableAt (by simp)
  have hmfderiv0 : mfderiv I 𝓘(ℝ) (fun y : M => g.inner y
        (smoothOrthoFrame (I := I) g x i y)
        (smoothOrthoFrame (I := I) g x j y)) x w = 0 := by
    rw [(frame_pairing_locally_const (I := I) g x i j).mfderiv_eq, mfderiv_const]
    rfl
  have hmc := (LeviCivita_isMetricCompatible (I := I) g).apply
    (Y := fun y => smoothOrthoFrame (I := I) g x i y)
    (Z := fun y => smoothOrthoFrame (I := I) g x j y)
    (x := x) hEi hEj w
  rw [hmfderiv0] at hmc
  exact hmc.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.connection_smoothOrthoFrame_inner_add_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.connection_smoothOrthoFrame_inner_add_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.connection_smoothOrthoFrame_inner_add_eq_zero ``Submission.DifferentialGeometry.Geometry.Curvature.connection_smoothOrthoFrame_inner_add_eq_zero

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem cometric_diagonal_skew
    (g : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) (w : TangentSpace I x) :
    g.inner x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x w)
        (smoothOrthoFrame (I := I) g x i x) = 0 := by
  have hcore := connection_smoothOrthoFrame_inner_add_eq_zero (I := I) g x i i w
  have hsymm : g.inner x
        (smoothOrthoFrame (I := I) g x i x)
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x w) =
      g.inner x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x w)
        (smoothOrthoFrame (I := I) g x i x) := g.symm x _ _
  rw [hsymm] at hcore
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.cometric_diagonal_skew then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.cometric_diagonal_skew"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.cometric_diagonal_skew ``Submission.DifferentialGeometry.Geometry.Curvature.cometric_diagonal_skew

end Curvature
end Geometry
end DifferentialGeometry

end
