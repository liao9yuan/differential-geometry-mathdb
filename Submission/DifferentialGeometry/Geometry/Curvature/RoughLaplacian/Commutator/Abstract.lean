import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.GradientField

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.CovariantDerivative _root_.Submission.CovariantDerivative _root_.Submission.DifferentialGeometry.Geometry.Curvature.CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix

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
  [T2Space M]

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

noncomputable def unitGradAbstractRoughLap
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    Tensor0SSpace 3 I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
        (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i) (unitGradField (I := I) (M := M) g T₀)) x
        (smoothOrthoFrame (I := I) g x i x) -
      (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
        (unitGradField (I := I) (M := M) g T₀) x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.unitGradAbstractRoughLap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.unitGradAbstractRoughLap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.unitGradAbstractRoughLap ``Submission.DifferentialGeometry.Geometry.Curvature.unitGradAbstractRoughLap

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma unitGradAbstractRoughLap_def
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    unitGradAbstractRoughLap (I := I) (M := M) g T₀ x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
            (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i) (unitGradField (I := I) (M := M) g T₀)) x
            (smoothOrthoFrame (I := I) g x i x) -
          (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
            (unitGradField (I := I) (M := M) g T₀) x
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x
              (smoothOrthoFrame (I := I) g x i x))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.unitGradAbstractRoughLap_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.unitGradAbstractRoughLap_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.unitGradAbstractRoughLap_def ``Submission.DifferentialGeometry.Geometry.Curvature.unitGradAbstractRoughLap_def

omit [CompactSpace M] in
theorem rawTensorConnLap_covGrad_unit_eval_eq_abstract_roughLap
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        rawTensorConnLap (I := I) g 0 3
          (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      unitGradAbstractRoughLap (I := I) (M := M) g T₀ x := by
  classical
  rw [rawTensorConnLap_covGrad_eq_frame_trace (I := I) (M := M) g T₀ x]
  rw [unitGradAbstractRoughLap_def]
  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          ∑ i : Fin (Module.finrank ℝ E),
            tensorSecondCovDeriv (I := I) g 0 3
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x)
          (unitZeroSec (I := I) (M := M) x) =
        ∑ i : Fin (Module.finrank ℝ E),
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            tensorSecondCovDeriv (I := I) g 0 3
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x)
            (unitZeroSec (I := I) (M := M) x) from by
        rw [sum_apply]]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) :=
    smoothOrthoFrame_smooth (I := I) g x i
  exact tensorSecondCovDeriv_covGrad_unit_eval_two (I := I) (M := M) g T₀ hB x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_covGrad_unit_eval_eq_abstract_roughLap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_covGrad_unit_eval_eq_abstract_roughLap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_covGrad_unit_eval_eq_abstract_roughLap ``Submission.DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_covGrad_unit_eval_eq_abstract_roughLap

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem abstract_succ_covDeriv_unfold_at
    (g : SmoothRiemannianMetric I M)
    (W : Π y : M, Tensor0SSpace 3 I y)
    {Vfield Y : Π b : M, TangentSpace I b} {x : M}
    (hC : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel 2 ℝ E))
      (fun y => TotalSpace.mk' (E →L[ℝ] Tensor0SModel 2 ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace 2 I z)) y
        (curriedSection I M W y)) x)
    (hVfield : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Vfield y)) x)
    (hYfield : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x) :
    (tensor0SCurry (I := I) (M := M) 2 x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          W x (Vfield x))) (Y x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun y : M => curriedSection I M W y (Y y)) x (Vfield x) -
        curriedSection I M W x
          ((LeviCivita (I := I) g).toFun Y x (Vfield x)) := by
  classical
  have hHom := HomConnection.homBundleCovariantDerivativeFun_apply_eq
    (I := I) (M := M) (E_U := E) (U := TangentSpace I) (F := Tensor0SModel 2 ℝ E)
    (V := fun z : M => Tensor0SSpace 2 I z)
    (cov_U := LeviCivita (I := I) g)
    (cov_V := tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g))
    (τ := curriedSection I M W) (x := x) hC
    (V_field := fun y => Vfield y) (Y := fun y => Y y) hVfield hYfield
  have hsucc : tensor0SCurry (I := I) (M := M) 2 x
      ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
        W x (Vfield x)) =
      HomConnection.homBundleCovariantDerivativeFun (I := I) (M := M) (E_U := E) (U := TangentSpace I)
        (F := Tensor0SModel 2 ℝ E)
        (V := fun z : M => Tensor0SSpace 2 I z)
        (cov_U := LeviCivita (I := I) g)
        (cov_V := tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g))
        (τ := curriedSection I M W) x (Vfield x) := by
    rw [show
        (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          W x (Vfield x) =
        (Tensor0SNabla.tensor0SCovariantDerivativeSucc I M (LeviCivita (I := I) g)
          (tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g))).toFun
          W x (Vfield x) from by
      rw [tensor0SCovariantDerivative_succ_eq]]
    rw [tensor0SCovariantDerivative_succ_apply]
    exact (tensor0SCurry (I := I) (M := M) 2 x).apply_symm_apply _
  rw [hsucc]
  exact hHom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.abstract_succ_covDeriv_unfold_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.abstract_succ_covDeriv_unfold_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.abstract_succ_covDeriv_unfold_at ``Submission.DifferentialGeometry.Geometry.Curvature.abstract_succ_covDeriv_unfold_at
end Curvature
end Geometry
end DifferentialGeometry

end
