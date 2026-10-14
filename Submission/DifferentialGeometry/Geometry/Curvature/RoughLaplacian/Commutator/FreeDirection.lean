import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.Naturality
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.TensorThirdOrder
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Sections

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
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

omit [CompactSpace M] in
lemma covGrad_rawConnLap_unit_eval_curry
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    tensor0SCurry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth g 0 2 T₀)).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth g 0 2 T₀) x
            (tangentSpaceModelContinuousLinearEquiv (I := I) x w))
        (unitZeroSec (I := I) (M := M) x) := by
  have := curry_covGrad_unit_eval (I := I) (M := M) g 2
    (rawTensorConnLapSmooth g 0 2 T₀) x w
  exact this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_unit_eval_curry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_unit_eval_curry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_unit_eval_curry ``Submission.DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_unit_eval_curry

omit [CompactSpace M] [I.Boundaryless] in
lemma rawConnLapSection_eq_frame_trace_secondCovDeriv_section
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    (rawTensorConnLapSmooth g 0 2 T₀).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g 0 2
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => T₀.toSection y) x := by
  rw [rawTensorConnLapSmooth_toSection_apply]
  exact rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g 0 2
    (fun y : M => T₀.toSection y) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rawConnLapSection_eq_frame_trace_secondCovDeriv_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rawConnLapSection_eq_frame_trace_secondCovDeriv_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rawConnLapSection_eq_frame_trace_secondCovDeriv_section ``Submission.DifferentialGeometry.Geometry.Curvature.rawConnLapSection_eq_frame_trace_secondCovDeriv_section

omit [CompactSpace M] [I.Boundaryless] in
lemma frame_trace_third_eq_swap_unit
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 2).toFun
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 2)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x))
        (unitZeroSec (I := I) (M := M) x) =
      (∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g 0 2).toFun
            (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
              (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
                (fun y : M => T₀.toSection y))) x
            (smoothExtensionTangent (I := I) x w x))
          (unitZeroSec (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorThirdOrderCurvatureDefect (I := I) g 0 2 (smoothExtensionTangent (I := I) x w)
            (fun y : M => T₀.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) := by
  classical
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothExtensionTangent (I := I) x w)) :=
    smoothExtensionTangent_contMDiff x w
  have hT₀ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) b (T₀.toSection b)) :=
    T₀.toSection.contMDiff
  have hswap := frame_trace_thirdCovDeriv_swap (I := I) g 0 2
    (W := smoothExtensionTangent (I := I) x w) (T := fun y : M => T₀.toSection y) (x := x)
    hW hT₀
  rw [hswap, add_apply, sum_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.frame_trace_third_eq_swap_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.frame_trace_third_eq_swap_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.frame_trace_third_eq_swap_unit ``Submission.DifferentialGeometry.Geometry.Curvature.frame_trace_third_eq_swap_unit

omit [CompactSpace M] in
lemma curry_unitGradAbstractRoughLap_along
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    tensor0SCurry (I := I) (M := M) 2 x
        (unitGradAbstractRoughLap (I := I) (M := M) g T₀ x)
        (smoothExtensionTangent (I := I) x w x) =
      ∑ i : Fin (Module.finrank ℝ E),
        ( ((Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
              (fun z : M =>
                curriedSection I M
                  (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3
                    (LeviCivita (I := I) g)) (smoothOrthoFrame (I := I) g x i)
                    (unitGradField (I := I) (M := M) g T₀)) z
                  (smoothExtensionTangent (I := I) x w z)) x
              (smoothOrthoFrame (I := I) g x i x) -
            curriedSection I M
              (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3
                (LeviCivita (I := I) g)) (smoothOrthoFrame (I := I) g x i)
                (unitGradField (I := I) (M := M) g T₀)) x
              ((LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x w) x
                (smoothOrthoFrame (I := I) g x i x))) -
          ((Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
              (fun z : M =>
                (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
                  tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ z
                    (tangentSpaceModelContinuousLinearEquiv (I := I) z
                      (smoothExtensionTangent (I := I) x w z)))
                  (unitZeroSec (I := I) (M := M) z)) x
              (smoothExtensionTangent (I := I) x
                ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
                  (smoothOrthoFrame (I := I) g x i x)) x) -
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ x
                (tangentSpaceModelContinuousLinearEquiv (I := I) x
                  ((LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x w) x
                    (smoothExtensionTangent (I := I) x
                      ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
                        (smoothOrthoFrame (I := I) g x i x)) x))))
              (unitZeroSec (I := I) (M := M) x))) := by
  classical
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothExtensionTangent (I := I) x w)) :=
    smoothExtensionTangent_contMDiff x w
  rw [unitGradAbstractRoughLap_def]
  rw [show (tensor0SCurry (I := I) (M := M) 2 x
        (∑ i : Fin (Module.finrank ℝ E),
          ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
              (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g))
                (smoothOrthoFrame (I := I) g x i) (unitGradField (I := I) (M := M) g T₀)) x
              (smoothOrthoFrame (I := I) g x i x) -
            (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
              (unitGradField (I := I) (M := M) g T₀) x
              ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x
                (smoothOrthoFrame (I := I) g x i x))))) =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensor0SCurry (I := I) (M := M) 2 x
          ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
              (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g))
                (smoothOrthoFrame (I := I) g x i) (unitGradField (I := I) (M := M) g T₀)) x
              (smoothOrthoFrame (I := I) g x i x) -
            (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
              (unitGradField (I := I) (M := M) g T₀) x
              ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x
                (smoothOrthoFrame (I := I) g x i x)))) from
      map_sum (tensor0SCurry (I := I) (M := M) 2 x) _ _]
  rw [sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hC : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (smoothExtensionTangent (I := I) x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))) :=
    smoothExtensionTangent_contMDiff x _
  rw [map_sub, sub_apply]
  rw [curry_abstract_covDeriv_covApply_unitGrad_unfold (I := I) (M := M) g T₀ hB hB hW]
  have hCx : smoothExtensionTangent (I := I) x
      ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
        (smoothOrthoFrame (I := I) g x i x)) x =
      (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
        (smoothOrthoFrame (I := I) g x i x) :=
    smoothExtensionTangent_eq x _
  rw [show
      (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
        (unitGradField (I := I) (M := M) g T₀) x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
        (unitGradField (I := I) (M := M) g T₀) x
        (smoothExtensionTangent (I := I) x
          ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
            (smoothOrthoFrame (I := I) g x i x)) x) from by rw [hCx]]
  rw [curry_abstract_covDeriv_unitGrad_unfold_of_contMDiff (I := I) (M := M) g T₀ hC hW]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curry_unitGradAbstractRoughLap_along then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curry_unitGradAbstractRoughLap_along"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curry_unitGradAbstractRoughLap_along ``Submission.DifferentialGeometry.Geometry.Curvature.curry_unitGradAbstractRoughLap_along

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covDeriv_unit_eval_eq_two
    (g : SmoothRiemannianMetric I M)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun y : M => TensorRSSpace 0 2 I y)⟯)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)
          (fun y : M => σ y) x v)
        (unitZeroSec (I := I) (M := M) x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from σ y)
            (unitZeroSec (I := I) (M := M) y))
        x v :=
  tensorRSCovariantDerivative_zeroS_unit_eval (I := I) (M := M) g 2 σ x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covDeriv_unit_eval_eq_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covDeriv_unit_eval_eq_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covDeriv_unit_eval_eq_two ``Submission.DifferentialGeometry.Geometry.Curvature.covDeriv_unit_eval_eq_two

end Curvature
end Geometry
end DifferentialGeometry

end
