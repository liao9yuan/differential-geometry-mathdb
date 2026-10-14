import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.Abstract
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Tensor0SRSCovariantDerivativeAgreement

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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] in
lemma zeroTensor_eq_smul_unit (x : M) (D : Tensor0SSpace 0 I x) :
    D = (tensor0Iso (I := I) M x D) • unitZeroSec (I := I) (M := M) x := by
  classical
  have hunit : tensor0Iso (I := I) M x (unitZeroSec (I := I) (M := M) x) = (1 : ℝ) := by
    have h := scalarFn_unitZero (I := I) (M := M)
    have := congrFun h x
    simpa [scalarFn_apply, unitZeroSec_apply] using this
  apply (tensor0Iso (I := I) M x).injective
  rw [map_smul, hunit, smul_eq_mul, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.zeroTensor_eq_smul_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.zeroTensor_eq_smul_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.zeroTensor_eq_smul_unit ``Submission.DifferentialGeometry.Geometry.Curvature.zeroTensor_eq_smul_unit

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] in
lemma tensor03_ext_unit {x : M}
    {φ ψ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x}
    (h : φ (unitZeroSec (I := I) (M := M) x) = ψ (unitZeroSec (I := I) (M := M) x)) :
    φ = ψ := by
  classical
  ext D
  rw [zeroTensor_eq_smul_unit (I := I) (M := M) x D]
  rw [map_smul, map_smul, h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor03_ext_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor03_ext_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor03_ext_unit ``Submission.DifferentialGeometry.Geometry.Curvature.tensor03_ext_unit

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma curry_unitGradField_eq (g : SmoothRiemannianMetric I M)
    (T₀ : SmoothCcTensor g 0 2) (y : M) (w : TangentSpace I y) :
    tensor0SCurry (I := I) (M := M) 2 y (unitGradField (I := I) (M := M) g T₀ y) w =
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
        tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ y
          (tangentSpaceModelContinuousLinearEquiv (I := I) y w))
        (unitZeroSec (I := I) (M := M) y) := by
  rw [unitGradField_apply]
  exact curry_covGrad_unit_eval (I := I) (M := M) g 2 T₀ y w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curry_unitGradField_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curry_unitGradField_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curry_unitGradField_eq ``Submission.DifferentialGeometry.Geometry.Curvature.curry_unitGradField_eq

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma curry_covGrad_unit_eval_two (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (x : M) (w : TangentSpace I x) :
    tensor0SCurry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g 0 2 S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g 0 2 S x
          (tangentSpaceModelContinuousLinearEquiv (I := I) x w))
        (unitZeroSec (I := I) (M := M) x) := by
  exact curry_covGrad_unit_eval (I := I) (M := M) g 2 S x w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curry_covGrad_unit_eval_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curry_covGrad_unit_eval_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curry_covGrad_unit_eval_two ``Submission.DifferentialGeometry.Geometry.Curvature.curry_covGrad_unit_eval_two

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma curry_abstract_covDeriv_unitGrad_unfold
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hC : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel 2 ℝ E))
      (fun y => TotalSpace.mk' (E →L[ℝ] Tensor0SModel 2 ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace 2 I z)) y
        (curriedSection I M (unitGradField (I := I) (M := M) g T₀) y)) x)
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (X y)) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x) :
    (tensor0SCurry (I := I) (M := M) 2 x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          (unitGradField (I := I) (M := M) g T₀) x (X x))) (Y x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
              tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ y
                (tangentSpaceModelContinuousLinearEquiv (I := I) y (Y y)))
              (unitZeroSec (I := I) (M := M) y)) x (X x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ x
            (tangentSpaceModelContinuousLinearEquiv (I := I) x
              ((LeviCivita (I := I) g).toFun Y x (X x))))
          (unitZeroSec (I := I) (M := M) x) := by
  classical
  have hstep := abstract_succ_covDeriv_unfold_at (I := I) (M := M) g
    (unitGradField (I := I) (M := M) g T₀) (Vfield := X) (Y := Y) (x := x) hC hX hY
  rw [hstep]
  have hsec : (fun y : M => curriedSection I M (unitGradField (I := I) (M := M) g T₀) y (Y y)) =
      (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
          tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ y
            (tangentSpaceModelContinuousLinearEquiv (I := I) y (Y y)))
          (unitZeroSec (I := I) (M := M) y)) := by
    funext y
    rw [curriedSection_apply]
    exact curry_unitGradField_eq (I := I) (M := M) g T₀ y (Y y)
  have hchr : curriedSection I M (unitGradField (I := I) (M := M) g T₀) x
        ((LeviCivita (I := I) g).toFun Y x (X x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ x
          (tangentSpaceModelContinuousLinearEquiv (I := I) x
            ((LeviCivita (I := I) g).toFun Y x (X x))))
        (unitZeroSec (I := I) (M := M) x) := by
    rw [curriedSection_apply]
    exact curry_unitGradField_eq (I := I) (M := M) g T₀ x
      ((LeviCivita (I := I) g).toFun Y x (X x))
  rw [hsec, hchr]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curry_abstract_covDeriv_unitGrad_unfold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curry_abstract_covDeriv_unitGrad_unfold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curry_abstract_covDeriv_unitGrad_unfold ``Submission.DifferentialGeometry.Geometry.Curvature.curry_abstract_covDeriv_unitGrad_unfold

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma contMDiff_unitGradField (g : SmoothRiemannianMetric I M)
    (T₀ : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SSpace 3 I z) y
        (unitGradField (I := I) (M := M) g T₀ y)) := by
  classical
  have hϕ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel 3 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel 3 ℝ E)
        (E := fun z : M => (Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 3 I z)) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
          (covGrad (I := I) (M := M) g 0 2 T₀).toSection y))) :=
    covGrad_contMDiff_totalSpaceMk (I := I) (M := M) g T₀
  have hv : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SSpace 0 I z) y
        (unitZeroSec (I := I) (M := M) y)) :=
    contMDiff_unitZeroSection (I := I) (M := M)
  exact ContMDiff.clm_bundle_apply (b := fun y : M => y)
    (E₁ := fun z : M => Tensor0SSpace 0 I z) (E₂ := fun z : M => Tensor0SSpace 3 I z)
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel 3 ℝ E) hϕ hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.contMDiff_unitGradField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.contMDiff_unitGradField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.contMDiff_unitGradField ``Submission.DifferentialGeometry.Geometry.Curvature.contMDiff_unitGradField

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma contMDiff_curried_unitGradField (g : SmoothRiemannianMetric I M)
    (T₀ : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel 2 ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace 2 I z)) y
        (curriedSection I M (unitGradField (I := I) (M := M) g T₀) y)) :=
  (contMDiff_curriedSection_iff_section (I := I) (M := M)
    (unitGradField (I := I) (M := M) g T₀)).mp
    (contMDiff_unitGradField (I := I) (M := M) g T₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.contMDiff_curried_unitGradField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.contMDiff_curried_unitGradField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.contMDiff_curried_unitGradField ``Submission.DifferentialGeometry.Geometry.Curvature.contMDiff_curried_unitGradField

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma curry_abstract_covDeriv_unitGrad_unfold_of_contMDiff
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    (tensor0SCurry (I := I) (M := M) 2 x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          (unitGradField (I := I) (M := M) g T₀) x (X x))) (Y x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
              tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ y
                (tangentSpaceModelContinuousLinearEquiv (I := I) y (Y y)))
              (unitZeroSec (I := I) (M := M) y)) x (X x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ x
            (tangentSpaceModelContinuousLinearEquiv (I := I) x
              ((LeviCivita (I := I) g).toFun Y x (X x))))
          (unitZeroSec (I := I) (M := M) x) := by
  classical
  refine curry_abstract_covDeriv_unitGrad_unfold (I := I) (M := M) g T₀ ?_ ?_ ?_
  · exact (contMDiff_curried_unitGradField (I := I) (M := M) g T₀ x).mdifferentiableAt (by simp)
  · exact (hX x).mdifferentiableAt (by simp)
  · exact (hY x).mdifferentiableAt (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curry_abstract_covDeriv_unitGrad_unfold_of_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curry_abstract_covDeriv_unitGrad_unfold_of_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curry_abstract_covDeriv_unitGrad_unfold_of_contMDiff ``Submission.DifferentialGeometry.Geometry.Curvature.curry_abstract_covDeriv_unitGrad_unfold_of_contMDiff

end Curvature
end Geometry
end DifferentialGeometry

end
