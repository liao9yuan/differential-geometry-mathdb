import Submission.DifferentialGeometry.Geometry.Metric.Euclidean
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Cross
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized
import Submission.DifferentialGeometry.Geometry.Metric.Scaling
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisIdentity
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciNaturalityCross
import Submission.DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import Submission.DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import Submission.DifferentialGeometry.Geometry.Metric.Product.Completeness
import Submission.DifferentialGeometry.Geometry.Operator.Product
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Real.Sqrt

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

noncomputable def gaussianPotential : C^∞⟮𝓘(Real, E), E; Real⟯ :=
  ⟨fun x : E => ‖x‖ ^ 2 / 4,
    ((contDiff_norm_sq Real).div_const 4).contMDiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gaussianPotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gaussianPotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gaussianPotential ``Submission.DifferentialGeometry.Geometry.gaussianPotential

omit [FiniteDimensional Real E] in
@[simp] theorem gaussianPotential_apply (x : E) :
    gaussianPotential x = ‖x‖ ^ 2 / 4 := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gaussianPotential_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gaussianPotential_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gaussianPotential_apply ``Submission.DifferentialGeometry.Geometry.gaussianPotential_apply

private lemma euclideanMetric_chartGramOnE
    (x : E) (i j : Fin (Module.finrank Real E)) :
    chartGramOnE (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x i j =
      fun _ => _root_.Inner.inner Real (chartModelBasis E i) (chartModelBasis E j) := by
  funext y
  simp only [chartGramOnE, chartGramMatrix, Matrix.of_apply,
    chartBasisVecFiber]
  simp only [TangentBundle.symmL_model_space]
  rw [DifferentialGeometry.euclideanMetric_inner]
  change _root_.Inner.inner Real ((1 : E →L[Real] E) (chartModelBasis E i))
      ((1 : E →L[Real] E) (chartModelBasis E j)) = _
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.euclideanMetric_chartGramOnE
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.euclideanMetric_chartGramOnE target :: scope.openDecls } }

private lemma euclideanMetric_chartChristoffel
    (x : E) (i j k : Fin (Module.finrank Real E)) :
    chartChristoffel (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x i j k = 0 := by
  funext y
  rw [chartChristoffel_def]
  simp_rw [euclideanMetric_chartGramOnE]
  simp [partialDeriv]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.euclideanMetric_chartChristoffel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.euclideanMetric_chartChristoffel target :: scope.openDecls } }

private lemma euclideanMetric_chartRiemannTensor
    (x : E) (i j k l : Fin (Module.finrank Real E)) :
    chartRiemannTensor (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x i j k l = 0 := by
  funext y
  rw [chartRiemannTensor_def]
  simp_rw [euclideanMetric_chartChristoffel]
  simp [partialDeriv]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.euclideanMetric_chartRiemannTensor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.euclideanMetric_chartRiemannTensor target :: scope.openDecls } }

theorem euclideanMetric_metricRm04At_eq_zero (x : E) :
    metricRm04At (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  ext v
  have hv : v = vec4 (I := 𝓘(Real, E)) (v 0) (v 1) (v 2) (v 3) := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  change metricRm04StandardAt (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x
    (v 0) (v 1) (v 2) (v 3) = 0
  rw [metricRm04StandardAt_eq_chartRiemannCLM,
    chartRiemannCLM_apply]
  simp only [euclideanMetric_chartRiemannTensor, Pi.zero_apply, _root_.MulZeroClass.mul_zero, zero_smul,
    Finset.sum_const_zero, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.euclideanMetric_metricRm04At_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.euclideanMetric_metricRm04At_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.euclideanMetric_metricRm04At_eq_zero ``Submission.DifferentialGeometry.Geometry.euclideanMetric_metricRm04At_eq_zero

theorem euclideanMetric_ricciTensor
    (x : E) (v w : TangentSpace 𝓘(Real, E) x) :
    ricciTensor (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x v w = 0 := by
  rw [Connection.ricciTensor_eq_chartRicciSwap_of_basis_identity
    (euclideanMetric (E := E)) x
    (Connection.chartRiemannBasisIdentity_holds
      (euclideanMetric (E := E)) x)]
  simp only [chartRicciTensor_def, euclideanMetric_chartRiemannTensor]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.euclideanMetric_ricciTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.euclideanMetric_ricciTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.euclideanMetric_ricciTensor ``Submission.DifferentialGeometry.Geometry.euclideanMetric_ricciTensor

private lemma gaussianPotential_partialDeriv
    (i : Fin (Module.finrank Real E)) (y : E) :
    partialDeriv (E := E) i (fun z : E => ‖z‖ ^ 2 / 4) y =
      (1 / 2 : Real) * _root_.Inner.inner Real y (chartModelBasis E i) := by
  unfold partialDeriv
  have hfun : (fun z : E => ‖z‖ ^ 2 / 4) =
      (1 / 4 : Real) • (fun z : E => ‖z‖ ^ 2) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, congrFun (fderiv_const_smul_field
    (𝕜 := Real) (f := fun z : E => ‖z‖ ^ 2) (1 / 4 : Real)) y]
  simp only [Pi.smul_apply, smul_apply, smul_eq_mul]
  rw [fderiv_norm_sq_apply]
  simp only [smul_apply, innerSL_apply_apply]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.gaussianPotential_partialDeriv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.gaussianPotential_partialDeriv target :: scope.openDecls } }

private lemma gaussianPotential_iteratedPartialDeriv
    (i j : Fin (Module.finrank Real E)) (y : E) :
    partialDeriv (E := E) i
        (partialDeriv (E := E) j (fun z : E => ‖z‖ ^ 2 / 4)) y =
      (1 / 2 : Real) * _root_.Inner.inner Real (chartModelBasis E i) (chartModelBasis E j) := by
  have hfirst : partialDeriv (E := E) j (fun z : E => ‖z‖ ^ 2 / 4) =
      fun z : E => (1 / 2 : Real) * _root_.Inner.inner Real z (chartModelBasis E j) := by
    funext z
    exact gaussianPotential_partialDeriv j z
  rw [hfirst]
  unfold partialDeriv
  have hfun :
      (fun z : E => (1 / 2 : Real) * _root_.Inner.inner Real z (chartModelBasis E j)) =
        (1 / 2 : Real) • (fun z : E => _root_.Inner.inner Real (chartModelBasis E j) z) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [real_inner_comm]
  rw [hfun, congrFun (fderiv_const_smul_field
    (𝕜 := Real) (f := fun z : E => _root_.Inner.inner Real (chartModelBasis E j) z)
      (1 / 2 : Real)) y]
  simp only [Pi.smul_apply, smul_apply]
  change (1 / 2 : Real) *
      fderiv Real (innerSL Real (chartModelBasis E j)) y (chartModelBasis E i) = _
  rw [(innerSL Real (chartModelBasis E j)).fderiv]
  simp only [innerSL_apply_apply]
  rw [real_inner_comm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.gaussianPotential_iteratedPartialDeriv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.gaussianPotential_iteratedPartialDeriv target :: scope.openDecls } }

private lemma gaussianPotential_chartHessianTensor
    (x : E) (i j : Fin (Module.finrank Real E)) :
    chartHessianTensor (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x
        (gaussianPotential (E := E)) i j x =
      (1 / 2 : Real) * _root_.Inner.inner Real (chartModelBasis E i) (chartModelBasis E j) := by
  rw [chartHessianTensor_def, chartIteratedPartialDeriv_def]
  have hscalar : scalarOnE (I := 𝓘(Real, E)) x
      (gaussianPotential (E := E)) = fun z : E => ‖z‖ ^ 2 / 4 := by
    funext z
    simp only [scalarOnE_def, gaussianPotential_apply]
    rw [extChartAt_model_space_eq_id]
    rfl
  rw [hscalar, gaussianPotential_iteratedPartialDeriv]
  simp_rw [euclideanMetric_chartChristoffel]
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.gaussianPotential_chartHessianTensor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.gaussianPotential_chartHessianTensor target :: scope.openDecls } }

private lemma gaussianPotential_hessFun_eq (x : E) :
    hessFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
        (gaussianPotential (E := E)) x =
      (1 / 2 : Real) • metricFlatLinear (I := 𝓘(Real, E))
        (euclideanMetric (E := E)) x := by
  apply Module.Basis.ext (centeredChartTangentBasis (I := 𝓘(Real, E)) x)
  intro i
  apply Module.Basis.ext (centeredChartTangentBasis (I := 𝓘(Real, E)) x)
  intro j
  rw [hessFun_basis_apply, gaussianPotential_chartHessianTensor]
  change (1 / 2 : Real) * _root_.Inner.inner Real (chartModelBasis E i) (chartModelBasis E j) =
    (1 / 2 : Real) * (euclideanMetric (E := E)).inner x
      (centeredChartTangentBasis (I := 𝓘(Real, E)) x i)
      (centeredChartTangentBasis (I := 𝓘(Real, E)) x j)
  rw [DifferentialGeometry.euclideanMetric_inner,
    centeredChartTangentBasis_apply, centeredChartTangentBasis_apply,
    centeredChartTangentEquiv_symm_apply, centeredChartTangentEquiv_symm_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.gaussianPotential_hessFun_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.gaussianPotential_hessFun_eq target :: scope.openDecls } }

theorem gaussianPotential_hessian
    (x : E) (v w : TangentSpace 𝓘(Real, E) x) :
    hessFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
        (gaussianPotential (E := E)) x v w =
      (1 / 2 : Real) * (euclideanMetric (E := E)).inner x v w := by
  have h := LinearMap.congr_fun
    (LinearMap.congr_fun (gaussianPotential_hessFun_eq x) v) w
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gaussianPotential_hessian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gaussianPotential_hessian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gaussianPotential_hessian ``Submission.DifferentialGeometry.Geometry.gaussianPotential_hessian

omit [FiniteDimensional Real E] in
private lemma gaussianPotential_mfderiv
    (x : E) (v : TangentSpace 𝓘(Real, E) x) :
    mfderiv 𝓘(Real, E) 𝓘(Real, Real) (gaussianPotential (E := E)) x v =
      (1 / 2 : Real) * _root_.Inner.inner Real x v := by
  rw [mfderiv_eq_fderiv]
  change fderiv Real (fun z : E => ‖z‖ ^ 2 / 4) x v = _
  have hfun : (fun z : E => ‖z‖ ^ 2 / 4) =
      (1 / 4 : Real) • (fun z : E => ‖z‖ ^ 2) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, congrFun (fderiv_const_smul_field
    (𝕜 := Real) (f := fun z : E => ‖z‖ ^ 2) (1 / 4 : Real)) x]
  have hfd : ((1 / 4 : Real) • fderiv Real (fun z : E => ‖z‖ ^ 2)) x =
      (1 / 2 : Real) • innerSL Real x := by
    ext u
    simp only [Pi.smul_apply, smul_apply]
    rw [fderiv_norm_sq_apply]
    simp only [smul_apply, innerSL_apply_apply]
    ring
  rw [hfd]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.gaussianPotential_mfderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.gaussianPotential_mfderiv target :: scope.openDecls } }

theorem gaussianPotential_gradFun (x : E) :
    (gradFun (euclideanMetric (E := E)) gaussianPotential x : E) =
      (1 / 2 : Real) • x := by
  change @Eq E _ ((1 / 2 : Real) • x)
  apply ext_inner_right Real (E := E)
  intro v
  have heuc := euclideanMetric_inner x
    (gradFun (euclideanMetric (E := E)) gaussianPotential x) v
  have hinner := inner_gradFun (euclideanMetric (E := E)) gaussianPotential x v
  have hderiv := gaussianPotential_mfderiv x v
  have hsmul : (1 / 2 : Real) * _root_.Inner.inner Real x v =
      inner Real ((1 / 2 : Real) • x) v := by
    rw [real_inner_smul_left]
  exact heuc.symm.trans (hinner.trans (hderiv.trans hsmul))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gaussianPotential_gradFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gaussianPotential_gradFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gaussianPotential_gradFun ``Submission.DifferentialGeometry.Geometry.gaussianPotential_gradFun

theorem gaussianPotential_normGradSqFun (x : E) :
    normGradSqFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
        (gaussianPotential (E := E)) x = gaussianPotential x := by
  rw [normGradSqFun_def, inner_gradFun, gaussianPotential_mfderiv]
  have hx := inner_gradFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
    (gaussianPotential (E := E)) x x
  have hdx : mfderiv 𝓘(Real, E) 𝓘(Real, Real) (gaussianPotential (E := E)) x
      (x : TangentSpace 𝓘(Real, E) x) = (1 / 2 : Real) * _root_.Inner.inner Real x x :=
    gaussianPotential_mfderiv x x
  rw [hdx] at hx
  change (1 / 2 : Real) * _root_.Inner.inner Real x
      (gradFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
        (gaussianPotential (E := E)) x) = gaussianPotential x
  have heuc : (euclideanMetric (E := E)).inner x
      (x : TangentSpace 𝓘(Real, E) x)
      (gradFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
        (gaussianPotential (E := E)) x) =
    inner Real x (gradFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
      (gaussianPotential (E := E)) x) :=
    DifferentialGeometry.euclideanMetric_inner x x _
  have hsymm : (euclideanMetric (E := E)).inner x
      (x : TangentSpace 𝓘(Real, E) x)
      (gradFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
        (gaussianPotential (E := E)) x) =
    (euclideanMetric (E := E)).inner x
      (gradFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
        (gaussianPotential (E := E)) x)
      (x : TangentSpace 𝓘(Real, E) x) :=
    (euclideanMetric (E := E)).symm x x _
  calc
    (1 / 2 : Real) * _root_.Inner.inner Real x
        (gradFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
          (gaussianPotential (E := E)) x) =
      (1 / 2 : Real) * (euclideanMetric (E := E)).inner x x
        (gradFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
          (gaussianPotential (E := E)) x) := by
        rw [heuc]
    _ = (1 / 2 : Real) * (euclideanMetric (E := E)).inner x
        (gradFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
          (gaussianPotential (E := E)) x) x := by
        rw [hsymm]
    _ = (1 / 2 : Real) * ((1 / 2 : Real) * _root_.Inner.inner Real x x) := by
        rw [hx]
    _ = gaussianPotential x := by
        rw [gaussianPotential_apply, real_inner_self_eq_norm_sq]
        ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gaussianPotential_normGradSqFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gaussianPotential_normGradSqFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gaussianPotential_normGradSqFun ``Submission.DifferentialGeometry.Geometry.gaussianPotential_normGradSqFun

theorem euclideanMetric_scalarCurvature (x : E) :
    metricScalarAt (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x = 0 := by
  have hRicci : metricRicciAt (I := 𝓘(Real, E))
      (euclideanMetric (E := E)) x = 0 := by
    apply Tensor0SBundle.ext0S_basis
      (centeredChartTangentBasis (I := 𝓘(Real, E)) x)
    intro slots
    simp only [Tensor0SBundle.component0S_apply]
    change metricRicciAt (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x
      (fun a : Fin 2 => centeredChartTangentBasis (I := 𝓘(Real, E)) x (slots a)) = 0
    have hslots :
        (fun a : Fin 2 => centeredChartTangentBasis (I := 𝓘(Real, E)) x (slots a)) =
          vec2 (I := 𝓘(Real, E))
            (centeredChartTangentBasis (I := 𝓘(Real, E)) x (slots 0))
            (centeredChartTangentBasis (I := 𝓘(Real, E)) x (slots 1)) := by
      funext a
      fin_cases a <;> rfl
    rw [hslots]
    rw [metricRicciAt_apply_eq_ricciTensor]
    exact euclideanMetric_ricciTensor x _ _
  rw [metricScalarAt_def, hRicci]
  change Tensor0SBundle.inner0S (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x 2
    (metricTensor0S (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x) 0 = 0
  rw [show (0 : Tensor0SBundle.Tensor0SSpace 2 𝓘(Real, E) x) =
      (0 : Real) • metricTensor0S (I := 𝓘(Real, E))
        (euclideanMetric (E := E)) x by simp,
    Tensor0SBundle.inner0S_smul_right]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.euclideanMetric_scalarCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.euclideanMetric_scalarCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.euclideanMetric_scalarCurvature ``Submission.DifferentialGeometry.Geometry.euclideanMetric_scalarCurvature

theorem gradientRicciSoliton_gaussian :
    gradientRicciSoliton (I := 𝓘(Real, E))
      (euclideanMetric (E := E)) (gaussianPotential (E := E)) 1 := by
  intro x v w
  rw [euclideanMetric_ricciTensor, gaussianPotential_hessian]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_gaussian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_gaussian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_gaussian ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_gaussian

theorem normalizedGradientRicciSoliton_gaussian :
    normalizedGradientRicciSoliton (I := 𝓘(Real, E))
      (euclideanMetric (E := E)) (gaussianPotential (E := E)) := by
  refine ⟨euclideanMetric_complete (E := E),
    gradientRicciSoliton_gaussian (E := E), ?_⟩
  intro x
  rw [euclideanMetric_scalarCurvature, gaussianPotential_normGradSqFun]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_gaussian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_gaussian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_gaussian ``Submission.DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_gaussian

theorem gaussian_hamiltonNormalized :
    hamiltonNormalized (I := 𝓘(Real, E))
      (euclideanMetric (E := E)) (gaussianPotential (E := E)) 1 :=
  normalizedGradientRicciSoliton_hamilton_normalized
    (normalizedGradientRicciSoliton_gaussian (E := E))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gaussian_hamiltonNormalized then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gaussian_hamiltonNormalized"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gaussian_hamiltonNormalized ``Submission.DifferentialGeometry.Geometry.gaussian_hamiltonNormalized

noncomputable def roundSphereShrinkerRadius (n : Nat) : Real :=
  Real.sqrt (2 * ((n : Real) - 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundSphereShrinkerRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundSphereShrinkerRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundSphereShrinkerRadius ``Submission.DifferentialGeometry.Geometry.roundSphereShrinkerRadius

theorem roundSphereShrinkerRadius_pos {n : Nat} (hn : 2 ≤ n) :
    0 < roundSphereShrinkerRadius n := by
  rw [roundSphereShrinkerRadius, Real.sqrt_pos]
  have h : (1 : Real) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundSphereShrinkerRadius_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundSphereShrinkerRadius_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundSphereShrinkerRadius_pos ``Submission.DifferentialGeometry.Geometry.roundSphereShrinkerRadius_pos

theorem roundSphereShrinkerRadius_sq {n : Nat} (hn : 2 ≤ n) :
    roundSphereShrinkerRadius n ^ 2 = 2 * ((n : Real) - 1) := by
  rw [roundSphereShrinkerRadius, Real.sq_sqrt]
  exact le_of_lt (by
    have h : (1 : Real) < n := by
      exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
    positivity)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundSphereShrinkerRadius_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundSphereShrinkerRadius_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundSphereShrinkerRadius_sq ``Submission.DifferentialGeometry.Geometry.roundSphereShrinkerRadius_sq

@[simp] theorem roundSphereShrinkerRadius_two :
    roundSphereShrinkerRadius 2 = Real.sqrt 2 := by
  norm_num [roundSphereShrinkerRadius]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundSphereShrinkerRadius_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundSphereShrinkerRadius_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundSphereShrinkerRadius_two ``Submission.DifferentialGeometry.Geometry.roundSphereShrinkerRadius_two

@[simp] theorem roundSphereShrinkerRadius_three :
    roundSphereShrinkerRadius 3 = 2 := by
  norm_num [roundSphereShrinkerRadius]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundSphereShrinkerRadius_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundSphereShrinkerRadius_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundSphereShrinkerRadius_three ``Submission.DifferentialGeometry.Geometry.roundSphereShrinkerRadius_three

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace Real A]
  [FiniteDimensional Real A]
variable {n : Nat} [Fact (Module.finrank Real A = n + 1)]

noncomputable def roundSphereShrinkerMetric (hn : 2 ≤ n) :
    SmoothRiemannianMetric (𝓡 n) (Metric.sphere (0 : A) 1) :=
  scaleMetric (roundSphereShrinkerRadius n ^ 2)
    (sq_pos_of_pos (roundSphereShrinkerRadius_pos hn))
    (roundMetric (E := A) (n := n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundSphereShrinkerMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundSphereShrinkerMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundSphereShrinkerMetric ``Submission.DifferentialGeometry.Geometry.roundSphereShrinkerMetric

noncomputable def roundSphereShrinkerPotential :
    C^∞⟮𝓡 n, Metric.sphere (0 : A) 1; Real⟯ :=
  ContMDiffMap.const ((n : Real) / 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundSphereShrinkerPotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundSphereShrinkerPotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundSphereShrinkerPotential ``Submission.DifferentialGeometry.Geometry.roundSphereShrinkerPotential

omit [FiniteDimensional Real A] in
@[simp] theorem roundSphereShrinkerPotential_apply
    (x : Metric.sphere (0 : A) 1) :
    roundSphereShrinkerPotential (A := A) (n := n) x = (n : Real) / 2 := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundSphereShrinkerPotential_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundSphereShrinkerPotential_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundSphereShrinkerPotential_apply ``Submission.DifferentialGeometry.Geometry.roundSphereShrinkerPotential_apply

omit [FiniteDimensional Real A] in
theorem roundSphereShrinkerMetric_ricciTensor
    (hn : 2 ≤ n) (x : Metric.sphere (0 : A) 1)
    (v w : TangentSpace (𝓡 n) x) :
    ricciTensor (I := 𝓡 n) (roundSphereShrinkerMetric (A := A) hn) x v w =
      (1 / 2 : Real) *
        (roundSphereShrinkerMetric (A := A) hn).inner x v w := by
  let : NeZero n :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (Nat.zero_lt_succ 1) hn)⟩
  rw [roundSphereShrinkerMetric, Curvature.ricciTensor_scaleMetric,
    roundMetric_ricciTensor, scaleMetric_inner,
    roundSphereShrinkerRadius_sq hn]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundSphereShrinkerMetric_ricciTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundSphereShrinkerMetric_ricciTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundSphereShrinkerMetric_ricciTensor ``Submission.DifferentialGeometry.Geometry.roundSphereShrinkerMetric_ricciTensor

omit [FiniteDimensional Real A] in
theorem roundSphereShrinkerPotential_hessian
    (hn : 2 ≤ n) (x : Metric.sphere (0 : A) 1)
    (v w : TangentSpace (𝓡 n) x) :
    hessFun (I := 𝓡 n) (roundSphereShrinkerMetric (A := A) hn)
        (roundSphereShrinkerPotential (A := A) (n := n)) x v w = 0 := by
  change hessFun (I := 𝓡 n) (roundSphereShrinkerMetric (A := A) hn)
      (fun _ : Metric.sphere (0 : A) 1 => (n : Real) / 2) x v w = 0
  rw [Connection.hessFun_eq_abstract
    (roundSphereShrinkerMetric (A := A) hn) contMDiff_const x v w]
  rw [Connection.abstractHessian_apply]
  have hderiv : mvfderiv (I := 𝓡 n)
      (fun _ : Metric.sphere (0 : A) 1 => (n : Real) / 2) =
        fun _ => 0 := by
    funext y
    exact mvfderiv_const (I := 𝓡 n)
      (M := Metric.sphere (0 : A) 1) ((n : Real) / 2) (x := y)
  rw [hderiv]
  let cov := Connection.cotangentCov
    (Connection.LeviCivita (I := 𝓡 n)
      (roundSphereShrinkerMetric (A := A) hn))
  change ((cov.toFun
    (fun y : Metric.sphere (0 : A) 1 =>
      (0 : TangentSpace (𝓡 n) y →L[Real] Real)) x v) w) = 0
  have hzero : cov.toFun
      (fun y : Metric.sphere (0 : A) 1 =>
        (0 : TangentSpace (𝓡 n) y →L[Real] Real)) x = 0 := by
    exact congrArg (fun φ => φ x) cov.zero
  rw [hzero]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundSphereShrinkerPotential_hessian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundSphereShrinkerPotential_hessian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundSphereShrinkerPotential_hessian ``Submission.DifferentialGeometry.Geometry.roundSphereShrinkerPotential_hessian

omit [FiniteDimensional Real A] in
theorem gradientRicciSoliton_roundSphere (hn : 2 ≤ n) :
    gradientRicciSoliton (I := 𝓡 n)
      (roundSphereShrinkerMetric (A := A) hn)
      (roundSphereShrinkerPotential (A := A) (n := n)) 1 := by
  intro x v w
  rw [roundSphereShrinkerMetric_ricciTensor hn,
    roundSphereShrinkerPotential_hessian hn]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_roundSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_roundSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_roundSphere ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_roundSphere

theorem roundSphereShrinkerMetric_complete (hn : 2 ≤ n) :
    RiemannianMetricComplete (I := 𝓡 n)
      (roundSphereShrinkerMetric (A := A) hn) := by
  let : CompactSpace (Metric.sphere (0 : A) 1) :=
    Metric.sphere.compactSpace 0 1
  have hround : RiemannianMetricComplete (I := 𝓡 n)
      (roundMetric (E := A) (n := n)) := by
    refine ⟨?_⟩
    infer_instance
  exact RiemannianMetricComplete.scaleMetric
    hround
    (roundSphereShrinkerRadius n ^ 2)
    (sq_pos_of_pos (roundSphereShrinkerRadius_pos hn))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundSphereShrinkerMetric_complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundSphereShrinkerMetric_complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundSphereShrinkerMetric_complete ``Submission.DifferentialGeometry.Geometry.roundSphereShrinkerMetric_complete

omit [FiniteDimensional Real A] in
theorem roundSphereShrinkerMetric_scalarCurvature
    (hn : 2 ≤ n) (x : Metric.sphere (0 : A) 1) :
    metricScalarAt (I := 𝓡 n) (roundSphereShrinkerMetric (A := A) hn) x =
      (n : Real) / 2 := by
  have h := gradientRicciSoliton_trace
    (gradientRicciSoliton_roundSphere (A := A) hn) x
  rw [show roundSphereShrinkerPotential (A := A) (n := n) =
      ContMDiffMap.const ((n : Real) / 2) by rfl,
    Operator.Δ_g_const] at h
  simpa [finrank_euclideanSpace_fin] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundSphereShrinkerMetric_scalarCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundSphereShrinkerMetric_scalarCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundSphereShrinkerMetric_scalarCurvature ``Submission.DifferentialGeometry.Geometry.roundSphereShrinkerMetric_scalarCurvature

omit [FiniteDimensional Real A] in
theorem roundSphereShrinkerPotential_normGradSqFun
    (hn : 2 ≤ n) (x : Metric.sphere (0 : A) 1) :
    normGradSqFun (I := 𝓡 n) (roundSphereShrinkerMetric (A := A) hn)
        (roundSphereShrinkerPotential (A := A) (n := n)) x = 0 := by
  change normGradSqFun (I := 𝓡 n) (roundSphereShrinkerMetric (A := A) hn)
      (fun _ : Metric.sphere (0 : A) 1 => (n : Real) / 2) x = 0
  rw [normGradSqFun_def, Operator.gradFun_const]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundSphereShrinkerPotential_normGradSqFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundSphereShrinkerPotential_normGradSqFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundSphereShrinkerPotential_normGradSqFun ``Submission.DifferentialGeometry.Geometry.roundSphereShrinkerPotential_normGradSqFun

theorem normalizedGradientRicciSoliton_roundSphere (hn : 2 ≤ n) :
    normalizedGradientRicciSoliton (I := 𝓡 n)
      (roundSphereShrinkerMetric (A := A) hn)
      (roundSphereShrinkerPotential (A := A) (n := n)) := by
  refine ⟨roundSphereShrinkerMetric_complete (A := A) hn,
    gradientRicciSoliton_roundSphere (A := A) hn, ?_⟩
  intro x
  rw [roundSphereShrinkerMetric_scalarCurvature hn,
    roundSphereShrinkerPotential_normGradSqFun hn,
    roundSphereShrinkerPotential_apply]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_roundSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_roundSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_roundSphere ``Submission.DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_roundSphere

theorem roundSphere_hamiltonNormalized (hn : 2 ≤ n) :
    hamiltonNormalized (I := 𝓡 n)
      (roundSphereShrinkerMetric (A := A) hn)
      (roundSphereShrinkerPotential (A := A) (n := n)) 1 :=
  normalizedGradientRicciSoliton_hamilton_normalized
    (normalizedGradientRicciSoliton_roundSphere (A := A) hn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundSphere_hamiltonNormalized then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundSphere_hamiltonNormalized"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundSphere_hamiltonNormalized ``Submission.DifferentialGeometry.Geometry.roundSphere_hamiltonNormalized

noncomputable def roundTwoSphereShrinkerMetric :
    SmoothRiemannianMetric (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  exact roundSphereShrinkerMetric
    (A := EuclideanSpace Real (Fin 3)) (n := 2) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundTwoSphereShrinkerMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundTwoSphereShrinkerMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundTwoSphereShrinkerMetric ``Submission.DifferentialGeometry.Geometry.roundTwoSphereShrinkerMetric

noncomputable def roundTwoSphereShrinkerPotential :
    C^∞⟮𝓡 2, Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1; Real⟯ :=
  ContMDiffMap.const 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundTwoSphereShrinkerPotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundTwoSphereShrinkerPotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundTwoSphereShrinkerPotential ``Submission.DifferentialGeometry.Geometry.roundTwoSphereShrinkerPotential

@[simp] theorem roundTwoSphereShrinkerPotential_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    roundTwoSphereShrinkerPotential x = 1 := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundTwoSphereShrinkerPotential_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundTwoSphereShrinkerPotential_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundTwoSphereShrinkerPotential_apply ``Submission.DifferentialGeometry.Geometry.roundTwoSphereShrinkerPotential_apply

theorem normalizedGradientRicciSoliton_roundTwoSphere :
    normalizedGradientRicciSoliton (I := 𝓡 2)
      roundTwoSphereShrinkerMetric roundTwoSphereShrinkerPotential := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  simpa [roundTwoSphereShrinkerMetric, roundTwoSphereShrinkerPotential,
    roundSphereShrinkerPotential] using
    (normalizedGradientRicciSoliton_roundSphere
      (A := EuclideanSpace Real (Fin 3)) (n := 2) (by decide))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_roundTwoSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_roundTwoSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_roundTwoSphere ``Submission.DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_roundTwoSphere

theorem roundTwoSphereShrinkerMetric_scalarCurvature
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    metricScalarAt (I := 𝓡 2) roundTwoSphereShrinkerMetric x = 1 := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  simpa [roundTwoSphereShrinkerMetric] using
    (roundSphereShrinkerMetric_scalarCurvature
      (A := EuclideanSpace Real (Fin 3)) (n := 2) (by decide) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundTwoSphereShrinkerMetric_scalarCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundTwoSphereShrinkerMetric_scalarCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundTwoSphereShrinkerMetric_scalarCurvature ``Submission.DifferentialGeometry.Geometry.roundTwoSphereShrinkerMetric_scalarCurvature

theorem roundTwoSphere_hamiltonNormalized :
    hamiltonNormalized (I := 𝓡 2)
      roundTwoSphereShrinkerMetric roundTwoSphereShrinkerPotential 1 :=
  normalizedGradientRicciSoliton_hamilton_normalized
    normalizedGradientRicciSoliton_roundTwoSphere

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundTwoSphere_hamiltonNormalized then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundTwoSphere_hamiltonNormalized"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundTwoSphere_hamiltonNormalized ``Submission.DifferentialGeometry.Geometry.roundTwoSphere_hamiltonNormalized

noncomputable def roundThreeSphereShrinkerMetric :
    SmoothRiemannianMetric (𝓡 3)
      (Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 4)) = 3 + 1) :=
    ⟨by simp⟩
  exact roundSphereShrinkerMetric
    (A := EuclideanSpace Real (Fin 4)) (n := 3) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeSphereShrinkerMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeSphereShrinkerMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeSphereShrinkerMetric ``Submission.DifferentialGeometry.Geometry.roundThreeSphereShrinkerMetric

noncomputable def roundThreeSphereShrinkerPotential :
    C^∞⟮𝓡 3, Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1; Real⟯ :=
  ContMDiffMap.const (3 / 2 : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeSphereShrinkerPotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeSphereShrinkerPotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeSphereShrinkerPotential ``Submission.DifferentialGeometry.Geometry.roundThreeSphereShrinkerPotential

@[simp] theorem roundThreeSphereShrinkerPotential_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) :
    roundThreeSphereShrinkerPotential x = (3 / 2 : Real) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeSphereShrinkerPotential_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeSphereShrinkerPotential_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeSphereShrinkerPotential_apply ``Submission.DifferentialGeometry.Geometry.roundThreeSphereShrinkerPotential_apply

theorem normalizedGradientRicciSoliton_roundThreeSphere :
    normalizedGradientRicciSoliton (I := 𝓡 3)
      roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 4)) = 3 + 1) :=
    ⟨by simp⟩
  simpa [roundThreeSphereShrinkerMetric, roundThreeSphereShrinkerPotential,
    roundSphereShrinkerPotential] using
    (normalizedGradientRicciSoliton_roundSphere
      (A := EuclideanSpace Real (Fin 4)) (n := 3) (by decide))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_roundThreeSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_roundThreeSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_roundThreeSphere ``Submission.DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_roundThreeSphere

theorem roundThreeSphereShrinkerMetric_scalarCurvature
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) :
    metricScalarAt (I := 𝓡 3) roundThreeSphereShrinkerMetric x =
      (3 / 2 : Real) := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 4)) = 3 + 1) :=
    ⟨by simp⟩
  simpa [roundThreeSphereShrinkerMetric] using
    (roundSphereShrinkerMetric_scalarCurvature
      (A := EuclideanSpace Real (Fin 4)) (n := 3) (by decide) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeSphereShrinkerMetric_scalarCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeSphereShrinkerMetric_scalarCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeSphereShrinkerMetric_scalarCurvature ``Submission.DifferentialGeometry.Geometry.roundThreeSphereShrinkerMetric_scalarCurvature

theorem roundThreeSphere_hamiltonNormalized :
    hamiltonNormalized (I := 𝓡 3)
      roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential 1 :=
  normalizedGradientRicciSoliton_hamilton_normalized
    normalizedGradientRicciSoliton_roundThreeSphere

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeSphere_hamiltonNormalized then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeSphere_hamiltonNormalized"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeSphere_hamiltonNormalized ``Submission.DifferentialGeometry.Geometry.roundThreeSphere_hamiltonNormalized

noncomputable def roundThreeCylinderShrinkerMetric :
    SmoothRiemannianMetric ((𝓡 2).prod 𝓘(Real, Real))
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :=
  roundTwoSphereShrinkerMetric.prod (euclideanMetric (E := Real))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeCylinderShrinkerMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerMetric ``Submission.DifferentialGeometry.Geometry.roundThreeCylinderShrinkerMetric

noncomputable def roundThreeCylinderShrinkerPotential :
    C^∞⟮(𝓡 2).prod 𝓘(Real, Real),
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real; Real⟯ :=
  roundTwoSphereShrinkerPotential.comp ContMDiffMap.fst +
    gaussianPotential.comp ContMDiffMap.snd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential ``Submission.DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential

@[simp] theorem roundThreeCylinderShrinkerPotential_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    roundThreeCylinderShrinkerPotential x = 1 + x.2 ^ 2 / 4 := by
  change roundTwoSphereShrinkerPotential x.1 + gaussianPotential x.2 = _
  rw [roundTwoSphereShrinkerPotential_apply, gaussianPotential_apply]
  simp [Real.norm_eq_abs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_apply ``Submission.DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_apply

def roundThreeCylinderCentralSlice :
    Set (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :=
  {x | x.2 = 0}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeCylinderCentralSlice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeCylinderCentralSlice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeCylinderCentralSlice ``Submission.DifferentialGeometry.Geometry.roundThreeCylinderCentralSlice

@[simp] theorem mem_roundThreeCylinderCentralSlice
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    x ∈ roundThreeCylinderCentralSlice ↔ x.2 = 0 :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.mem_roundThreeCylinderCentralSlice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.mem_roundThreeCylinderCentralSlice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.mem_roundThreeCylinderCentralSlice ``Submission.DifferentialGeometry.Geometry.mem_roundThreeCylinderCentralSlice

theorem roundThreeCylinderCentralSlice_eq_range :
    roundThreeCylinderCentralSlice =
      Set.range (fun y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        (y, (0 : Real))) := by
  ext x
  constructor
  · intro hx
    exact ⟨x.1, Prod.ext rfl hx.symm⟩
  · rintro ⟨y, rfl⟩
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeCylinderCentralSlice_eq_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeCylinderCentralSlice_eq_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeCylinderCentralSlice_eq_range ``Submission.DifferentialGeometry.Geometry.roundThreeCylinderCentralSlice_eq_range

theorem isCompact_roundThreeCylinderCentralSlice :
    IsCompact roundThreeCylinderCentralSlice := by
  rw [roundThreeCylinderCentralSlice_eq_range]
  exact isCompact_range (continuous_id.prodMk continuous_const)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isCompact_roundThreeCylinderCentralSlice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isCompact_roundThreeCylinderCentralSlice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isCompact_roundThreeCylinderCentralSlice ``Submission.DifferentialGeometry.Geometry.isCompact_roundThreeCylinderCentralSlice

theorem roundThreeCylinderShrinkerPotential_eq_one_iff
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    roundThreeCylinderShrinkerPotential x = 1 ↔
      x ∈ roundThreeCylinderCentralSlice := by
  rw [roundThreeCylinderShrinkerPotential_apply,
    mem_roundThreeCylinderCentralSlice]
  constructor
  · intro h
    nlinarith [sq_nonneg x.2]
  · intro h
    rw [h]
    norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_eq_one_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_eq_one_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_eq_one_iff ``Submission.DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_eq_one_iff

theorem roundThreeCylinderCentralSlice_preimage_eq_of_potential_preserving
    (γ : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real →
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (hγ : ∀ x, roundThreeCylinderShrinkerPotential (γ x) =
      roundThreeCylinderShrinkerPotential x) :
    γ ⁻¹' roundThreeCylinderCentralSlice =
      roundThreeCylinderCentralSlice := by
  ext x
  calc
    x ∈ γ ⁻¹' roundThreeCylinderCentralSlice ↔
        roundThreeCylinderShrinkerPotential (γ x) = 1 :=
      roundThreeCylinderShrinkerPotential_eq_one_iff (γ x) |>.symm
    _ ↔ roundThreeCylinderShrinkerPotential x = 1 := by rw [hγ x]
    _ ↔ x ∈ roundThreeCylinderCentralSlice :=
      roundThreeCylinderShrinkerPotential_eq_one_iff x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeCylinderCentralSlice_preimage_eq_of_potential_preserving then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeCylinderCentralSlice_preimage_eq_of_potential_preserving"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeCylinderCentralSlice_preimage_eq_of_potential_preserving ``Submission.DifferentialGeometry.Geometry.roundThreeCylinderCentralSlice_preimage_eq_of_potential_preserving

theorem gradientRicciSoliton_roundThreeCylinder :
    gradientRicciSoliton (I := (𝓡 2).prod 𝓘(Real, Real))
      roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential 1 := by
  simpa [roundThreeCylinderShrinkerMetric,
    roundThreeCylinderShrinkerPotential] using
    gradientRicciSoliton_prod
      normalizedGradientRicciSoliton_roundTwoSphere.2.1
      (gradientRicciSoliton_gaussian (E := Real))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_roundThreeCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_roundThreeCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_roundThreeCylinder ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_roundThreeCylinder

theorem roundThreeCylinderShrinkerMetric_complete :
    RiemannianMetricComplete (I := (𝓡 2).prod 𝓘(Real, Real))
      roundThreeCylinderShrinkerMetric := by
  simpa [roundThreeCylinderShrinkerMetric] using
    RiemannianMetricComplete.prod
      normalizedGradientRicciSoliton_roundTwoSphere.1
      (normalizedGradientRicciSoliton_gaussian (E := Real)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerMetric_complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeCylinderShrinkerMetric_complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerMetric_complete ``Submission.DifferentialGeometry.Geometry.roundThreeCylinderShrinkerMetric_complete

theorem roundThreeCylinderShrinkerMetric_scalarCurvature
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    metricScalarAt (I := (𝓡 2).prod 𝓘(Real, Real))
      roundThreeCylinderShrinkerMetric x = 1 := by
  rw [roundThreeCylinderShrinkerMetric, Curvature.metricScalarAt_productMetric,
    roundTwoSphereShrinkerMetric_scalarCurvature,
    euclideanMetric_scalarCurvature]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerMetric_scalarCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeCylinderShrinkerMetric_scalarCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerMetric_scalarCurvature ``Submission.DifferentialGeometry.Geometry.roundThreeCylinderShrinkerMetric_scalarCurvature

theorem roundThreeCylinderShrinkerPotential_normGradSqFun
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    normGradSqFun (I := (𝓡 2).prod 𝓘(Real, Real))
        roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential x =
      x.2 ^ 2 / 4 := by
  have hsphere := normalizedGradientRicciSoliton_roundTwoSphere.2.2 x.1
  rw [roundTwoSphereShrinkerMetric_scalarCurvature,
    roundTwoSphereShrinkerPotential_apply] at hsphere
  have hnorm : normGradSqFun (I := 𝓡 2) roundTwoSphereShrinkerMetric
      roundTwoSphereShrinkerPotential x.1 = 0 := by
    linarith [hsphere]
  change normGradSqFun (I := (𝓡 2).prod 𝓘(Real, Real))
      (roundTwoSphereShrinkerMetric.prod (euclideanMetric (E := Real)))
      (fun q : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real =>
        roundTwoSphereShrinkerPotential q.1 + gaussianPotential q.2) x = _
  rw [Operator.normGradSqFun_prod, hnorm,
    gaussianPotential_normGradSqFun, gaussianPotential_apply]
  simp [Real.norm_eq_abs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_normGradSqFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_normGradSqFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_normGradSqFun ``Submission.DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_normGradSqFun

theorem normalizedGradientRicciSoliton_roundThreeCylinder :
    normalizedGradientRicciSoliton
      (I := (𝓡 2).prod 𝓘(Real, Real))
      roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential := by
  simpa [roundThreeCylinderShrinkerMetric,
    roundThreeCylinderShrinkerPotential] using
    normalizedGradientRicciSoliton_prod
      normalizedGradientRicciSoliton_roundTwoSphere
      (normalizedGradientRicciSoliton_gaussian (E := Real))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_roundThreeCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_roundThreeCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_roundThreeCylinder ``Submission.DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_roundThreeCylinder

theorem roundThreeCylinder_hamiltonNormalized :
    hamiltonNormalized (I := (𝓡 2).prod 𝓘(Real, Real))
      roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential 1 :=
  normalizedGradientRicciSoliton_hamilton_normalized
    normalizedGradientRicciSoliton_roundThreeCylinder

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeCylinder_hamiltonNormalized then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeCylinder_hamiltonNormalized"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeCylinder_hamiltonNormalized ``Submission.DifferentialGeometry.Geometry.roundThreeCylinder_hamiltonNormalized

def isGaussianGradientRicciSoliton
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (σ : Real) : Prop :=
  ∃ hσ : 0 < σ, ∃ Ψ : M ≃ₘ⟮I, 𝓘(Real, E)⟯ E, ∃ b : Real,
    Diffeomorph.pullbackMetricCross euclideanMetric Ψ =
        scaleMetric (I := I) σ hσ g ∧
      f + ContMDiffMap.const b = gaussianPotential.comp Ψ.toContMDiffMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton ``Submission.DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton

theorem isGaussianGradientRicciSoliton_add_const
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (c : Real) :
    isGaussianGradientRicciSoliton (I := I) g
      (f + ContMDiffMap.const c) σ ↔
      isGaussianGradientRicciSoliton (I := I) g f σ := by
  constructor
  · rintro ⟨hσ, Ψ, b, hmetric, hpotential⟩
    refine ⟨hσ, Ψ, b + c, hmetric, ?_⟩
    apply ContMDiffMap.ext
    intro x
    have hx := congrArg (fun q : C^∞⟮I, M; Real⟯ => q x) hpotential
    change f x + (b + c) = gaussianPotential (Ψ x)
    change (f x + c) + b = gaussianPotential (Ψ x) at hx
    rw [show f x + (b + c) = (f x + c) + b by ring]
    exact hx
  · rintro ⟨hσ, Ψ, b, hmetric, hpotential⟩
    refine ⟨hσ, Ψ, b - c, hmetric, ?_⟩
    apply ContMDiffMap.ext
    intro x
    have hx := congrArg (fun q : C^∞⟮I, M; Real⟯ => q x) hpotential
    change (f x + c) + (b - c) = gaussianPotential (Ψ x)
    change f x + b = gaussianPotential (Ψ x) at hx
    rw [show (f x + c) + (b - c) = f x + b by ring]
    exact hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_add_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_add_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_add_const ``Submission.DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_add_const

theorem isGaussianGradientRicciSoliton_scaleMetric
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (hσ : 0 < σ) :
    isGaussianGradientRicciSoliton (E := E)
        (scaleMetric (I := I) σ hσ g) f 1 ↔
      isGaussianGradientRicciSoliton (E := E) g f σ := by
  constructor
  · rintro ⟨hone, Ψ, b, hmetric, hpotential⟩
    refine ⟨hσ, Ψ, b, ?_, hpotential⟩
    calc
      Diffeomorph.pullbackMetricCross euclideanMetric Ψ =
          scaleMetric (I := I) 1 hone
            (scaleMetric (I := I) σ hσ g) := hmetric
      _ = scaleMetric (I := I) σ hσ g := by
        apply SmoothRiemannianMetric.ext_inner
        intro x v w
        simp only [scaleMetric_inner, one_mul]
  · rintro ⟨hσ', Ψ, b, hmetric, hpotential⟩
    refine ⟨zero_lt_one, Ψ, b, ?_, hpotential⟩
    calc
      Diffeomorph.pullbackMetricCross euclideanMetric Ψ =
          scaleMetric (I := I) σ hσ' g := hmetric
      _ = scaleMetric (I := I) 1 zero_lt_one
          (scaleMetric (I := I) σ hσ g) := by
        apply SmoothRiemannianMetric.ext_inner
        intro x v w
        simp only [scaleMetric_inner, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_scaleMetric ``Submission.DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_scaleMetric

theorem isGaussianGradientRicciSoliton_euclidean :
    isGaussianGradientRicciSoliton
      (euclideanMetric (E := E)) (gaussianPotential (E := E)) 1 := by
  refine ⟨zero_lt_one, _root_.Diffeomorph.refl 𝓘(Real, E) E ∞, 0, ?_, ?_⟩
  · rw [Diffeomorph.pullbackMetricCross_refl]
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [scaleMetric_inner]
    ring
  · apply ContMDiffMap.ext
    intro x
    change gaussianPotential x + 0 = gaussianPotential x
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_euclidean then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_euclidean"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_euclidean ``Submission.DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_euclidean

theorem isGaussianGradientRicciSoliton_metricRm04At_eq_zero
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {sigma : Real}
    (hGaussian : isGaussianGradientRicciSoliton (E := E) g f sigma) (x : M) :
    metricRm04At (I := I) g x = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  obtain ⟨hsigma, Ψ, b, hmetric, hpotential⟩ := hGaussian
  ext v
  have hv : v = vec4 (I := I) (v 0) (v 1) (v 2) (v 3) := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  change metricRm04StandardAt (I := I) g x (v 0) (v 1) (v 2) (v 3) = 0
  have hpull := metricRm04Standard_pullbackCross (I := I) (J := 𝓘(Real, E))
    (euclideanMetric (E := E)) Ψ x (v 0) (v 1) (v 2) (v 3)
  rw [hmetric, metricRmStandard_scale] at hpull
  simp only [metricRm04StandardAt_apply, euclideanMetric_metricRm04At_eq_zero] at hpull
  have hprod : sigma * metricRm04StandardAt (I := I) g x
      (v 0) (v 1) (v 2) (v 3) = 0 := hpull
  exact (mul_eq_zero.mp hprod).resolve_left hsigma.ne'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_metricRm04At_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_metricRm04At_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_metricRm04At_eq_zero ``Submission.DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_metricRm04At_eq_zero

theorem isGaussianGradientRicciSoliton_ricciTensor_eq_zero
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (hGaussian : isGaussianGradientRicciSoliton (E := E) g f σ)
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) g x v w = 0 := by
  obtain ⟨hσ, Ψ, b, hmetric, hpotential⟩ := hGaussian
  have hRicci := Curvature.ricciTensor_pullbackCross
    (g := euclideanMetric (E := E)) Ψ x v w
  rw [euclideanMetric_ricciTensor] at hRicci
  rw [hmetric, Curvature.ricciTensor_scaleMetric] at hRicci
  exact hRicci

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_ricciTensor_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_ricciTensor_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_ricciTensor_eq_zero ``Submission.DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_ricciTensor_eq_zero

theorem isGaussianGradientRicciSoliton_scalarCurvature_eq_zero
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (hGaussian : isGaussianGradientRicciSoliton (E := E) g f σ)
    (x : M) :
    metricScalarAt (I := I) g x = 0 := by
  apply metricScalarAt_eq_zero_of_ricciTensor_eq_zero
  exact isGaussianGradientRicciSoliton_ricciTensor_eq_zero hGaussian x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_scalarCurvature_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_scalarCurvature_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_scalarCurvature_eq_zero ``Submission.DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_scalarCurvature_eq_zero

end DifferentialGeometry.Geometry
