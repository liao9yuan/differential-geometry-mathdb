import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Matrix

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem hessFun_add_const
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (c : Real)
    (x : M) (v w : TangentSpace I x) :
    hessFun (I := I) g (fun y => f y + c) x v w =
      hessFun (I := I) g f x v w := by
  rw [Connection.hessFun_eq_abstract (I := I) (f := fun y => f y + c)
    g (f.contMDiff.add contMDiff_const) x v w]
  rw [Connection.hessFun_eq_abstract (I := I) (f := f) g f.contMDiff x v w]
  simp only [Connection.abstractHessian_apply]
  have hderiv :
      mvfderiv (I := I) (fun y : M => f y + c) = mvfderiv (I := I) f := by
    funext y
    rw [show (fun z : M => f z + c) =
      (fun z : M => f z) + (fun _ : M => c) by rfl]
    rw [mvfderiv_add
      (f.contMDiff.mdifferentiable (by simp) y)
      (mdifferentiableAt_const (c := c))]
    rw [mvfderiv_const]
    simp
  rw [hderiv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.hessFun_add_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.hessFun_add_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.hessFun_add_const ``Submission.DifferentialGeometry.Geometry.Operator.hessFun_add_const

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless] in
private theorem matrix_inv_smul_of_ne_zero {n : Type*} [DecidableEq n] [Fintype n]
    {c : Real} (hc : c ≠ 0) (A : Matrix n n Real) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  by_cases h : IsUnit A.det
  · have hu := Matrix.inv_smul' (A := A) (Units.mk0 c hc) h
    simpa [Units.smul_def] using hu
  · have hA : A⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit A h
    have hdet0 : A.det = 0 := by
      rw [isUnit_iff_ne_zero, _root_.Classical.not_not] at h
      exact h
    have hdet : ¬ IsUnit (c • A).det := by
      rw [Matrix.det_smul, hdet0, _root_.MulZeroClass.mul_zero, isUnit_iff_ne_zero, _root_.Classical.not_not]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hdet, hA, smul_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.matrix_inv_smul_of_ne_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.matrix_inv_smul_of_ne_zero target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless] in
private theorem partialDeriv_const_mul
    (i : Fin (Module.finrank Real E)) (c : Real) (u : E → Real) (y : E) :
    partialDeriv (E := E) i (fun z => c * u z) y =
      c * partialDeriv (E := E) i u y := by
  have hfun : (fun z : E => c * u z) = c • u := by
    funext z
    simp
  rw [hfun]
  unfold partialDeriv
  rw [congrFun (fderiv_const_smul_field (𝕜 := Real) (f := u) c) y]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.partialDeriv_const_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.partialDeriv_const_mul target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless] in
private theorem chartGramMatrix_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x₀ x : M) :
    chartGramMatrix (I := I) (scaleMetric (I := I) c hc g) x₀ x =
      c • chartGramMatrix (I := I) g x₀ x := by
  ext i j
  simp [chartGramMatrix_apply, scaleMetric_inner]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.chartGramMatrix_scaleMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.chartGramMatrix_scaleMetric target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless] in
private theorem chartInvGramMatrix_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x₀ x : M) :
    chartInvGramMatrix (I := I) (scaleMetric (I := I) c hc g) x₀ x =
      c⁻¹ • chartInvGramMatrix (I := I) g x₀ x := by
  unfold chartInvGramMatrix
  rw [chartGramMatrix_scaleMetric (I := I) c hc g x₀ x]
  exact matrix_inv_smul_of_ne_zero (ne_of_gt hc) _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.chartInvGramMatrix_scaleMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.chartInvGramMatrix_scaleMetric target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless] in
private theorem chartGramOnE_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : Fin (Module.finrank Real E)) :
    chartGramOnE (I := I) (scaleMetric (I := I) c hc g) x₀ i j =
      fun y => c * chartGramOnE (I := I) g x₀ i j y := by
  funext y
  simp [chartGramOnE, chartGramMatrix_apply, scaleMetric_inner]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.chartGramOnE_scaleMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.chartGramOnE_scaleMetric target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless] in
private theorem chartChristoffel_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j k : Fin (Module.finrank Real E)) (y : E) :
    chartChristoffel (I := I) (scaleMetric (I := I) c hc g) x₀ i j k y =
      chartChristoffel (I := I) g x₀ i j k y := by
  classical
  have hpd : ∀ a b m : Fin (Module.finrank Real E),
      partialDeriv (E := E) m
          (chartGramOnE (I := I) (scaleMetric (I := I) c hc g) x₀ a b) y =
        c * partialDeriv (E := E) m (chartGramOnE (I := I) g x₀ a b) y := by
    intro a b m
    rw [chartGramOnE_scaleMetric (I := I) c hc g x₀ a b,
      partialDeriv_const_mul (E := E) m c (chartGramOnE (I := I) g x₀ a b) y]
  rw [chartChristoffel_def, chartChristoffel_def]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro l _
  have hginv := congrFun₂ (chartInvGramMatrix_scaleMetric (I := I) c hc g x₀
    ((extChartAt I x₀).symm y)) k l
  rw [Matrix.smul_apply, smul_eq_mul] at hginv
  rw [hginv, hpd l j i, hpd l i j, hpd i j l]
  field_simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.chartChristoffel_scaleMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.chartChristoffel_scaleMetric target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless] in
private theorem chartHessianTensor_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x₀ : M)
    (f : M → Real) (i j : Fin (Module.finrank Real E)) (x : M) :
    chartHessianTensor (I := I) (scaleMetric (I := I) c hc g) x₀ f i j x =
      chartHessianTensor (I := I) g x₀ f i j x := by
  simp only [chartHessianTensor_def, chartChristoffel_scaleMetric (I := I) c hc g]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.chartHessianTensor_scaleMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.chartHessianTensor_scaleMetric target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless] in
theorem hessFun_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (f : M → Real) (x : M) :
    hessFun (I := I) (scaleMetric (I := I) c hc g) f x =
      hessFun (I := I) g f x := by
  ext v w
  simp only [hessFun_apply, chartHessianTensor_scaleMetric (I := I) c hc g]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.hessFun_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.hessFun_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.hessFun_scaleMetric ``Submission.DifferentialGeometry.Geometry.Operator.hessFun_scaleMetric

end DifferentialGeometry.Geometry.Operator
