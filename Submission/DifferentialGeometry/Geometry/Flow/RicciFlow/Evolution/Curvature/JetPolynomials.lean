import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.IteratedCovariantDerivativeFields
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian
import Mathlib.Topology.Algebra.MvPolynomial

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.BigOperators

abbrev CurvatureJetPolynomialVariable (n N : ℕ) :=
  (Fin n × Fin n) ⊕ (Σ j : Fin (N + 1), Fin (4 + j.val) → Fin n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CurvatureJetPolynomialVariable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CurvatureJetPolynomialVariable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CurvatureJetPolynomialVariable ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CurvatureJetPolynomialVariable

def polynomialCoefficientBound {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (C : σ → ℝ) : ℝ :=
  ∑ d ∈ P.support, |P.coeff d| * ∏ i : σ, C i ^ d i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.polynomialCoefficientBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.polynomialCoefficientBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.polynomialCoefficientBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.polynomialCoefficientBound

theorem polynomialCoefficientBound_nonneg {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) {C : σ → ℝ} (hC : ∀ i, 0 ≤ C i) :
    0 ≤ polynomialCoefficientBound P C := by
  exact Finset.sum_nonneg fun d _ => mul_nonneg (abs_nonneg _)
    (Finset.prod_nonneg fun i _ => pow_nonneg (hC i) _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.polynomialCoefficientBound_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.polynomialCoefficientBound_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.polynomialCoefficientBound_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.polynomialCoefficientBound_nonneg

theorem abs_polynomial_eval_le {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) {v C : σ → ℝ}
    (hv : ∀ i, |v i| ≤ C i) :
    |MvPolynomial.eval v P| ≤ polynomialCoefficientBound P C := by
  classical
  rw [MvPolynomial.eval_eq', polynomialCoefficientBound]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun d _ => ?_
  rw [abs_mul, Finset.abs_prod]
  simp only [abs_pow]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact Finset.prod_le_prod (fun i _ => pow_nonneg (abs_nonneg _) _)
    (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hv i) _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.abs_polynomial_eval_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.abs_polynomial_eval_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.abs_polynomial_eval_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.abs_polynomial_eval_le

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance jetPolynomialC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.jetPolynomialC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.jetPolynomialC1 target :: scope.openDecls } }
private local instance jetPolynomialC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.jetPolynomialC2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.jetPolynomialC2 target :: scope.openDecls } }

def tensorOfPolynomialComponents {n r : ℕ} {σ : Type*} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (P : (Fin r → Fin n) → MvPolynomial σ ℝ) (v : σ → ℝ) :
    Tensor0SSpace r I x :=
  (coordEquiv0S (I := I) basis r).symm (fun slots => MvPolynomial.eval v (P slots))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensorOfPolynomialComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensorOfPolynomialComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensorOfPolynomialComponents ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensorOfPolynomialComponents

theorem component0S_tensorOfPolynomialComponents
    {n r : ℕ} {σ : Type*} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (P : (Fin r → Fin n) → MvPolynomial σ ℝ) (v : σ → ℝ)
    (slots : Fin r → Fin n) :
    component0S (I := I) basis (tensorOfPolynomialComponents basis P v) slots =
      MvPolynomial.eval v (P slots) := by
  have h := congrFun ((coordEquiv0S (I := I) basis r).apply_symm_apply
    (fun slots => MvPolynomial.eval v (P slots))) slots
  simpa only [tensorOfPolynomialComponents, coordEquiv0S_apply] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.component0S_tensorOfPolynomialComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.component0S_tensorOfPolynomialComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.component0S_tensorOfPolynomialComponents ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.component0S_tensorOfPolynomialComponents

theorem tensorOfPolynomialComponents_eq_of_components
    {n r : ℕ} {σ : Type*} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (P : (Fin r → Fin n) → MvPolynomial σ ℝ) (v : σ → ℝ)
    (A : Tensor0SSpace r I x)
    (hA : ∀ slots, component0S (I := I) basis A slots = MvPolynomial.eval v (P slots)) :
    tensorOfPolynomialComponents basis P v = A := by
  apply ext0S_basis basis
  intro slots
  rw [component0S_tensorOfPolynomialComponents, hA slots]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensorOfPolynomialComponents_eq_of_components then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensorOfPolynomialComponents_eq_of_components"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensorOfPolynomialComponents_eq_of_components ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensorOfPolynomialComponents_eq_of_components

theorem tensor0S_continuousWithinAt_of_components
    {n r : ℕ} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    {A : ℝ → Tensor0SSpace r I x} {J : Set ℝ} {t : ℝ}
    (hA : ∀ slots, ContinuousWithinAt (fun s => component0S (I := I) basis (A s) slots) J t) :
    ContinuousWithinAt A J t := by
  have hsum : ContinuousWithinAt
      (fun s => ∑ slots, component0S (I := I) basis (A s) slots •
        tensor0SBasis (I := I) basis r slots) J t :=
    tendsto_finsetSum Finset.univ fun slots _ => (hA slots).smul tendsto_const_nhds
  simpa only [← tensor0SBasis_repr, Module.Basis.sum_repr] using hsum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor0S_continuousWithinAt_of_components then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor0S_continuousWithinAt_of_components"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor0S_continuousWithinAt_of_components ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor0S_continuousWithinAt_of_components

theorem tensorOfPolynomialComponents_continuousWithinAt
    {n r : ℕ} {σ : Type*} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (P : (Fin r → Fin n) → MvPolynomial σ ℝ)
    {v : ℝ → σ → ℝ} {J : Set ℝ} {t : ℝ}
    (hv : ∀ i, ContinuousWithinAt (fun s => v s i) J t) :
    ContinuousWithinAt (fun s => tensorOfPolynomialComponents basis P (v s)) J t := by
  let L : ((Fin r → Fin n) → ℝ) →L[ℝ] Tensor0SSpace r I x :=
    (coordEquiv0S (I := I) basis r).symm.toLinearMap.toContinuousLinearMap
  have hvals : ContinuousWithinAt v J t := continuousWithinAt_pi.mpr hv
  have heval : ContinuousWithinAt
      (fun s slots => MvPolynomial.eval (v s) (P slots)) J t := by
    exact continuousWithinAt_pi.mpr fun slots =>
      (P slots).continuous_eval.continuousAt.comp_continuousWithinAt hvals
  exact L.continuous.continuousAt.comp_continuousWithinAt heval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensorOfPolynomialComponents_continuousWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensorOfPolynomialComponents_continuousWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensorOfPolynomialComponents_continuousWithinAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensorOfPolynomialComponents_continuousWithinAt

section Flow

variable [CompleteSpace E] [T2Space M]

def curvatureJetPolynomialValues {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (N : ℕ) (t : ℝ) {n : ℕ} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) :
    CurvatureJetPolynomialVariable n N → ℝ
  | Sum.inl ij => basisInvMetric (I := I) (S.base.metric t) x basis ij.1 ij.2
  | Sum.inr js => component0S (I := I) basis (nablaKRm04Field S t js.1.val x) js.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetPolynomialValues then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetPolynomialValues"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetPolynomialValues ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetPolynomialValues

end Flow

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
