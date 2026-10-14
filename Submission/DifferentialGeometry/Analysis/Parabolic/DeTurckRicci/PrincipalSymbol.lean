import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Submission.DifferentialGeometry.Analysis.Parabolic.PrincipalSymbol.Defs
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.Symbol.SecondOrderPart
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.PrincipalSymbol.Remainder
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Local.Formula

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open _root_.Submission.DifferentialGeometry.PDE.DeTurck
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def chartPushforwardFrameVec (α : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    TangentSpace I x :=
  (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ x (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.chartPushforwardFrameVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.chartPushforwardFrameVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.chartPushforwardFrameVec ``Submission.DifferentialGeometry.PDE.RicciFlow.chartPushforwardFrameVec

def chartFComponentOnE
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y =>
    F g ((extChartAt I α).symm y)
      (chartPushforwardFrameVec (I := I) α i ((extChartAt I α).symm y))
      (chartPushforwardFrameVec (I := I) α j ((extChartAt I α).symm y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE ``Submission.DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE

def IsMetricPerturbationFamily
    (g₀ : SmoothRiemannianMetric I M) (α : M) (h : ChartMetricPerturbation E)
    (gfam : ℝ → SmoothRiemannianMetric I M) : Prop :=
  gfam 0 = g₀ ∧
    (∀ (i j : Fin (Module.finrank ℝ E)) {y : E}, y ∈ interior (extChartAt I α).target →
      HasDerivAt (fun s : ℝ => chartGramOnE (I := I) (gfam s) α i j y) (h i j y) 0) ∧
    (∀ (i j : Fin (Module.finrank ℝ E)) {y : E},
        y ∈ interior (extChartAt I α).target →
        ContDiffAt ℝ ∞
          (fun p : ℝ × E => chartGramOnE (I := I) (gfam p.1) α i j p.2) (0, y)) ∧
    (∀ (i j p : Fin (Module.finrank ℝ E)) {y : E},
        y ∈ interior (extChartAt I α).target →
        HasDerivAt
          (fun s : ℝ => DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p (chartGramOnE (I := I) (gfam s) α i j) y)
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p (h i j) y) 0) ∧
    (∀ (i j p q : Fin (Module.finrank ℝ E)) {y : E},
        y ∈ interior (extChartAt I α).target →
        HasDerivAt
          (fun s : ℝ =>
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p
              (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q (chartGramOnE (I := I) (gfam s) α i j)) y)
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q (h i j)) y) 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IsMetricPerturbationFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IsMetricPerturbationFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IsMetricPerturbationFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.IsMetricPerturbationFamily

def IsFirstOrderInPerturbation
    (R : ChartMetricPerturbation E → M → Fin (Module.finrank ℝ E) →
         Fin (Module.finrank ℝ E) → E → ℝ) : Prop :=
  ∀ (α : M) (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E))
      {y : E}, y ∈ interior (extChartAt I α).target →
      (∀ a b, h a b y = 0) →
      (∀ p a b, DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p (h a b) y = 0) →
      R h α i j y = 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IsFirstOrderInPerturbation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IsFirstOrderInPerturbation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IsFirstOrderInPerturbation ``Submission.DifferentialGeometry.PDE.RicciFlow.IsFirstOrderInPerturbation

def IsChartLinearizationSecondOrderPart
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g₀ : SmoothRiemannianMetric I M)
    (P : ChartMetricPerturbation E → M → Fin (Module.finrank ℝ E) →
         Fin (Module.finrank ℝ E) → E → ℝ) : Prop :=
  ∃ R : ChartMetricPerturbation E → M → Fin (Module.finrank ℝ E) →
        Fin (Module.finrank ℝ E) → E → ℝ,
    IsFirstOrderInPerturbation (I := I) R ∧
      ∀ (α : M) (h : ChartMetricPerturbation E)
          (gfam : ℝ → SmoothRiemannianMetric I M),
          IsMetricPerturbationFamily (I := I) g₀ α h gfam →
          ∀ (i j : Fin (Module.finrank ℝ E)) {y : E},
            y ∈ interior (extChartAt I α).target →
            deriv (fun s : ℝ => chartFComponentOnE (I := I) F (gfam s) α i j y) 0 =
              P h α i j y + R h α i j y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IsChartLinearizationSecondOrderPart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IsChartLinearizationSecondOrderPart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IsChartLinearizationSecondOrderPart ``Submission.DifferentialGeometry.PDE.RicciFlow.IsChartLinearizationSecondOrderPart

def symbolTestPerturbation (x : M) (α : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) : ChartMetricPerturbation E where
  toFun c d := fun y =>
    (1 / 2 : ℝ) *
      ((∑ a : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (y - extChartAt I α x) a)) ^ 2 *
      formComp (I := I) x t c d
  symmetric c d y := by rw [formComp_symm (I := I) x t ht c d]
  contDiff c d := by
    have hsum : ContDiff ℝ ∞ (fun y : E =>
        ∑ a : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (y - extChartAt I α x) a) := by
      refine ContDiff.sum (fun a _ => ?_)
      refine contDiff_const.mul ?_
      have hlin : (fun y : E => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (y - extChartAt I α x) a) =
          fun y : E => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord a (y - extChartAt I α x) := by
        funext y; rw [Module.Basis.coord_apply]
      rw [hlin]
      exact (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord a).toContinuousLinearMap.contDiff).comp
        (contDiff_id.sub contDiff_const)
    exact ContDiff.mul (ContDiff.mul contDiff_const (hsum.pow 2)) contDiff_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.symbolTestPerturbation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.symbolTestPerturbation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.symbolTestPerturbation ``Submission.DifferentialGeometry.PDE.RicciFlow.symbolTestPerturbation

private def testLinear (x α : M) (ξ : E) (y : E) : ℝ :=
  ∑ a : Fin (Module.finrank ℝ E),
    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (y - extChartAt I α x) a

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.testLinear
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.testLinear target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
private lemma symbolTestPerturbation_apply (x α : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) (ht : ∀ v w, t v w = t w v)
    (c d : Fin (Module.finrank ℝ E)) (y : E) :
    symbolTestPerturbation (I := I) x α ξ t ht c d y =
      (1 / 2 : ℝ) * (testLinear (I := I) x α ξ y) ^ 2 * formComp (I := I) x t c d := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.symbolTestPerturbation_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.symbolTestPerturbation_apply target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
private lemma testLinear_self (x α : M) (ξ : E) :
    testLinear (I := I) x α ξ (extChartAt I α x) = 0 := by
  simp [testLinear]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.testLinear_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.testLinear_self target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
lemma symbolTestPerturbation_apply_self (x α : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) (ht : ∀ v w, t v w = t w v)
    (c d : Fin (Module.finrank ℝ E)) :
    symbolTestPerturbation (I := I) x α ξ t ht c d (extChartAt I α x) = 0 := by
  rw [symbolTestPerturbation_apply, testLinear_self]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.symbolTestPerturbation_apply_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.symbolTestPerturbation_apply_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.symbolTestPerturbation_apply_self ``Submission.DifferentialGeometry.PDE.RicciFlow.symbolTestPerturbation_apply_self

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
private lemma testLinear_differentiableAt (x α : M) (ξ : E) (y : E) :
    DifferentiableAt ℝ (testLinear (I := I) x α ξ) y := by
  refine DifferentiableAt.fun_sum (fun a _ => ?_)
  refine (differentiableAt_const _).mul ?_
  have hlin : (fun y : E => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (y - extChartAt I α x) a) =
      fun y : E => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord a (y - extChartAt I α x) := by
    funext z; rw [Module.Basis.coord_apply]
  rw [hlin]
  exact (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord a).toContinuousLinearMap.differentiableAt).comp y
    ((differentiableAt_id).sub (differentiableAt_const _))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.testLinear_differentiableAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.testLinear_differentiableAt target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
lemma partialDeriv_symbolTestPerturbation_self (x α : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) (ht : ∀ v w, t v w = t w v)
    (p c d : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p
        (symbolTestPerturbation (I := I) x α ξ t ht c d) (extChartAt I α x) = 0 := by
  have hfun : (symbolTestPerturbation (I := I) x α ξ t ht c d) =
      fun y => ((1 / 2 : ℝ) * formComp (I := I) x t c d) *
        (testLinear (I := I) x α ξ y) ^ 2 := by
    funext y; rw [symbolTestPerturbation_apply]; ring
  rw [hfun]
  rw [partialDeriv_const_mul (E := E) ((1 / 2 : ℝ) * formComp (I := I) x t c d)
      (fun y => (testLinear (I := I) x α ξ y) ^ 2)
      (((testLinear_differentiableAt (I := I) x α ξ
        (extChartAt I α x)).pow 2))]
  have hpow : (fun y => (testLinear (I := I) x α ξ y) ^ 2) =
      fun y => (testLinear (I := I) x α ξ y) * (testLinear (I := I) x α ξ y) := by
    funext y; ring
  rw [hpow,
    partialDeriv_mul (E := E) (testLinear (I := I) x α ξ) (testLinear (I := I) x α ξ)
      (testLinear_differentiableAt (I := I) x α ξ (extChartAt I α x))
      (testLinear_differentiableAt (I := I) x α ξ (extChartAt I α x)),
    testLinear_self]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.partialDeriv_symbolTestPerturbation_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.partialDeriv_symbolTestPerturbation_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.partialDeriv_symbolTestPerturbation_self ``Submission.DifferentialGeometry.PDE.RicciFlow.partialDeriv_symbolTestPerturbation_self

def IsPrincipalSymbolOfSecondOrderPart
    (g₀ : SmoothRiemannianMetric I M)
    (P : ChartMetricPerturbation E → M → Fin (Module.finrank ℝ E) →
         Fin (Module.finrank ℝ E) → E → ℝ)
    (σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M) : Prop :=
  ∀ (x : M) (ξ : E), ξ ≠ 0 →
    ∀ t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ,
      (∀ v w, t v w = t w v) →
        (∀ ht : ∀ v w, t v w = t w v, ∀ i j : Fin (Module.finrank ℝ E),
            P (symbolTestPerturbation (I := I) x x ξ t ht) x i j (extChartAt I x x) =
              - (σ x ξ t) (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x i)
                (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x j)) ∧
          σ x ξ t =
              (- DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ) •
                t ∧
            0 < DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IsPrincipalSymbolOfSecondOrderPart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IsPrincipalSymbolOfSecondOrderPart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IsPrincipalSymbolOfSecondOrderPart ``Submission.DifferentialGeometry.PDE.RicciFlow.IsPrincipalSymbolOfSecondOrderPart

def HasPrincipalSymbol
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g₀ : SmoothRiemannianMetric I M)
    (σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M) : Prop :=
  ∃ P : ChartMetricPerturbation E → M → Fin (Module.finrank ℝ E) →
        Fin (Module.finrank ℝ E) → E → ℝ,
    IsChartLinearizationSecondOrderPart (I := I) F g₀ P ∧
      IsPrincipalSymbolOfSecondOrderPart (I := I) g₀ P σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol ``Submission.DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem HasPrincipalSymbol.isotropic_of
    {F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)}
    {g₀ : SmoothRiemannianMetric I M}
    {σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M}
    (h : HasPrincipalSymbol (I := I) F g₀ σ)
    (x : M) (ξ : E) (hξ : ξ ≠ 0)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    σ x ξ t =
        (- DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ) • t ∧
      0 < DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ := by
  obtain ⟨_, _, hσ⟩ := h
  exact (hσ x ξ hξ t ht).2

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol.isotropic_of then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol.isotropic_of"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol.isotropic_of ``Submission.DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol.isotropic_of

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem HasPrincipalSymbol.symbol_apply_eq_neg_normSq_smul
    {F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)}
    {g₀ : SmoothRiemannianMetric I M}
    {σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M}
    (h : HasPrincipalSymbol (I := I) F g₀ σ)
    (x : M) (ξ : E) (hξ : ξ ≠ 0)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    σ x ξ t =
      (- DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ) • t :=
  (h.isotropic_of x ξ hξ t ht).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol.symbol_apply_eq_neg_normSq_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol.symbol_apply_eq_neg_normSq_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol.symbol_apply_eq_neg_normSq_smul ``Submission.DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol.symbol_apply_eq_neg_normSq_smul

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartFComponentOnE_zero_operator
    (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartFComponentOnE (I := I)
      (fun (_ : SmoothRiemannianMetric I M) (_ : M) => (0 :
        TangentSpace I _ →L[ℝ] TangentSpace I _ →L[ℝ] ℝ)) g α i j y = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE_zero_operator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE_zero_operator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE_zero_operator ``Submission.DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE_zero_operator

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem not_hasPrincipalSymbol_zero_operator [I.Boundaryless]
    (g₀ : SmoothRiemannianMetric I M) (x : M) {ξ : E} (hξ : ξ ≠ 0)
    {t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ}
    (ht : ∀ v w, t v w = t w v) (ht0 : t ≠ 0)
    (hfam : ∀ (h : ChartMetricPerturbation E),
      ∃ gfam : ℝ → SmoothRiemannianMetric I M,
        IsMetricPerturbationFamily (I := I) g₀ x h gfam) :
    ¬ ∃ σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M,
        HasPrincipalSymbol (I := I)
          (fun (_ : SmoothRiemannianMetric I M) (_ : M) => (0 :
            TangentSpace I _ →L[ℝ] TangentSpace I _ →L[ℝ] ℝ)) g₀ σ := by
  rintro ⟨σ, P, ⟨R, hR_first, hsplit⟩, hσ⟩
  set hξt : ChartMetricPerturbation E := symbolTestPerturbation (I := I) x x ξ t ht with hξt_def
  have hy_int : extChartAt I x x ∈ interior (extChartAt I x).target := by
    have hx_source : x ∈ (extChartAt I x).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact mem_chart_source H x
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) x
      ((extChartAt I x).map_source hx_source)
  obtain ⟨gfam, hfam0, hfam_deriv, hfam_smooth, hfam_jet1, hfam_jet2⟩ := hfam hξt
  have hσ_zero : ∀ i j : Fin (Module.finrank ℝ E),
      (σ x ξ t) (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x i)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x j) = 0 := by
    intro i j
    have hsymbol := (hσ x ξ hξ t ht).1 ht i j
    have hderiv0 :
        deriv (fun s : ℝ =>
          chartFComponentOnE (I := I)
            (fun (_ : SmoothRiemannianMetric I M) (_ : M) => (0 :
              TangentSpace I _ →L[ℝ] TangentSpace I _ →L[ℝ] ℝ)) (gfam s) x i j
            (extChartAt I x x)) 0 = 0 := by
      simp only [chartFComponentOnE_zero_operator]
      exact deriv_const 0 0
    have hsplit' := hsplit x hξt gfam ⟨hfam0, hfam_deriv, hfam_smooth, hfam_jet1, hfam_jet2⟩
      i j hy_int
    rw [hderiv0] at hsplit'
    have hR0 : R hξt x i j (extChartAt I x x) = 0 :=
      hR_first x hξt i j hy_int
        (fun a b => symbolTestPerturbation_apply_self (I := I) x x ξ t ht a b)
        (fun p a b => partialDeriv_symbolTestPerturbation_self (I := I) x x ξ t ht p a b)
    have hP0 : P hξt x i j (extChartAt I x x) = 0 := by
      rw [hR0, add_zero] at hsplit'
      exact hsplit'.symm
    rw [hP0] at hsymbol
    linarith [hsymbol]
  have hσt_zero : σ x ξ t = 0 := by
    refine LinearMap.ext_basis (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x)
      (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x) (fun i j => ?_)
    exact hσ_zero i j
  have hσt_isotropic := (hσ x ξ hξ t ht).2.1
  rw [hσt_zero] at hσt_isotropic
  have hnorm_pos := (hσ x ξ hξ t ht).2.2
  have htneg : (- DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ)
      • t = 0 := hσt_isotropic.symm
  have hcoeff_ne : (- DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ)
      ≠ 0 := by
    rw [neg_ne_zero]
    exact ne_of_gt hnorm_pos
  exact ht0 ((smul_eq_zero.mp htneg).resolve_left hcoeff_ne)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.not_hasPrincipalSymbol_zero_operator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.not_hasPrincipalSymbol_zero_operator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.not_hasPrincipalSymbol_zero_operator ``Submission.DifferentialGeometry.PDE.RicciFlow.not_hasPrincipalSymbol_zero_operator

end RicciFlow
end PDE
end DifferentialGeometry

end
