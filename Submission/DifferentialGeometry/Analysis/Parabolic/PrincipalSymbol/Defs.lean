import Submission.DifferentialGeometry.Geometry.Operator.Hessian.TraceFormula

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev OperatorSymbol (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] : Type _ :=
  ∀ x : M, E → (F x →ₗ[ℝ] F x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.OperatorSymbol then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.OperatorSymbol"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.OperatorSymbol ``Submission.DifferentialGeometry.PDE.DeTurck.OperatorSymbol

variable (I M) in
abbrev TensorSymbol : Type _ :=
  OperatorSymbol (E := E)
    (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.TensorSymbol then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.TensorSymbol"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.TensorSymbol ``Submission.DifferentialGeometry.PDE.DeTurck.TensorSymbol

variable (M) in
abbrev ScalarSymbol : Type _ :=
  OperatorSymbol (E := E) (fun _ : M => ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.ScalarSymbol then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.ScalarSymbol"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.ScalarSymbol ``Submission.DifferentialGeometry.PDE.DeTurck.ScalarSymbol

def metricCovectorNormSq (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j *
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i) * ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq ``Submission.DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma metricCovectorNormSq_def (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    metricCovectorNormSq (I := I) g x ξ =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i j *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i) * ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq_def ``Submission.DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq_def

omit [NeZero (Module.finrank ℝ E)] in
lemma metricCovectorNormSq_zero (g : SmoothRiemannianMetric I M) (x : M) :
    metricCovectorNormSq (I := I) g x 0 = 0 := by
  simp [metricCovectorNormSq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq_zero ``Submission.DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq_zero

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartInvGramMatrix_self_posDef (g : SmoothRiemannianMetric I M) (x : M) :
    (chartInvGramMatrix (I := I) g x x).PosDef := by
  have hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  have hG : (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x).PosDef :=
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_posDef (I := I) g x hx
  rw [chartInvGramMatrix]
  exact hG.inv

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.DeTurck.chartInvGramMatrix_self_posDef
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.DeTurck.chartInvGramMatrix_self_posDef target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma metricCovectorNormSq_eq_dotProduct_mulVec
    (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    metricCovectorNormSq (I := I) g x ξ =
      _root_.Star.star (fun i => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i) ⬝ᵥ
        (chartInvGramMatrix (I := I) g x x) *ᵥ
          (fun i => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i) := by
  classical
  rw [metricCovectorNormSq_def]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, _root_.TrivialStar.star_trivial]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq_eq_dotProduct_mulVec
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq_eq_dotProduct_mulVec target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem metricCovectorNormSq_nonneg (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    0 ≤ metricCovectorNormSq (I := I) g x ξ := by
  classical
  rw [metricCovectorNormSq_eq_dotProduct_mulVec]
  exact (chartInvGramMatrix_self_posDef (I := I) g x).posSemidef.dotProduct_mulVec_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq_nonneg ``Submission.DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq_nonneg

omit [NeZero (Module.finrank ℝ E)] in
theorem metricCovectorNormSq_pos (g : SmoothRiemannianMetric I M) (x : M)
    {ξ : E} (hξ : ξ ≠ 0) :
    0 < metricCovectorNormSq (I := I) g x ξ := by
  classical
  rw [metricCovectorNormSq_eq_dotProduct_mulVec]
  have hcoord : (fun i => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i) ≠ 0 := by
    intro hzero
    apply hξ
    have hrepr : (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ = 0 := by
      ext i
      exact congrFun hzero i
    have := congrArg (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr.symm hrepr
    simpa using this
  exact (chartInvGramMatrix_self_posDef (I := I) g x).dotProduct_mulVec_pos hcoord

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq_pos ``Submission.DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq_pos

def isotropicSymbol (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] (c : M → E → ℝ) :
    OperatorSymbol (E := E) F :=
  fun x ξ => (c x ξ) • LinearMap.id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.isotropicSymbol then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.isotropicSymbol"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.isotropicSymbol ``Submission.DifferentialGeometry.PDE.DeTurck.isotropicSymbol

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [TopologicalSpace M] in
@[simp] lemma isotropicSymbol_apply (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] (c : M → E → ℝ) (x : M) (ξ : E) :
    isotropicSymbol (E := E) F c x ξ = (c x ξ) • LinearMap.id := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.isotropicSymbol_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.isotropicSymbol_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.isotropicSymbol_apply ``Submission.DifferentialGeometry.PDE.DeTurck.isotropicSymbol_apply

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [TopologicalSpace M] in
@[simp] lemma isotropicSymbol_apply_apply (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] (c : M → E → ℝ) (x : M) (ξ : E)
    (v : F x) :
    isotropicSymbol (E := E) F c x ξ v = (c x ξ) • v := by
  rw [isotropicSymbol_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.isotropicSymbol_apply_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.isotropicSymbol_apply_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.isotropicSymbol_apply_apply ``Submission.DifferentialGeometry.PDE.DeTurck.isotropicSymbol_apply_apply

def deTurckSymbolCoeff (g : SmoothRiemannianMetric I M) : M → E → ℝ :=
  fun x ξ => -metricCovectorNormSq (I := I) g x ξ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff ``Submission.DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma deTurckSymbolCoeff_apply (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    deTurckSymbolCoeff (I := I) g x ξ = -metricCovectorNormSq (I := I) g x ξ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff_apply ``Submission.DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff_apply

def IsStrictlyParabolic (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)]
    (g : SmoothRiemannianMetric I M) (σ : OperatorSymbol (E := E) F) : Prop :=
  ∀ x : M, ∀ ξ : E, ξ ≠ 0 →
    σ x ξ = isotropicSymbol (E := E) F (deTurckSymbolCoeff (I := I) g) x ξ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.IsStrictlyParabolic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.IsStrictlyParabolic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.IsStrictlyParabolic ``Submission.DifferentialGeometry.PDE.DeTurck.IsStrictlyParabolic

omit [NeZero (Module.finrank ℝ E)] in
lemma isStrictlyParabolic_iff (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)]
    (g : SmoothRiemannianMetric I M) (σ : OperatorSymbol (E := E) F) :
    IsStrictlyParabolic (E := E) F g σ ↔
      ∀ x : M, ∀ ξ : E, ξ ≠ 0 →
        σ x ξ = (-metricCovectorNormSq (I := I) g x ξ) • LinearMap.id :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.isStrictlyParabolic_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.isStrictlyParabolic_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.isStrictlyParabolic_iff ``Submission.DifferentialGeometry.PDE.DeTurck.isStrictlyParabolic_iff

omit [NeZero (Module.finrank ℝ E)] in
theorem isStrictlyParabolic_isotropic_deTurckSymbolCoeff (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] (g : SmoothRiemannianMetric I M) :
    IsStrictlyParabolic (E := E) F g
      (isotropicSymbol (E := E) F (deTurckSymbolCoeff (I := I) g)) :=
  fun _ _ _ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.isStrictlyParabolic_isotropic_deTurckSymbolCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.isStrictlyParabolic_isotropic_deTurckSymbolCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.isStrictlyParabolic_isotropic_deTurckSymbolCoeff ``Submission.DifferentialGeometry.PDE.DeTurck.isStrictlyParabolic_isotropic_deTurckSymbolCoeff

def secondOrderSymbol (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)]
    (a : M → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) :
    OperatorSymbol (E := E) F :=
  fun x ξ =>
    (-∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          a x i j * ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i) * ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j)) •
      LinearMap.id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.secondOrderSymbol then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.secondOrderSymbol"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.secondOrderSymbol ``Submission.DifferentialGeometry.PDE.DeTurck.secondOrderSymbol

omit [NeZero (Module.finrank ℝ E)] [TopologicalSpace M] in
@[simp] lemma secondOrderSymbol_apply (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)]
    (a : M → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (x : M) (ξ : E) :
    secondOrderSymbol (E := E) F a x ξ =
      (-∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            a x i j * ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i) *
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j)) • LinearMap.id := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.secondOrderSymbol_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.secondOrderSymbol_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.secondOrderSymbol_apply ``Submission.DifferentialGeometry.PDE.DeTurck.secondOrderSymbol_apply

omit [NeZero (Module.finrank ℝ E)] [TopologicalSpace M] in
lemma secondOrderSymbol_apply_apply (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)]
    (a : M → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (x : M) (ξ : E) (v : F x) :
    secondOrderSymbol (E := E) F a x ξ v =
      (-∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            a x i j * ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i) *
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j)) • v := by
  rw [secondOrderSymbol_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.secondOrderSymbol_apply_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.secondOrderSymbol_apply_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.secondOrderSymbol_apply_apply ``Submission.DifferentialGeometry.PDE.DeTurck.secondOrderSymbol_apply_apply

omit [NeZero (Module.finrank ℝ E)] in
theorem secondOrderSymbol_invGram_eq_isotropic (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] (g : SmoothRiemannianMetric I M) :
    secondOrderSymbol (E := E) F (fun x => chartInvGramMatrix (I := I) g x x) =
      isotropicSymbol (E := E) F (deTurckSymbolCoeff (I := I) g) := by
  funext x ξ
  rw [secondOrderSymbol_apply, isotropicSymbol_apply, deTurckSymbolCoeff_apply,
    metricCovectorNormSq_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.secondOrderSymbol_invGram_eq_isotropic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.secondOrderSymbol_invGram_eq_isotropic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.secondOrderSymbol_invGram_eq_isotropic ``Submission.DifferentialGeometry.PDE.DeTurck.secondOrderSymbol_invGram_eq_isotropic

omit [NeZero (Module.finrank ℝ E)] in
theorem secondOrderSymbol_invGram_isStrictlyParabolic (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] (g : SmoothRiemannianMetric I M) :
    IsStrictlyParabolic (E := E) F g
      (secondOrderSymbol (E := E) F (fun x => chartInvGramMatrix (I := I) g x x)) := by
  rw [secondOrderSymbol_invGram_eq_isotropic]
  exact isStrictlyParabolic_isotropic_deTurckSymbolCoeff (E := E) F g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.secondOrderSymbol_invGram_isStrictlyParabolic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.secondOrderSymbol_invGram_isStrictlyParabolic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.secondOrderSymbol_invGram_isStrictlyParabolic ``Submission.DifferentialGeometry.PDE.DeTurck.secondOrderSymbol_invGram_isStrictlyParabolic

def laplacianSymbol (g : SmoothRiemannianMetric I M) : ScalarSymbol (E := E) M :=
  secondOrderSymbol (E := E) (fun _ : M => ℝ)
    (fun x => chartInvGramMatrix (I := I) g x x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.laplacianSymbol then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.laplacianSymbol"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.laplacianSymbol ``Submission.DifferentialGeometry.PDE.DeTurck.laplacianSymbol

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma laplacianSymbol_apply (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    laplacianSymbol (I := I) g x ξ =
      (-∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x i j *
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i) *
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j)) • LinearMap.id := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.laplacianSymbol_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.laplacianSymbol_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.laplacianSymbol_apply ``Submission.DifferentialGeometry.PDE.DeTurck.laplacianSymbol_apply

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianSymbol_eq_isotropic (g : SmoothRiemannianMetric I M) :
    laplacianSymbol (I := I) g =
      isotropicSymbol (E := E) (fun _ : M => ℝ) (deTurckSymbolCoeff (I := I) g) := by
  rw [laplacianSymbol, secondOrderSymbol_invGram_eq_isotropic]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.laplacianSymbol_eq_isotropic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.laplacianSymbol_eq_isotropic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.laplacianSymbol_eq_isotropic ``Submission.DifferentialGeometry.PDE.DeTurck.laplacianSymbol_eq_isotropic

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianSymbol_apply_eq (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    laplacianSymbol (I := I) g x ξ =
      (-metricCovectorNormSq (I := I) g x ξ) • LinearMap.id := by
  rw [laplacianSymbol_eq_isotropic, isotropicSymbol_apply, deTurckSymbolCoeff_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.laplacianSymbol_apply_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.laplacianSymbol_apply_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.laplacianSymbol_apply_eq ``Submission.DifferentialGeometry.PDE.DeTurck.laplacianSymbol_apply_eq

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianSymbol_apply_apply (g : SmoothRiemannianMetric I M)
    (x : M) (ξ : E) (t : ℝ) :
    laplacianSymbol (I := I) g x ξ t =
      (-metricCovectorNormSq (I := I) g x ξ) • t := by
  rw [laplacianSymbol_apply_eq]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.laplacianSymbol_apply_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.laplacianSymbol_apply_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.laplacianSymbol_apply_apply ``Submission.DifferentialGeometry.PDE.DeTurck.laplacianSymbol_apply_apply

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianSymbol_isStrictlyParabolic (g : SmoothRiemannianMetric I M) :
    IsStrictlyParabolic (E := E) (fun _ : M => ℝ) g (laplacianSymbol (I := I) g) := by
  rw [laplacianSymbol_eq_isotropic]
  exact isStrictlyParabolic_isotropic_deTurckSymbolCoeff (E := E) (fun _ : M => ℝ) g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.laplacianSymbol_isStrictlyParabolic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.laplacianSymbol_isStrictlyParabolic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.laplacianSymbol_isStrictlyParabolic ``Submission.DifferentialGeometry.PDE.DeTurck.laplacianSymbol_isStrictlyParabolic

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianSymbol_neg_of_ne_zero (g : SmoothRiemannianMetric I M) (x : M)
    {ξ : E} (hξ : ξ ≠ 0) :
    laplacianSymbol (I := I) g x ξ =
        (-metricCovectorNormSq (I := I) g x ξ) • LinearMap.id ∧
      metricCovectorNormSq (I := I) g x ξ > 0 :=
  ⟨laplacianSymbol_apply_eq (I := I) g x ξ,
    metricCovectorNormSq_pos (I := I) g x hξ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.laplacianSymbol_neg_of_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.laplacianSymbol_neg_of_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.laplacianSymbol_neg_of_ne_zero ``Submission.DifferentialGeometry.PDE.DeTurck.laplacianSymbol_neg_of_ne_zero

end DeTurck
end PDE
end DifferentialGeometry
