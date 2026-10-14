import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Local
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.Tensor0SChartChristoffel
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Bundle.SectionRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

def chartParallelExtend (α b : M) (v : TangentSpace I b) (b' : M) :
    TangentSpace I b' :=
  trivFromE (I := I) α b' (trivToE (I := I) α b v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartParallelExtend then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartParallelExtend"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartParallelExtend ``Submission.DifferentialGeometry.Geometry.Connection.chartParallelExtend

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartParallelExtend_def (α b : M) (v : TangentSpace I b) (b' : M) :
    chartParallelExtend (I := I) α b v b' =
      trivFromE (I := I) α b' (trivToE (I := I) α b v) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartParallelExtend_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartParallelExtend_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartParallelExtend_def ``Submission.DifferentialGeometry.Geometry.Connection.chartParallelExtend_def

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartE_section_repr_chartParallelExtend
    (α b : M) (v : TangentSpace I b) {b' : M}
    (hb' : b' ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    chartESectionRepr (I := I) α
        (chartParallelExtend (I := I) α b v) b' =
      trivToE (I := I) α b v := by
  classical
  unfold chartParallelExtend
  change trivToE (I := I) α b' (trivFromE (I := I) α b' (trivToE (I := I) α b v))
      = trivToE (I := I) α b v
  exact trivToE_trivFromE (I := I) α hb' _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartE_section_repr_chartParallelExtend then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartE_section_repr_chartParallelExtend"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartE_section_repr_chartParallelExtend ``Submission.DifferentialGeometry.Geometry.Connection.chartE_section_repr_chartParallelExtend

def chartLeviCivitaParallelCLM
    (g : SmoothRiemannianMetric I M) (α b : M)
    (X : Π b' : M, TangentSpace I b') :
    TangentSpace I b →L[ℝ] TangentSpace I b :=
  (trivFromE (I := I) α b).comp
    (christoffelCorrection (I := I) g α b
      (trivToE (I := I) α b (X b)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivitaParallelCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivitaParallelCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivitaParallelCLM ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivitaParallelCLM

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartLeviCivitaParallelCLM_apply
    (g : SmoothRiemannianMetric I M) (α b : M)
    (X : Π b' : M, TangentSpace I b') (v : TangentSpace I b) :
    chartLeviCivitaParallelCLM (I := I) g α b X v =
      trivFromE (I := I) α b
        (christoffelCorrection (I := I) g α b
          (trivToE (I := I) α b (X b)) v) := by
  classical
  unfold chartLeviCivitaParallelCLM
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivitaParallelCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivitaParallelCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivitaParallelCLM_apply ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivitaParallelCLM_apply

private def slotCLM (s : ℕ) {b : M}
    (k : Fin s) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    (i : Fin s) : TangentSpace I b →L[ℝ] TangentSpace I b :=
  if i = k then Φ else ContinuousLinearMap.id ℝ (TangentSpace I b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.slotCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.slotCLM target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
private lemma slotCLM_self (s : ℕ) {b : M}
    (k : Fin s) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) :
    slotCLM (I := I) s k Φ k = Φ := by
  unfold slotCLM
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.slotCLM_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.slotCLM_self target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
private lemma slotCLM_other (s : ℕ) {b : M}
    (k : Fin s) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    {i : Fin s} (h : i ≠ k) :
    slotCLM (I := I) s k Φ i = ContinuousLinearMap.id ℝ (TangentSpace I b) := by
  unfold slotCLM
  simp [h]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.slotCLM_other
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.slotCLM_other target :: scope.openDecls } }

def chartTensor0SSlotCorrection (s : ℕ) (g : SmoothRiemannianMetric I M)
    (α : M) (T : Π b' : M, Tensor0SSpace s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin s) :
    Tensor0SSpace s I b :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) s b).symm
    (ContinuousMultilinearMap.compContinuousLinearMap
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) s b (T b))
      (slotCLM (I := I) s k (chartLeviCivitaParallelCLM (I := I) g α b X)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection ``Submission.DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SSlotCorrection_apply (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, Tensor0SSpace s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin s)
    (m : Fin s → TangentSpace I b) :
    Tensor0SSpace.eval (chartTensor0SSlotCorrection (I := I) s g α T X b k) m =
      Tensor0SSpace.eval (T b) (fun i =>
        slotCLM (I := I) s k
            (chartLeviCivitaParallelCLM (I := I) g α b X) i (m i)) := by
  classical
  unfold chartTensor0SSlotCorrection
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_apply ``Submission.DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_apply

def chartTensor0SCovariantDerivative :
    (s : ℕ) → SmoothRiemannianMetric I M → (α : M) →
      (T : Π b : M, Tensor0SSpace s I b) →
      (X : Π b : M, TangentSpace I b) →
      (b : M) → Tensor0SSpace s I b
  | 0, _g, _α, T, X, b =>
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 b).symm
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I b)
          (mvfderiv (I := I) (fun b' : M =>
            Tensor0SSpace.eval (T b') (fun i => Fin.elim0 i)) b (X b)))
  | s + 1, g, α, T, X, b =>
      tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b)
        - ∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative ``Submission.DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SCovariantDerivative_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, Tensor0SSpace 0 I b)
    (X : Π b : M, TangentSpace I b) (b : M) :
    chartTensor0SCovariantDerivative (I := I) 0 g α T X b =
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 b).symm
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I b)
          (mvfderiv (I := I) (fun b' : M =>
            Tensor0SSpace.eval (T b') (fun i => Fin.elim0 i)) b (X b))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_zero ``Submission.DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_zero

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SCovariantDerivative_succ (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (X : Π b : M, TangentSpace I b) (b : M) :
    chartTensor0SCovariantDerivative (I := I) (s + 1) g α T X b =
      tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b)
        - ∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_succ ``Submission.DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_succ

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SCovariantDerivative_zero_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, Tensor0SSpace 0 I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (m : Fin 0 → TangentSpace I b) :
    Tensor0SSpace.eval
      (chartTensor0SCovariantDerivative (I := I) 0 g α T X b) m =
      mvfderiv (I := I) (fun b' : M =>
        Tensor0SSpace.eval (T b') (fun i => Fin.elim0 i)) b (X b) := by
  classical
  rw [chartTensor0SCovariantDerivative_zero]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_zero_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_zero_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_zero_apply ``Submission.DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_zero_apply

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SCovariantDerivative_succ_apply (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (m : Fin (s + 1) → TangentSpace I b) :
    Tensor0SSpace.eval
      (chartTensor0SCovariantDerivative (I := I) (s + 1) g α T X b) m =
      Tensor0SSpace.eval
        (tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b)) m
      - ∑ k : Fin (s + 1),
          Tensor0SSpace.eval
            (chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) m := by
  classical
  rw [chartTensor0SCovariantDerivative_succ]
  rw [Tensor0SSpace.eval_sub, Tensor0SSpace.eval_sum]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_succ_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_succ_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_succ_apply ``Submission.DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_succ_apply

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SCovariantDerivative_zero_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (T₁ T₂ : Π b : M, Tensor0SSpace 0 I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (h₁ : MDiffAt
        (fun b' : M => Tensor0SSpace.eval (T₁ b') (fun i => Fin.elim0 i)) b)
    (h₂ : MDiffAt
        (fun b' : M => Tensor0SSpace.eval (T₂ b') (fun i => Fin.elim0 i)) b) :
    chartTensor0SCovariantDerivative (I := I) 0 g α (T₁ + T₂) X b =
      chartTensor0SCovariantDerivative (I := I) 0 g α T₁ X b
        + chartTensor0SCovariantDerivative (I := I) 0 g α T₂ X b := by
  classical
  apply tensor0SSpace_ext
  intro m
  change Tensor0SSpace.eval
      (chartTensor0SCovariantDerivative (I := I) 0 g α (T₁ + T₂) X b) m =
    Tensor0SSpace.eval
      (chartTensor0SCovariantDerivative (I := I) 0 g α T₁ X b
        + chartTensor0SCovariantDerivative (I := I) 0 g α T₂ X b) m
  rw [Tensor0SSpace.eval_add]
  rw [chartTensor0SCovariantDerivative_zero_apply,
      chartTensor0SCovariantDerivative_zero_apply,
      chartTensor0SCovariantDerivative_zero_apply]
  have hpw :
      (fun b' : M =>
          Tensor0SSpace.eval ((T₁ + T₂) b') (fun i => Fin.elim0 i)) =
        (fun b' : M =>
            Tensor0SSpace.eval (T₁ b') (fun i => Fin.elim0 i)) +
          (fun b' : M =>
              Tensor0SSpace.eval (T₂ b') (fun i => Fin.elim0 i)) := by
    funext b'
    rfl
  rw [hpw]
  rw [mvfderiv_add h₁ h₂]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_zero_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_zero_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_zero_add ``Submission.DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_zero_add

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SCovariantDerivative_zero_smul
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (T : Π b : M, Tensor0SSpace 0 I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (hT : MDiffAt
        (fun b' : M => Tensor0SSpace.eval (T b') (fun i => Fin.elim0 i)) b) :
    chartTensor0SCovariantDerivative (I := I) 0 g α (c • T) X b =
      c • chartTensor0SCovariantDerivative (I := I) 0 g α T X b := by
  classical
  apply tensor0SSpace_ext
  intro m
  change Tensor0SSpace.eval
      (chartTensor0SCovariantDerivative (I := I) 0 g α (c • T) X b) m =
    Tensor0SSpace.eval
      (c • chartTensor0SCovariantDerivative (I := I) 0 g α T X b) m
  rw [Tensor0SSpace.eval_smul]
  rw [chartTensor0SCovariantDerivative_zero_apply,
      chartTensor0SCovariantDerivative_zero_apply]
  have hpw :
      (fun b' : M =>
          Tensor0SSpace.eval ((c • T) b') (fun i => Fin.elim0 i)) =
        c • (fun b' : M =>
            Tensor0SSpace.eval (T b') (fun i => Fin.elim0 i)) := by
    funext b'
    rfl
  rw [hpw]
  change (mvfderiv (I := I)
      ((fun _ : M => c) • fun b' : M =>
        Tensor0SSpace.eval (T b') (fun i => Fin.elim0 i)) b) (X b) = _
  rw [mvfderiv_smul (mdifferentiableAt_const (c := c)) hT]
  rw [mvfderiv_const]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_zero_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_zero_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_zero_smul ``Submission.DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_zero_smul

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SSlotCorrection_add (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T₁ T₂ : Π b' : M, Tensor0SSpace s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin s) :
    chartTensor0SSlotCorrection (I := I) s g α (T₁ + T₂) X b k =
      chartTensor0SSlotCorrection (I := I) s g α T₁ X b k
        + chartTensor0SSlotCorrection (I := I) s g α T₂ X b k := by
  classical
  unfold chartTensor0SSlotCorrection
  have hT_add : ((T₁ + T₂) b
        : ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ) =
      (T₁ b : ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ)
        + (T₂ b : ContinuousMultilinearMap ℝ
            (fun _ : Fin s => TangentSpace I b) ℝ) := by
    rfl
  rw [hT_add]
  apply ContinuousMultilinearMap.ext
  intro m
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_add ``Submission.DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_add

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SSlotCorrection_smul (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (T : Π b' : M, Tensor0SSpace s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin s) :
    chartTensor0SSlotCorrection (I := I) s g α (c • T) X b k =
      c • chartTensor0SSlotCorrection (I := I) s g α T X b k := by
  classical
  unfold chartTensor0SSlotCorrection
  have hT_smul : ((c • T) b
        : ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ) =
      c • (T b : ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ) := by
    rfl
  rw [hT_smul]
  apply ContinuousMultilinearMap.ext
  intro m
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_smul ``Submission.DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_smul

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SCovariantDerivative_succ_add (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T₁ T₂ : Π b : M, Tensor0SSpace (s + 1) I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (h₁ : DifferentiableAt ℝ
      (tensor0SChartESectionRepr (I := I) (s + 1) α T₁ ∘ (extChartAt I α).symm)
      (extChartAt I α b))
    (h₂ : DifferentiableAt ℝ
      (tensor0SChartESectionRepr (I := I) (s + 1) α T₂ ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    chartTensor0SCovariantDerivative (I := I) (s + 1) g α (T₁ + T₂) X b =
      chartTensor0SCovariantDerivative (I := I) (s + 1) g α T₁ X b
        + chartTensor0SCovariantDerivative (I := I) (s + 1) g α T₂ X b := by
  classical
  rw [chartTensor0SCovariantDerivative_succ,
      chartTensor0SCovariantDerivative_succ,
      chartTensor0SCovariantDerivative_succ]
  have hsplit_intrinsic :
      tensor0SIntrinsicChartCLM (I := I) (s + 1) α (T₁ + T₂) b (X b) =
        tensor0SIntrinsicChartCLM (I := I) (s + 1) α T₁ b (X b) +
          tensor0SIntrinsicChartCLM (I := I) (s + 1) α T₂ b (X b) := by
    have hCLM := tensor0SIntrinsicChartCLM_add_section
      (I := I) (s + 1) α T₁ T₂ b h₁ h₂
    have := congrArg (fun L : TangentSpace I b →L[ℝ] Tensor0SSpace (s + 1) I b
                        => L (X b)) hCLM
    simpa using this
  rw [hsplit_intrinsic]
  have hsplit_slot :
      (∑ k : Fin (s + 1),
          chartTensor0SSlotCorrection (I := I) (s + 1) g α (T₁ + T₂) X b k) =
        (∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T₁ X b k) +
          (∑ k : Fin (s + 1),
              chartTensor0SSlotCorrection (I := I) (s + 1) g α T₂ X b k) := by
    rw [show (∑ k : Fin (s + 1),
          chartTensor0SSlotCorrection (I := I) (s + 1) g α (T₁ + T₂) X b k) =
        ∑ k : Fin (s + 1),
          (chartTensor0SSlotCorrection (I := I) (s + 1) g α T₁ X b k
            + chartTensor0SSlotCorrection (I := I) (s + 1) g α T₂ X b k) from
      Finset.sum_congr rfl (fun k _ =>
        chartTensor0SSlotCorrection_add (I := I) (s + 1) g α T₁ T₂ X b k)]
    exact Finset.sum_add_distrib
      (f := fun k : Fin (s + 1) =>
        chartTensor0SSlotCorrection (I := I) (s + 1) g α T₁ X b k)
      (g := fun k : Fin (s + 1) =>
        chartTensor0SSlotCorrection (I := I) (s + 1) g α T₂ X b k)
  rw [hsplit_slot]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_succ_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_succ_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_succ_add ``Submission.DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_succ_add

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SCovariantDerivative_succ_smul (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (hT : DifferentiableAt ℝ
      (tensor0SChartESectionRepr (I := I) (s + 1) α T ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    chartTensor0SCovariantDerivative (I := I) (s + 1) g α (c • T) X b =
      c • chartTensor0SCovariantDerivative (I := I) (s + 1) g α T X b := by
  classical
  rw [chartTensor0SCovariantDerivative_succ,
      chartTensor0SCovariantDerivative_succ]
  have hsplit_intrinsic :
      tensor0SIntrinsicChartCLM (I := I) (s + 1) α (c • T) b (X b) =
        c • tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b) := by
    have hCLM := tensor0SIntrinsicChartCLM_smul_section
      (I := I) (s + 1) α c T b hT
    have := congrArg (fun L : TangentSpace I b →L[ℝ] Tensor0SSpace (s + 1) I b
                        => L (X b)) hCLM
    simpa using this
  rw [hsplit_intrinsic]
  have hsplit_slot :
      (∑ k : Fin (s + 1),
          chartTensor0SSlotCorrection (I := I) (s + 1) g α (c • T) X b k) =
        c • (∑ k : Fin (s + 1),
              chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) := by
    have hterm :
        (∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α (c • T) X b k) =
          ∑ k : Fin (s + 1),
            c • chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact chartTensor0SSlotCorrection_smul (I := I) (s + 1) g α c T X b k
    rw [hterm]
    classical
    have hmap :
        c • (∑ k : Fin (s + 1),
              chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) =
          ∑ k : Fin (s + 1),
            c • chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k := by
      have hLM := map_sum (LinearMap.lsmul ℝ (Tensor0SSpace (s + 1) I b) c)
          (fun k => chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k)
          Finset.univ
      exact hLM
    rw [hmap]
  rw [hsplit_slot]
  have hsub :
      c • (tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b) (X b)
        - c • (∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) =
      c • ((tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b) (X b)
        - ∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) :=
    ((LinearMap.lsmul ℝ (Tensor0SSpace (s + 1) I b) c).map_sub
        (tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b))
        (∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k)).symm
  exact hsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_succ_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_succ_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_succ_smul ``Submission.DifferentialGeometry.Geometry.Connection.chartTensor0SCovariantDerivative_succ_smul

end Connection
end Geometry
end DifferentialGeometry
