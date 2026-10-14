import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartTensor0SCovariantDerivative
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.PartialEvaluation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor0SPartialEval

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

def localSlotCLM (s : ℕ) {b : M}
    (k : Fin s) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    (i : Fin s) : TangentSpace I b →L[ℝ] TangentSpace I b :=
  if i = k then Φ else ContinuousLinearMap.id ℝ (TangentSpace I b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.localSlotCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.localSlotCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.localSlotCLM ``Submission.DifferentialGeometry.Geometry.Connection.localSlotCLM

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
@[simp] lemma localSlotCLM_self (s : ℕ) {b : M}
    (k : Fin s) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) :
    localSlotCLM (I := I) s k Φ k = Φ := by
  unfold localSlotCLM
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.localSlotCLM_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.localSlotCLM_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.localSlotCLM_self ``Submission.DifferentialGeometry.Geometry.Connection.localSlotCLM_self

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
lemma localSlotCLM_other (s : ℕ) {b : M}
    (k : Fin s) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    {i : Fin s} (h : i ≠ k) :
    localSlotCLM (I := I) s k Φ i = ContinuousLinearMap.id ℝ (TangentSpace I b) := by
  unfold localSlotCLM
  simp [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.localSlotCLM_other then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.localSlotCLM_other"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.localSlotCLM_other ``Submission.DifferentialGeometry.Geometry.Connection.localSlotCLM_other

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SSlotCorrection_eq_localSlotCLM_compose (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, Tensor0SSpace s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin s) :
    chartTensor0SSlotCorrection (I := I) s g α T X b k =
      ContinuousMultilinearMap.compContinuousLinearMap
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin s => TangentSpace I b) ℝ from T b)
        (localSlotCLM (I := I) s k
          (chartLeviCivitaParallelCLM (I := I) g α b X)) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_eq_localSlotCLM_compose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_eq_localSlotCLM_compose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_eq_localSlotCLM_compose ``Submission.DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_eq_localSlotCLM_compose

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SSlotCorrection_apply_localSlotCLM (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, Tensor0SSpace s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin s)
    (m : Fin s → TangentSpace I b) :
    Tensor0SSpace.eval (chartTensor0SSlotCorrection (I := I) s g α T X b k) m =
      Tensor0SSpace.eval (T b) (fun i : Fin s =>
        localSlotCLM (I := I) s k
            (chartLeviCivitaParallelCLM (I := I) g α b X) i (m i)) := by
  rw [chartTensor0SSlotCorrection_eq_localSlotCLM_compose
    (I := I) s g α T X b k]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_apply_localSlotCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_apply_localSlotCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_apply_localSlotCLM ``Submission.DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_apply_localSlotCLM

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensor0SPartialEval_apply_tangent (s : ℕ)
    (T : Π b' : M, Tensor0SSpace (s + 1) I b')
    (Y : Π b' : M, TangentSpace I b') (b : M)
    (vs : Fin s → TangentSpace I b) :
    Tensor0SSpace.eval (tensor0SPartialEval I M T Y b) vs =
      Tensor0SSpace.eval (T b) (Fin.cons (Y b) vs) := by
  classical
  exact (Tensor0SSpace.eval_eq _ _).trans
    ((TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := T b) (v0 := Y b) (vs := vs)).trans
        (Tensor0SSpace.eval_eq _ _).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor0SPartialEval_apply_tangent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor0SPartialEval_apply_tangent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor0SPartialEval_apply_tangent ``Submission.DifferentialGeometry.Geometry.Connection.tensor0SPartialEval_apply_tangent

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
private lemma slot_shift_tuple_eq (s : ℕ) {b : M}
    (k : Fin s) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    (w : TangentSpace I b) (m : Fin s → TangentSpace I b) :
    (fun i : Fin (s + 1) =>
        localSlotCLM (I := I) (s + 1) k.succ Φ i
          ((Fin.cons w m : Fin (s + 1) → TangentSpace I b) i)) =
      (Fin.cons w (fun j : Fin s =>
        localSlotCLM (I := I) s k Φ j (m j))
        : Fin (s + 1) → TangentSpace I b) := by
  classical
  funext i
  refine Fin.cases ?_ ?_ i
  · have h_ne : (0 : Fin (s + 1)) ≠ k.succ := by
      intro h
      exact (Fin.succ_ne_zero k h.symm).elim
    have hL_cons : (Fin.cons w m : Fin (s + 1) → TangentSpace I b) 0 = w :=
      Fin.cons_zero (α := fun _ : Fin (s + 1) => TangentSpace I b) w m
    have hR_cons : (Fin.cons w (fun j : Fin s =>
        localSlotCLM (I := I) s k Φ j (m j))
        : Fin (s + 1) → TangentSpace I b) 0 = w :=
      Fin.cons_zero (α := fun _ : Fin (s + 1) => TangentSpace I b) w _
    change localSlotCLM (I := I) (s + 1) k.succ Φ 0
        ((Fin.cons w m : Fin (s + 1) → TangentSpace I b) 0) =
      (Fin.cons w _ : Fin (s + 1) → TangentSpace I b) 0
    rw [hL_cons, hR_cons]
    rw [localSlotCLM_other (I := I) (s + 1) k.succ Φ h_ne]
    rfl
  · intro j
    have hL_cons : (Fin.cons w m : Fin (s + 1) → TangentSpace I b) j.succ = m j :=
      Fin.cons_succ (α := fun _ : Fin (s + 1) => TangentSpace I b) w m j
    have hR_cons : (Fin.cons w (fun j' : Fin s =>
        localSlotCLM (I := I) s k Φ j' (m j'))
        : Fin (s + 1) → TangentSpace I b) j.succ =
      localSlotCLM (I := I) s k Φ j (m j) :=
      Fin.cons_succ (α := fun _ : Fin (s + 1) => TangentSpace I b) w _ j
    change localSlotCLM (I := I) (s + 1) k.succ Φ j.succ
        ((Fin.cons w m : Fin (s + 1) → TangentSpace I b) j.succ) =
      (Fin.cons w _ : Fin (s + 1) → TangentSpace I b) j.succ
    rw [hL_cons, hR_cons]
    have hCLM_eq :
        localSlotCLM (I := I) (s + 1) k.succ Φ j.succ =
          localSlotCLM (I := I) s k Φ j := by
      unfold localSlotCLM
      by_cases hjk : j = k
      · subst hjk; simp
      · have hsucc_ne : (j.succ : Fin (s + 1)) ≠ k.succ := by
          intro h
          exact hjk (Fin.succ_injective _ h)
        simp [hjk, hsucc_ne]
    rw [hCLM_eq]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.slot_shift_tuple_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.slot_shift_tuple_eq target :: scope.openDecls } }

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem chartTensor0SSlotCorrection_succ_eq_partialEval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (T : Π b' : M, Tensor0SSpace (s + 1) I b')
    (X : Π b' : M, TangentSpace I b')
    (b : M) (v : TangentSpace I b)
    (k : Fin s) (m : Fin s → TangentSpace I b) :
    Tensor0SSpace.eval
        (chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k.succ)
          (Fin.cons (chartParallelExtend (I := I) α b v b) m) =
      Tensor0SSpace.eval
        (chartTensor0SSlotCorrection (I := I) s g α
          (tensor0SPartialEval I M T
            (chartParallelExtend (I := I) α b v)) X b k) m := by
  classical
  set Φ : TangentSpace I b →L[ℝ] TangentSpace I b :=
    chartLeviCivitaParallelCLM (I := I) g α b X with hΦ_def
  set w : TangentSpace I b := chartParallelExtend (I := I) α b v b with hw_def
  rw [chartTensor0SSlotCorrection_apply_localSlotCLM (I := I) (s + 1) g α
    T X b k.succ (Fin.cons w m)]
  rw [chartTensor0SSlotCorrection_apply_localSlotCLM (I := I) s g α
    (tensor0SPartialEval I M T (chartParallelExtend (I := I) α b v)) X b k m]
  rw [tensor0SPartialEval_apply_tangent (s := s) (T := T)
    (Y := chartParallelExtend (I := I) α b v) (b := b)
    (vs := fun j : Fin s =>
      localSlotCLM (I := I) s k Φ j (m j))]
  congr 1
  exact slot_shift_tuple_eq (I := I) s k Φ w m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_succ_eq_partialEval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_succ_eq_partialEval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_succ_eq_partialEval ``Submission.DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_succ_eq_partialEval

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem chartTensor0SSlotCorrection_succ_eq_partialEval_of_mem
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (T : Π b' : M, Tensor0SSpace (s + 1) I b')
    (X : Π b' : M, TangentSpace I b')
    {b : M}
    (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (v : TangentSpace I b)
    (k : Fin s) (m : Fin s → TangentSpace I b) :
    Tensor0SSpace.eval
        (chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k.succ)
          (Fin.cons v m) =
      Tensor0SSpace.eval
        (chartTensor0SSlotCorrection (I := I) s g α
          (tensor0SPartialEval I M T
            (chartParallelExtend (I := I) α b v)) X b k) m := by
  classical
  have hcollapse : chartParallelExtend (I := I) α b v b = v := by
    unfold chartParallelExtend
    exact trivFromE_trivToE (I := I) α hb v
  rw [show
      (Fin.cons v m : Fin (s + 1) → TangentSpace I b) =
        Fin.cons (chartParallelExtend (I := I) α b v b) m from by
      rw [hcollapse]]
  exact chartTensor0SSlotCorrection_succ_eq_partialEval (I := I)
    g s α T X b v k m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_succ_eq_partialEval_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_succ_eq_partialEval_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_succ_eq_partialEval_of_mem ``Submission.DifferentialGeometry.Geometry.Connection.chartTensor0SSlotCorrection_succ_eq_partialEval_of_mem

end Connection
end Geometry
end DifferentialGeometry

end
