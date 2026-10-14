import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.IndexRaising
import Submission.DifferentialGeometry.Geometry.Connection.MetricTrace.CovariantDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

section Perm

def reLowerPermutationWithTwoInputs (s : ℕ) : Equiv.Perm (Fin (s + 1 + 2)) :=
  Equiv.ofLeftInverseOfCardLE (le_refl _)
    (fun k : Fin (s + 1 + 2) =>
      if h : (k : ℕ) < s then ⟨(k : ℕ) + 2, by omega⟩
      else if (k : ℕ) = s then ⟨0, by omega⟩
      else if (k : ℕ) = s + 1 then ⟨1, by omega⟩
      else k)
    (fun l : Fin (s + 1 + 2) =>
      if (l : ℕ) = 0 then ⟨s, by omega⟩
      else if (l : ℕ) = 1 then ⟨s + 1, by omega⟩
      else if h : (l : ℕ) < s + 2 then ⟨(l : ℕ) - 2, by omega⟩
      else l)
    (by
      intro k
      have hk : (k : ℕ) < s + 1 + 2 := k.isLt
      refine Fin.ext ?_
      dsimp only
      split_ifs <;> simp_all <;> omega)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs ``Submission.DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs

theorem reLowerPermutationWithTwoInputs_value (s : ℕ) (k : Fin (s + 1 + 2)) :
    ((reLowerPermutationWithTwoInputs s k : Fin (s + 1 + 2)) : ℕ) =
      if (k : ℕ) < s then (k : ℕ) + 2
      else if (k : ℕ) = s then 0 else if (k : ℕ) = s + 1 then 1 else (k : ℕ) := by
  change ((if h : (k : ℕ) < s then (⟨(k : ℕ) + 2, by omega⟩ : Fin (s + 1 + 2))
      else if (k : ℕ) = s then ⟨0, by omega⟩
      else if (k : ℕ) = s + 1 then ⟨1, by omega⟩ else k : Fin (s + 1 + 2)) : ℕ) = _
  split_ifs <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs_value then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs_value"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs_value ``Submission.DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs_value

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLowerPermutationWithTwoInputs_first_block {s : ℕ} {x : M} (a b : TangentSpace I x)
    (tail : Fin (s + 1) -> TangentSpace I x) (k : Fin (s + 1)) :
    metricTraceInput (I := I) a b tail (reLowerPermutationWithTwoInputs s (Fin.castAdd 2 k)) =
      Function.update tail (Fin.last s) a k := by
  classical
  have hk : (k : ℕ) < s + 1 := k.isLt
  have hcast : ((Fin.castAdd 2 k : Fin (s + 1 + 2)) : ℕ) = (k : ℕ) := rfl
  rw [metricTraceInput_apply]
  by_cases h1 : (k : ℕ) < s
  · have hv : ((reLowerPermutationWithTwoInputs s (Fin.castAdd 2 k) : Fin (s + 1 + 2)) : ℕ) = (k : ℕ) + 2 := by
      rw [reLowerPermutationWithTwoInputs_value, hcast, if_pos h1]
    have hne : k ≠ Fin.last s := by
      intro hcon
      rw [hcon] at h1
      simp at h1
    simp only [hv, Function.update_of_ne hne]
    rw [dif_neg (by omega : ¬((k : ℕ) + 2 = 0)), dif_neg (by omega : ¬((k : ℕ) + 2 = 1))]
    exact congrArg tail (Fin.ext (by simp))
  · have hks : (k : ℕ) = s := by omega
    have hv : ((reLowerPermutationWithTwoInputs s (Fin.castAdd 2 k) : Fin (s + 1 + 2)) : ℕ) = 0 := by
      rw [reLowerPermutationWithTwoInputs_value, hcast, if_neg h1, if_pos hks]
    have hlast : k = Fin.last s := Fin.ext (by simp [hks])
    simp only [hv]
    rw [dif_pos (trivial : True), hlast, Function.update_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs_first_block then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs_first_block"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs_first_block ``Submission.DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs_first_block

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLowerPermutationWithTwoInputs_tail_zero {s : ℕ} {x : M} (a b : TangentSpace I x)
    (tail : Fin (s + 1) -> TangentSpace I x) :
    metricTraceInput (I := I) a b tail (reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) (0 : Fin 2))) = b := by
  have hcast : ((Fin.natAdd (s + 1) (0 : Fin 2) : Fin (s + 1 + 2)) : ℕ) = s + 1 := by
    simp [Fin.natAdd]
  have hv : ((reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) (0 : Fin 2)) : Fin (s + 1 + 2)) : ℕ) = 1 := by
    rw [reLowerPermutationWithTwoInputs_value, hcast, if_neg (by omega), if_neg (by omega), if_pos rfl]
  rw [metricTraceInput_apply]
  simp only [hv]
  rw [dif_neg (by omega : ¬((1 : ℕ) = 0)), dif_pos (trivial : True)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs_tail_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs_tail_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs_tail_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs_tail_zero

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLowerPermutationWithTwoInputs_tail_one {s : ℕ} {x : M} (a b : TangentSpace I x)
    (tail : Fin (s + 1) -> TangentSpace I x) :
    metricTraceInput (I := I) a b tail (reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) (1 : Fin 2))) =
      tail (Fin.last s) := by
  have hcast : ((Fin.natAdd (s + 1) (1 : Fin 2) : Fin (s + 1 + 2)) : ℕ) = s + 2 := by
    simp [Fin.natAdd]
  have hv : ((reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) (1 : Fin 2)) : Fin (s + 1 + 2)) : ℕ) = s + 2 := by
    rw [reLowerPermutationWithTwoInputs_value, hcast, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [metricTraceInput_apply]
  simp only [hv]
  rw [dif_neg (by omega : ¬(s + 2 = 0)), dif_neg (by omega : ¬(s + 2 = 1))]
  exact congrArg tail (Fin.ext (by simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs_tail_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs_tail_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs_tail_one ``Submission.DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithTwoInputs_tail_one

end Perm

section ReLower

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem traceField_eq_sum {s : ℕ} (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x)) (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) g x basis gInv)
    (tail : Fin s -> TangentSpace I x) :
    Tensor0SSpace.eval (metricTraceFirstTwoField (I := I) (M := M) g A x) tail =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * Tensor0SSpace.eval (A x)
          (metricTraceInput (I := I) (basis i) (basis j) tail) := by
  have h := metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv (A x) tail
  calc
    Tensor0SSpace.eval (metricTraceFirstTwoField (I := I) (M := M) g A x) tail =
        metricTraceFirstTwo0SAt (I := I) g (A x) tail := by
      rw [metricTraceFirstTwoField_apply]
      exact metricTraceFirstTwo0STensor_apply (I := I) g (A x) tail
    _ = metricTrace0S2InBasis (I := I) basis gInv (A x) tail := h
    _ = ∑ i : Idx, ∑ j : Idx,
        gInv i j * Tensor0SSpace.eval (A x)
          (metricTraceInput (I := I) (basis i) (basis j) tail) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.traceField_eq_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.traceField_eq_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.traceField_eq_sum ``Submission.DifferentialGeometry.PDE.RicciFlow.traceField_eq_sum

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem slot_expand {s : ℕ} {Idx : Type*} [Fintype Idx] {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (m : Fin s -> TangentSpace I x) (i : Fin s) (c : Idx -> Real)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    Tensor0SSpace.eval A (Function.update m i (∑ p : Idx, c p • basis p)) =
      ∑ p : Idx, c p * Tensor0SSpace.eval A (Function.update m i (basis p)) := by
  classical
  calc Tensor0SSpace.eval A (Function.update m i (∑ p : Idx, c p • basis p))
      = ∑ p : Idx, Tensor0SSpace.eval A (Function.update m i (c p • basis p)) :=
        A.toMultilinearMap.map_update_sum Finset.univ i (fun p => c p • basis p) m
    _ = ∑ p : Idx, c p * Tensor0SSpace.eval A (Function.update m i (basis p)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        have h := Tensor0SSpace.map_update_smul (I := I) A m i (c p) (basis p)
        change Tensor0SSpace.eval A (Function.update m i (c p • basis p)) =
          c p • Tensor0SSpace.eval A (Function.update m i (basis p)) at h
        simpa [smul_eq_mul] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.slot_expand
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.slot_expand target :: scope.openDecls } }

def reLower (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1) :=
  metricTraceFirstTwoField (I := I) (M := M) (s := s + 1) g₂
    (Tensor0SField.domDomCongr (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) (reLowerPermutationWithTwoInputs s)
      (tensor0SFieldProduct (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (∞ : WithTop ℕ∞) T (metricTensorField (I := I) g₁)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLower ``Submission.DifferentialGeometry.PDE.RicciFlow.reLower

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLower_eval (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x)) (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) g₂ x basis gInv)
    (tail : Fin (s + 1) -> TangentSpace I x) :
    Tensor0SSpace.eval (reLower (I := I) g₁ g₂ T x) tail =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * (Tensor0SSpace.eval (T x)
          (Function.update tail (Fin.last s) (basis i)) *
          g₁.inner x (basis j) (tail (Fin.last s))) := by
  classical
  with_unfolding_all
    rw [reLower, traceField_eq_sum (I := I) g₂ _ basis gInv hinv tail]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  change Tensor0SSpace.eval
      (Tensor0SSpace.domDomCongr
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) T (metricTensorField (I := I) g₁) x)
        (reLowerPermutationWithTwoInputs s)) _ = _
  rw [Tensor0SSpace.eval_domDomCongr, tensor0SField_product_eval, metricTensorField_eval]
  congr 1
  · exact congrArg (Tensor0SSpace.eval (T x))
      (funext fun k => reLowerPermutationWithTwoInputs_first_block (I := I) (basis i) (basis j) tail k)
  · change g₁.inner x
        (metricTraceInput (I := I) (basis i) (basis j) tail
          (reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) (0 : Fin 2))))
        (metricTraceInput (I := I) (basis i) (basis j) tail
          (reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) (1 : Fin 2)))) = _
    rw [reLowerPermutationWithTwoInputs_tail_zero (I := I) (basis i) (basis j) tail,
      reLowerPermutationWithTwoInputs_tail_one (I := I) (basis i) (basis j) tail]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLower_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLower_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLower_eval ``Submission.DifferentialGeometry.PDE.RicciFlow.reLower_eval

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem sharpFlat_eq_raise (g₁ g₂ : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x)) (V : TangentSpace I x) :
    sharpFlat (I := I) g₁ g₂ x V =
      raiseAt (I := I) g₂ x basis (fun l : Idx => g₁.inner x V (basis l)) := by
  have hflat : ∀ l : Idx,
      g₂.inner x (sharpFlat (I := I) g₁ g₂ x V) (basis l) = g₁.inner x V (basis l) := by
    intro l
    have h2 : tangentFlatEquiv (I := I) g₂ x (sharpFlat (I := I) g₁ g₂ x V) =
        tangentFlatEquiv (I := I) g₁ x V := by
      change tangentFlatEquiv (I := I) g₂ x
        ((tangentFlatEquiv (I := I) g₂ x).symm
          ((tangentFlatEquiv (I := I) g₁ x) V)) = _
      exact (tangentFlatEquiv (I := I) g₂ x).apply_symm_apply _
    rw [← tangentFlatEquiv_apply (I := I) g₂ x, h2,
      tangentFlatEquiv_apply (I := I) g₁ x]
  rw [show (fun l : Idx => g₁.inner x V (basis l)) =
      fun l : Idx => g₂.inner x (sharpFlat (I := I) g₁ g₂ x V) (basis l) from
    (funext fun l => (hflat l).symm)]
  exact (raiseAt_lower (I := I) g₂ x basis (sharpFlat (I := I) g₁ g₂ x V)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.sharpFlat_eq_raise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.sharpFlat_eq_raise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.sharpFlat_eq_raise ``Submission.DifferentialGeometry.PDE.RicciFlow.sharpFlat_eq_raise

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLower_apply (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (x : M) (tail : Fin (s + 1) -> TangentSpace I x) :
    Tensor0SSpace.eval (reLower (I := I) g₁ g₂ T x) tail =
      Tensor0SSpace.eval (T x) (Function.update tail (Fin.last s)
        (sharpFlat (I := I) g₁ g₂ x (tail (Fin.last s)))) := by
  classical
  set basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x) with hbasis
  set gInv := basisInvMetric (I := I) g₂ x basis with hgInv
  have hinv : MetricInverseInBasis (I := I) (M := M) g₂ x basis gInv :=
    basisInvMetric_isInverse (I := I) g₂ x basis
  rw [reLower_eval (I := I) g₁ g₂ T basis gInv hinv tail,
    sharpFlat_eq_raise (I := I) g₁ g₂ basis (tail (Fin.last s)), raiseAt_eq,
    slot_expand (I := I) (T x) tail (Fin.last s)
      (fun p => ∑ l, gInv p l * g₁.inner x (tail (Fin.last s)) (basis l)) basis]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [g₁.symm x (basis l) (tail (Fin.last s))]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLower_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLower_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLower_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.reLower_apply

end ReLower

section Pair

def reLowerPermutationWithThreeInputs (s : ℕ) : Equiv.Perm (Fin (s + 1 + 3)) :=
  Equiv.ofLeftInverseOfCardLE (le_refl _)
    (fun k : Fin (s + 1 + 3) =>
      if h : (k : ℕ) < s then ⟨(k : ℕ) + 3, by omega⟩
      else if (k : ℕ) = s then ⟨0, by omega⟩
      else if (k : ℕ) = s + 1 then ⟨2, by omega⟩
      else if (k : ℕ) = s + 2 then ⟨1, by omega⟩
      else k)
    (fun l : Fin (s + 1 + 3) =>
      if (l : ℕ) = 0 then ⟨s, by omega⟩
      else if (l : ℕ) = 1 then ⟨s + 2, by omega⟩
      else if (l : ℕ) = 2 then ⟨s + 1, by omega⟩
      else if h : (l : ℕ) < s + 3 then ⟨(l : ℕ) - 3, by omega⟩
      else l)
    (by
      intro k
      have hk : (k : ℕ) < s + 1 + 3 := k.isLt
      refine Fin.ext ?_
      dsimp only
      split_ifs <;> simp_all <;> omega)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs ``Submission.DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs

theorem reLowerPermutationWithThreeInputs_value (s : ℕ) (k : Fin (s + 1 + 3)) :
    ((reLowerPermutationWithThreeInputs s k : Fin (s + 1 + 3)) : ℕ) =
      if (k : ℕ) < s then (k : ℕ) + 3
      else if (k : ℕ) = s then 0
      else if (k : ℕ) = s + 1 then 2
      else if (k : ℕ) = s + 2 then 1 else (k : ℕ) := by
  change ((if h : (k : ℕ) < s then (⟨(k : ℕ) + 3, by omega⟩ : Fin (s + 1 + 3))
      else if (k : ℕ) = s then ⟨0, by omega⟩
      else if (k : ℕ) = s + 1 then ⟨2, by omega⟩
      else if (k : ℕ) = s + 2 then ⟨1, by omega⟩ else k : Fin (s + 1 + 3)) : ℕ) = _
  split_ifs <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_value then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_value"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_value ``Submission.DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_value

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLowerPermutationWithThreeInputs_first_block {s : ℕ} {x : M} (a b : TangentSpace I x)
    (u : Fin (s + 2) -> TangentSpace I x) (k : Fin (s + 1)) :
    metricTraceInput (I := I) a b u (reLowerPermutationWithThreeInputs s (Fin.castAdd 3 k)) =
      Function.update (Fin.tail u) (Fin.last s) a k := by
  classical
  have hk : (k : ℕ) < s + 1 := k.isLt
  have hcast : ((Fin.castAdd 3 k : Fin (s + 1 + 3)) : ℕ) = (k : ℕ) := rfl
  rw [metricTraceInput_apply]
  by_cases h1 : (k : ℕ) < s
  · have hv : ((reLowerPermutationWithThreeInputs s (Fin.castAdd 3 k) : Fin (s + 1 + 3)) : ℕ) = (k : ℕ) + 3 := by
      rw [reLowerPermutationWithThreeInputs_value, hcast, if_pos h1]
    have hne : k ≠ Fin.last s := by
      intro hcon
      rw [hcon] at h1
      simp at h1
    simp only [hv, Function.update_of_ne hne]
    rw [dif_neg (by omega : ¬((k : ℕ) + 3 = 0)), dif_neg (by omega : ¬((k : ℕ) + 3 = 1))]
    exact congrArg u (Fin.ext (by simp))
  · have hks : (k : ℕ) = s := by omega
    have hv : ((reLowerPermutationWithThreeInputs s (Fin.castAdd 3 k) : Fin (s + 1 + 3)) : ℕ) = 0 := by
      rw [reLowerPermutationWithThreeInputs_value, hcast, if_neg h1, if_pos hks]
    have hlast : k = Fin.last s := Fin.ext (by simp [hks])
    simp only [hv]
    rw [dif_pos (trivial : True), hlast, Function.update_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_first_block then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_first_block"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_first_block ``Submission.DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_first_block

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLowerPermutationWithThreeInputs_tail_zero {s : ℕ} {x : M} (a b : TangentSpace I x)
    (u : Fin (s + 2) -> TangentSpace I x) :
    metricTraceInput (I := I) a b u (reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) (0 : Fin 3))) = u 0 := by
  have hcast : ((Fin.natAdd (s + 1) (0 : Fin 3) : Fin (s + 1 + 3)) : ℕ) = s + 1 := by
    simp [Fin.natAdd]
  have hv : ((reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) (0 : Fin 3)) : Fin (s + 1 + 3)) : ℕ) = 2 := by
    rw [reLowerPermutationWithThreeInputs_value, hcast, if_neg (by omega), if_neg (by omega), if_pos rfl]
  rw [metricTraceInput_apply]
  simp only [hv]
  rw [dif_neg (by omega : ¬((2 : ℕ) = 0)), dif_neg (by omega : ¬((2 : ℕ) = 1))]
  exact congrArg u (Fin.ext (by simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_tail_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_tail_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_tail_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_tail_zero

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLowerPermutationWithThreeInputs_tail_one {s : ℕ} {x : M} (a b : TangentSpace I x)
    (u : Fin (s + 2) -> TangentSpace I x) :
    metricTraceInput (I := I) a b u (reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) (1 : Fin 3))) = b := by
  have hcast : ((Fin.natAdd (s + 1) (1 : Fin 3) : Fin (s + 1 + 3)) : ℕ) = s + 2 := by
    simp [Fin.natAdd]
  have hv : ((reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) (1 : Fin 3)) : Fin (s + 1 + 3)) : ℕ) = 1 := by
    rw [reLowerPermutationWithThreeInputs_value, hcast, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos rfl]
  rw [metricTraceInput_apply]
  simp only [hv]
  rw [dif_neg (by omega : ¬((1 : ℕ) = 0)), dif_pos (trivial : True)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_tail_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_tail_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_tail_one ``Submission.DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_tail_one

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLowerPermutationWithThreeInputs_tail_two {s : ℕ} {x : M} (a b : TangentSpace I x)
    (u : Fin (s + 2) -> TangentSpace I x) :
    metricTraceInput (I := I) a b u (reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) (2 : Fin 3))) =
      u (Fin.last (s + 1)) := by
  have hcast : ((Fin.natAdd (s + 1) (2 : Fin 3) : Fin (s + 1 + 3)) : ℕ) = s + 3 := by
    simp [Fin.natAdd]
  have hv : ((reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) (2 : Fin 3)) : Fin (s + 1 + 3)) : ℕ) = s + 3 := by
    rw [reLowerPermutationWithThreeInputs_value, hcast, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  rw [metricTraceInput_apply]
  simp only [hv]
  rw [dif_neg (by omega : ¬(s + 3 = 0)), dif_neg (by omega : ¬(s + 3 = 1))]
  exact congrArg u (Fin.ext (by simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_tail_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_tail_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_tail_two ``Submission.DifferentialGeometry.PDE.RicciFlow.reLowerPermutationWithThreeInputs_tail_two

def reLowerPair (g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (K : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2) :=
  metricTraceFirstTwoField (I := I) (M := M) (s := s + 2) g₂
    (Tensor0SField.domDomCongr (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) (reLowerPermutationWithThreeInputs s)
      (tensor0SFieldProduct (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (∞ : WithTop ℕ∞) T K))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLowerPair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLowerPair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLowerPair ``Submission.DifferentialGeometry.PDE.RicciFlow.reLowerPair

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLowerPair_eval (g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (K : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x)) (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) g₂ x basis gInv)
    (u : Fin (s + 2) -> TangentSpace I x) :
    Tensor0SSpace.eval (reLowerPair (I := I) g₂ T K x) u =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * (Tensor0SSpace.eval (T x)
          (Function.update (Fin.tail u) (Fin.last s) (basis i)) *
          Tensor0SSpace.eval (K x)
            (vec3 (I := I) (u 0) (basis j) (u (Fin.last (s + 1))))) := by
  classical
  with_unfolding_all
    rw [reLowerPair, traceField_eq_sum (I := I) g₂ _ basis gInv hinv u]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  change Tensor0SSpace.eval
      (Tensor0SSpace.domDomCongr
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) T K x)
        (reLowerPermutationWithThreeInputs s)) _ = _
  rw [Tensor0SSpace.eval_domDomCongr, tensor0SField_product_eval]
  congr 1
  · exact congrArg (Tensor0SSpace.eval (T x))
      (funext fun k => reLowerPermutationWithThreeInputs_first_block (I := I) (basis i) (basis j) u k)
  · refine congrArg (Tensor0SSpace.eval (K x)) (funext fun p => ?_)
    change metricTraceInput (I := I) (basis i) (basis j) u
        (reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) p)) = _
    fin_cases p
    · change metricTraceInput (I := I) (basis i) (basis j) u
          (reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) (0 : Fin 3))) =
        vec3 (I := I) (u 0) (basis j) (u (Fin.last (s + 1))) (0 : Fin 3)
      rw [reLowerPermutationWithThreeInputs_tail_zero (I := I) (basis i) (basis j) u]
      simp [vec3]
    · change metricTraceInput (I := I) (basis i) (basis j) u
          (reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) (1 : Fin 3))) =
        vec3 (I := I) (u 0) (basis j) (u (Fin.last (s + 1))) (1 : Fin 3)
      rw [reLowerPermutationWithThreeInputs_tail_one (I := I) (basis i) (basis j) u]
      simp [vec3]
    · change metricTraceInput (I := I) (basis i) (basis j) u
          (reLowerPermutationWithThreeInputs s (Fin.natAdd (s + 1) (2 : Fin 3))) =
        vec3 (I := I) (u 0) (basis j) (u (Fin.last (s + 1))) (2 : Fin 3)
      rw [reLowerPermutationWithThreeInputs_tail_two (I := I) (basis i) (basis j) u]
      simp [vec3]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLowerPair_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLowerPair_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLowerPair_eval ``Submission.DifferentialGeometry.PDE.RicciFlow.reLowerPair_eval

end Pair

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem reLower_eq_trace (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    reLower (I := I) g₁ g₂ T =
      metricTraceFirstTwoField (I := I) (M := M) (s := s + 1) g₂
        (Tensor0SField.domDomCongr (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (∞ : WithTop ℕ∞) (reLowerPermutationWithTwoInputs s)
          (tensor0SFieldProduct (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (∞ : WithTop ℕ∞) T (metricTensorField (I := I) g₁))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLower_eq_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLower_eq_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLower_eq_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.reLower_eq_trace


end DifferentialGeometry.PDE.RicciFlow
