import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace Tensor0SBundle

noncomputable section

open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem inner0S_comm
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A B = inner0S (I := I) g x s B A :=
  (tensor0SMetricData (I := I) g x s).inner_comm A B

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Tensor0SBundle.inner0S_comm then
    throwError "Refusing to shadow existing declaration Tensor0SBundle.inner0S_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `Tensor0SBundle.inner0S_comm ``Submission.Tensor0SBundle.inner0S_comm

theorem inner0S_sub_right
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B C : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A (B - C) =
      inner0S (I := I) g x s A B - inner0S (I := I) g x s A C := by
  rw [inner0S_comm (I := I) g x s A (B - C), inner0S_sub_left,
    inner0S_comm (I := I) g x s B A, inner0S_comm (I := I) g x s C A]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Tensor0SBundle.inner0S_sub_right then
    throwError "Refusing to shadow existing declaration Tensor0SBundle.inner0S_sub_right"
  Lean.modifyEnv fun env => Lean.addAlias env `Tensor0SBundle.inner0S_sub_right ``Submission.Tensor0SBundle.inner0S_sub_right

theorem inner0S_smul_left
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat) (c : Real)
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s (c • A) B = c * inner0S (I := I) g x s A B := by
  unfold inner0S MetricFiberData.inner
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Tensor0SBundle.inner0S_smul_left then
    throwError "Refusing to shadow existing declaration Tensor0SBundle.inner0S_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `Tensor0SBundle.inner0S_smul_left ``Submission.Tensor0SBundle.inner0S_smul_left

theorem inner0S_smul_right
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat) (c : Real)
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A (c • B) = c * inner0S (I := I) g x s A B := by
  rw [inner0S_comm (I := I) g x s A (c • B), inner0S_smul_left,
    inner0S_comm (I := I) g x s B A]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Tensor0SBundle.inner0S_smul_right then
    throwError "Refusing to shadow existing declaration Tensor0SBundle.inner0S_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `Tensor0SBundle.inner0S_smul_right ``Submission.Tensor0SBundle.inner0S_smul_right

theorem normSq0S_add
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s (A + B) =
      normSq0S (I := I) g x s A + 2 * inner0S (I := I) g x s A B +
        normSq0S (I := I) g x s B := by
  simp only [normSq0S_eq_inner, inner0S_add_left, inner0S_add_right]
  rw [inner0S_comm (I := I) g x s B A]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Tensor0SBundle.normSq0S_add then
    throwError "Refusing to shadow existing declaration Tensor0SBundle.normSq0S_add"
  Lean.modifyEnv fun env => Lean.addAlias env `Tensor0SBundle.normSq0S_add ``Submission.Tensor0SBundle.normSq0S_add

theorem normSq0S_sub
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s (A - B) =
      normSq0S (I := I) g x s A - 2 * inner0S (I := I) g x s A B +
        normSq0S (I := I) g x s B := by
  simp only [normSq0S_eq_inner, inner0S_sub_left, inner0S_sub_right]
  rw [inner0S_comm (I := I) g x s B A]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Tensor0SBundle.normSq0S_sub then
    throwError "Refusing to shadow existing declaration Tensor0SBundle.normSq0S_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `Tensor0SBundle.normSq0S_sub ``Submission.Tensor0SBundle.normSq0S_sub

theorem normSq0S_neg
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s (-A) = normSq0S (I := I) g x s A := by
  have h : (-A : Tensor0SSpace s I x) = (-1 : Real) • A := by
    rw [neg_one_smul]
  rw [h]
  simp only [normSq0S_eq_inner]
  rw [inner0S_smul_left, inner0S_smul_right]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Tensor0SBundle.normSq0S_neg then
    throwError "Refusing to shadow existing declaration Tensor0SBundle.normSq0S_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `Tensor0SBundle.normSq0S_neg ``Submission.Tensor0SBundle.normSq0S_neg

theorem abs_inner0S_le
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    |inner0S (I := I) g x s A B| ≤
      Real.sqrt (normSq0S (I := I) g x s A) *
        Real.sqrt (normSq0S (I := I) g x s B) := by
  have hcs := Real.sqrt_le_sqrt (inner0S_sq_le_mul (I := I) g x s A B)
  rwa [Real.sqrt_sq_eq_abs,
    Real.sqrt_mul (normSq0S_nonneg (I := I) g x s A)] at hcs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Tensor0SBundle.abs_inner0S_le then
    throwError "Refusing to shadow existing declaration Tensor0SBundle.abs_inner0S_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Tensor0SBundle.abs_inner0S_le ``Submission.Tensor0SBundle.abs_inner0S_le

theorem two_inner0S_le
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    2 * inner0S (I := I) g x s A B ≤
      normSq0S (I := I) g x s A + normSq0S (I := I) g x s B := by
  have h := normSq0S_nonneg (I := I) g x s (A - B)
  rw [normSq0S_sub] at h
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Tensor0SBundle.two_inner0S_le then
    throwError "Refusing to shadow existing declaration Tensor0SBundle.two_inner0S_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Tensor0SBundle.two_inner0S_le ``Submission.Tensor0SBundle.two_inner0S_le

theorem neg_two_inner0S_le
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    -(normSq0S (I := I) g x s A + normSq0S (I := I) g x s B) ≤
      2 * inner0S (I := I) g x s A B := by
  have h := normSq0S_nonneg (I := I) g x s (A + B)
  rw [normSq0S_add] at h
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Tensor0SBundle.neg_two_inner0S_le then
    throwError "Refusing to shadow existing declaration Tensor0SBundle.neg_two_inner0S_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Tensor0SBundle.neg_two_inner0S_le ``Submission.Tensor0SBundle.neg_two_inner0S_le

theorem normSq0S_add_le
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s (A + B) ≤
      2 * normSq0S (I := I) g x s A + 2 * normSq0S (I := I) g x s B := by
  have h := two_inner0S_le (I := I) g x s A B
  rw [normSq0S_add]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Tensor0SBundle.normSq0S_add_le then
    throwError "Refusing to shadow existing declaration Tensor0SBundle.normSq0S_add_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Tensor0SBundle.normSq0S_add_le ``Submission.Tensor0SBundle.normSq0S_add_le

theorem normSq0S_sub_le
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s (A - B) ≤
      2 * normSq0S (I := I) g x s A + 2 * normSq0S (I := I) g x s B := by
  have h := neg_two_inner0S_le (I := I) g x s A B
  rw [normSq0S_sub]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Tensor0SBundle.normSq0S_sub_le then
    throwError "Refusing to shadow existing declaration Tensor0SBundle.normSq0S_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Tensor0SBundle.normSq0S_sub_le ``Submission.Tensor0SBundle.normSq0S_sub_le

theorem sqrt_normSq0S_add_le
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    Real.sqrt (normSq0S (I := I) g x s (A + B)) ≤
      Real.sqrt (normSq0S (I := I) g x s A) +
        Real.sqrt (normSq0S (I := I) g x s B) := by
  have hA := normSq0S_nonneg (I := I) g x s A
  have hB := normSq0S_nonneg (I := I) g x s B
  have hsA : Real.sqrt (normSq0S (I := I) g x s A) ^ 2 =
      normSq0S (I := I) g x s A := Real.sq_sqrt hA
  have hsB : Real.sqrt (normSq0S (I := I) g x s B) ^ 2 =
      normSq0S (I := I) g x s B := Real.sq_sqrt hB
  have hcs : inner0S (I := I) g x s A B ≤
      Real.sqrt (normSq0S (I := I) g x s A) *
        Real.sqrt (normSq0S (I := I) g x s B) :=
    le_trans (le_abs_self _) (abs_inner0S_le (I := I) g x s A B)
  have hexp : (Real.sqrt (normSq0S (I := I) g x s A) +
        Real.sqrt (normSq0S (I := I) g x s B)) ^ 2 =
      normSq0S (I := I) g x s A +
        2 * (Real.sqrt (normSq0S (I := I) g x s A) *
          Real.sqrt (normSq0S (I := I) g x s B)) +
        normSq0S (I := I) g x s B := by
    rw [add_sq, hsA, hsB]; ring
  have key : normSq0S (I := I) g x s (A + B) ≤
      (Real.sqrt (normSq0S (I := I) g x s A) +
        Real.sqrt (normSq0S (I := I) g x s B)) ^ 2 := by
    rw [normSq0S_add, hexp]
    linarith
  calc Real.sqrt (normSq0S (I := I) g x s (A + B))
      ≤ Real.sqrt ((Real.sqrt (normSq0S (I := I) g x s A) +
          Real.sqrt (normSq0S (I := I) g x s B)) ^ 2) := Real.sqrt_le_sqrt key
    _ = Real.sqrt (normSq0S (I := I) g x s A) +
          Real.sqrt (normSq0S (I := I) g x s B) :=
        Real.sqrt_sq (by positivity)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Tensor0SBundle.sqrt_normSq0S_add_le then
    throwError "Refusing to shadow existing declaration Tensor0SBundle.sqrt_normSq0S_add_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Tensor0SBundle.sqrt_normSq0S_add_le ``Submission.Tensor0SBundle.sqrt_normSq0S_add_le

theorem sqrt_normSq0S_sub_le
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    Real.sqrt (normSq0S (I := I) g x s (A - B)) ≤
      Real.sqrt (normSq0S (I := I) g x s A) +
        Real.sqrt (normSq0S (I := I) g x s B) := by
  rw [sub_eq_add_neg]
  refine le_trans (sqrt_normSq0S_add_le (I := I) g x s A (-B)) ?_
  rw [normSq0S_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Tensor0SBundle.sqrt_normSq0S_sub_le then
    throwError "Refusing to shadow existing declaration Tensor0SBundle.sqrt_normSq0S_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Tensor0SBundle.sqrt_normSq0S_sub_le ``Submission.Tensor0SBundle.sqrt_normSq0S_sub_le

end

end Tensor0SBundle
