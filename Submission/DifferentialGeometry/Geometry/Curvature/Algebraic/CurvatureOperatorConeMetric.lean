import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorCone
import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M]

def algebraicCurvatureIdentityQuadraticEval
    (g : SmoothRiemannianMetric I M) {x : M} {n : Nat}
    (c : Fin n → Real) (v w : Fin n → TangentSpace I x) : Real :=
  ∑ i, ∑ j, c i * c j *
    ((g.inner x (v i) (v j)) * (g.inner x (w i) (w j)) -
      (g.inner x (v i) (w j)) * (g.inner x (w i) (v j)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureIdentityQuadraticEval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicCurvatureIdentityQuadraticEval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureIdentityQuadraticEval ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicCurvatureIdentityQuadraticEval

def curvatureOperatorLowerBoundAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) (K : Real) : Prop :=
  ∀ (n : Nat) (c : Fin n → Real) (v w : Fin n → TangentSpace I x),
    0 ≤ algebraicCurvatureOperatorQuadraticEval (I := I) (M := M) A c v w +
      K * algebraicCurvatureIdentityQuadraticEval (I := I) g c v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt

noncomputable def leastCurvatureOperatorEigenvalueAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) : Real :=
  -_root_.InfSet.sInf {K : Real | curvatureOperatorLowerBoundAt (I := I) g x A K}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt ``Submission.DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt

section Scaling

omit [FiniteDimensional Real E] [CompleteSpace E]
  [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M]

open scoped _root_.Pointwise

theorem curvatureOperatorLowerBoundAt_smul_iff
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    {c : Real} (hc : 0 < c) (K : Real) :
    curvatureOperatorLowerBoundAt (I := I) g x (c • A) K ↔
      curvatureOperatorLowerBoundAt (I := I) g x A (K / c) := by
  have heq : ∀ n (a : Fin n → Real) (v w : Fin n → TangentSpace I x),
      algebraicCurvatureOperatorQuadraticEval (I := I) (c • A) a v w +
          K * algebraicCurvatureIdentityQuadraticEval (I := I) g a v w =
        c * (algebraicCurvatureOperatorQuadraticEval (I := I) A a v w +
          (K / c) * algebraicCurvatureIdentityQuadraticEval (I := I) g a v w) := by
    intro n a v w
    have hscale : algebraicCurvatureOperatorQuadraticEval (I := I) (c • A) a v w =
        c * algebraicCurvatureOperatorQuadraticEval (I := I) A a v w := by
      simp only [algebraicCurvatureOperatorQuadraticEval, tensor04StandardAt_apply,
        SetLike.val_smul, smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hscale]
    field_simp
  constructor
  · intro h n a v w
    have hh := h n a v w
    rw [heq] at hh
    exact (mul_nonneg_iff_of_pos_left hc).mp hh
  · intro h n a v w
    rw [heq]
    exact mul_nonneg hc.le (h n a v w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_smul_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_smul_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_smul_iff ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_smul_iff

private theorem leastCurvatureOperatorEigenvalueAt_smul_of_pos
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    {c : Real} (hc : 0 < c) :
    leastCurvatureOperatorEigenvalueAt (I := I) g x (c • A) =
      c * leastCurvatureOperatorEigenvalueAt (I := I) g x A := by
  have hset : {K : Real | curvatureOperatorLowerBoundAt (I := I) g x (c • A) K} =
      c • {K : Real | curvatureOperatorLowerBoundAt (I := I) g x A K} := by
    ext K
    rw [Set.mem_ofPred_eq, curvatureOperatorLowerBoundAt_smul_iff (I := I) g x A hc]
    constructor
    · intro hK
      exact ⟨K / c, hK, by simp only [smul_eq_mul]; field_simp⟩
    · rintro ⟨k, hk, heq⟩
      change c * k = K at heq
      rw [← heq, mul_div_cancel_left₀ _ hc.ne']
      exact hk
  unfold leastCurvatureOperatorEigenvalueAt
  rw [hset, Real.sInf_smul_of_nonneg hc.le]
  simp only [smul_eq_mul, mul_neg]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_smul_of_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_smul_of_pos target :: scope.openDecls } }

@[simp] theorem leastCurvatureOperatorEigenvalueAt_zero
    (g : SmoothRiemannianMetric I M) (x : M) :
    leastCurvatureOperatorEigenvalueAt (I := I) g x 0 = 0 := by
  have h := leastCurvatureOperatorEigenvalueAt_smul_of_pos (I := I) g x 0
    (by norm_num : 0 < (2 : Real))
  rw [smul_zero] at h
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_zero ``Submission.DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_zero

theorem leastCurvatureOperatorEigenvalueAt_smul_of_nonneg
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    {c : Real} (hc : 0 ≤ c) :
    leastCurvatureOperatorEigenvalueAt (I := I) g x (c • A) =
      c * leastCurvatureOperatorEigenvalueAt (I := I) g x A := by
  rcases hc.eq_or_lt with hzero | hpos
  · rw [← hzero, zero_smul, leastCurvatureOperatorEigenvalueAt_zero, _root_.MulZeroClass.zero_mul]
  · exact leastCurvatureOperatorEigenvalueAt_smul_of_pos (I := I) g x A hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_smul_of_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_smul_of_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_smul_of_nonneg ``Submission.DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_smul_of_nonneg

end Scaling

omit [SigmaCompactSpace M] in
theorem metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) ↔
      ∀ (n : Nat) (c : Fin n → Real)
        (v w : Fin n → TangentSpace I x),
        0 ≤ ∑ i, ∑ j, c i * c j *
          metricRm04StandardAt (I := I) (M := M) g x
            (v i) (w i) (w j) (v j) := by
  simp [algebraicCurvatureOperatorQuadraticEval,
    metricRm04StandardAt_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff ``Submission.DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff

end DifferentialGeometry.Geometry.Curvature
