import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.LeastEigenvalue
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

private theorem matrix_quad_abs_le_of_component_bound
    {n : Type*} [Fintype n] (A : Matrix n n Real) {R : Real} (hR : 0 ≤ R)
    (hA : ∀ i j, |A i j| ≤ R) (c : n → Real) :
    |∑ i, ∑ j, c i * c j * A i j| ≤
      (Fintype.card n : Real) * R * ∑ i, c i ^ 2 := by
  calc
    |∑ i, ∑ j, c i * c j * A i j|
        ≤ ∑ i, ∑ j, |c i * c j * A i j| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |c i| * |c j| * R := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (hA i j)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = R * (∑ i, |c i|) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ R * ((Fintype.card n : Real) * ∑ i, c i ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hR
          have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset n)
            (fun i => |c i|) (fun _ => (1 : Real))
          simpa only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, sq_abs, mul_comm] using hcs
    _ = (Fintype.card n : Real) * R * ∑ i, c i ^ 2 := by ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.matrix_quad_abs_le_of_component_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.DimensionThree.matrix_quad_abs_le_of_component_bound target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem curvatureOperatorLowerBoundAt_iff_le_leastCurvatureOperatorEigenvalueAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) (K : Real) :
    curvatureOperatorLowerBoundAt (I := I) g x A K ↔
      -K ≤ leastCurvatureOperatorEigenvalueAt (I := I) g x A := by
  rw [curvatureOperatorLowerBoundAt_iff_neg_leastCurvatureOperatorEigenvalueAt_le basis horth]
  constructor <;> intro h <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.DimensionThree.curvatureOperatorLowerBoundAt_iff_le_leastCurvatureOperatorEigenvalueAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.DimensionThree.curvatureOperatorLowerBoundAt_iff_le_leastCurvatureOperatorEigenvalueAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.DimensionThree.curvatureOperatorLowerBoundAt_iff_le_leastCurvatureOperatorEigenvalueAt ``Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.curvatureOperatorLowerBoundAt_iff_le_leastCurvatureOperatorEigenvalueAt

theorem curvatureOperatorLowerBoundAt_sqrt_normSq0S
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    curvatureOperatorLowerBoundAt (I := I) g x A
      (3 * Real.sqrt (normSq0S (I := I) g x 4 A.1)) := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) g x hdim
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Fin 3)) :=
    metricInverseInBasis_of_orthonormal (I := I) g basis horth
  have hcomp : ∀ i j, |curvatureOperatorMatrixAt (I := I) x basis A i j| ≤
      Real.sqrt (normSq0S (I := I) g x 4 A.1) := by
    intro i j
    have h := abs_component0S_le_sqrt_normSq0S (I := I) g basis hinv A.1
      (slots4 (bivectorIndex3 i).1 (bivectorIndex3 i).2
        (bivectorIndex3 j).2 (bivectorIndex3 j).1)
    change |rm04CompAt (I := I) basis A.1
      (bivectorIndex3 i).1 (bivectorIndex3 i).2
      (bivectorIndex3 j).2 (bivectorIndex3 j).1| ≤ _ at h
    simpa only [rm04CompAt_apply, curvatureOperatorMatrixAt, tensor04StandardAt_apply] using h
  intro n c v w
  rw [algebraicCurvatureOperatorQuadraticEval_eq_bivectorQuad (I := I) x basis A c v w,
    algebraicCurvatureIdentityQuadraticEval_eq_bivectorNormSq (I := I) g x c v w basis horth]
  let b : Fin 3 → Real := fun i => ∑ k : Fin n, c k *
    (basis.repr (v k) (bivectorIndex3 i).1 * basis.repr (w k) (bivectorIndex3 i).2 -
      basis.repr (v k) (bivectorIndex3 i).2 * basis.repr (w k) (bivectorIndex3 i).1)
  have hbound := matrix_quad_abs_le_of_component_bound
    (curvatureOperatorMatrixAt (I := I) x basis A) (Real.sqrt_nonneg _) hcomp b
  simp only [Fintype.card_fin, Nat.cast_ofNat] at hbound
  have hlower := (abs_le.mp hbound).1
  change 0 ≤ (∑ i, ∑ j, b i * b j * curvatureOperatorMatrixAt (I := I) x basis A i j) +
    3 * Real.sqrt (normSq0S (I := I) g x 4 A.1) * ∑ i, b i ^ 2
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.DimensionThree.curvatureOperatorLowerBoundAt_sqrt_normSq0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.DimensionThree.curvatureOperatorLowerBoundAt_sqrt_normSq0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.DimensionThree.curvatureOperatorLowerBoundAt_sqrt_normSq0S ``Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.curvatureOperatorLowerBoundAt_sqrt_normSq0S

theorem exists_curvatureOperatorLowerBoundAt_metricRm04
    [FiniteDimensional Real E] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 3) :
    ∃ K : Real, 0 < K ∧ ∀ x : M,
      curvatureOperatorLowerBoundAt (I := I) g x
        ⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ K := by
  obtain ⟨K, _, hK⟩ := exists_rm04_bound (I := I) g
  refine ⟨3 * Real.sqrt K + 1, by positivity, fun x => ?_⟩
  have hdimx : Module.finrank Real (TangentSpace I x) = 3 := hdim
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) g x hdimx
  rw [curvatureOperatorLowerBoundAt_iff_le_leastCurvatureOperatorEigenvalueAt
    (I := I) g x basis horth]
  have h := curvatureOperatorLowerBoundAt_sqrt_normSq0S (I := I) g x hdimx
    ⟨metricRm04 (I := I) g x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩
  rw [curvatureOperatorLowerBoundAt_iff_le_leastCurvatureOperatorEigenvalueAt
    (I := I) g x basis horth] at h
  have hsqrt := Real.sqrt_le_sqrt (hK x)
  dsimp only at h
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.DimensionThree.exists_curvatureOperatorLowerBoundAt_metricRm04 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.DimensionThree.exists_curvatureOperatorLowerBoundAt_metricRm04"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.DimensionThree.exists_curvatureOperatorLowerBoundAt_metricRm04 ``Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.exists_curvatureOperatorLowerBoundAt_metricRm04

end DifferentialGeometry.Geometry.Curvature.DimensionThree
