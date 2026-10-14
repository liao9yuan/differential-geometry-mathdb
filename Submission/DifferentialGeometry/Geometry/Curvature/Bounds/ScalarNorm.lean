import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Rough

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open _root_.Submission.DifferentialGeometry.Geometry.Operator
namespace DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
theorem scalar_abs_le_rm (g : SmoothRiemannianMetric I M) (x : M) :
    |metricScalarAt (I := I) (M := M) g x| ≤
      (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
        Real.sqrt (normSq0S (I := I) g x 4
          (metricRm04At (I := I) (M := M) g x)) := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) :=
    DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON
  have htrace : metricScalarAt (I := I) (M := M) g x =
      ∑ i, metricRicciAt (I := I) (M := M) g x
        (vec2 (I := I) (basis i) (basis i)) := by
    rw [metricScalarAt_def (I := I) g x,
      metricTracePair0SAt_eq_sum_basis (I := I) g basis
        (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x))))
        hinv (metricRicciAt (I := I) (M := M) g x)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp only [identityInvMetric_apply_self, one_mul]
    · intro j _ hji
      have hij : i ≠ j := fun hij => hji hij.symm
      rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne hij, _root_.MulZeroClass.zero_mul]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rw [htrace]
  calc
    |∑ i, metricRicciAt (I := I) (M := M) g x
        (vec2 (I := I) (basis i) (basis i))| ≤
        ∑ i, |metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace I x)),
        (Module.finrank ℝ (TangentSpace I x) : ℝ) *
          Real.sqrt (normSq0S (I := I) g x 4
            (metricRm04At (I := I) (M := M) g x)) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Fintype.card_fin] using
        metricRicciComp_le (I := I) (M := M) g basis hON i i
    _ = (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
        Real.sqrt (normSq0S (I := I) g x 4
          (metricRm04At (I := I) (M := M) g x)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm ``Submission.DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm

omit [SigmaCompactSpace M] in
theorem metricScalarAt_eq_zero_of_finrank_eq_zero
    (g : SmoothRiemannianMetric I M) (hE : Module.finrank ℝ E = 0) (x : M) :
    metricScalarAt (I := I) g x = 0 := by
  have h := scalar_abs_le_rm g x
  change |metricScalarAt (I := I) g x| ≤ (Module.finrank ℝ E : ℝ) ^ 2 * _ at h
  simpa only [hE, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), _root_.MulZeroClass.zero_mul, abs_nonpos_iff] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricScalarAt_eq_zero_of_finrank_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricScalarAt_eq_zero_of_finrank_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricScalarAt_eq_zero_of_finrank_eq_zero ``Submission.DifferentialGeometry.Geometry.Curvature.metricScalarAt_eq_zero_of_finrank_eq_zero

omit [SigmaCompactSpace M] in
theorem sq_mul_scalar_abs_le_of_rm_bound
    (g : SmoothRiemannianMetric I M) (x : M) {r : ℝ}
    (hbound : r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1) :
    r ^ 2 * |metricScalarAt g x| ≤ (Module.finrank ℝ E : ℝ) ^ 2 := by
  have hsq : (r ^ 2 * Real.sqrt (normSq0S g x 4 (metricRm04At g x))) ^ 2 ≤ 1 := by
    rw [mul_pow, ← pow_mul, Real.sq_sqrt (normSq0S_nonneg _ _ _ _)]
    exact hbound
  have hnorm : r ^ 2 * Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤ 1 := by
    nlinarith
  have hscalar := scalar_abs_le_rm g x
  change |metricScalarAt g x| ≤ (Module.finrank ℝ E : ℝ) ^ 2 * _ at hscalar
  have hscaled := mul_le_mul_of_nonneg_right hscalar (sq_nonneg r)
  have hdim := mul_le_mul_of_nonneg_left hnorm (sq_nonneg (Module.finrank ℝ E : ℝ))
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.sq_mul_scalar_abs_le_of_rm_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.sq_mul_scalar_abs_le_of_rm_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.sq_mul_scalar_abs_le_of_rm_bound ``Submission.DifferentialGeometry.Geometry.Curvature.sq_mul_scalar_abs_le_of_rm_bound

omit [SigmaCompactSpace M] in
theorem scalar_abs_le_div_sq_of_rm_bound
    (g : SmoothRiemannianMetric I M) (x : M) {r : ℝ} (hr : r ≠ 0)
    (hbound : r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1) :
    |metricScalarAt g x| ≤ (Module.finrank ℝ E : ℝ) ^ 2 / r ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_ne_zero hr)).mpr
  simpa only [mul_comm] using sq_mul_scalar_abs_le_of_rm_bound g x hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.scalar_abs_le_div_sq_of_rm_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.scalar_abs_le_div_sq_of_rm_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.scalar_abs_le_div_sq_of_rm_bound ``Submission.DifferentialGeometry.Geometry.Curvature.scalar_abs_le_div_sq_of_rm_bound

end DifferentialGeometry.Geometry.Curvature
