import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.TensorCommutator
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.PointwiseBound
import Mathlib.Topology.Order.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.FiberBundle _root_.NormedSpace _root_.Filter _root_.CovariantDerivative _root_.Submission.CovariantDerivative _root_.Submission.DifferentialGeometry.Geometry.Curvature.CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [BoundarylessManifold I M]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [T2Space M]
    [BoundarylessManifold I M] in
lemma exists_fiberNormSq_le_factor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (T : TensorRSSpace r s I x) :
    ∃ B : ℝ, 0 ≤ B ∧
      riemannianFiberNormSq (I := I) (M := M) g r s x T ≤ ‖T‖ ^ 2 * B := by
  obtain ⟨Ab, hAb_nonneg, hbound⟩ :=
    exists_riemannianFiberNormSq_pointwise_bound (I := I) (M := M) g r s x T
  refine ⟨_, ?_, hbound⟩
  refine mul_nonneg (pow_nonneg ?_ _) (pow_nonneg hAb_nonneg _)
  unfold metricInnerOpNorm
  exact norm_nonneg (g.inner x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.exists_fiberNormSq_le_factor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.exists_fiberNormSq_le_factor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.exists_fiberNormSq_le_factor ``Submission.DifferentialGeometry.Geometry.Curvature.exists_fiberNormSq_le_factor

noncomputable def curvValueFrameScalar
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v w : TangentSpace I x) (T : TensorRSSpace r s I x) : ℝ :=
  (exists_fiberNormSq_le_factor (I := I) (M := M) g r s x
    (riemannOp (tensorCov (I := I) g r s) x v w T)).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvValueFrameScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvValueFrameScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvValueFrameScalar ``Submission.DifferentialGeometry.Geometry.Curvature.curvValueFrameScalar

omit [NeZero (Module.finrank ℝ E)] in
lemma curvValueFrameScalar_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v w : TangentSpace I x) (T : TensorRSSpace r s I x) :
    0 ≤ curvValueFrameScalar (I := I) (M := M) g r s x v w T :=
  (exists_fiberNormSq_le_factor (I := I) (M := M) g r s x
    (riemannOp (tensorCov (I := I) g r s) x v w T)).choose_spec.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvValueFrameScalar_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvValueFrameScalar_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvValueFrameScalar_nonneg ``Submission.DifferentialGeometry.Geometry.Curvature.curvValueFrameScalar_nonneg

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannOp_tensorCov_fiberNormSq_le_frameScalar
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v w : TangentSpace I x) (T : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x
        (riemannOp (tensorCov (I := I) g r s) x v w T) ≤
      ‖riemannOp (tensorCov (I := I) g r s) x v w T‖ ^ 2 *
        curvValueFrameScalar (I := I) (M := M) g r s x v w T :=
  (exists_fiberNormSq_le_factor (I := I) (M := M) g r s x
    (riemannOp (tensorCov (I := I) g r s) x v w T)).choose_spec.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.riemannOp_tensorCov_fiberNormSq_le_frameScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.riemannOp_tensorCov_fiberNormSq_le_frameScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.riemannOp_tensorCov_fiberNormSq_le_frameScalar ``Submission.DifferentialGeometry.Geometry.Curvature.riemannOp_tensorCov_fiberNormSq_le_frameScalar

noncomputable def curvContractionFiberNormBoundSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (Z : Π b : M, TensorRSSpace r s I b)
    (x : M) : ℝ :=
  ‖riemannOp (tensorCov (I := I) g r s) x (X x) (Y x) (Z x)‖ ^ 2 *
    curvValueFrameScalar (I := I) (M := M) g r s x (X x) (Y x) (Z x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvContractionFiberNormBoundSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvContractionFiberNormBoundSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvContractionFiberNormBoundSq ``Submission.DifferentialGeometry.Geometry.Curvature.curvContractionFiberNormBoundSq

omit [NeZero (Module.finrank ℝ E)] in
lemma curvContractionFiberNormBoundSq_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (Z : Π b : M, TensorRSSpace r s I b)
    (x : M) :
    0 ≤ curvContractionFiberNormBoundSq (I := I) (M := M) g r s X Y Z x := by
  unfold curvContractionFiberNormBoundSq
  exact mul_nonneg (sq_nonneg _)
    (curvValueFrameScalar_nonneg (I := I) (M := M) g r s x (X x) (Y x) (Z x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvContractionFiberNormBoundSq_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvContractionFiberNormBoundSq_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvContractionFiberNormBoundSq_nonneg ``Submission.DifferentialGeometry.Geometry.Curvature.curvContractionFiberNormBoundSq_nonneg

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannOp_tensorCov_fiberNormSq_le_boundSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (Z : Π b : M, TensorRSSpace r s I b)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r s x
        (riemannOp (tensorCov (I := I) g r s) x (X x) (Y x) (Z x)) ≤
      curvContractionFiberNormBoundSq (I := I) (M := M) g r s X Y Z x :=
  riemannOp_tensorCov_fiberNormSq_le_frameScalar (I := I) (M := M) g r s x
    (X x) (Y x) (Z x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.riemannOp_tensorCov_fiberNormSq_le_boundSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.riemannOp_tensorCov_fiberNormSq_le_boundSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.riemannOp_tensorCov_fiberNormSq_le_boundSq ``Submission.DifferentialGeometry.Geometry.Curvature.riemannOp_tensorCov_fiberNormSq_le_boundSq

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_bound_riemannOp_tensorCov_fiberNormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (Z : Π b : M, TensorRSSpace r s I b)
    (hbdd : BddAbove (Set.range
      (fun x : M => curvContractionFiberNormBoundSq (I := I) (M := M) g r s X Y Z x))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r s x
        (riemannOp (tensorCov (I := I) g r s) x (X x) (Y x) (Z x)) ≤ K := by
  classical
  set f : M → ℝ := fun x => curvContractionFiberNormBoundSq (I := I) (M := M) g r s X Y Z x
    with hf_def
  set K : ℝ := _root_.SupSet.sSup (Set.range f) with hK_def
  have h_le_K : ∀ x : M, f x ≤ K := fun x => le_csSup hbdd (Set.mem_range_self x)
  refine ⟨K, ?_, ?_⟩
  · rcases isEmpty_or_nonempty M with hM | hM
    · have hrange : Set.range f = (∅ : Set ℝ) := by
        rw [Set.range_eq_empty_iff]; exact hM
      rw [hK_def, hrange, Real.sSup_empty]
    · obtain ⟨x₀⟩ := hM
      exact le_trans (curvContractionFiberNormBoundSq_nonneg (I := I) (M := M) g r s X Y Z x₀)
        (h_le_K x₀)
  · intro x
    exact le_trans
      (riemannOp_tensorCov_fiberNormSq_le_boundSq (I := I) (M := M) g r s X Y Z x)
      (h_le_K x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.exists_bound_riemannOp_tensorCov_fiberNormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.exists_bound_riemannOp_tensorCov_fiberNormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.exists_bound_riemannOp_tensorCov_fiberNormSq ``Submission.DifferentialGeometry.Geometry.Curvature.exists_bound_riemannOp_tensorCov_fiberNormSq

end Curvature
end Geometry
end DifferentialGeometry

end
