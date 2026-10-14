import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita
import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling
import Submission.DifferentialGeometry.Geometry.Operator.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
theorem metricRm_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm04 (I := I) (M := M) (scaleMetric (I := I) c hc g) x =
      c • metricRm04 (I := I) (M := M) g x := by
  ext v
  have hv :
      v = vec4 (I := I) (v 0) (v 1) (v 2) (v 3) := by
    funext i
    fin_cases i <;> simp [vec4]
  rw [hv]
  simp [metricRm04, metricCov, scaleMetric_inner, lcConn_scaleMetric,
    smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricRm_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricRm_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricRm_scale ``Submission.DifferentialGeometry.Geometry.Curvature.metricRm_scale

omit [SigmaCompactSpace M] in
theorem metricRmStandard_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    metricRm04StandardAt (I := I) (M := M) (scaleMetric (I := I) c hc g)
        x X Y Z W =
      c * metricRm04StandardAt (I := I) (M := M) g x X Y Z W := by
  have h := congrArg
    (fun Rm : Tensor04At (I := I) (M := M) x =>
      Rm (vec4 (I := I) X Y Z W))
    (metricRm_scale (I := I) c hc g x)
  simpa [metricRm04_apply, metricRm04StandardAt_apply, smul_eq_mul] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricRmStandard_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricRmStandard_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricRmStandard_scale ``Submission.DifferentialGeometry.Geometry.Curvature.metricRmStandard_scale

omit [SigmaCompactSpace M] in
theorem metricAlgebraicCurvatureTensorAt_scaleMetric
    [IsManifold I 2 M] [IsManifold I 3 M]
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    metricAlgebraicCurvatureTensorAt (I := I) (M := M)
        (scaleMetric (I := I) c hc g) x =
      c • metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x := by
  apply Subtype.ext
  change metricRm04At (I := I) (M := M) (scaleMetric (I := I) c hc g) x =
    ((c • metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x :
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
        Tensor04At (I := I) (M := M) x)
  rw [Submodule.coe_smul_of_tower, metricAlgebraicCurvatureTensorAt_coe]
  simpa only [metricRm04_apply] using metricRm_scale (I := I) c hc g x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_scaleMetric ``Submission.DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_scaleMetric

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem algebraicCurvatureIdentityQuadraticEval_scaleMetric
    (a : Real) (ha : 0 < a) (g : SmoothRiemannianMetric I M)
    {x : M} {n : Nat} (c : Fin n → Real)
    (v w : Fin n → TangentSpace I x) :
    algebraicCurvatureIdentityQuadraticEval (I := I)
        (scaleMetric (I := I) a ha g) c v w =
      a ^ 2 * algebraicCurvatureIdentityQuadraticEval (I := I) g c v w := by
  unfold algebraicCurvatureIdentityQuadraticEval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [scaleMetric_inner]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureIdentityQuadraticEval_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicCurvatureIdentityQuadraticEval_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureIdentityQuadraticEval_scaleMetric ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicCurvatureIdentityQuadraticEval_scaleMetric

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem algebraicCurvatureOperatorQuadraticEval_smul
    (a : Real) {x : M} {n : Nat}
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (c : Fin n → Real) (v w : Fin n → TangentSpace I x) :
    algebraicCurvatureOperatorQuadraticEval (I := I) (M := M) (a • A) c v w =
      a * algebraicCurvatureOperatorQuadraticEval (I := I) (M := M) A c v w := by
  unfold algebraicCurvatureOperatorQuadraticEval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Submodule.coe_smul_of_tower, tensor04StandardAt, Tensor0SSpace.smul_apply,
    smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureOperatorQuadraticEval_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicCurvatureOperatorQuadraticEval_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureOperatorQuadraticEval_smul ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicCurvatureOperatorQuadraticEval_smul

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem curvatureOperatorLowerBoundAt_scaleMetric
    {a : Real} (ha : 0 < a) {g : SmoothRiemannianMetric I M} {x : M}
    {A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x} {K : Real} :
    curvatureOperatorLowerBoundAt (I := I) (scaleMetric (I := I) a ha g) x (a • A) K ↔
      curvatureOperatorLowerBoundAt (I := I) g x A (a * K) := by
  constructor
  · intro h n c v w
    have hbound := h n c v w
    rw [algebraicCurvatureOperatorQuadraticEval_smul,
      algebraicCurvatureIdentityQuadraticEval_scaleMetric] at hbound
    nlinarith
  · intro h n c v w
    have hbound := h n c v w
    rw [algebraicCurvatureOperatorQuadraticEval_smul,
      algebraicCurvatureIdentityQuadraticEval_scaleMetric]
    nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_scaleMetric ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_scaleMetric

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem metricRicciAt_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    metricRicciAt (I := I) (M := M) (scaleMetric (I := I) c hc g) x =
      metricRicciAt (I := I) (M := M) g x := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  ext slots
  simp [metricRicciAt, metricCov, lcConn_scaleMetric]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricRicciAt_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricRicciAt_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricRicciAt_scaleMetric ``Submission.DifferentialGeometry.Geometry.Curvature.metricRicciAt_scaleMetric

theorem metricScalarAt_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    metricScalarAt (I := I) (M := M) (scaleMetric (I := I) c hc g) x =
      c⁻¹ * metricScalarAt (I := I) (M := M) g x := by
  rw [metricScalarAt_def, metricScalarAt_def,
    DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_scaleMetric]
  rw [metricRicciAt_scaleMetric]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricScalarAt_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricScalarAt_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricScalarAt_scaleMetric ``Submission.DifferentialGeometry.Geometry.Curvature.metricScalarAt_scaleMetric

section

variable [T2Space M] [BoundarylessManifold I M]

theorem riemannOp_scaleMetric
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    riemannOp (LeviCivita (I := I) (scaleMetric c hc g)) x =
      riemannOp (LeviCivita (I := I) g) x := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have he : LeviCivita (I := I) (scaleMetric c hc g) = LeviCivita (I := I) g :=
    lcConn_scaleMetric c hc g
  simp only [he]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.riemannOp_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.riemannOp_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.riemannOp_scaleMetric ``Submission.DifferentialGeometry.Geometry.Curvature.riemannOp_scaleMetric

theorem ricciTensor_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) (scaleMetric (I := I) c hc g) x v w =
      ricciTensor (I := I) g x v w := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  simp [ricciTensor_apply, ricciEndo, LeviCivita, lcConn_scaleMetric]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciTensor_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciTensor_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciTensor_scaleMetric ``Submission.DifferentialGeometry.Geometry.Curvature.ricciTensor_scaleMetric

theorem ricciSharp_scaleMetric
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    ricciSharp (I := I) (scaleMetric c hc g) x = c⁻¹ • ricciSharp (I := I) g x := by
  ext v
  apply DifferentialGeometry.Geometry.Operator.metricFlatLinear_injective (I := I) (scaleMetric c hc g) x
  ext w
  change (scaleMetric c hc g).inner x (ricciSharp (scaleMetric c hc g) x v) w =
    (scaleMetric c hc g).inner x (c⁻¹ • ricciSharp g x v) w
  rw [inner_ricciSharp, ricciTensor_scaleMetric, scaleMetric_inner, map_smul,
    smul_apply, smul_eq_mul, inner_ricciSharp]
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciSharp_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciSharp_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciSharp_scaleMetric ``Submission.DifferentialGeometry.Geometry.Curvature.ricciSharp_scaleMetric


omit [BoundarylessManifold I M] in
theorem metricRm04At_scaleMetric_inv_sqrt_smul
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 4 → TangentSpace I x) :
    metricRm04At (scaleMetric c hc g) x (fun i => (Real.sqrt c)⁻¹ • v i) =
      c⁻¹ * metricRm04At g x v := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have heq : metricRm04At (scaleMetric c hc g) x = c • metricRm04At g x :=
    metricRm_scale c hc g x
  rw [heq, smul_apply]
  have hs := (metricRm04At g x).map_smul_univ (fun _ => (Real.sqrt c)⁻¹) v
  rw [hs]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hfour : Real.sqrt c ^ 4 = c ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hc.le]
  have hw : c * ((Real.sqrt c)⁻¹) ^ 4 = c⁻¹ := by
    rw [inv_pow, hfour]
    field_simp
  rw [← mul_assoc, hw]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricRm04At_scaleMetric_inv_sqrt_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricRm04At_scaleMetric_inv_sqrt_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricRm04At_scaleMetric_inv_sqrt_smul ``Submission.DifferentialGeometry.Geometry.Curvature.metricRm04At_scaleMetric_inv_sqrt_smul


end

end DifferentialGeometry.Geometry.Curvature
