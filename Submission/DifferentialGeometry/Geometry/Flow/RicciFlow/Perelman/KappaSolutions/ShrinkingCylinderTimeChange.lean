import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StrongNeck
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

private local instance cylinderTimeChangeSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderTimeChangeSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderTimeChangeSphereDimension target :: scope.openDecls } }


theorem shrinkingCylinder_scaled_time_error_inner
    (a : ℝ) (ha : 0 < a) (s : ℝ) (hs : s ≤ 0)
    (x : SpatialNeckCylinder) (v w : TangentSpace SpatialNeckCylinderModel x) :
    (scaleMetric a ha (scalarOneShrinkingCylinderMetric (s / a)
      ((div_nonpos_of_nonpos_of_nonneg hs ha.le).trans_lt zero_lt_one))).inner x v w -
      (scalarOneShrinkingCylinderMetric s (hs.trans_lt zero_lt_one)).inner x v w =
        (a - 1) * doubleSphereCylinderMetric.inner x v w := by
  rcases x with ⟨y, z⟩
  rcases v with ⟨v, r⟩
  rcases w with ⟨w, t⟩
  erw [scaleMetric_inner, scalarOneShrinkingCylinderMetric_inner,
    scalarOneShrinkingCylinderMetric_inner, doubleSphereCylinderMetric_inner]
  field_simp [ha.ne']
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_scaled_time_error_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_scaled_time_error_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_scaled_time_error_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_scaled_time_error_inner


theorem shrinkingCylinder_backward_forward_reference_equivalent
    (theta s : ℝ) (htheta : theta ∈ _root_.Set.Icc (1 : ℝ) 3) (hs : s ∈ _root_.Set.Icc (-1 : ℝ) 0) :
    MetricUniformEquivalentOn (I := SpatialNeckCylinderModel) _root_.Set.univ
      (scalarOneShrinkingCylinderMetric (1 - theta) (by linarith [htheta.1]))
      (scalarOneShrinkingCylinderMetric s (hs.2.trans_lt zero_lt_one)) 3 := by
  refine ⟨by norm_num, ?_⟩
  rintro ⟨y, z⟩ _ ⟨v, r⟩
  have hround : 0 ≤ (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v v := by
    by_cases hv : v = 0
    · subst v
      exact (map_zero ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y 0)).ge
    · exact ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).pos y v hv).le
  have hlo : 2 * (1 - (1 - theta)) ≤ 3 * (2 * (1 - s)) := by
    linarith [htheta.2, hs.2]
  have hhi : 2 * (1 - s) ≤ 3 * (2 * (1 - (1 - theta))) := by
    linarith [htheta.1, hs.1]
  have hlo' := mul_le_mul_of_nonneg_right hlo hround
  have hhi' := mul_le_mul_of_nonneg_right hhi hround
  erw [scalarOneShrinkingCylinderMetric_inner, scalarOneShrinkingCylinderMetric_inner]
  constructor <;> nlinarith [sq_nonneg r]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_backward_forward_reference_equivalent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_backward_forward_reference_equivalent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_backward_forward_reference_equivalent ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_backward_forward_reference_equivalent


theorem shrinkingCylinder_backward_forward_tensor_norm_le
    (theta s : ℝ) (htheta : theta ∈ _root_.Set.Icc (1 : ℝ) 3) (hs : s ∈ _root_.Set.Icc (-1 : ℝ) 0)
    (x : SpatialNeckCylinder) (r : ℕ) (T : Tensor0SSpace r SpatialNeckCylinderModel x) :
    Real.sqrt (normSq0S (scalarOneShrinkingCylinderMetric s (hs.2.trans_lt zero_lt_one)) x r T) ≤
      Real.sqrt ((3 : ℝ) ^ r) *
        Real.sqrt (normSq0S (scalarOneShrinkingCylinderMetric (1 - theta)
          (by linarith [htheta.1])) x r T) := by
  have heq := shrinkingCylinder_backward_forward_reference_equivalent theta s htheta hs
  exact sqrt_normSq0S_le_of_metric_equiv _ _ x r (by norm_num) (heq.2 x (_root_.Set.mem_univ x)) T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_backward_forward_tensor_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_backward_forward_tensor_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_backward_forward_tensor_norm_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_backward_forward_tensor_norm_le


theorem strongNeckBackground_scaled_time_error_inner
    (epsilon a : ℝ) (ha : 0 < a) (s : ℝ) (hs : s ≤ 0)
    (x : spatialNeckBuffer epsilon) (v w : TangentSpace SpatialNeckCylinderModel x) :
    (scaleMetric a ha (strongNeckBackgroundMetric epsilon (s / a))).inner x v w -
      (strongNeckBackgroundMetric epsilon s).inner x v w =
        (a - 1) * (strongNeckBackgroundMetric epsilon 0).inner x v w := by
  have hsa : s / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs ha.le
  have hmodel := shrinkingCylinder_scaled_time_error_inner a ha s hs
    (x : SpatialNeckCylinder) v w
  erw [scaleMetric_inner] at hmodel
  rw [scaleMetric_inner, strongNeckBackgroundMetric_of_nonpos epsilon (s / a) hsa,
    strongNeckBackgroundMetric_of_nonpos epsilon s hs,
    strongNeckBackgroundMetric_of_nonpos epsilon 0 le_rfl,
    scalarOneShrinkingCylinderMetric_zero]
  simpa only [SmoothRiemannianMetric.restrictOpen_inner] using hmodel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.strongNeckBackground_scaled_time_error_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.strongNeckBackground_scaled_time_error_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.strongNeckBackground_scaled_time_error_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.strongNeckBackground_scaled_time_error_inner


theorem strongNeckBackground_time_error_hasDerivWithinAt
    (epsilon a : ℝ) (ha : 0 < a) (s : ℝ) (hs : s ∈ _root_.Set.Icc (-1 : ℝ) 0)
    (x : spatialNeckBuffer epsilon) (v w : TangentSpace SpatialNeckCylinderModel x) :
    HasDerivWithinAt (fun t =>
      (scaleMetric a ha (strongNeckBackgroundMetric epsilon (t / a))).inner x v w -
        (strongNeckBackgroundMetric epsilon t).inner x v w) 0 (_root_.Set.Icc (-1 : ℝ) 0) s := by
  exact (hasDerivWithinAt_const s (_root_.Set.Icc (-1 : ℝ) 0)
    ((a - 1) * (strongNeckBackgroundMetric epsilon 0).inner x v w)).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun t ht =>
      strongNeckBackground_scaled_time_error_inner epsilon a ha t ht.2 x v w)
    (strongNeckBackground_scaled_time_error_inner epsilon a ha s hs.2 x v w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.strongNeckBackground_time_error_hasDerivWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.strongNeckBackground_time_error_hasDerivWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.strongNeckBackground_time_error_hasDerivWithinAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.strongNeckBackground_time_error_hasDerivWithinAt

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
