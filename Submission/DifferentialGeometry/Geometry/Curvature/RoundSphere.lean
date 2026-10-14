import Submission.DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.ConstantRicci
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature

theorem ricciTensor_roundSphere
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (x : Metric.sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) x) :
    ricciTensor (roundMetric (E := E) (n := n)) x v w =
      ((n : ℝ) - 1) * (roundMetric (E := E) (n := n)).inner x v w := by
  by_cases hn : n = 0
  · subst n
    have hv : v = 0 := by
      let : Subsingleton (TangentSpace (𝓡 0) x) :=
        inferInstanceAs (Subsingleton (EuclideanSpace ℝ (Fin 0)))
      exact Subsingleton.elim _ _
    simp [hv]
  · let : NeZero n := ⟨hn⟩
    let : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
      rw [finrank_euclideanSpace_fin]
      infer_instance
    have h := ricci_of_op (roundMetric (E := E) (n := n)) x 1
      (fun X Y Z ↦ by simpa only [one_smul] using round_riemann_one x X Y Z) v w
    simpa only [finrank_euclideanSpace_fin, mul_one] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciTensor_roundSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciTensor_roundSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciTensor_roundSphere ``Submission.DifferentialGeometry.Geometry.Curvature.ricciTensor_roundSphere

theorem ricciTensor_scaledRoundSphere
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (c : ℝ) (hc : 0 < c) (x : Metric.sphere (0 : E) 1)
    (v w : TangentSpace (𝓡 n) x) :
    ricciTensor (scaleMetric c hc (roundMetric (E := E) (n := n))) x v w =
      (((n : ℝ) - 1) / c) *
        (scaleMetric c hc (roundMetric (E := E) (n := n))).inner x v w := by
  rw [ricciTensor_scaleMetric, ricciTensor_roundSphere, scaleMetric_inner]
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciTensor_scaledRoundSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciTensor_scaledRoundSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciTensor_scaledRoundSphere ``Submission.DifferentialGeometry.Geometry.Curvature.ricciTensor_scaledRoundSphere

end DifferentialGeometry.Geometry.Curvature
