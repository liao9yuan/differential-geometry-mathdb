import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Quotient.Descent
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.ConstantRicci
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.RoundSphereQuotient

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] [NeZero n]

theorem gQuot_scalar (D : RoundSphereQuotient E n) (x : D.Q) :
    metricScalarAt (I := 𝓡 n) D.gQuot x = (n : ℝ) * ((n : ℝ) - 1) := by
  let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
    ⟨by simpa only [finrank_euclideanSpace_fin] using (NeZero.ne n)⟩
  obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis D.gQuot x
  rw [metricScalarAt_eq_orthonormal_trace D.gQuot x b hb]
  have hRic := ricci_of_sec D.gQuot 1
    (fun y v w => by simpa only [one_mul] using D.gQuot_sectional_one y v w)
  simp only [hRic, hb, if_true, finrank_euclideanSpace_fin, mul_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    exact finrank_euclideanSpace_fin
  rw [hdim]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.RoundSphereQuotient.gQuot_scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.RoundSphereQuotient.gQuot_scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.RoundSphereQuotient.gQuot_scalar ``Submission.DifferentialGeometry.Geometry.RoundSphereQuotient.gQuot_scalar

end DifferentialGeometry.Geometry.RoundSphereQuotient
