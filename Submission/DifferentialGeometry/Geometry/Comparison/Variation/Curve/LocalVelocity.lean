import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem velocity_rep_diffAt
    (gamma : ℝ → M) (t : ℝ)
    (hgamma : ContMDiffAt (modelWithCornersSelf ℝ ℝ) I ∞ gamma t) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) gamma
        (fun s ↦ (mfderiv (modelWithCornersSelf ℝ ℝ) I gamma s :
          ℝ →L[ℝ] TangentSpace I (gamma s)) (1 : ℝ)) t) t := by
  have hgamma2 : ContMDiffAt (modelWithCornersSelf ℝ ℝ) I 2 gamma t :=
    hgamma.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  change DifferentiableAt ℝ
    (fun u : ℝ =>
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (gamma t)).continuousLinearMapAt
        ℝ (gamma u)) (mfderiv 𝓘(ℝ, ℝ) I gamma u (1 : ℝ))) t
  exact MFDerivAlongCurve.velocity_coord_diff (I := I) gamma t hgamma2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.velocity_rep_diffAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.velocity_rep_diffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.velocity_rep_diffAt ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.velocity_rep_diffAt

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
