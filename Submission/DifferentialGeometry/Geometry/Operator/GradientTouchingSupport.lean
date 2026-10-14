import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Minimum

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter _root_.Manifold
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem gradientFun_eq_of_touching_upper_support
    (g : SmoothRiemannianMetric I M) {f phi : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hphi : MDifferentiableAt I 𝓘(ℝ, ℝ) phi x)
    (hcontact : phi x = f x)
    (hupper : ∀ᶠ y in 𝓝 x, f y ≤ phi y) :
    gradientFun g f x = gradientFun g phi x := by
  have hmin : IsLocalMin (fun y => phi y - f y) x := by
    change ∀ᶠ y in 𝓝 x, phi x - f x ≤ phi y - f y
    filter_upwards [hupper] with y hy
    rw [hcontact, sub_self]
    exact sub_nonneg.mpr hy
  have hzero := gradientFun_eq_zero_at_spatial_min g hmin (hphi.sub hf)
  rw [gradientFun_sub g hphi hf] at hzero
  exact (sub_eq_zero.mp hzero).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.gradientFun_eq_of_touching_upper_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.gradientFun_eq_of_touching_upper_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.gradientFun_eq_of_touching_upper_support ``Submission.DifferentialGeometry.Geometry.Operator.gradientFun_eq_of_touching_upper_support

end DifferentialGeometry.Geometry.Operator

end
