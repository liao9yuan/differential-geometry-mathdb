import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Local

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
set_option autoImplicit false

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry

variable {E F G H H' H'' M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'} {K : ModelWithCorners ℝ G H''}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]

omit [FiniteDimensional ℝ G] in
theorem localPullMetric_comp
    (g : SmoothRiemannianMetric K P) (h : N → P) (f : M → N)
    (hh : IsLocalDiffeomorph J K ∞ h) (hf : IsLocalDiffeomorph I J ∞ f)
    (hhf : IsLocalDiffeomorph I K ∞ (h ∘ f)) :
    localPullMetric (localPullMetric g h hh) f hf = localPullMetric g (h ∘ f) hhf := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, localPullMetric_inner, localPullMetric_inner]
  have hd : mfderiv I K (h ∘ f) x = (mfderiv J K h (f x)).comp (mfderiv I J f x) :=
    mfderiv_comp x (hh.mdifferentiable (by decide) (f x)) (hf.mdifferentiable (by decide) x)
  rw [hd]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.localPullMetric_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.localPullMetric_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.localPullMetric_comp ``Submission.DifferentialGeometry.localPullMetric_comp

end DifferentialGeometry

end

end
