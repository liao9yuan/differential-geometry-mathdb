import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Cross

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Bundle _root_.Manifold
open _root_.Submission.DifferentialGeometry
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Metric

variable {E F H G Q N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  [TopologicalSpace P] [ChartedSpace G P]

theorem pullbackMetricCross_symm_comp_inner (g : SmoothRiemannianMetric I Q)
    (e : Q ≃ₘ⟮I, I⟯ N) (f : P → Q) (hf : ContMDiff J I ∞ f)
    (x : P) (V W : TangentSpace J x) :
    (Diffeomorph.pullbackMetricCross g e.symm).inner (e (f x))
      (mfderiv J I (e ∘ f) x V) (mfderiv J I (e ∘ f) x W) =
        g.inner (f x) (mfderiv J I f x V) (mfderiv J I f x W) := by
  let : T2Space Q := e.toHomeomorph.symm.t2Space
  have he : Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetricCross g e.symm) e = g :=
    Diffeomorph.pullbackMetricCross_symm_eq_iff.mpr rfl
  conv_rhs => rw [← he]
  rw [Diffeomorph.pullbackMetricCross_inner,
    mfderiv_comp x (e.contMDiff.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.pullbackMetricCross_symm_comp_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.pullbackMetricCross_symm_comp_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.pullbackMetricCross_symm_comp_inner ``Submission.DifferentialGeometry.Geometry.Metric.pullbackMetricCross_symm_comp_inner

end DifferentialGeometry.Geometry.Metric
