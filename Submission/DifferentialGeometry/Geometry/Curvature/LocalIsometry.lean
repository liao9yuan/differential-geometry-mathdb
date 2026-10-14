import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Local

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Set _root_.TopologicalSpace
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space M] [T2Space N]

theorem metricRm04StdAt_of_pullback_on_opens
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (U : _root_.TopologicalSpace.Opens M) (V : _root_.TopologicalSpace.Opens N) [SigmaCompactSpace U] [SigmaCompactSpace V]
    (Φ : U ≃ₘ⟮I, I⟯ V)
    (heq : ∀ (y : U) (v w : TangentSpace I y),
      g.inner (y : M) v w = h.inner (Φ y : N)
        (mfderiv I I (Φ : U → V) y v) (mfderiv I I (Φ : U → V) y w))
    (x : U) (v w z u : TangentSpace I x) :
    metricRm04StandardAt g (x : M) v w z u =
      metricRm04StandardAt h (Φ x : N)
        (mfderiv I I (Φ : U → V) x v) (mfderiv I I (Φ : U → V) x w)
        (mfderiv I I (Φ : U → V) x z) (mfderiv I I (Φ : U → V) x u) := by
  have hm : g.restrictOpen U = Diffeomorph.pullbackMetric (h.restrictOpen V) Φ := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [SmoothRiemannianMetric.restrictOpen_inner, Diffeomorph.pullbackMetric_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    exact heq y v w
  have hr := metricRm04StandardAt_restrictOpen g U x v w z u
  rw [hm] at hr
  have hp := metricRm04StandardAt_pullback_localDiffeo h V U Φ x v w z u
  simpa only [mfderiv_subtype_val_apply] using hr.symm.trans hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.metricRm04StdAt_of_pullback_on_opens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.metricRm04StdAt_of_pullback_on_opens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.metricRm04StdAt_of_pullback_on_opens ``Submission.DifferentialGeometry.Geometry.Riemannian.metricRm04StdAt_of_pullback_on_opens

end DifferentialGeometry.Geometry.Riemannian
