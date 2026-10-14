import Submission.DifferentialGeometry.Geometry.Comparison.BallCapture

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem ball_subset_image_of_metric_lower_crossModel
    (h : SmoothRiemannianMetric J N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph J I N M ∞) (p : N)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hcpt : IsCompact (riemannianClosedBallOf h p R))
    (hsource : riemannianClosedBallOf h p R ⊆ F.source)
    (hlower : ∀ y ∈ riemannianClosedBallOf h p R,
      ∀ v : TangentSpace J y, h.inner y v v ≤
        L ^ 2 * g.inner (F y) (mfderiv J I (F : N → M) y v)
          (mfderiv J I (F : N → M) y v)) :
    riemannianBallOf g (F p) (R / L) ⊆
      (F : N → M) '' riemannianClosedBallOf h p R :=
  _root_.Submission.DifferentialGeometry.PartialDiffeomorph.ball_subset_image_closedBall_of_metric_lower
    h g F p hR hL hcpt hsource hlower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.ball_subset_image_of_metric_lower_crossModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.ball_subset_image_of_metric_lower_crossModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.ball_subset_image_of_metric_lower_crossModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.ball_subset_image_of_metric_lower_crossModel

theorem closedBall_subset_image_of_metric_lower_crossModel
    (h : SmoothRiemannianMetric J N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph J I N M ∞) (p : N)
    {R L r : ℝ} (hR : 0 < R) (hL : 0 < L) (hr : r < R / L)
    (hcpt : IsCompact (riemannianClosedBallOf h p R))
    (hsource : riemannianClosedBallOf h p R ⊆ F.source)
    (hlower : ∀ y ∈ riemannianClosedBallOf h p R,
      ∀ v : TangentSpace J y, h.inner y v v ≤
        L ^ 2 * g.inner (F y) (mfderiv J I (F : N → M) y v)
          (mfderiv J I (F : N → M) y v)) :
    riemannianClosedBallOf g (F p) r ⊆
      (F : N → M) '' riemannianClosedBallOf h p R :=
  _root_.Submission.DifferentialGeometry.PartialDiffeomorph.closedBall_subset_image_closedBall_of_metric_lower
    h g F p hR hL hr hcpt hsource hlower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.closedBall_subset_image_of_metric_lower_crossModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.closedBall_subset_image_of_metric_lower_crossModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.closedBall_subset_image_of_metric_lower_crossModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.closedBall_subset_image_of_metric_lower_crossModel

theorem short_curve_mem_image_of_metric_lower_crossModel
    (h : SmoothRiemannianMetric J N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph J I N M ∞) (p : N)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hcpt : IsCompact (riemannianClosedBallOf h p R))
    (hsource : riemannianClosedBallOf h p R ⊆ F.source)
    (hlower : ∀ y ∈ riemannianClosedBallOf h p R,
      ∀ v : TangentSpace J y, h.inner y v v ≤
        L ^ 2 * g.inner (F y) (mfderiv J I (F : N → M) y v)
          (mfderiv J I (F : N → M) y v))
    {gamma : ℝ → M} {a b : ℝ}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (_root_.Set.Icc a b))
    (hstart : gamma a = F p)
    (hlen : metricPathELength g gamma a b < ENNReal.ofReal (R / L)) :
    ∀ s ∈ _root_.Set.Icc a b, gamma s ∈ (F : N → M) '' riemannianClosedBallOf h p R :=
  _root_.Submission.DifferentialGeometry.PartialDiffeomorph.curve_mem_image_closedBall_of_metric_lower
    h g F p hR hL hcpt hsource hlower hgamma hstart hlen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.short_curve_mem_image_of_metric_lower_crossModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.short_curve_mem_image_of_metric_lower_crossModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.short_curve_mem_image_of_metric_lower_crossModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.short_curve_mem_image_of_metric_lower_crossModel

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

end
