import Submission.DifferentialGeometry.Topology.Covering.Line
import Submission.DifferentialGeometry.Geometry.Metric.Product.Completeness
import Submission.DifferentialGeometry.Geometry.Metric.DistancePullback
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Topology
import Submission.DifferentialGeometry.Geometry.Metric.Euclidean

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem not_intrinsic_line_of_compact_cylinder_cover_reflection
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (proj : M × ℝ → N) (hproj : IsLocalDiffeomorph (I.prod 𝓘(ℝ, ℝ)) J ∞ proj)
    (hcover : IsCoveringMap proj) (hsurj : Function.Surjective proj)
    (hmetric : ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p),
      h.inner (proj p) (mfderiv (I.prod 𝓘(ℝ, ℝ)) J proj p v)
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) J proj p w) = g.inner p.1 v.1 w.1 + v.2 * w.2)
    (τ : M → M) (hreflection : ∀ p : M × ℝ, proj (τ p.1, -p.2) = proj p)
    (γ : ℝ → N) :
    ¬ (∀ s t : ℝ, riemannianEDistOf h (γ s) (γ t) = ENNReal.ofReal |s - t|) := by
  intro hline
  let _ : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  let _ : RegularSpace M := inferInstance
  let _ : LocallyCompactSpace N := Manifold.locallyCompact_of_finiteDimensional (M := N) J
  let _ : RegularSpace N := inferInstance
  let _ : PathConnectedSpace N := hsurj.pathConnectedSpace hproj.contMDiff.continuous
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  let _ : PseudoMetricSpace N := h.toPseudoMetricSpace
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp (isCompact_univ : IsCompact (_root_.Set.univ : Set M)).isBounded
  have hdiam (x y : M) : riemannianEDistOf g x y ≤ ENNReal.ofReal (_root_.Max.max D 0) := by
    change _root_.EDist.edist x y ≤ _
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal ((hD (x := x) (y := y) (_root_.Set.mem_univ _) (_root_.Set.mem_univ _)).trans (le_max_left _ _))
  have hmap (p q : M × ℝ) : riemannianEDistOf h (proj p) (proj q) ≤
      riemannianEDistOf (g.prod (euclideanMetric (E := ℝ))) p q := by
    have hb := Metric.edistOf_le_of_quad_of_localDiffeomorph
      (g.prod (euclideanMetric (E := ℝ))) h proj hproj (c := 1) zero_lt_one (by
        intro p v
        rw [hmetric]
        simp only [one_mul, SmoothRiemannianMetric.prod_inner]
        rfl) p q
    simpa only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] using hb
  have hbound (p q : M × ℝ) : _root_.Dist.dist (proj p) (proj q) ≤ |p.2 - q.2| + _root_.Max.max D 0 := by
    have heuc : riemannianEDistOf (euclideanMetric (E := ℝ)) p.2 q.2 =
        ENNReal.ofReal |p.2 - q.2| := by
      change Manifold.riemannianEDist 𝓘(ℝ, ℝ) p.2 q.2 = _
      rw [← IsRiemannianManifold.out, edist_dist, Real.dist_eq]
    have hp := riemannianEDistOf_triangle (g.prod (euclideanMetric (E := ℝ))) p (q.1, p.2) q
    rw [riemannianEDistOf_prod_left, riemannianEDistOf_prod_right, heuc] at hp
    have hb := (hmap p q).trans (hp.trans (add_le_add (hdiam p.1 q.1) le_rfl))
    rw [← ENNReal.ofReal_add (le_max_right D 0) (abs_nonneg _), add_comm (_root_.Max.max D 0)] at hb
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rw [ENNReal.toReal_ofReal (add_nonneg (abs_nonneg _) (le_max_right D 0))] at hr
    exact hr
  apply DifferentialGeometry.Topology.not_isometry_of_covering_reflection proj hcover hsurj τ hreflection
    (_root_.Max.max D 0) hbound γ
  intro s t
  change riemannianEDistOf h (γ s) (γ t) = _root_.EDist.edist s t
  rw [hline, edist_dist, Real.dist_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.not_intrinsic_line_of_compact_cylinder_cover_reflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.not_intrinsic_line_of_compact_cylinder_cover_reflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.not_intrinsic_line_of_compact_cylinder_cover_reflection ``Submission.DifferentialGeometry.Geometry.not_intrinsic_line_of_compact_cylinder_cover_reflection

end DifferentialGeometry.Geometry

end
