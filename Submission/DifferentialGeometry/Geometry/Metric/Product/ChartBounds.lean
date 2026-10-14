import Submission.DifferentialGeometry.Geometry.Coordinates.Frame.TangentProduct
import Submission.DifferentialGeometry.Geometry.Metric.Product
import Submission.DifferentialGeometry.Geometry.Metric.Euclidean
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.SmoothRiemannianMetric

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

theorem prod_chart_norm_comparison
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (p : M × N) {q : M × N}
    (hq : q ∈ (_root_.FiberBundle.trivializationAt (E × F) (TangentSpace (I.prod J)) p).baseSet)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hg : ∀ v : TangentSpace I q.1,
      Real.sqrt (g.inner q.1 v v) ≤
        C * ‖(_root_.FiberBundle.trivializationAt E (TangentSpace I) p.1).continuousLinearMapAt ℝ q.1 v‖ ∧
      ‖(_root_.FiberBundle.trivializationAt E (TangentSpace I) p.1).continuousLinearMapAt ℝ q.1 v‖ ≤
        C * Real.sqrt (g.inner q.1 v v))
    (hh : ∀ v : TangentSpace J q.2,
      Real.sqrt (h.inner q.2 v v) ≤
        D * ‖(_root_.FiberBundle.trivializationAt F (TangentSpace J) p.2).continuousLinearMapAt ℝ q.2 v‖ ∧
      ‖(_root_.FiberBundle.trivializationAt F (TangentSpace J) p.2).continuousLinearMapAt ℝ q.2 v‖ ≤
        D * Real.sqrt (h.inner q.2 v v))
    (v : TangentSpace (I.prod J) q) :
    Real.sqrt ((g.prod h).inner q v v) ≤ (C + D) *
      ‖(_root_.FiberBundle.trivializationAt (E × F) (TangentSpace (I.prod J)) p).continuousLinearMapAt ℝ q v‖ ∧
    ‖(_root_.FiberBundle.trivializationAt (E × F) (TangentSpace (I.prod J)) p).continuousLinearMapAt ℝ q v‖ ≤
      (C + D) * Real.sqrt ((g.prod h).inner q v v) := by
  rw [prod_inner, trivializationAt_continuousLinearMapAt_prod_of_mem p hq v, Prod.norm_def]
  let a := g.inner q.1 v.1 v.1
  let b := h.inner q.2 v.2 v.2
  have ha : 0 ≤ a := metric_inner_self_nonneg g q.1 v.1
  have hb : 0 ≤ b := metric_inner_self_nonneg h q.2 v.2
  have hab : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), ?_⟩
    nlinarith only [Real.sq_sqrt ha, Real.sq_sqrt hb,
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  have hma := le_max_left
    ‖(_root_.FiberBundle.trivializationAt E (TangentSpace I) p.1).continuousLinearMapAt ℝ q.1 v.1‖
    ‖(_root_.FiberBundle.trivializationAt F (TangentSpace J) p.2).continuousLinearMapAt ℝ q.2 v.2‖
  have hmb := le_max_right
    ‖(_root_.FiberBundle.trivializationAt E (TangentSpace I) p.1).continuousLinearMapAt ℝ q.1 v.1‖
    ‖(_root_.FiberBundle.trivializationAt F (TangentSpace J) p.2).continuousLinearMapAt ℝ q.2 v.2‖
  refine ⟨hab.trans ?_, max_le ?_ ?_⟩
  · exact (add_le_add (hg v.1).1 (hh v.2).1).trans (by
      nlinarith only [mul_le_mul_of_nonneg_left hma hC, mul_le_mul_of_nonneg_left hmb hD])
  · exact (hg v.1).2.trans ((mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (le_add_of_nonneg_right hb)) hC).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (Real.sqrt_nonneg (a + b))))
  · exact (hh v.2).2.trans ((mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (le_add_of_nonneg_left ha)) hD).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (Real.sqrt_nonneg (a + b))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.prod_chart_norm_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.prod_chart_norm_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.prod_chart_norm_comparison ``Submission.DifferentialGeometry.SmoothRiemannianMetric.prod_chart_norm_comparison

theorem prod_euclidean_chart_norm_comparison
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (g : SmoothRiemannianMetric I M) (p : M × V) {q : M × V}
    (hq : q.1 ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) p.1).baseSet)
    {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ v : TangentSpace I q.1,
      Real.sqrt (g.inner q.1 v v) ≤
        C * ‖(_root_.FiberBundle.trivializationAt E (TangentSpace I) p.1).continuousLinearMapAt ℝ q.1 v‖ ∧
      ‖(_root_.FiberBundle.trivializationAt E (TangentSpace I) p.1).continuousLinearMapAt ℝ q.1 v‖ ≤
        C * Real.sqrt (g.inner q.1 v v))
    (v : TangentSpace (I.prod 𝓘(ℝ, V)) q) :
    Real.sqrt ((g.prod (euclideanMetric (E := V))).inner q v v) ≤ (C + 1) *
      ‖(_root_.FiberBundle.trivializationAt (E × V) (TangentSpace (I.prod 𝓘(ℝ, V))) p).continuousLinearMapAt ℝ q v‖ ∧
    ‖(_root_.FiberBundle.trivializationAt (E × V) (TangentSpace (I.prod 𝓘(ℝ, V))) p).continuousLinearMapAt ℝ q v‖ ≤
      (C + 1) * Real.sqrt ((g.prod (euclideanMetric (E := V))).inner q v v) := by
  have hprod : q ∈ (_root_.FiberBundle.trivializationAt (E × V) (TangentSpace (I.prod 𝓘(ℝ, V))) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, prodChartedSpace_chartAt,
      OpenPartialHomeomorph.prod_source, _root_.Set.mem_prod, chartAt_self_eq,
      OpenPartialHomeomorph.refl_source, _root_.Set.mem_univ, and_true] using hq
  apply prod_chart_norm_comparison g euclideanMetric p hprod hC zero_le_one hg
  have hh (y u : V) : Real.sqrt ((euclideanMetric (E := V)).inner y u u) ≤ 1 * ‖u‖ ∧
      ‖u‖ ≤ 1 * Real.sqrt ((euclideanMetric (E := V)).inner y u u) := by
    change Real.sqrt (_root_.Inner.inner ℝ u u) ≤ 1 * ‖u‖ ∧ ‖u‖ ≤ 1 * Real.sqrt (_root_.Inner.inner ℝ u u)
    simp only [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg u), one_mul, le_refl, and_self]
  intro w
  rw [TangentBundle.continuousLinearMapAt_model_space]
  exact hh q.2 w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.prod_euclidean_chart_norm_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.prod_euclidean_chart_norm_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.prod_euclidean_chart_norm_comparison ``Submission.DifferentialGeometry.SmoothRiemannianMetric.prod_euclidean_chart_norm_comparison

end DifferentialGeometry.SmoothRiemannianMetric
