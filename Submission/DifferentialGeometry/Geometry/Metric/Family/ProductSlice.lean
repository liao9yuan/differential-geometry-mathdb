import Submission.DifferentialGeometry.Geometry.Metric.ProductSlice
import Submission.DifferentialGeometry.Geometry.Metric.Family.Pullback
import Submission.DifferentialGeometry.Geometry.Metric.Product

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Filter _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
  [T2Space N]

omit [T2Space N] in
set_option backward.isDefEq.respectTransparency false in
theorem MetricFamilySmoothOn.sliceFst
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric (I.prod J) (M × N)}
    (hg : MetricFamilySmoothOn D g) (y : N) :
    MetricFamilySmoothOn D (fun t => (g t).sliceFst y) := by
  apply hg.of_pullback (fun t => (g t).sliceFst y) (fun x : M => (x, y))
    (contMDiff_id.prodMk contMDiff_const)
  intro t x v w
  rw [mfderiv_prod_left]
  exact SmoothRiemannianMetric.sliceFst_inner (g t) y x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.sliceFst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.sliceFst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.sliceFst ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.sliceFst

set_option backward.isDefEq.respectTransparency false in
theorem MetricFamilySmoothOn.eq_sliceFst_prod_at_terminal_of_lt
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric (I.prod J) (M × N)}
    (hg : MetricFamilySmoothOn D g) {b : ℝ} (hcarrier : _root_.Set.Iic b ⊆ D.carrier)
    (h : SmoothRiemannianMetric J N) (y : N)
    (hprod : ∀ t < b, g t = ((g t).sliceFst y).prod h) :
    g b = ((g b).sliceFst y).prod h := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  rw [SmoothRiemannianMetric.prod_inner, SmoothRiemannianMetric.sliceFst_inner]
  have hA : ContinuousWithinAt (fun t : ℝ => (g t).inner z v w) (_root_.Set.Iic b) b := by
    have hc := (hg.coeff_cont z v w).mono hcarrier
    exact hc.continuousWithinAt (by simp only [_root_.Set.mem_Iic, le_refl])
  have hB : ContinuousWithinAt
      (fun t : ℝ => (g t).inner (z.1, y) (v.1, 0) (w.1, 0) + h.inner z.2 v.2 w.2)
      (_root_.Set.Iic b) b := by
    have hc := (hg.coeff_cont (z.1, y) (v.1, 0) (w.1, 0)).mono hcarrier
    exact (hc.continuousWithinAt (by simp only [_root_.Set.mem_Iic, le_refl])).add
      continuousWithinAt_const
  have heq : (fun t : ℝ => (g t).inner z v w) =ᶠ[𝓝[_root_.Set.Iio b] b]
      (fun t : ℝ => (g t).inner (z.1, y) (v.1, 0) (w.1, 0) + h.inner z.2 v.2 w.2) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h := congrArg (fun q => q.inner z v w) (hprod t ht)
    simpa only [SmoothRiemannianMetric.prod_inner, SmoothRiemannianMetric.sliceFst_inner]
      using h
  exact tendsto_nhds_unique (hA.mono_left (nhdsWithin_mono b _root_.Set.Iio_subset_Iic_self))
    ((hB.mono_left (nhdsWithin_mono b _root_.Set.Iio_subset_Iic_self)).congr' heq.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.eq_sliceFst_prod_at_terminal_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.eq_sliceFst_prod_at_terminal_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.eq_sliceFst_prod_at_terminal_of_lt ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.eq_sliceFst_prod_at_terminal_of_lt

theorem MetricFamilySmoothOn.eq_sliceFst_prod_at_terminal_of_eventually
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric (I.prod J) (M × N)}
    (hg : MetricFamilySmoothOn D g) {b : ℝ} (hb : b ∈ D.carrier)
    (hleft : D.carrier ∈ 𝓝[<] b)
    (h : SmoothRiemannianMetric J N) (y : N)
    (hprod : ∀ᶠ t in 𝓝[<] b, g t = ((g t).sliceFst y).prod h) :
    g b = ((g b).sliceFst y).prod h := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  have hinner (t : ℝ) :
      (((g t).sliceFst y).prod h).inner z v w =
        (g t).inner (z.1, y) (v.1, 0) (w.1, 0) + h.inner z.2 v.2 w.2 :=
    (SmoothRiemannianMetric.prod_inner ((g t).sliceFst y) h z v w).trans
      (congrArg (fun r : ℝ => r + h.inner z.2 v.2 w.2)
        (SmoothRiemannianMetric.sliceFst_inner (g t) y z.1 v.1 w.1))
  have hA : ContinuousWithinAt (fun t : ℝ => (g t).inner z v w) (_root_.Set.Iio b) b :=
    (hg.coeff_cont z v w b hb).mono_of_mem_nhdsWithin hleft
  have hB : ContinuousWithinAt
      (fun t : ℝ => (g t).inner (z.1, y) (v.1, 0) (w.1, 0) + h.inner z.2 v.2 w.2)
      (_root_.Set.Iio b) b :=
    ((hg.coeff_cont (z.1, y) (v.1, 0) (w.1, 0) b hb).mono_of_mem_nhdsWithin
      hleft).add continuousWithinAt_const
  have heq : (fun t : ℝ => (g t).inner z v w) =ᶠ[𝓝[<] b]
      (fun t : ℝ => (g t).inner (z.1, y) (v.1, 0) (w.1, 0) + h.inner z.2 v.2 w.2) := by
    filter_upwards [hprod] with t ht
    exact (congrArg (fun q : SmoothRiemannianMetric (I.prod J) (M × N) =>
      q.inner z v w) ht).trans (hinner t)
  exact (tendsto_nhds_unique hA (hB.congr' heq.symm)).trans (hinner b).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.eq_sliceFst_prod_at_terminal_of_eventually then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.eq_sliceFst_prod_at_terminal_of_eventually"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.eq_sliceFst_prod_at_terminal_of_eventually ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.eq_sliceFst_prod_at_terminal_of_eventually

end DifferentialGeometry.Geometry.Curvature
