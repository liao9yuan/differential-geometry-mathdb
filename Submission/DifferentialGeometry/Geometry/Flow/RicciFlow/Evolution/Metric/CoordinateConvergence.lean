import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartFrameBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedIntervalDerivative
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Tower
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.UniformConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem exists_chartGramMatrix_right_endpoint_bound
    (R : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hchart : K ⊆ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (B C : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D), IsSolutionOn S →
      ∀ {a b : ℝ}, a < b → _root_.Set.Icc a b ⊆ D.carrier → _root_.Set.Ioo a b ⊆ D.regular →
      (∀ t ∈ _root_.Set.Icc a b, ∀ x ∈ K, ∀ v : TangentSpace I x,
        (S.family.metric t).inner x v v ≤ B * R.inner x v v) →
      MovingShiBoundOn K a b (fun _ t => S.family.metric t) 0 C →
      ∀ t ∈ _root_.Set.Icc a b, ∀ x ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        _root_.Dist.dist (chartGramMatrix (S.family.metric b) α x i j)
          (chartGramMatrix (S.family.metric t) α x i j) ≤ L * (b - t) := by
  obtain ⟨Rf, _, hframe⟩ := exists_pos_bound_chartBasisVec_on_compact R α hK hchart
  refine ⟨max 0 (2 * C * _root_.Max.max 0 B * (Rf * Rf)), le_max_left _ _, ?_⟩
  intro D S hS a b hab hcarrier hregular hmetric hShi t ht x hx i j
  have hsub : _root_.Set.Icc t b ⊆ _root_.Set.Icc a b := _root_.Set.Icc_subset_Icc ht.1 le_rfl
  have hderiv (s : ℝ) (hs : s ∈ _root_.Set.Icc t b) :
      HasDerivWithinAt (fun r => chartGramMatrix (S.family.metric r) α x i j)
        (-2 * S.ricciAt s x
          (vec2 (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x)))
        (_root_.Set.Icc t b) s :=
    (metric_inner_hasDerivWithinAt_on_closed_interval S hS hab hcarrier hregular
      (hsub hs) x (chartBasisVecFiber (I := I) α i x)
      (chartBasisVecFiber (I := I) α j x)).mono hsub
  have hbound (s : ℝ) (hs : s ∈ _root_.Set.Ico t b) :
      ‖-2 * S.ricciAt s x
        (vec2 (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x))‖ ≤
      max 0 (2 * C * _root_.Max.max 0 B * (Rf * Rf)) := by
    have hs' : s ∈ _root_.Set.Icc a b := ⟨ht.1.trans hs.1, hs.2.le⟩
    have hRic : Real.sqrt (normSq0S (S.family.metric s) x 2 (S.ricciAt s x)) ≤ C :=
      hShi 0 le_rfl 0 s hs' x hx
    exact (norm_ricci_pairing_le_of_metric_le S R (le_max_left 0 B) x
      (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x)
      (fun v => (hmetric s hs' x hx v).trans
        (mul_le_mul_of_nonneg_right (le_max_right 0 B) (metric_inner_self_nonneg R x v)))
      hRic (hframe x hx i) (hframe x hx j)).trans
      (le_max_right _ _)
  simpa only [dist_eq_norm] using
    norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound b (right_mem_Icc.mpr ht.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_chartGramMatrix_right_endpoint_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_chartGramMatrix_right_endpoint_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_chartGramMatrix_right_endpoint_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_chartGramMatrix_right_endpoint_bound

theorem tendstoUniformlyOn_chartGramOnE_right_endpoint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hcarrier : _root_.Set.Icc a b ⊆ D.carrier)
    (hregular : _root_.Set.Ioo a b ⊆ D.regular)
    (R : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hchart : K ⊆ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    {B C : ℝ}
    (hmetric : ∀ t ∈ _root_.Set.Icc a b, MetricUniformEquivalentOn K R (S.family.metric t) B)
    (hShi : MovingShiBoundOn K a b (fun _ t => S.family.metric t) 0 C)
    {U : Set E} (hU : _root_.Set.MapsTo (extChartAt I α).symm U K)
    (i j : Fin (Module.finrank ℝ E)) :
    TendstoUniformlyOn (fun t => chartGramOnE (S.family.metric t) α i j)
      (chartGramOnE (S.family.metric b) α i j) (𝓝[_root_.Set.Ioo a b] b) U := by
  obtain ⟨L, _, hL⟩ := exists_chartGramMatrix_right_endpoint_bound R α hK hchart B C
  have hmod : _root_.Filter.Tendsto (fun t : ℝ => L * (b - t)) (𝓝[_root_.Set.Ioo a b] b) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => L * (b - t)) b := by fun_prop
    simpa only [sub_self, _root_.MulZeroClass.mul_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_mem_nhdsWithin, hmod.eventually_lt_const hε]
    with t ht hsmall y hy
  exact (hL S hS hab hcarrier hregular
    (fun s hs x hx v => ((hmetric s hs).2 x hx v).2) hShi t (_root_.Set.Ioo_subset_Icc_self ht)
    ((extChartAt I α).symm y) (hU hy) i j).trans_lt hsmall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.tendstoUniformlyOn_chartGramOnE_right_endpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.tendstoUniformlyOn_chartGramOnE_right_endpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.tendstoUniformlyOn_chartGramOnE_right_endpoint ``Submission.DifferentialGeometry.PDE.RicciFlow.tendstoUniformlyOn_chartGramOnE_right_endpoint

end DifferentialGeometry.PDE.RicciFlow

end

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow
open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem tendstoUniformlyOn_chartGramOnE_left_endpoint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hcarrier : _root_.Set.Icc a b ⊆ D.carrier)
    (hregular : _root_.Set.Ioo a b ⊆ D.regular)
    (R : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hchart : K ⊆ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    {B C : ℝ}
    (hmetric : ∀ t ∈ _root_.Set.Icc a b, MetricUniformEquivalentOn K R (S.family.metric t) B)
    (hShi : MovingShiBoundOn K a b (fun _ t => S.family.metric t) 0 C)
    {U : Set E} (hU : _root_.Set.MapsTo (extChartAt I α).symm U K)
    (i j : Fin (Module.finrank ℝ E)) :
    TendstoUniformlyOn (fun t : ℝ => chartGramOnE (S.family.metric t) α i j)
      (chartGramOnE (S.family.metric a) α i j) (𝓝[_root_.Set.Ioo a b] a) U := by
  obtain ⟨L, _, hL⟩ := exists_chartGramMatrix_right_endpoint_bound R α hK hchart B C
  have hmod : _root_.Filter.Tendsto (fun t : ℝ => L * (t - a)) (𝓝[_root_.Set.Ioo a b] a) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => L * (t - a)) a := by fun_prop
    simpa only [sub_self, _root_.MulZeroClass.mul_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_mem_nhdsWithin, hmod.eventually_lt_const hε]
    with t ht hsmall y hy
  have hcarrier' : _root_.Set.Icc a t ⊆ D.carrier := by
    intro s hs
    exact hcarrier ⟨hs.1, hs.2.trans ht.2.le⟩
  have hregular' : _root_.Set.Ioo a t ⊆ D.regular := by
    intro s hs
    exact hregular ⟨hs.1, hs.2.trans ht.2⟩
  have hmetric' : ∀ s ∈ _root_.Set.Icc a t,
      ∀ x ∈ K, ∀ v : TangentSpace I x,
        (S.family.metric s).inner x v v ≤ B * R.inner x v v := by
    intro s hs x hx v
    exact ((hmetric s ⟨hs.1, hs.2.trans ht.2.le⟩).2 x hx v).2
  have hShi' : MovingShiBoundOn K a t (fun _ s => S.family.metric s) 0 C := by
    intro n hn q s hs x hx
    exact hShi n hn q s ⟨hs.1, hs.2.trans ht.2.le⟩ x hx
  have hbound := hL S hS ht.1 hcarrier' hregular' hmetric' hShi' a
    ⟨le_rfl, ht.1.le⟩ ((extChartAt I α).symm y) (hU hy) i j
  simpa only [chartGramOnE, dist_comm] using hbound.trans_lt hsmall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.tendstoUniformlyOn_chartGramOnE_left_endpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.tendstoUniformlyOn_chartGramOnE_left_endpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.tendstoUniformlyOn_chartGramOnE_left_endpoint ``Submission.DifferentialGeometry.PDE.RicciFlow.tendstoUniformlyOn_chartGramOnE_left_endpoint

end DifferentialGeometry.PDE.RicciFlow

end
