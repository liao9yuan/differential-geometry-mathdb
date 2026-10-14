import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.InitialContinuity
import Submission.DifferentialGeometry.Geometry.Metric.ModelChange
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.DensityBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Bounds.ClosedInterval
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.BoundedDensity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Solution.DerivativeBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.EndpointEquality
import Submission.DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciLower
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import Submission.DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import Submission.DifferentialGeometry.Geometry.Metric.Family.Regularity.Pair

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

section InnerProductModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

private theorem forward_unique_on_Ioo_of_complete_bounded_curvature_of_buffered_reference_of_innerProductSpace
    {D₁ D₂ : RealTimeInterval}
    (S₁ : SolutionOn (I := I) (M := M) D₁)
    (S₂ : SolutionOn (I := I) (M := M) D₂)
    (hS₁ : IsSolutionOn S₁) (hS₂ : IsSolutionOn S₂)
    {a₀ a b R₁ R₂ : ℝ} (hbuffer : a₀ < a) (hab : a < b)
    (hcarrier₁ : _root_.Set.Icc a b ⊆ D₁.carrier)
    (hcarrier₂ : _root_.Set.Icc a₀ b ⊆ D₂.carrier)
    (hregular₁ : _root_.Set.Ioc a b ⊆ D₁.regular)
    (hregular₂ : _root_.Set.Ioc a₀ b ⊆ D₂.regular)
    (hcomplete₂ : RiemannianMetricComplete (I := I) (S₂.base.metric a₀))
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (hcurv₁ : ∀ t ∈ _root_.Set.Icc a b, ∀ x : M,
      normSq0S (S₁.base.metric t) x 4 (S₁.base.rm04 t x) ≤ R₁)
    (hcurv₂ : ∀ t ∈ _root_.Set.Icc a₀ b, ∀ x : M,
      normSq0S (S₂.base.metric t) x 4 (S₂.base.rm04 t x) ≤ R₂)
    (hinit : S₁.base.metric a = S₂.base.metric a) :
    ∀ t ∈ _root_.Set.Ioo a b, S₁.base.metric t = S₂.base.metric t := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hsub : _root_.Set.Icc a b ⊆ _root_.Set.Icc a₀ b := fun _ ht => ⟨hbuffer.le.trans ht.1, ht.2⟩
  have hsubreg : _root_.Set.Ioc a b ⊆ _root_.Set.Ioc a₀ b := fun _ ht => ⟨hbuffer.trans ht.1, ht.2⟩
  have hcarrier₂' : _root_.Set.Icc a b ⊆ D₂.carrier := hsub.trans hcarrier₂
  have hregular₂' : _root_.Set.Ioc a b ⊆ D₂.regular := hsubreg.trans hregular₂
  have hric₂ : ∀ t ∈ _root_.Set.Icc a₀ b, ∀ x : M, ∀ v : TangentSpace I x,
      |ricciTensor (S₂.base.metric t) x v v| ≤
        ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt R₂) *
          (S₂.base.metric t).inner x v v := by
    intro t ht x v
    exact ricci_quadratic_form_bound_of_solution_curvature_bound S₂ x v (hcurv₂ t ht x)
  have hcomplete₂a : RiemannianMetricComplete (I := I) (S₂.base.metric a) :=
    complete_of_ricBound S₂ hS₂ hcarrier₂ hregular₂ (by positivity) hric₂ hcomplete₂
      ⟨hbuffer.le, hab.le⟩
  have hcomplete₁ : RiemannianMetricComplete (I := I) (S₁.base.metric a) := by
    rw [hinit]
    exact hcomplete₂a
  obtain ⟨Λ₁, hΛ₁, heq₁⟩ :=
    exists_uniform_metric_equivalence_on_closed_interval_of_curvature_bound
      S₁ hS₁ hab hcarrier₁ (fun t ht => hregular₁ ⟨ht.1, ht.2.le⟩) hcurv₁
  obtain ⟨Λ₂, hΛ₂, heq₂⟩ :=
    exists_uniform_metric_equivalence_on_closed_interval_of_curvature_bound
      S₂ hS₂ hab hcarrier₂' (fun t ht => hregular₂' ⟨ht.1, ht.2.le⟩)
      (fun t ht => hcurv₂ t (hsub ht))
  have hC : 1 ≤ Λ₁ * Λ₂ := one_le_mul_of_one_le_of_one_le hΛ₁ hΛ₂
  have hequiv : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M, ∀ v : TangentSpace I x,
      (Λ₁ * Λ₂)⁻¹ * (S₁.base.metric t).inner x v v ≤ (S₂.base.metric t).inner x v v ∧
        (S₂.base.metric t).inner x v v ≤ (Λ₁ * Λ₂) * (S₁.base.metric t).inner x v v := by
    intro t ht x v
    have heq₂' : MetricUniformEquivalentOn (I := I) _root_.Set.univ
        (S₁.base.metric a) (S₂.base.metric t) Λ₂ := by
      rw [hinit]
      exact heq₂ t (_root_.Set.Ioo_subset_Icc_self ht)
    exact ((metricUniformEquivalentOn_symm (heq₁ t (_root_.Set.Ioo_subset_Icc_self ht))).trans
      heq₂').2 x (_root_.Set.mem_univ x) v
  obtain ⟨B, _, hdensity⟩ := forwardUniqueDensity_uniform_bound_on_closed_interval
    S₁ S₂ hS₁ hS₂ hab hcarrier₁ hcarrier₂' hregular₁ hregular₂'
    hcomplete₁ hR₁ hR₂ hcurv₁ (fun t ht => hcurv₂ t (hsub ht)) hinit
  obtain ⟨D₁', D₂', _, _, hderiv₁, hderiv₂⟩ :=
    exists_uniform_curvature_first_second_derivative_bounds_on_slab S₂ hS₂
      hbuffer hab.le hcarrier₂ hregular₂ hcomplete₂ hR₂ hcurv₂
  have hjoint {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
      (hS : IsSolutionOn S) (hr : _root_.Set.Ioo a b ⊆ D.regular) :
      ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => Tensor.Coordinates.chartGramMatrix
            (I := I) (S.base.metric p.1) α p.2 i j)
          (_root_.Set.Ioo a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) := by
    apply chartGramMatrix_joint_contMDiffOn
    intro p hp
    exact (hS.smoothMetric.metricCLMSmoothAt
      (D.regular_isOpen.mem_nhds (hr hp.1))).contMDiffWithinAt
  have hpde {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
      (hS : IsSolutionOn S) (hr : _root_.Set.Ioo a b ⊆ D.regular) :
      ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : ℝ => (S.base.metric s).inner x v w)
          (-2 * ricciTensor (S.base.metric t) x v w) (_root_.Set.Ici a) t := by
    intro t ht x v w
    simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
      metricRicciAt_apply_eq_ricciTensor, SolutionOn.family_metric] using
      (metricDerivAt S hS ⟨t, hr ht⟩ x v w).hasDerivWithinAt (s := _root_.Set.Ici a)
  have hr₁ : _root_.Set.Ioo a b ⊆ D₁.regular := fun t ht => hregular₁ ⟨ht.1, ht.2.le⟩
  have hr₂ : _root_.Set.Ioo a b ⊆ D₂.regular := fun t ht => hregular₂' ⟨ht.1, ht.2.le⟩
  obtain ⟨q, hq, hRic⟩ := Geometry.Riemannian.BonnetMyers.exists_ricciBoundedBelow_of_normSqRm_le
    (S₁.base.metric a) (hcurv₁ a (left_mem_Icc.mpr hab.le))
  have hzero : ∀ x : M,
      _root_.Filter.Tendsto (fun t => forwardUniqueDensity S₁.base.metric S₂.base.metric t x)
        (𝓝[>] a) (𝓝 0) := by
    intro x
    simpa only [nhdsWithin_Ioo_eq_nhdsGT hab] using
      tendsto_forwardUniqueDensity_zero_of_complete_bounded_curvature
        S₁ S₂ hS₁ hS₂ hab hcarrier₁ hcarrier₂' hregular₁ hregular₂'
        hcomplete₁ hR₁ hR₂ hcurv₁ (fun t ht => hcurv₂ t (hsub ht)) hinit x
  exact forward_unique_on_Ioo_of_uniform_bounds_of_bounded_density_tendsto_zero
    S₁.base.metric S₂.base.metric hab (hjoint S₁ hS₁ hr₁) (hjoint S₂ hS₂ hr₂)
    (hpde S₁ hS₁ hr₁) (hpde S₂ hS₂ hr₂) hC hequiv
    (fun t ht => hcurv₁ t (_root_.Set.Ioo_subset_Icc_self ht))
    (fun t ht => hcurv₂ t (hsub (_root_.Set.Ioo_subset_Icc_self ht)))
    (fun t ht => hderiv₁ t (_root_.Set.Ioo_subset_Icc_self ht))
    (fun t ht => hderiv₂ t (_root_.Set.Ioo_subset_Icc_self ht))
    (S₁.base.metric a) hcomplete₁ (Classical.arbitrary M) hq hΛ₁ hRic
    (fun t ht x v => (heq₁ t (_root_.Set.Ioo_subset_Icc_self ht)).2 x (_root_.Set.mem_univ x) v)
    (fun t ht => hdensity t (_root_.Set.Ioo_subset_Icc_self ht)) hzero

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.forward_unique_on_Ioo_of_complete_bounded_curvature_of_buffered_reference_of_innerProductSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.forward_unique_on_Ioo_of_complete_bounded_curvature_of_buffered_reference_of_innerProductSpace target :: scope.openDecls } }

private theorem forward_unique_on_closed_slab_of_complete_bounded_curvature_of_buffered_reference_of_innerProductSpace
    {D₁ D₂ : RealTimeInterval}
    (S₁ : SolutionOn (I := I) (M := M) D₁)
    (S₂ : SolutionOn (I := I) (M := M) D₂)
    (hS₁ : IsSolutionOn S₁) (hS₂ : IsSolutionOn S₂)
    {a₀ a b R₁ R₂ : ℝ} (hbuffer : a₀ < a) (hab : a < b)
    (hcarrier₁ : _root_.Set.Icc a b ⊆ D₁.carrier)
    (hcarrier₂ : _root_.Set.Icc a₀ b ⊆ D₂.carrier)
    (hregular₁ : _root_.Set.Ioo a b ⊆ D₁.regular)
    (hregular₂ : _root_.Set.Ioo a₀ b ⊆ D₂.regular)
    (hcomplete₂ : RiemannianMetricComplete (I := I) (S₂.base.metric a₀))
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (hcurv₁ : ∀ t ∈ _root_.Set.Icc a b, ∀ x : M,
      normSq0S (S₁.base.metric t) x 4 (S₁.base.rm04 t x) ≤ R₁)
    (hcurv₂ : ∀ t ∈ _root_.Set.Icc a₀ b, ∀ x : M,
      normSq0S (S₂.base.metric t) x 4 (S₂.base.rm04 t x) ≤ R₂)
    (hinit : S₁.base.metric a = S₂.base.metric a) :
    ∀ t ∈ _root_.Set.Icc a b, S₁.base.metric t = S₂.base.metric t := by
  apply solution_metric_eqOn_Icc_of_eqOn_Ico S₁ S₂ hS₁ hS₂ hab hcarrier₁
    (fun t ht => hcarrier₂ ⟨hbuffer.le.trans ht.1, ht.2⟩)
  intro t ht
  rcases ht.1.eq_or_lt with hat | hat
  · subst t
    exact hinit
  obtain ⟨c, htc, hcb⟩ := exists_between ht.2
  have hac : a < c := hat.trans htc
  exact forward_unique_on_Ioo_of_complete_bounded_curvature_of_buffered_reference_of_innerProductSpace
    S₁ S₂ hS₁ hS₂ hbuffer hac
    (fun s hs => hcarrier₁ ⟨hs.1, hs.2.trans hcb.le⟩)
    (fun s hs => hcarrier₂ ⟨hs.1, hs.2.trans hcb.le⟩)
    (fun s hs => hregular₁ ⟨hs.1, hs.2.trans_lt hcb⟩)
    (fun s hs => hregular₂ ⟨hs.1, hs.2.trans_lt hcb⟩)
    hcomplete₂ hR₁ hR₂
    (fun s hs => hcurv₁ s ⟨hs.1, hs.2.trans hcb.le⟩)
    (fun s hs => hcurv₂ s ⟨hs.1, hs.2.trans hcb.le⟩) hinit t ⟨hat, htc⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.forward_unique_on_closed_slab_of_complete_bounded_curvature_of_buffered_reference_of_innerProductSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.forward_unique_on_closed_slab_of_complete_bounded_curvature_of_buffered_reference_of_innerProductSpace target :: scope.openDecls } }

end InnerProductModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem forward_unique_on_closed_slab_of_complete_bounded_curvature_of_buffered_reference
    {D₁ D₂ : RealTimeInterval}
    (S₁ : SolutionOn (I := I) (M := M) D₁)
    (S₂ : SolutionOn (I := I) (M := M) D₂)
    (hS₁ : IsSolutionOn S₁) (hS₂ : IsSolutionOn S₂)
    {a₀ a b R₁ R₂ : ℝ} (hbuffer : a₀ < a) (hab : a < b)
    (hcarrier₁ : _root_.Set.Icc a b ⊆ D₁.carrier)
    (hcarrier₂ : _root_.Set.Icc a₀ b ⊆ D₂.carrier)
    (hregular₁ : _root_.Set.Ioo a b ⊆ D₁.regular)
    (hregular₂ : _root_.Set.Ioo a₀ b ⊆ D₂.regular)
    (hcomplete₂ : RiemannianMetricComplete (I := I) (S₂.base.metric a₀))
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (hcurv₁ : ∀ t ∈ _root_.Set.Icc a b, ∀ x : M,
      normSq0S (S₁.base.metric t) x 4 (S₁.base.rm04 t x) ≤ R₁)
    (hcurv₂ : ∀ t ∈ _root_.Set.Icc a₀ b, ∀ x : M,
      normSq0S (S₂.base.metric t) x 4 (S₂.base.rm04 t x) ≤ R₂)
    (hinit : S₁.base.metric a = S₂.base.metric a) :
    ∀ t ∈ _root_.Set.Icc a b, S₁.base.metric t = S₂.base.metric t := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ E)) ℝ).symm
  let J := I.transContinuousLinearEquiv e
  let Φ := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e
  let U₁ : SolutionOn (I := J) (M := M) D₁ := S₁.pullback Φ.symm
  let U₂ : SolutionOn (I := J) (M := M) D₂ := S₂.pullback Φ.symm
  have hU₁ : IsSolutionOn U₁ := hS₁.pullback S₁ Φ.symm
  have hU₂ : IsSolutionOn U₂ := hS₂.pullback S₂ Φ.symm
  let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :=
    ⟨by simpa using (NeZero.ne (Module.finrank ℝ E))⟩
  have hcompleteU : RiemannianMetricComplete (I := J) (U₂.base.metric a₀) :=
    RiemannianMetricComplete.pullbackCross (S₂.base.metric a₀) Φ.symm hcomplete₂
  have hcurv_trans {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
      {K : Set ℝ} {R : ℝ}
      (hc : ∀ t ∈ K, ∀ x : M,
        normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ R) :
      ∀ t ∈ K, ∀ x : M,
        normSq0S (I := J) ((S.pullback Φ.symm).base.metric t) x 4
          ((S.pullback Φ.symm).base.rm04 t x) ≤ R := by
    intro t ht x
    change normSq0S (I := J) (Diffeomorph.pullbackMetricCross (S.base.metric t) Φ.symm)
      x 4 (metricRm04At (I := J)
        (Diffeomorph.pullbackMetricCross (S.base.metric t) Φ.symm) x) ≤ R
    rw [riemannNormSq_cross]
    exact hc t ht (Φ.symm x)
  have hinitU : U₁.base.metric a = U₂.base.metric a := by
    change Diffeomorph.pullbackMetricCross (S₁.base.metric a) Φ.symm =
      Diffeomorph.pullbackMetricCross (S₂.base.metric a) Φ.symm
    rw [hinit]
  have heq := forward_unique_on_closed_slab_of_complete_bounded_curvature_of_buffered_reference_of_innerProductSpace
    U₁ U₂ hU₁ hU₂ hbuffer hab hcarrier₁ hcarrier₂ hregular₁ hregular₂
    hcompleteU hR₁ hR₂ (hcurv_trans S₁ hcurv₁) (hcurv_trans S₂ hcurv₂) hinitU
  intro t ht
  have hpull := congrArg (fun g : SmoothRiemannianMetric J M =>
    Diffeomorph.pullbackMetricCross g Φ) (heq t ht)
  change Diffeomorph.pullbackMetricCross ((S₁.base.metric t).transContinuousLinearEquiv e) Φ =
    Diffeomorph.pullbackMetricCross ((S₂.base.metric t).transContinuousLinearEquiv e) Φ at hpull
  exact (SmoothRiemannianMetric.pullback_transContinuousLinearEquiv (S₁.base.metric t) e).symm.trans
    (hpull.trans (SmoothRiemannianMetric.pullback_transContinuousLinearEquiv (S₂.base.metric t) e))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.forward_unique_on_closed_slab_of_complete_bounded_curvature_of_buffered_reference then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.forward_unique_on_closed_slab_of_complete_bounded_curvature_of_buffered_reference"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.forward_unique_on_closed_slab_of_complete_bounded_curvature_of_buffered_reference ``Submission.DifferentialGeometry.PDE.RicciFlow.forward_unique_on_closed_slab_of_complete_bounded_curvature_of_buffered_reference

theorem forward_unique_on_Ioo_of_complete_bounded_curvature_of_buffered_reference
    {D₁ D₂ : RealTimeInterval}
    (S₁ : SolutionOn (I := I) (M := M) D₁)
    (S₂ : SolutionOn (I := I) (M := M) D₂)
    (hS₁ : IsSolutionOn S₁) (hS₂ : IsSolutionOn S₂)
    {a₀ a b R₁ R₂ : ℝ} (hbuffer : a₀ < a) (hab : a < b)
    (hcarrier₁ : _root_.Set.Icc a b ⊆ D₁.carrier)
    (hcarrier₂ : _root_.Set.Icc a₀ b ⊆ D₂.carrier)
    (hregular₁ : _root_.Set.Ioo a b ⊆ D₁.regular)
    (hregular₂ : _root_.Set.Ioo a₀ b ⊆ D₂.regular)
    (hcomplete₂ : RiemannianMetricComplete (I := I) (S₂.base.metric a₀))
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (hcurv₁ : ∀ t ∈ _root_.Set.Icc a b, ∀ x : M,
      normSq0S (S₁.base.metric t) x 4 (S₁.base.rm04 t x) ≤ R₁)
    (hcurv₂ : ∀ t ∈ _root_.Set.Icc a₀ b, ∀ x : M,
      normSq0S (S₂.base.metric t) x 4 (S₂.base.rm04 t x) ≤ R₂)
    (hinit : S₁.base.metric a = S₂.base.metric a) :
    ∀ t ∈ _root_.Set.Ioo a b, S₁.base.metric t = S₂.base.metric t := by
  have heq := forward_unique_on_closed_slab_of_complete_bounded_curvature_of_buffered_reference
    S₁ S₂ hS₁ hS₂ hbuffer hab hcarrier₁ hcarrier₂
    hregular₁ hregular₂ hcomplete₂ hR₁ hR₂ hcurv₁ hcurv₂ hinit
  exact fun t ht => heq t (_root_.Set.Ioo_subset_Icc_self ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.forward_unique_on_Ioo_of_complete_bounded_curvature_of_buffered_reference then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.forward_unique_on_Ioo_of_complete_bounded_curvature_of_buffered_reference"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.forward_unique_on_Ioo_of_complete_bounded_curvature_of_buffered_reference ``Submission.DifferentialGeometry.PDE.RicciFlow.forward_unique_on_Ioo_of_complete_bounded_curvature_of_buffered_reference

end DifferentialGeometry.PDE.RicciFlow

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem forward_unique_on_closedOpen_of_complete_bounded_curvature_of_buffered_reference
    {D : RealTimeInterval} {a b s c R : ℝ} (hsc : s < c)
    (U : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen s c hsc))
    (S : SolutionOn (I := I) (M := M) D)
    (hU : IsSolutionOn U) (hS : IsSolutionOn S)
    (hs : s ∈ _root_.Set.Ioo a b) (hcb : c < b)
    (hregular : _root_.Set.Ioo a b ⊆ D.regular)
    (hcomplete : ∀ t ∈ _root_.Set.Ioo a b, RiemannianMetricComplete (S.base.metric t))
    (hbound : ∀ u v, a < u → u < v → v < b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ _root_.Set.Icc u v, ∀ x : M,
        normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : 0 ≤ R)
    (hUbound : ∀ t ∈ _root_.Set.Ico s c, ∀ x : M,
      normSq0S (U.base.metric t) x 4 (U.base.rm04 t x) ≤ R)
    (hinit : U.base.metric s = S.base.metric s) :
    ∀ t ∈ _root_.Set.Ico s c, U.base.metric t = S.base.metric t := by
  obtain ⟨r, har, hrs⟩ := exists_between hs.1
  intro t ht
  obtain ⟨v, htv, hvc⟩ := exists_between ht.2
  have hsv : s < v := ht.1.trans_lt htv
  have hvb : v < b := hvc.trans hcb
  obtain ⟨C, hC, hcurv⟩ := hbound r v har (hrs.trans hsv) hvb
  have hsub : _root_.Set.Icc r v ⊆ _root_.Set.Ioo a b := fun q hq =>
    ⟨har.trans_le hq.1, hq.2.trans_lt hvb⟩
  exact forward_unique_on_closed_slab_of_complete_bounded_curvature_of_buffered_reference
    U S hU hS hrs hsv
    (fun q hq => ⟨hq.1, hq.2.trans_lt hvc⟩)
    (fun q hq => D.regular_subset (hregular (hsub hq)))
    (fun q hq => ⟨hq.1, hq.2.trans hvc⟩)
    (fun q hq => hregular (hsub (_root_.Set.Ioo_subset_Icc_self hq)))
    (hcomplete r ⟨har, hrs.trans hs.2⟩) hR hC
    (fun q hq => hUbound q ⟨hq.1, hq.2.trans_lt hvc⟩)
    hcurv hinit t ⟨ht.1, htv.le⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.forward_unique_on_closedOpen_of_complete_bounded_curvature_of_buffered_reference then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.forward_unique_on_closedOpen_of_complete_bounded_curvature_of_buffered_reference"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.forward_unique_on_closedOpen_of_complete_bounded_curvature_of_buffered_reference ``Submission.DifferentialGeometry.PDE.RicciFlow.forward_unique_on_closedOpen_of_complete_bounded_curvature_of_buffered_reference

end DifferentialGeometry.PDE.RicciFlow
