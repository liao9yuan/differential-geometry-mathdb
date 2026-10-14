import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductIntegralBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.PhysicalCoordinates
import Submission.DifferentialGeometry.Analysis.Calculus.TimeJet.PartialDerivatives

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic
open _root_.Submission.DifferentialGeometry.Analysis

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : RealTimeInterval} {a b s u : ℝ}

theorem axial_weighted_total_curvature_le (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (hc : c.IsSolutionOn B.family.metric lambda J)
    (has : a ≤ s) (hsu : s < u) (hub : u ≤ b) (hinterval : _root_.Set.Icc a u ⊆ J)
    {L₀ Θ₀ δ p q t C G₀ K r : ℝ}
    (hL₀ : c.length B.family.metric lambda a ≤ L₀)
    (hΘ₀ : c.totalCurvature B.family.metric lambda a ≤ Θ₀)
    (hpq : p ≤ q) (hqp : q ≤ p + 1) (ht : t ∈ _root_.Set.Icc s u)
    (hsmall : c.arcTotalCurvature B.family.metric lambda p q s ≤ δ)
    (hC : 0 < C) (hG₀ : 0 ≤ G₀) (hK : 0 ≤ K) (hr : 0 < r) (hr1 : r ≤ 1)
    (A : (E × ℝ) →L[ℝ] F) (β : M × ℝ) (L : F →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (center : ℝ) :
    let γ := fun y τ => c.physicalLift lambda y τ
    let G := fun τ => coverProductMetric (B.family.metric τ) 1 zero_lt_one
    let W := fun y τ => A (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ y τ))
    let d := r / (8 * C)
    let φ := fun y τ => ballCutoff center (d / 2) d (L (W y τ))
    let Q := Real.exp ((B.C + B.B₀) * (b - a)) * (Θ₀ + L₀)
    let α := 64 * CutoffProfile.derivBound * C ^ 2 * Real.sqrt K / r
    let H₀ := 1024 * CutoffProfile.derivBound * C ^ 4 + 32 * CutoffProfile.derivBound * G₀ * C ^ 3
    (∀ τ ∈ _root_.Set.Icc s u, ∀ y ∈ _root_.Set.Icc p q, γ y τ ∈ (chartAt (ModelProd H ℝ) β).source) →
    (∀ τ ∈ _root_.Set.Ioo s t, ∀ y ∈ _root_.Set.Icc p q, ∀ V : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ y τ),
      ‖A ((_root_.FiberBundle.trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt
        ℝ (γ y τ) V)‖ ≤ C * Real.sqrt ((G τ).inner (γ y τ) V V)) →
    (∀ τ ∈ _root_.Set.Ioo s t, ∀ y ∈ _root_.Set.Icc p q, ∀ v w : E × ℝ,
      ‖A (chartChristoffelContraction (G τ) β v w (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ y τ)))‖ ≤
        G₀ * ‖A v‖ * ‖A w‖) →
    (∀ τ ∈ _root_.Set.Ioo s t, ∀ y ∈ _root_.Set.Icc p q, c.curvatureSq B.family.metric lambda y τ ≤ K / (τ - s)) →
    (∀ τ ∈ _root_.Set.Ioo s t, d ≤ _root_.Dist.dist (L (W p τ)) center ∧ d ≤ _root_.Dist.dist (L (W q τ)) center) →
    (∫ y in p..q, φ y t * c.curvature B.family.metric lambda y t * c.speed B.family.metric lambda y t) ≤
      δ + Q * (2 * α * Real.sqrt (t - s) + (H₀ / r ^ 2 + (B.C + B.B₀)) * (t - s)) +
        B.C * Q * (t - s) := by
  dsimp only
  intro hchart hupper hΓ hcurv hboundary
  let W := fun y τ => A (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (c.physicalLift lambda y τ))
  let d := r / (8 * C)
  let φ := fun y τ => ballCutoff center (d / 2) d (L (W y τ))
  let φt := fun y τ => derivWithin (φ y) J τ
  have hsub : _root_.Set.Icc s u ⊆ J := (_root_.Set.Icc_subset_Icc has le_rfl).trans hinterval
  have hdomain : _root_.Set.Icc p q ×ˢ _root_.Set.Icc s u ⊆ _root_.Set.univ ×ˢ J := _root_.Set.prod_mono (_root_.Set.subset_univ _) hsub
  have hφsmooth (τ : ℝ) (hτ : τ ∈ _root_.Set.Icc s u) (y : ℝ) (hy : y ∈ _root_.Set.Icc p q) :
      ContDiffWithinAt ℝ ∞ (fun z : ℝ × ℝ => φ z.1 z.2) (_root_.Set.univ ×ˢ J) (y, τ) :=
    (ballCutoff_contDiff center (d / 2) d).contDiffAt.comp_contDiffWithinAt (y, τ)
      (L.contDiff.contDiffAt.comp_contDiffWithinAt (y, τ)
        (c.contDiffWithinAt_physical_chart lambda hc.smooth A β y τ (hsub hτ) (hchart τ hτ y hy)))
  have hφc : ContinuousOn (fun z : ℝ × ℝ => φ z.1 z.2) (_root_.Set.Icc p q ×ˢ _root_.Set.Icc s u) :=
    fun z hz => ((hφsmooth z.2 hz.2 z.1 hz.1).continuousWithinAt).mono hdomain
  have hφtc : ContinuousOn (fun z : ℝ × ℝ => φt z.1 z.2) (_root_.Set.Icc p q ×ˢ _root_.Set.Icc s u) := by
    intro z hz
    exact ((contDiffWithinAt_derivWithin_snd hJ ⟨mem_univ z.1, hsub hz.2⟩
      (hφsmooth z.2 hz.2 z.1 hz.1) (m := ∞) (by simp)).continuousWithinAt).mono hdomain
  have hφt : ∀ y ∈ _root_.Set.Icc p q, ∀ τ ∈ _root_.Set.Icc s u,
      HasDerivWithinAt (φ y) (φt y τ) (_root_.Set.Icc s u) τ := by
    intro y hy τ hτ
    have hh : ContDiffWithinAt ℝ ∞ (φ y) J τ :=
      (hφsmooth τ hτ y hy).comp (f := fun σ : ℝ => (y, σ)) τ
        (contDiffWithinAt_const.prodMk contDiffWithinAt_id) (fun σ hσ => ⟨mem_univ y, hσ⟩)
    exact (hh.differentiableWithinAt (by simp)).hasDerivWithinAt.mono hsub
  have hφxx : ∀ τ ∈ _root_.Set.Ioo s t, ∀ y ∈ _root_.Set.Icc p q, ContDiffAt ℝ 2 (fun z => φ z τ) y := by
    intro τ hτ y hy
    have hh : ContDiffAt ℝ ∞ (fun z => φ z τ) y := by
      apply contDiffWithinAt_univ.mp
      exact (hφsmooth τ ⟨hτ.1.le, hτ.2.le.trans ht.2⟩ y hy).comp (f := fun z : ℝ => (z, τ)) y
        (contDiffWithinAt_id.prodMk contDiffWithinAt_const)
        (fun z _ => ⟨mem_univ z, hsub ⟨hτ.1.le, hτ.2.le.trans ht.2⟩⟩)
    exact hh.of_le (WithTop.coe_le_coe.mpr le_top)
  have hφrange (τ y : ℝ) : φ y τ ∈ _root_.Set.Icc 0 1 := ballCutoff_mem_Icc _ _ _ _
  have hd : 0 < d := by dsimp only [d]; positivity
  have hφboundary : ∀ τ ∈ _root_.Set.Ioo s t, φ p τ = 0 ∧ φ q τ = 0 ∧
      deriv (fun y => φ y τ) p = 0 ∧ deriv (fun y => φ y τ) q = 0 := by
    intro τ hτ
    have hzero (y : ℝ) (hy : d ≤ _root_.Dist.dist (L (W y τ)) center) : φ y τ = 0 :=
      ballCutoff_eq_zero_of_le_dist (by positivity) (by linarith) hy
    have hp := hzero p (hboundary τ hτ).1
    have hq := hzero q (hboundary τ hτ).2
    have hderiv (y : ℝ) (hy : φ y τ = 0) : deriv (fun z => φ z τ) y = 0 := by
      have hmin : IsLocalMin (fun z => φ z τ) y := by
        filter_upwards [] with z
        rw [hy]
        exact (hφrange τ z).1
      exact hmin.deriv_eq_zero
    exact ⟨hp, hq, hderiv p hp, hderiv q hq⟩
  have hcut : ∀ τ ∈ _root_.Set.Ioo s t, ∀ y ∈ _root_.Set.Icc p q,
      φt y τ + c.ds B.family.metric lambda (c.ds B.family.metric lambda φ) y τ ≤
        (64 * CutoffProfile.derivBound * C ^ 2 * Real.sqrt K / r) / Real.sqrt (τ - s) +
          (1024 * CutoffProfile.derivBound * C ^ 4 + 32 * CutoffProfile.derivBound * G₀ * C ^ 3) / r ^ 2 := by
    intro τ hτ y hy
    have hτu : τ ∈ _root_.Set.Icc s u := ⟨hτ.1.le, hτ.2.le.trans ht.2⟩
    have hh := c.physical_axial_cutoff_derivative_bound_of_curvatureSq_le B.family.metric lambda hlambda
      hc A β y τ (hsub hτu) (hJ τ (hsub hτu)) hC hG₀ hK (sub_pos.mpr hτ.1) hr hr1
      (hcurv τ hτ y hy) L hL center (hchart τ hτu y hy) (hupper τ hτ y hy) (hΓ τ hτ y hy)
    refine (add_le_add (le_abs_self (φt y τ))
      (le_abs_self (c.ds B.family.metric lambda (c.ds B.family.metric lambda φ) y τ))).trans ?_
    exact hh
  have hJnn := CutoffProfile.derivBound_nonneg
  exact c.weighted_total_curvature_le_of_initial_and_sqrt_cutoff_bound B lambda hlambda hJ hc has hsu hub
    hinterval hL₀ hΘ₀ hpq hqp ht hsmall hφc hφtc hφt hφxx (fun τ _ y _ => hφrange τ y) hφboundary
    (by positivity) (by positivity) hcut

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.axial_weighted_total_curvature_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.axial_weighted_total_curvature_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.axial_weighted_total_curvature_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.axial_weighted_total_curvature_le

theorem axial_arcTotalCurvature_le (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (hc : c.IsSolutionOn B.family.metric lambda J)
    (has : a ≤ s) (hsu : s < u) (hub : u ≤ b) (hinterval : _root_.Set.Icc a u ⊆ J)
    {L₀ Θ₀ δ p q p₀ q₀ t C G₀ K r : ℝ}
    (hL₀ : c.length B.family.metric lambda a ≤ L₀)
    (hΘ₀ : c.totalCurvature B.family.metric lambda a ≤ Θ₀)
    (hpq : p ≤ q) (hqp : q ≤ p + 1)
    (hpp₀ : p ≤ p₀) (hp₀q₀ : p₀ ≤ q₀) (hq₀q : q₀ ≤ q) (ht : t ∈ _root_.Set.Icc s u)
    (hsmall : c.arcTotalCurvature B.family.metric lambda p q s ≤ δ)
    (hC : 0 < C) (hG₀ : 0 ≤ G₀) (hK : 0 ≤ K) (hr : 0 < r) (hr1 : r ≤ 1)
    (A : (E × ℝ) →L[ℝ] F) (β : M × ℝ) (L : F →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (center : ℝ) :
    let γ := fun y τ => c.physicalLift lambda y τ
    let G := fun τ => coverProductMetric (B.family.metric τ) 1 zero_lt_one
    let W := fun y τ => A (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ y τ))
    let d := r / (8 * C)
    let Q := Real.exp ((B.C + B.B₀) * (b - a)) * (Θ₀ + L₀)
    let α := 64 * CutoffProfile.derivBound * C ^ 2 * Real.sqrt K / r
    let H₀ := 1024 * CutoffProfile.derivBound * C ^ 4 + 32 * CutoffProfile.derivBound * G₀ * C ^ 3
    (∀ τ ∈ _root_.Set.Icc s u, ∀ y ∈ _root_.Set.Icc p q, γ y τ ∈ (chartAt (ModelProd H ℝ) β).source) →
    (∀ τ ∈ _root_.Set.Ioo s t, ∀ y ∈ _root_.Set.Icc p q, ∀ V : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ y τ),
      ‖A ((_root_.FiberBundle.trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt
        ℝ (γ y τ) V)‖ ≤ C * Real.sqrt ((G τ).inner (γ y τ) V V)) →
    (∀ τ ∈ _root_.Set.Ioo s t, ∀ y ∈ _root_.Set.Icc p q, ∀ v w : E × ℝ,
      ‖A (chartChristoffelContraction (G τ) β v w (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ y τ)))‖ ≤
        G₀ * ‖A v‖ * ‖A w‖) →
    (∀ τ ∈ _root_.Set.Ioo s t, ∀ y ∈ _root_.Set.Icc p q, c.curvatureSq B.family.metric lambda y τ ≤ K / (τ - s)) →
    (∀ τ ∈ _root_.Set.Ioo s t, d ≤ _root_.Dist.dist (L (W p τ)) center ∧ d ≤ _root_.Dist.dist (L (W q τ)) center) →
    (∀ y ∈ _root_.Set.Icc p₀ q₀, _root_.Dist.dist (L (W y t)) center ≤ d / 2) →
    c.arcTotalCurvature B.family.metric lambda p₀ q₀ t ≤
      δ + Q * (2 * α * Real.sqrt (t - s) + (H₀ / r ^ 2 + (B.C + B.B₀)) * (t - s)) +
        B.C * Q * (t - s) := by
  dsimp only
  intro hchart hupper hΓ hcurv hboundary hcentral
  have hweighted := c.axial_weighted_total_curvature_le B lambda hlambda hJ hc has hsu hub hinterval
    hL₀ hΘ₀ hpq hqp ht hsmall hC hG₀ hK hr hr1 A β L hL center hchart hupper hΓ hcurv hboundary
  let W := fun y τ => A (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (c.physicalLift lambda y τ))
  let d := r / (8 * C)
  let φ := fun y => ballCutoff center (d / 2) d (L (W y t))
  have htt : t ∈ J := hinterval ⟨has.trans ht.1, ht.2⟩
  have hφc : ContinuousOn φ (_root_.Set.Icc p q) := by
    intro y hy
    have hh := c.contDiffWithinAt_physical_chart lambda hc.smooth A β y t htt (hchart t ht y hy)
    have hW : ContDiffAt ℝ ∞ (fun z => W z t) y := by
      apply contDiffWithinAt_univ.mp
      exact hh.comp (f := fun z : ℝ => (z, t)) y
        (contDiffWithinAt_id.prodMk contDiffWithinAt_const) (fun z _ => ⟨mem_univ z, htt⟩)
    exact ((ballCutoff_contDiff center (d / 2) d).contDiffAt.comp y
      (L.contDiff.contDiffAt.comp y hW)).continuousAt.continuousWithinAt
  let Ahat : QuotientProductAtlas I M := quotientProductAtlas
  let _ := Ahat.charts
  let _ := Ahat.smoothManifold
  let ghat := fun τ => quotientProductMetric Ahat (B.family.metric τ) lambda hlambda
  have hs := c.smoothOn_map Ahat hc.smooth
  have hi := (c.map_immersedOn_iff Ahat hc.smooth).mpr hc.immersed
  have hsq : Continuous (fun y => c.curvatureSq B.family.metric lambda y t) := by
    simpa only [ghat, c.map_curvatureSq_eq Ahat B.family.metric lambda hlambda hc.smooth hc.immersed _ t htt]
      using (c.map.curvatureSq_contDiff ghat J hs hi t htt).continuous
  have hsp := (c.speed_contDiff_of_immersedOn B.family.metric lambda hlambda hc.smooth hc.immersed t htt).continuous
  have hiw : IntervalIntegrable
      (fun y => φ y * c.curvature B.family.metric lambda y t * c.speed B.family.metric lambda y t)
      volume p q := by
    apply ContinuousOn.intervalIntegrable
    rw [_root_.Set.uIcc_of_le hpq]
    exact (hφc.mul hsq.sqrt.continuousOn).mul hsp.continuousOn
  have hn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (_root_.Set.Ioc p q)]
      (fun y => φ y * c.curvature B.family.metric lambda y t * c.speed B.family.metric lambda y t) := by
    filter_upwards [] with y
    exact mul_nonneg (mul_nonneg (ballCutoff_mem_Icc _ _ _ _).1 (Real.sqrt_nonneg _))
      (c.speed_nonneg B.family.metric lambda y t)
  have hmono := intervalIntegral.integral_mono_interval hpp₀ hp₀q₀ hq₀q hn hiw
  have hd : 0 < d := by dsimp only [d]; positivity
  have heq : c.arcTotalCurvature B.family.metric lambda p₀ q₀ t =
      ∫ y in p₀..q₀, φ y * c.curvature B.family.metric lambda y t * c.speed B.family.metric lambda y t := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [_root_.Set.uIcc_of_le hp₀q₀] at hy
    have hφ : φ y = 1 := ballCutoff_eq_one_of_mem_closedBall (by positivity) (by linarith)
      (hcentral y hy)
    change _ = φ y * _ * _
    rw [hφ, one_mul]
  exact heq.trans_le (hmono.trans hweighted)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.axial_arcTotalCurvature_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.axial_arcTotalCurvature_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.axial_arcTotalCurvature_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.axial_arcTotalCurvature_le

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
