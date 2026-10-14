import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ParabolicComparisonContinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonTimeRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalComparisonComposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P]
  [IsManifold I3 ∞ P] [T2Space P] [SigmaCompactSpace P]

private local instance comparisonStabilityC1 : IsManifold I3 1 P :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.comparisonStabilityC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.comparisonStabilityC1 target :: scope.openDecls } }

theorem exists_rescaledMetric_comparison_tolerance_on_compact
    {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := P) D) (hS : IsSolutionOn S)
    {a t depth Q : ℝ} (hdepth : 0 < depth) (hQ : 0 < Q)
    (hbuffer : a < t - depth / Q)
    (hslab : _root_.Set.Icc a t ⊆ D.carrier) (hreg : _root_.Set.Ioo a t ⊆ D.regular)
    (U : TopologicalSpace.Opens P) (hUcompact : IsCompact (closure (U : Set P)))
    {K : Set P} (hK : IsCompact K) (hKU : K ⊆ U)
    (order : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ eta beta : ℝ, 0 < eta ∧ 0 < beta ∧
      ∀ c : ℝ, ∀ hc : 0 < c, |c - Q| < eta →
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M],
      ∀ {D' : RealTimeInterval} (T : SolutionOn (I := I3) (M := M) D'), IsSolutionOn T →
      ∀ {b : ℝ}, b < -depth → _root_.Set.Icc b 0 ⊆ D'.carrier → _root_.Set.Ioo b 0 ⊆ D'.regular →
      ∀ F : PartialDiffeomorph I3 I3 P M ∞, (U : Set P) ⊆ F.source →
      MetricComparisonOn (rescaledMetric S t c hc) T.base.metric F U
        (_root_.Set.Icc (-depth) 0) order beta →
      Nonempty (MetricComparisonOn (rescaledMetric S t Q hQ) T.base.metric F K
        (_root_.Set.Icc (-depth) 0) order eps) := by
  let alpha := _root_.Min.min (eps / 2) (backgroundJetSmallness ThreeSpace order)
  have halpha : 0 < alpha := lt_min (by positivity) (backgroundJetSmallness_pos _ _)
  have halphaeps : alpha ≤ eps / 2 := min_le_left _ _
  have halphasmall : alpha ≤ backgroundJetSmallness ThreeSpace order := min_le_right _ _
  let B := backgroundJetConstant ThreeSpace order * ((order : ℝ) + 1)
  have hBpos : 0 < B := mul_pos (backgroundJetConstant_pos _ _) (by positivity)
  let beta := (eps / 2) / B
  have hbeta : 0 < beta := div_pos (by positivity) hBpos
  have herror : alpha + B * beta ≤ eps := by
    have hh : B * beta = eps / 2 := by
      dsimp only [beta]
      field_simp
    linarith
  have hleft : (a - t) * Q < -depth := by
    have hh := mul_lt_mul_of_pos_right hbuffer hQ
    simp only [sub_mul, div_mul_cancel₀ _ hQ.ne'] at hh
    nlinarith
  let start := ((a - t) * Q - depth) / 2
  have hstart : start < -depth := by dsimp only [start]; linarith
  have hstartQ : a < parabolicTime t Q start := by
    have hh : (a - t) * Q < start := by dsimp only [start]; linarith
    have hh' := (lt_div_iff₀ hQ).mpr hh
    change a < t + start / Q
    linarith
  have hat : a < t := hbuffer.trans (sub_lt_self _ (div_pos hdepth hQ))
  have ht : t ∈ D.carrier := hslab ⟨hat.le, le_rfl⟩
  have hvalid : ∀ᶠ c in 𝓝 Q, 0 < c ∧ a < parabolicTime t c start := by
    have hcont : ContinuousAt (fun c : ℝ => parabolicTime t c start) Q :=
      continuousAt_const.add (continuousAt_const.div continuousAt_id hQ.ne')
    filter_upwards [eventually_gt_nhds hQ, hcont.eventually (eventually_gt_nhds hstartQ)] with c hc hs
    exact ⟨hc, hs⟩
  have hnear := (eventually_rescaledMetric_comparison_on_compact S hS hdepth hQ hbuffer
    hslab hreg hUcompact order halpha).and hvalid
  obtain ⟨eta, heta, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨eta, beta, heta, hbeta, ?_⟩
  intro c hc hclose M _ _ _ _ _ D' T hT b hb hTdomain hTregular F hF C'
  obtain ⟨⟨_hc, ⟨C₀⟩⟩, _hc', hstartc⟩ := hball (by
    simpa only [Metric.mem_ball, Real.dist_eq] using hclose)
  let Phi := PartialDiffeomorph.refl (I := I3) P
  let C : MetricComparisonOn (rescaledMetric S t Q hQ) (rescaledMetric S t c hc)
      Phi U (_root_.Set.Icc (-depth) 0) order alpha := C₀.mono subset_closure le_rfl le_rfl
  have hscaledDomain (R : ℝ) (hR : 0 < R) (hstartR : a < parabolicTime t R start) :
      Icc start 0 ⊆ (parabolicInterval D t R ht).carrier := by
    intro s hs
    apply hslab
    change a ≤ t + s / R ∧ t + s / R ≤ t
    have hlo := (div_le_div_iff_of_pos_right hR).mpr hs.1
    have hhi := div_nonpos_of_nonpos_of_nonneg hs.2 hR.le
    change a < t + start / R at hstartR
    constructor <;> linarith
  have hscaledRegular (R : ℝ) (hR : 0 < R) (hstartR : a < parabolicTime t R start) :
      Ioo start 0 ⊆ (parabolicInterval D t R ht).regular := by
    intro s hs
    apply hreg
    change a < t + s / R ∧ t + s / R < t
    have hlo := (div_lt_div_iff_of_pos_right hR).mpr hs.1
    have hhi := div_neg_of_neg_of_pos hs.2 hR
    change a < t + start / R at hstartR
    constructor <;> linarith
  let Sq := parabolicSolution S t Q hQ ht
  let Sc := parabolicSolution S t c hc ht
  have hSq : IsSolutionOn Sq := parabolicSolution_isSolutionOn S hS t Q hQ ht
  have hSc : IsSolutionOn Sc := parabolicSolution_isSolutionOn S hS t c hc ht
  have hqDomain := hscaledDomain Q hQ hstartQ
  have hcDomain := hscaledDomain c hc hstartc
  have hqRegular := hscaledRegular Q hQ hstartQ
  have hcRegular := hscaledRegular c hc hstartc
  obtain ⟨Cfinal⟩ := MetricComparisonOn.exists_trans_on_compact Phi F U
    (_root_.Set.subset_univ _) hF (fun _ hy => hy) C C' le_rfl hbeta.le halpha halphasmall (by
      intro q s hs _hu y hy v
      exact (C.jet_contDiffOn_of_solutions Sq hSq Sc hSc hstart hstart
        (neg_lt_zero.mpr hdepth) hqDomain hqRegular hcDomain hcRegular q y hy v s hs).differentiableWithinAt (by simp)) (by
      intro q s hs z hz v
      obtain ⟨y, hy, rfl⟩ := hz
      exact (C'.jet_contDiffOn_of_solutions Sc hSc T hT hstart hb
        (neg_lt_zero.mpr hdepth) hcDomain hcRegular hTdomain hTregular q y hy v s hs).differentiableWithinAt (by simp)) hK hKU
  exact ⟨Cfinal.mono subset_rfl le_rfl herror⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_rescaledMetric_comparison_tolerance_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_rescaledMetric_comparison_tolerance_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_rescaledMetric_comparison_tolerance_on_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_rescaledMetric_comparison_tolerance_on_compact

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
