import Submission.DifferentialGeometry.Analysis.Schauder.Holder.LocalDerivativeLimit
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.ChartHessianBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineCoefficientBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointChartGradientBound
import Mathlib.Analysis.SpecificLimits.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.Analysis.Schauder
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal _root_.BigOperators _root_.NNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_3 : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_3 : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_2 : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2 : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2 target :: scope.openDecls } }

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "θ" => (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1))

namespace HalfLineMetricConvergenceData

theorem poleEndpoint_redLength_limit_chart_terminal_fderiv
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A : ℝ}
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ _root_.Set.Icc 1 2,
      _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) _root_.Filter.atTop (𝓝 (ell (y, t))))
    (hsmooth : ∀ n : ℕ, ContMDiff I 𝓘(ℝ) ∞ (fun x => ell (x, θ n)))
    (hsol : ∀ n : ℕ, gradientRicciSoliton (co.gInf (1 - θ n))
      (⟨fun x => ell (x, θ n), hsmooth n⟩ : C^∞⟮I, P.M; ℝ⟯) (1 / θ n))
    (α : P.M) (center : E) {r rMid rOut : ℝ}
    (hr : r < rMid) (hMid : rMid < rOut)
    (hWt : Metric.closedBall center rOut ⊆ (extChartAt I α).target)
    (hWJ : _root_.Set.MapsTo (extChartAt I α).symm (Metric.closedBall center rOut) J) :
    (∀ y ∈ Metric.ball center rMid,
      DifferentiableAt ℝ (fun w : E => ell ((extChartAt I α).symm w, 1)) y) ∧
      TendstoUniformlyOn
        (fun n => fderiv ℝ (fun w : E => ell ((extChartAt I α).symm w, θ n)))
        (fderiv ℝ (fun w : E => ell ((extChartAt I α).symm w, 1)))
        atTop (Metric.ball center r) := by
  classical
  have hθpos (n : ℕ) : 1 < θ n := by
    change 1 < 1 + 1 / ((n : ℝ) + 1)
    have h : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hθband (n : ℕ) : θ n ∈ _root_.Set.Icc (1 : ℝ) 2 := by
    refine ⟨(hθpos n).le, ?_⟩
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hdiv : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr hn
    change 1 + 1 / ((n : ℝ) + 1) ≤ 2
    linarith
  have hθlim : _root_.Filter.Tendsto θ _root_.Filter.atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let fn : ℕ → E → ℝ := fun n w => ell ((extChartAt I α).symm w, θ n)
  let f₁ : E → ℝ := fun w => ell ((extChartAt I α).symm w, 1)
  have hinner : Metric.ball center rMid ⊆ Metric.closedBall center rOut := by
    intro y hy
    exact Metric.mem_closedBall.mpr ((Metric.mem_ball.mp hy).trans hMid).le
  have hLL : LocallyLipschitzOn (Metric.closedBall center rOut ×ˢ _root_.Set.Icc (1 : ℝ) 2)
      (fun v : E × ℝ => ell ((extChartAt I α).symm v.1, v.2)) :=
    locallyLipschitzOn_poleEndpoint_redLength_limit_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ le_rfl hbase
      rho hrho ell hconv α hWt hWJ
  obtain ⟨Ktime, hKtime⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    ((_root_.ProperSpace.isCompact_closedBall center rOut).prod _root_.CompactIccSpace.isCompact_Icc) hLL
  have hvalue : TendstoUniformlyOn fn f₁ _root_.Filter.atTop (Metric.ball center rMid) := by
    have hzero : _root_.Filter.Tendsto (fun n => (Ktime : ℝ) * _root_.Dist.dist (1 : ℝ) (θ n)) _root_.Filter.atTop (𝓝 0) := by
      simpa only [dist_self, _root_.MulZeroClass.mul_zero] using
        (tendsto_const_nhds (x := (Ktime : ℝ))).mul
          ((tendsto_const_nhds (x := (1 : ℝ))).dist hθlim)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hzero.eventually (gt_mem_nhds hε)] with n hn
    intro y hy
    have hv := hKtime.dist_le_mul (y, 1) ⟨hinner hy, by norm_num⟩
      (y, θ n) ⟨hinner hy, hθband n⟩
    have hval : _root_.Dist.dist (f₁ y) (fn n y) ≤ (Ktime : ℝ) * _root_.Dist.dist (1 : ℝ) (θ n) := by
      simpa only [fn, f₁, dist_prod_same_left] using hv
    exact hval.trans_lt hn
  obtain ⟨Kgrad, hKgrad⟩ := exists_poleEndpoint_redLength_limit_chart_fderiv_bound
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ le_rfl hbase
      rho hrho ell hconv α center hMid hWt hWJ
  obtain ⟨B, hB⟩ := co.exists_chart_coefficient_bound_on_closed_band Phi
    (by rfl : (Y).D.carrier = Iic 0) (by intro t ht; exact ht)
    α (_root_.ProperSpace.isCompact_closedBall center rOut) hWt (by norm_num : (1 : ℝ) < 2)
  let L : ℝ≥0 := Kgrad * ∑ k : Fin (Module.finrank ℝ E), ‖chartModelBasis E k‖₊
  let Kbasis : ℝ≥0 := (Module.finrank ℝ E : ℝ≥0) *
    ‖(chartModelBasis E).equivFunL.toContinuousLinearMap‖₊
  let C : ℝ≥0 := (B + B + (Module.finrank ℝ E : ℝ≥0) * B * L) * Kbasis ^ 2
  have hfn (n : ℕ) (y : E) (hy : y ∈ Metric.ball center rMid) :
      ContDiffAt ℝ ∞ (fn n) y := by
    exact (scalarOnE_contDiffOn (I := I) α (hsmooth n)).contDiffAt
      ((isOpen_extChartAt_target (I := I) α).mem_nhds (hWt (hinner hy)))
  have hsecond (n : ℕ) (y : E) (hy : y ∈ Metric.ball center rMid) :
      ‖fderiv ℝ (fderiv ℝ (fn n)) y‖ ≤ (C : ℝ) := by
    let x := (extChartAt I α).symm y
    let f : C^∞⟮I, P.M; ℝ⟯ := ⟨fun x => ell (x, θ n), hsmooth n⟩
    have hyT : y ∈ (extChartAt I α).target := hWt (hinner hy)
    have hx : x ∈ (chartAt H α).source := by
      simpa only [extChartAt_source] using (extChartAt I α).map_target hyT
    have hxy : extChartAt I α x = y := (extChartAt I α).right_inv hyT
    obtain ⟨hG, hQ, hΓ⟩ := hB (θ n) (hθband n) y (hinner hy)
    have hL (k : Fin (Module.finrank ℝ E)) :
        |partialDeriv k (scalarOnE (I := I) α f) (extChartAt I α x)| ≤ (L : ℝ) := by
      rw [hxy]
      change ‖fderiv ℝ (fn n) y (chartModelBasis E k)‖ ≤ (L : ℝ)
      calc
        _ ≤ ‖fderiv ℝ (fn n) y‖ * ‖chartModelBasis E k‖ :=
          (fderiv ℝ (fn n) y).le_opNorm _
        _ ≤ (Kgrad : ℝ) * ‖chartModelBasis E k‖ :=
          mul_le_mul_of_nonneg_right
            (hKgrad (θ n) (hθband n) y (Metric.mem_closedBall.mpr
              (Metric.mem_ball.mp hy).le)) (norm_nonneg _)
        _ ≤ (L : ℝ) := by
          have hk : ‖chartModelBasis E k‖ ≤
              ∑ j : Fin (Module.finrank ℝ E), ‖chartModelBasis E j‖ :=
            Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ k)
          simpa only [L, NNReal.coe_mul, NNReal.coe_sum, coe_nnnorm] using
            mul_le_mul_of_nonneg_left hk Kgrad.coe_nonneg
    have hnorm := gradientRicciSoliton_norm_fderiv_fderiv_scalarOnE_le
      (hsol n) α hx B B B L hG hQ
      (by intro i j k; simpa only [hxy] using hΓ i j k) hL
    rw [hxy] at hnorm
    have hσ : |(1 / θ n) / 2| ≤ (1 : ℝ) := by
      have htn : 0 < θ n := zero_lt_one.trans (hθpos n)
      rw [abs_of_nonneg (by positivity)]
      have h1 : (1 : ℝ) / θ n ≤ 1 := (div_le_one (by linarith [hθpos n])).mpr
        (hθpos n).le
      linarith
    have hT : |(1 / θ n) / 2| * (B : ℝ) + B +
        (Module.finrank ℝ E : ℝ) * B * L ≤
        B + B + (Module.finrank ℝ E : ℝ) * B * L := by
      nlinarith [mul_le_mul_of_nonneg_right hσ B.coe_nonneg]
    refine hnorm.trans ?_
    change _ ≤ ((B : ℝ) + B + (Module.finrank ℝ E : ℝ) * B * L) *
      ((Module.finrank ℝ E : ℝ) *
        ‖(chartModelBasis E).equivFunL.toContinuousLinearMap‖) ^ 2
    exact mul_le_mul_of_nonneg_right hT (sq_nonneg _)
  have hholder (n : ℕ) : HolderOnWith C 1 (fderiv ℝ (fn n))
      (Metric.ball center rMid) := by
    apply LipschitzOnWith.holderOnWith
    apply (convex_ball center rMid).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · intro y hy
      exact ((hfn n y hy).fderiv_right (m := 1) (by decide)).differentiableAt_one
    · intro y hy
      exact_mod_cast hsecond n y hy
  have hdiff : ∀ n, ∀ y ∈ Metric.ball center rMid, DifferentiableAt ℝ (fn n) y :=
    fun n y hy => (hfn n y hy).differentiableAt (by simp)
  have hlimit := differentiableOn_ball_of_tendstoUniformlyOn_of_holder_fderiv
    (by norm_num : (0 : ℝ≥0) < 1) hdiff hholder hvalue
  refine ⟨fun y hy => (hlimit y hy).differentiableAt (Metric.isOpen_ball.mem_nhds hy), ?_⟩
  exact tendstoUniformlyOn_fderiv_ball_of_holderOnWith hr
    (by norm_num : (0 : ℝ≥0) < 1) hdiff hholder hvalue

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_chart_terminal_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_chart_terminal_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_chart_terminal_fderiv ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_chart_terminal_fderiv

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
