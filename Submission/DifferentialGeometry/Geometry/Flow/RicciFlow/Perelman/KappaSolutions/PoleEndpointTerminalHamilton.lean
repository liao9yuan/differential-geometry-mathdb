import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointTerminalFirstDerivative
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.ClosedHalfLineSolution
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedRegularity
import Submission.DifferentialGeometry.Geometry.Metric.Family.Regularity.JointDifferentialOperator
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.HamiltonNormalizationLimit

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
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal _root_.BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

namespace HalfLineMetricConvergenceData

private theorem tendsto_chartInvGramMatrix_and_scalar_at_zero
    {X : PointedFlowSeq.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps X P subseq) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcarrier : X.D.carrier = _root_.Set.Iic 0) (hregular : _root_.Set.Iio 0 ⊆ X.D.regular)
    (α : P.M) {x : P.M} (hx : x ∈ (chartAt H α).source)
    {a : ℝ} (ha : a < 0) (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈ _root_.Set.Icc a 0) (htend : _root_.Filter.Tendsto t _root_.Filter.atTop (𝓝 0)) :
    (∀ i j : Fin (Module.finrank ℝ E),
      _root_.Filter.Tendsto (fun n => chartInvGramMatrix (co.gInf (t n)) α x i j) _root_.Filter.atTop
        (𝓝 (chartInvGramMatrix (co.gInf 0) α x i j))) ∧
      _root_.Filter.Tendsto (fun n => metricScalarAt (co.gInf (t n)) x) _root_.Filter.atTop
        (𝓝 (metricScalarAt (co.gInf 0) x)) := by
  let S : SolutionOn (I := I) (M := P.M) X.D := { base := { metric := co.gInf } }
  have hS : IsSolutionOn S := co.isSolutionOn Phi hcarrier hregular
  have hslab : _root_.Set.Icc (a - 1) 0 ⊆ X.D.carrier := by
    rw [hcarrier]
    exact _root_.Set.Icc_subset_Iic_self
  have hreg : _root_.Set.Ioo (a - 1) 0 ⊆ X.D.regular := Ioo_subset_Iio_self.trans hregular
  have hmet :=
    DifferentialGeometry.PDE.RicciFlow.solution_metricCLMSection_contMDiffOn_closed
      S hS
    (sub_lt_self a zero_lt_one) ha hslab hreg
  have hxsrc : x ∈ (extChartAt I α).source := by
    simpa only [extChartAt_source] using hx
  have hxint : extChartAt I α x ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact (extChartAt I α).map_source hxsrc
  have hzero : (0 : ℝ) ∈ _root_.Set.Icc a 0 := ⟨ha.le, le_rfl⟩
  constructor
  · intro i j
    have hc := chartInvGramOnE_continuousOn_of_contMDiffOn co.gInf hmet α i j
    have hpath : _root_.Filter.Tendsto (fun n => (t n, extChartAt I α x)) _root_.Filter.atTop
        (𝓝[_root_.Set.Icc a 0 ×ˢ interior (extChartAt I α).target] (0, extChartAt I α x)) :=
      tendsto_nhdsWithin_iff.mpr ⟨htend.prodMk_nhds tendsto_const_nhds,
        Eventually.of_forall fun n => ⟨ht n, hxint⟩⟩
    have hh := (hc (0, extChartAt I α x) ⟨hzero, hxint⟩).tendsto.comp hpath
    simpa only [Function.comp_def, chartInvGramOnE_def,
      (extChartAt I α).left_inv hxsrc] using hh
  · have hzeroD : (0 : ℝ) ∈ X.D.carrier := by
      rw [hcarrier]
      exact (le_rfl : (0 : ℝ) ≤ 0)
    have hpath : _root_.Filter.Tendsto (fun n => (t n, x)) _root_.Filter.atTop
        (𝓝[X.D.carrier ×ˢ (_root_.Set.univ : Set P.M)] (0, x)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨htend.prodMk_nhds tendsto_const_nhds, Eventually.of_forall fun n => ?_⟩
      refine ⟨?_, _root_.Set.mem_univ x⟩
      rw [hcarrier]
      exact (ht n).2
    have hscalar : ContinuousOn
        (fun z : ℝ × P.M => metricScalarAt (co.gInf z.1) z.2)
        (X.D.carrier ×ˢ (_root_.Set.univ : Set P.M)) := hS.scalarCont
    have hlimit := (hscalar (0, x) ⟨hzeroD, _root_.Set.mem_univ x⟩).tendsto.comp hpath
    exact hlimit

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_chartInvGramMatrix_and_scalar_at_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_chartInvGramMatrix_and_scalar_at_zero target :: scope.openDecls } }

section PoleEndpoint

variable {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b) {phi : ℕ → ℕ}

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instTopologicalSpaceM : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instTopologicalSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instTopologicalSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instChartedSpaceM : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instChartedSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instChartedSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instIsManifoldRealSomeENatTopM : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instIsManifoldRealSomeENatTopM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instIsManifoldRealSomeENatTopM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instSigmaCompactSpaceM : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instSigmaCompactSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instSigmaCompactSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instT2SpaceM : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instT2SpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instT2SpaceM target :: scope.openDecls } }

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "θ" => (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1))

theorem poleEndpoint_redLength_limit_terminal_hamilton
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {A : ℝ}
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y : P.M, ∀ t ∈ _root_.Set.Icc 1 2,
      _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) _root_.Filter.atTop (𝓝 (ell (y, t))))
    (hsmooth : ∀ n : ℕ, ContMDiff I 𝓘(ℝ) ∞ (fun x => ell (x, θ n)))
    (hsol : ∀ n : ℕ, gradientRicciSoliton (co.gInf (1 - θ n))
      (⟨fun x => ell (x, θ n), hsmooth n⟩ : C^∞⟮I, P.M; ℝ⟯) (1 / θ n))
    (hnormal : ∀ n : ℕ, ∀ x : P.M,
      metricScalarAt (co.gInf (1 - θ n)) x +
        normGradSqFun (co.gInf (1 - θ n)) (fun x => ell (x, θ n)) x =
          (1 / θ n) * ell (x, θ n)) :
    ∀ x : P.M, metricScalarAt (co.gInf 0) x +
      normGradSqFun (co.gInf 0) (fun x => ell (x, 1)) x = ell (x, 1) := by
  intro x
  classical
  let z : E := extChartAt I x x
  have hzt : z ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (mem_extChartAt_source x)
  obtain ⟨rOut, hrOut, hWt⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((isOpen_extChartAt_target (I := I) x).mem_nhds hzt)
  let J : Set P.M := (extChartAt I x).symm '' Metric.closedBall z rOut
  have hJ : IsCompact J := (_root_.ProperSpace.isCompact_closedBall z rOut).image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := I) x).mono hWt)
  have hWJ : _root_.Set.MapsTo (extChartAt I x).symm (Metric.closedBall z rOut) J :=
    fun y hy => _root_.Set.mem_image_of_mem _ hy
  have hconvJ : ∀ y ∈ J, ∀ t ∈ _root_.Set.Icc 1 2,
      _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) _root_.Filter.atTop (𝓝 (ell (y, t))) :=
    fun y _ t ht => hconv y t ht
  obtain ⟨hdiff, hD⟩ := poleEndpoint_redLength_limit_chart_terminal_fderiv
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ hbase
      rho hrho ell hconvJ hsmooth hsol x z
      (r := rOut / 4) (rMid := rOut / 2) (rOut := rOut)
      (by linarith) (by linarith) hWt hWJ
  have hzsmall : z ∈ Metric.ball z (rOut / 4) := Metric.mem_ball_self (by positivity)
  have hzmid : z ∈ Metric.ball z (rOut / 2) := Metric.mem_ball_self (by positivity)
  have hzclosed : z ∈ Metric.closedBall z rOut := Metric.mem_closedBall_self hrOut.le
  have hθpos (n : ℕ) : 1 < θ n := by
    change 1 < 1 + 1 / ((n : ℝ) + 1)
    have h : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hθband (n : ℕ) : θ n ∈ _root_.Set.Icc (1 : ℝ) 2 := by
    refine ⟨(hθpos n).le, ?_⟩
    have hdiv : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
    change 1 + 1 / ((n : ℝ) + 1) ≤ 2
    linarith
  have hθlim : _root_.Filter.Tendsto θ _root_.Filter.atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht : ∀ n : ℕ, 1 - θ n ∈ _root_.Set.Icc (-1 : ℝ) 0 := by
    intro n
    obtain ⟨hlo, hhi⟩ := hθband n
    constructor <;> linarith
  have htend : _root_.Filter.Tendsto (fun n => 1 - θ n) _root_.Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub hθlim
  obtain ⟨hInv, hScalar⟩ := tendsto_chartInvGramMatrix_and_scalar_at_zero
    Phi co (by rfl : (Y).D.carrier = Iic 0) (by intro t ht; exact ht)
      x (mem_chart_source H x) (by norm_num : (-1 : ℝ) < 0)
      (fun n => 1 - θ n) ht htend
  have hf₁ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => ell (y, 1)) x := by
    rw [mdifferentiableAt_iff_source_of_mem_source (mem_chart_source H x),
      I.range_eq_univ, mdifferentiableWithinAt_univ,
      mdifferentiableAt_iff_differentiableAt]
    exact hdiff z hzmid
  have hGrad := tendsto_normGradSqFun_of_chart
    (fun n => co.gInf (1 - θ n)) (co.gInf 0)
    (fun n y => ell (y, θ n)) (fun y => ell (y, 1)) x
    (mem_chart_source H x)
    (Eventually.of_forall fun n => (hsmooth n).mdifferentiableAt (by simp)) hf₁ hInv
    (fun i => ((continuous_id.clm_apply (continuous_const :
      Continuous (fun _ : E →L[ℝ] ℝ => chartModelBasis E i))).tendsto _).comp
        (hD.tendsto_at hzsmall))
  have hLL := locallyLipschitzOn_poleEndpoint_redLength_limit_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ le_rfl hbase
      rho hrho ell hconvJ x hWt hWJ
  have hpath : _root_.Filter.Tendsto (fun n => (z, θ n)) _root_.Filter.atTop
      (𝓝[Metric.closedBall z rOut ×ˢ _root_.Set.Icc (1 : ℝ) 2] (z, 1)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.prodMk_nhds hθlim,
      Eventually.of_forall fun n => ⟨hzclosed, hθband n⟩⟩
  have hval : _root_.Filter.Tendsto (fun n => ell (x, θ n)) _root_.Filter.atTop (𝓝 (ell (x, 1))) := by
    have hv := (hLL.continuousOn (z, 1) ⟨hzclosed, by norm_num⟩).tendsto.comp hpath
    simpa only [Function.comp_def, z, extChartAt_to_inv] using hv
  have hσ : _root_.Filter.Tendsto (fun n => 1 / θ n) _root_.Filter.atTop (𝓝 (1 : ℝ)) := by
    simpa only [Pi.div_def, one_div_one] using
      (tendsto_const_nhds (x := (1 : ℝ))).div hθlim (by norm_num : (1 : ℝ) ≠ 0)
  have hleft := hScalar.add hGrad
  have hright : _root_.Filter.Tendsto (fun n => (1 / θ n) * ell (x, θ n)) _root_.Filter.atTop
      (𝓝 (ell (x, 1))) := by simpa only [one_mul] using hσ.mul hval
  apply tendsto_nhds_unique_of_eventuallyEq hleft hright
  exact Eventually.of_forall fun n => hnormal n x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_terminal_hamilton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_terminal_hamilton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_terminal_hamilton ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_terminal_hamilton

end PoleEndpoint

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
