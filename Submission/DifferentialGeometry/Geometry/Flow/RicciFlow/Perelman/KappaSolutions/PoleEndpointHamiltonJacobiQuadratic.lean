import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointHamiltonJacobiAE
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointJointDifferentiabilityTail
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.GradientPullback
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.SpacetimeQuadraticForm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
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

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instBorelSpace_differentialGeometry target :: scope.openDecls } }

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

namespace HalfLineMetricConvergenceData

theorem eventually_ae_poleEndpoint_redLength_hamilton_jacobi_eq_chartGradientBilin
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (x : P.M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : _root_.Set.MapsTo (extChartAt I x).symm W J) :
    ∀ᶠ k in _root_.Filter.atTop,
      ∀ᵐ z ∂(DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod _root_.MeasureTheory.MeasureSpace.volume,
        z ∈ W ×ˢ _root_.Set.Ioo a c →
        let i := phi (co.φ k)
        let v := (extChartAt I x).symm z.1
        let ell := fun w : E × ℝ => redLength ((U).term i).S 0 p
          (Phi.map (co.φ k) ((extChartAt I x).symm w.1)) w.2
        let d := (fderiv ℝ ell z).comp (ContinuousLinearMap.inl ℝ E ℝ)
        fderiv ℝ ell z (0, 1) + (1 / 2 : ℝ) *
          chartGradientBilin (gSeqExt Phi R bf hsrc htgt (co.φ k) (1 - z.2)) x v d d -
          (1 / 2 : ℝ) * ((Y).term i).S.scalar (1 - z.2) (Phi.map (co.φ k) v) +
          ell z / (2 * z.2) = 0 := by
  have hae := eventually_ae_differentiableAt_poleEndpoint_redLength_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ (c := c) ha hbase
    x hW hWt hWJ
  have henergy := co.strictMono.tendsto_atTop.eventually
    (eventually_normGradSqFun_gSeqExt_eq_on_compact Phi R bf hsrc htgt hJ)
  obtain ⟨N, hN⟩ := Phi.source_subset hJ
  have hsource : ∀ᶠ k in _root_.Filter.atTop, J ⊆ Phi.source (co.φ k) :=
    (co.strictMono.tendsto_atTop.eventually (_root_.Filter.eventually_ge_atTop N)).mono
      fun k hk => hN (co.φ k) hk
  filter_upwards [hae, henergy, hsource] with k hkd hke hksource
  filter_upwards [hkd] with z hdz
  intro hzw
  let i := phi (co.φ k)
  let v := (extChartAt I x).symm z.1
  let y := Phi.map (co.φ k) v
  let ell := fun w : E × ℝ => redLength ((U).term i).S 0 p
    (Phi.map (co.φ k) ((extChartAt I x).symm w.1)) w.2
  have hcoord : DifferentiableAt ℝ ell z := hdz hzw
  have hpull : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun w : ℝ × P.M => redLength ((U).term i).S 0 p
        (Phi.map (co.φ k) w.2) w.1) (z.2, v) :=
    DifferentialGeometry.Topology.Manifold.mdifferentiableAt_prod_of_differentiableAt_chart
      (fun w : ℝ × P.M => redLength ((U).term i).S 0 p (Phi.map (co.φ k) w.2) w.1)
      x (hWt hzw.1) z.2 hcoord
  have hlocal := (Phi.partialDiffeomorph (co.φ k)).isLocalDiffeomorphAt I I ∞
    (hksource (hWJ hzw.1))
  have hdiff : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun w : ℝ × F.M => redLength ((U).term i).S 0 p w.2 w.1) (z.2, y) :=
    hlocal.mdifferentiableAt_prodMap_of_comp (by simp) z.2 hpull
  have hpos : 0 < z.2 := (zero_lt_one.trans_le ha).trans hzw.2.1
  have hk := ancient_redLength_hamilton_jacobi_eq_of_mdifferentiableAt
    ((U).term i) (hancient i) hpos p y hdiff
  have htime : deriv (fun s => redLength ((U).term i).S 0 p y s) z.2 =
      fderiv ℝ ell z (0, 1) := by
    exact (hcoord.hasFDerivAt.comp_hasDerivAt z.2
      ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv
  rw [htime] at hk
  have hslice : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun w => redLength ((U).term i).S 0 p w z.2) y :=
    hdiff.comp y (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have hmetric : ((Y).term i).S.base.metric (1 - z.2) =
      ((U).term i).S.base.metric (-z.2) := by
    rw [poleEndpointRescaledFlowSeq_metric_eq_shift]
    congr 1
    ring
  have hscalar : ((Y).term i).S.scalar (1 - z.2) y =
      ((U).term i).S.scalar (-z.2) y := by
    change metricScalarAt (((Y).term i).S.base.metric (1 - z.2)) y =
      metricScalarAt (((U).term i).S.base.metric (-z.2)) y
    rw [hmetric]
    rfl
  have he := hke (1 - z.2) v (hWJ hzw.1)
    (fun w => redLength ((U).term i).S 0 p w z.2) hslice
  have hv : v ∈ (chartAt H x).source := by
    simpa only [extChartAt_source] using (extChartAt I x).map_target (hWt hzw.1)
  have hchart := normGradSqFun_eq_chartGradientBilin_comp_inl
    (gSeqExt Phi R bf hsrc htgt (co.φ k) (1 - z.2))
    (f := fun w s => redLength ((U).term i).S 0 p (Phi.map (co.φ k) w) s)
    (t := z.2) hv (by
      simpa only [v, (extChartAt I x).right_inv (hWt hzw.1), Prod.mk.eta] using hcoord)
  simp only [v, (extChartAt I x).right_inv (hWt hzw.1), Prod.mk.eta] at hchart
  rw [hmetric] at he
  have heq := hchart.symm.trans he
  dsimp only at hk ⊢
  rw [heq, hscalar]
  exact hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_ae_poleEndpoint_redLength_hamilton_jacobi_eq_chartGradientBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_ae_poleEndpoint_redLength_hamilton_jacobi_eq_chartGradientBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_ae_poleEndpoint_redLength_hamilton_jacobi_eq_chartGradientBilin ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_ae_poleEndpoint_redLength_hamilton_jacobi_eq_chartGradientBilin

theorem ae_eventually_poleEndpoint_redLength_hamilton_jacobi_eq_chartGradientBilin
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (x : P.M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : _root_.Set.MapsTo (extChartAt I x).symm W J) :
    ∀ᵐ z ∂(DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod _root_.MeasureTheory.MeasureSpace.volume,
      z ∈ W ×ˢ _root_.Set.Ioo a c → ∀ᶠ k in _root_.Filter.atTop,
        let i := phi (co.φ k)
        let v := (extChartAt I x).symm z.1
        let ell := fun w : E × ℝ => redLength ((U).term i).S 0 p
          (Phi.map (co.φ k) ((extChartAt I x).symm w.1)) w.2
        let d := (fderiv ℝ ell z).comp (ContinuousLinearMap.inl ℝ E ℝ)
        fderiv ℝ ell z (0, 1) + (1 / 2 : ℝ) *
          chartGradientBilin (gSeqExt Phi R bf hsrc htgt (co.φ k) (1 - z.2)) x v d d -
          (1 / 2 : ℝ) * ((Y).term i).S.scalar (1 - z.2) (Phi.map (co.φ k) v) +
          ell z / (2 * z.2) = 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_ae_poleEndpoint_redLength_hamilton_jacobi_eq_chartGradientBilin
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ (c := c) ha hbase
      x hW hWt hWJ)
  have hcommon := ae_all_iff.mpr (fun k : {k : ℕ // N ≤ k} => hN k.1 k.2)
  filter_upwards [hcommon] with z hz
  intro hzw
  filter_upwards [_root_.Filter.eventually_ge_atTop N] with k hk
  exact hz ⟨k, hk⟩ hzw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_eventually_poleEndpoint_redLength_hamilton_jacobi_eq_chartGradientBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_eventually_poleEndpoint_redLength_hamilton_jacobi_eq_chartGradientBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_eventually_poleEndpoint_redLength_hamilton_jacobi_eq_chartGradientBilin ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_eventually_poleEndpoint_redLength_hamilton_jacobi_eq_chartGradientBilin

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
