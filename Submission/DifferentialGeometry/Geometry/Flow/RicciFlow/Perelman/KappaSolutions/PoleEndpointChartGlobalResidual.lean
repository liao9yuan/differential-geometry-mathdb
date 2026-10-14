import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointChartResidualSupport
import Mathlib.Topology.Order.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set

namespace DifferentialGeometry.Analysis.Parabolic

private theorem exists_nested_Ioo_of_isCompact_subset_Ioi
    {K : Set ℝ} {r : ℝ} (hK : IsCompact K) (hKr : K ⊆ _root_.Set.Ioi r) :
    ∃ a a' c' c : ℝ, r < a ∧ a < a' ∧ a' ≤ c' ∧ c' < c ∧ K ⊆ _root_.Set.Ioo a' c' := by
  obtain ⟨m, hrm, hm⟩ :=
    hK.exists_forall_le' (f := fun t : ℝ => t) continuousOn_id (fun t ht => hKr ht)
  obtain ⟨a, hra, ham⟩ := exists_between hrm
  obtain ⟨a', haa', ha'm⟩ := exists_between ham
  obtain ⟨B, hB⟩ := hK.bddAbove
  obtain ⟨c', hc'⟩ := _root_.NoMaxOrder.exists_gt (_root_.Max.max B a')
  obtain ⟨c, hc⟩ := _root_.NoMaxOrder.exists_gt c'
  refine ⟨a, a', c', c, hra, haa', (le_max_right B a').trans hc'.le, hc, ?_⟩
  intro t ht
  exact ⟨ha'm.trans_le (hm t ht), ((hB ht).trans (le_max_left B a')).trans_lt hc'⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.exists_nested_Ioo_of_isCompact_subset_Ioi
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.exists_nested_Ioo_of_isCompact_subset_Ioi target :: scope.openDecls } }

private theorem exists_nested_Ioo_of_hasCompactSupport
    {E : Type*} [TopologicalSpace E] {ψ : ℝ × E → ℝ} {r : ℝ} {T : Set E}
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ _root_.Set.Ioi r ×ˢ T) :
    ∃ a a' c' c : ℝ, r < a ∧ a < a' ∧ a' ≤ c' ∧ c' < c ∧
      tsupport ψ ⊆ _root_.Set.Ioo a' c' ×ˢ T := by
  have hK : IsCompact (Prod.fst '' tsupport ψ) := hψc.image continuous_fst
  have hKr : Prod.fst '' tsupport ψ ⊆ _root_.Set.Ioi r := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hψs hz).1
  obtain ⟨a, a', c', c, hra, haa', ha'c', hc'c, hKac⟩ :=
    exists_nested_Ioo_of_isCompact_subset_Ioi hK hKr
  refine ⟨a, a', c', c, hra, haa', ha'c', hc'c, ?_⟩
  intro z hz
  exact ⟨hKac ⟨z, hz, rfl⟩, (hψs hz).2⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.exists_nested_Ioo_of_hasCompactSupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.exists_nested_Ioo_of_hasCompactSupport target :: scope.openDecls } }

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.Analysis

open _root_.Filter
open scoped _root_.Topology _root_.Submission.Topology

private theorem time_spatial_derivatives_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℝ × E → ℝ) {z : ℝ × E} (hz : z ∉ tsupport ψ) :
    deriv (fun t => ψ (t, z.2)) z.1 = 0 ∧
      fderiv ℝ (fun y => ψ (z.1, y)) z.2 = 0 := by
  have ht : z.1 ∉ tsupport (fun t => ψ (t, z.2)) := by
    intro ht
    exact hz (tsupport_comp_subset_preimage ψ
      (continuous_id.prodMk continuous_const) ht)
  have hx : z.2 ∉ tsupport (fun y => ψ (z.1, y)) := by
    intro hx
    exact hz (tsupport_comp_subset_preimage ψ
      (continuous_const.prodMk continuous_id) hx)
  exact ⟨deriv_of_notMem_tsupport ht, fderiv_of_notMem_tsupport ℝ hx⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.time_spatial_derivatives_eq_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.time_spatial_derivatives_eq_zero target :: scope.openDecls } }

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

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
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpaceM : MeasurableSpace F.M := borel F.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpaceM : BorelSpace F.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instBorelSpaceM target :: scope.openDecls } }

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpaceM_1 : MeasurableSpace P.M := borel P.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpaceM_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpaceM_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpaceM_1 : BorelSpace P.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpaceM_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instBorelSpaceM_1 target :: scope.openDecls } }

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

namespace HalfLineMetricConvergenceData

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic

theorem integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_on_Ioi_of_ancient
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (hb : b < 0) {kappa0 : ℝ}
    (hAncient : IsAncientKappaSolution kappa0 F)
    (p : F.M) {A : ℝ}
    (hbase : ∀ i, redLength ((U).term i).S 0 p (q i) 1 ≤ A)
    (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop) (hphi : StrictMono phi)
    (psi : ℕ → ℕ) (hpsi : StrictMono psi) (ellC : C(P.M × _root_.Set.Ici (1 : ℝ), ℝ))
    (hconv : TendstoLocallyUniformly
      (fun k (z : P.M × _root_.Set.Ici (1 : ℝ)) =>
        redLength ((U).term (phi (co.φ (psi k)))).S 0 p
          (Phi.map (co.φ (psi k)) z.1) z.2) ellC _root_.Filter.atTop)
    (ell : P.M × ℝ → ℝ)
    (hagree : ∀ (y : P.M) (t : ℝ) (ht : 1 ≤ t), ell (y, t) = ellC (y, ⟨t, ht⟩))
    (hcompleteOn : ∀ t ∈ _root_.Set.Ioi (1 : ℝ), MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - t) } : PointedRiemannianManifold (I := I)))
    (x : P.M) (ψ : ℝ × E → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ _root_.Set.Ioi (1 : ℝ) ×ˢ interior (extChartAt I x).target) :
    let f : ℝ × E → ℝ := fun z => ell ((extChartAt I x).symm z.2, z.1)
    let u : ℝ × E → ℝ := fun z => Real.exp (-f z -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    (∫ z in _root_.Set.Ioi (1 : ℝ) ×ˢ interior (extChartAt I x).target,
      chartDensity (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2) * u z *
        (deriv (fun t => ψ (t, z.2)) z.1 +
          chartGradientBilin (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
            (fderiv ℝ (fun y => f (z.1, y)) z.2)
            (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).prod (modelHaar (E := E))) = 0 := by
  intro f u
  obtain ⟨a, a', c', c, ha, haa, hac, hcc, hψtime⟩ :=
    DifferentialGeometry.Analysis.Parabolic.exists_nested_Ioo_of_hasCompactSupport hψc hψsupp
  let r : ℝ × E → ℝ := fun z =>
    chartDensity (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2) * u z *
      (deriv (fun t => ψ (t, z.2)) z.1 +
        chartGradientBilin (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
          (fderiv ℝ (fun y => f (z.1, y)) z.2)
          (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
  have hrzero {z : ℝ × E} (hz : z ∉ tsupport ψ) : r z = 0 := by
    obtain ⟨ht, hx⟩ := DifferentialGeometry.Analysis.time_spatial_derivatives_eq_zero ψ hz
    simp only [r, ht, hx, map_zero, zero_add, _root_.MulZeroClass.mul_zero]
  have hzero :=
    co.integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_on_interval_of_ancient
      F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt
        hcomplete hboundary kappa hF hb hAncient p ha hbase hescape hphi
        psi hpsi ellC hconv ell hagree haa hac hcc
        (fun t ht => hcompleteOn t ((ha.trans haa).trans_le ht.1))
        x ψ hψ hψc hψtime
  calc
    (∫ z in _root_.Set.Ioi (1 : ℝ) ×ˢ interior (extChartAt I x).target,
        r z ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).prod (modelHaar (E := E))) =
        ∫ z, r z ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).prod (modelHaar (E := E)) := by
      apply _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      exact hrzero fun h => hz (hψsupp h)
    _ = ∫ z in _root_.Set.Ioo a' c' ×ˢ interior (extChartAt I x).target,
        r z ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).prod (modelHaar (E := E)) := by
      symm
      apply _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      exact hrzero fun h => hz (hψtime h)
    _ = 0 := hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_on_Ioi_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_on_Ioi_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_on_Ioi_of_ancient ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_on_Ioi_of_ancient

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness

end
