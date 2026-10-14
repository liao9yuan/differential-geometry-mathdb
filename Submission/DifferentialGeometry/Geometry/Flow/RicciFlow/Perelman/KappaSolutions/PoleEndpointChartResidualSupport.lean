import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointChartSourceResidual
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Topology.Separation.Regular
import Submission.DifferentialGeometry.Analysis.Integration.Integral.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Analysis.Sobolev.Chart

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private theorem exists_isOpen_chart_domain_containing_tsupport
    {P : Type*} [TopologicalSpace P]
    (α : M) {ψ : P × E → ℝ} {s : Set P}
    (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ s ×ˢ interior (extChartAt I α).target) :
    ∃ Ω : Set EuStd, IsOpen Ω ∧ IsCompact (closure Ω) ∧
      (toEuclidean (E := E)).symm '' closure Ω ⊆ (extChartAt I α).target ∧
      tsupport ψ ⊆ s ×ˢ ((toEuclidean (E := E)) ⁻¹' Ω) := by
  let e := toEuclidean (E := E)
  let K : Set EuStd := (fun z : P × E => e z.2) '' tsupport ψ
  let U : Set EuStd := e.symm ⁻¹' interior (extChartAt I α).target
  have hK : IsCompact K := hψc.image (e.continuous.comp continuous_snd)
  have hU : IsOpen U := isOpen_interior.preimage e.symm.continuous
  have hKU : K ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    change e.symm (e z.2) ∈ interior (extChartAt I α).target
    rw [e.symm_apply_apply]
    exact (hψs hz).2
  obtain ⟨Ω, hΩ, hKΩ, hΩU, hΩc⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  refine ⟨Ω, hΩ, hΩc, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact interior_subset (hΩU hy)
  · intro z hz
    exact ⟨(hψs hz).1, hKΩ ⟨z, hz, rfl⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.exists_isOpen_chart_domain_containing_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.exists_isOpen_chart_domain_containing_tsupport target :: scope.openDecls } }

end DifferentialGeometry.Analysis.Sobolev.Chart


namespace DifferentialGeometry.Analysis

open _root_.Set _root_.Submission.Set _root_.Filter
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

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.Set
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

theorem integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_on_interval_of_ancient
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
    (p : F.M) {a c A : ℝ} (ha : 1 < a)
    (hbase : ∀ i, redLength ((U).term i).S 0 p (q i) 1 ≤ A)
    (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop) (hphi : StrictMono phi)
    (psi : ℕ → ℕ) (hpsi : StrictMono psi) (ellC : C(P.M × _root_.Set.Ici (1 : ℝ), ℝ))
    (hconv : TendstoLocallyUniformly
      (fun k (z : P.M × _root_.Set.Ici (1 : ℝ)) =>
        redLength ((U).term (phi (co.φ (psi k)))).S 0 p
          (Phi.map (co.φ (psi k)) z.1) z.2) ellC _root_.Filter.atTop)
    (ell : P.M × ℝ → ℝ)
    (hagree : ∀ (y : P.M) (t : ℝ) (ht : 1 ≤ t), ell (y, t) = ellC (y, ⟨t, ht⟩))
    {a' c' : ℝ} (haa : a < a') (hac : a' ≤ c') (hcc : c' < c)
    (hcompleteOn : ∀ t ∈ _root_.Set.Icc a' c', MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - t) } : PointedRiemannianManifold (I := I)))
    (x : P.M) (ψ : ℝ × E → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ _root_.Set.Ioo a' c' ×ˢ interior (extChartAt I x).target) :
    let f : ℝ × E → ℝ := fun z => ell ((extChartAt I x).symm z.2, z.1)
    let u : ℝ × E → ℝ := fun z => Real.exp (-f z -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    (∫ z in _root_.Set.Ioo a' c' ×ˢ interior (extChartAt I x).target,
      chartDensity (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2) * u z *
        (deriv (fun t => ψ (t, z.2)) z.1 +
          chartGradientBilin (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
            (fderiv ℝ (fun y => f (z.1, y)) z.2)
            (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).prod (modelHaar (E := E))) = 0 := by
  intro f u
  obtain ⟨Ω, hΩ, hΩc, hΩt, hψΩ⟩ :=
    exists_isOpen_chart_domain_containing_tsupport x hψc hψsupp
  let W : Set E := (toEuclidean (E := E)) ⁻¹' Ω
  let r : ℝ × E → ℝ := fun z =>
    chartDensity (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2) * u z *
      (deriv (fun t => ψ (t, z.2)) z.1 +
        chartGradientBilin (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
          (fderiv ℝ (fun y => f (z.1, y)) z.2)
          (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
  have hrzero {z : ℝ × E} (hz : z ∉ tsupport ψ) : r z = 0 := by
    obtain ⟨ht, hx⟩ := DifferentialGeometry.Analysis.time_spatial_derivatives_eq_zero ψ hz
    simp only [r, ht, hx, map_zero, zero_add, _root_.MulZeroClass.mul_zero]
  have hzero := co.integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_of_ancient
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt
      hcomplete hboundary kappa hF hb hAncient p ha hbase hescape hphi
      psi hpsi ellC hconv ell hagree haa hac hcc hcompleteOn x hΩ hΩc hΩt
      ψ hψ hψc hψΩ
  calc
    (∫ z in _root_.Set.Ioo a' c' ×ˢ interior (extChartAt I x).target,
        r z ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).prod (modelHaar (E := E))) =
        ∫ z, r z ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).prod (modelHaar (E := E)) := by
      apply _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      exact hrzero fun h => hz (hψsupp h)
    _ = ∫ z, r z ∂(volume.restrict (_root_.Set.Ioc a' c')).prod
        ((modelHaar (E := E)).restrict W) := by
      apply integral_eq_integral_restrict_prod_of_support
      intro z hz
      apply hrzero
      intro hs
      exact hz ⟨⟨(hψΩ hs).1.1, (hψΩ hs).1.2.le⟩, (hψΩ hs).2⟩
    _ = 0 := hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_on_interval_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_on_interval_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_on_interval_of_ancient ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_on_interval_of_ancient

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness

end
