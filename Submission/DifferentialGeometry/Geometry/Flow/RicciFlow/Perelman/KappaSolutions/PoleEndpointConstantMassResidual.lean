import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointResidualVanishing
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointCutoffResidualLimit
import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import Mathlib.Order.Filter.AtTopBot.Archimedean

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Integral.Measure
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

theorem integral_poleEndpoint_redDensity_limit_residual_eq_zero_of_const_mass
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {a c A : ℝ} (ha : 1 < a)
    (hbase : ∀ i, redLength ((U).term i).S 0 p (q i) 1 ≤ A)
    (psi : ℕ → ℕ) (hpsi : StrictMono psi) (ellC : C(P.M × _root_.Set.Ici (1 : ℝ), ℝ))
    (hconv : TendstoLocallyUniformly
      (fun k (z : P.M × _root_.Set.Ici (1 : ℝ)) =>
        redLength ((U).term (phi (co.φ (psi k)))).S 0 p
          (Phi.map (co.φ (psi k)) z.1) z.2) ellC _root_.Filter.atTop)
    (ell : P.M × ℝ → ℝ)
    (hagree : ∀ (y : P.M) (t : ℝ) (ht : 1 ≤ t), ell (y, t) = ellC (y, ⟨t, ht⟩))
    (hlog : ∀ (x : P.M) (W : Set E), IsOpen W → IsCompact (closure W) →
      closure W ⊆ (extChartAt I x).target →
      ∀ v : ℝ × E → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
        tsupport v ⊆ _root_.Set.Ioo a c ×ˢ W → (∀ z, 0 ≤ v z) →
      let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
      let d := fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
      let B := fun z => chartGradientBilin (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
      let ρ := fun z => chartDensity (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
      let S := fun z => metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2)
      0 ≤ ∫ z, ρ z *
        (((1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * S z +
            ((Module.finrank ℝ E : ℝ) - f z) / (2 * z.1)) * v z +
          B z (d z) (fderiv ℝ (fun y => v (z.1, y)) z.2))
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).prod (modelHaar (E := E)))
    {a' c' : ℝ} (haa : a < a') (hac : a' ≤ c') (hcc : c' < c)
    (hcompleteOn : ∀ t ∈ _root_.Set.Icc a' c', MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - t) } : PointedRiemannianManifold (I := I)))
    (m : ℝ)
    (hmass : ∀ᵐ s : _root_.Set.Ioo a' c', (∫ y,
      Real.exp (-ellC (y, (⟨(s : ℝ), (ha.le.trans haa.le).trans s.property.1.le⟩ : _root_.Set.Ici (1 : ℝ))) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
      ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - (s : ℝ)))) = m)
    (ψ : ℝ × P.M → ℝ)
    (hψ : ContMDiff ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) 1 ψ)
    (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ _root_.Set.Ioo a' c' ×ˢ (_root_.Set.univ : Set P.M)) :
    let g := fun t : ℝ => co.gInf (1 - t)
    let density := fun z : ℝ × P.M => Real.exp (-ell (z.2, z.1) -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    let residual := fun (t : ℝ) (x : P.M) => density (t, x) *
      (deriv (fun s => ψ (s, x)) t +
        (g t).inner x (gradientFun (g t) (fun y => ell (y, t)) x)
          (gradientFun (g t) (fun y => ψ (t, y)) x))
    (∀ᵐ t ∂volume.restrict (_root_.Set.Ioc a' c'),
      Integrable (residual t) (riemannianVolumeMeasure (I := I) (M := P.M) (g t))) ∧
      _root_.MeasureTheory.Integrable (fun t => ∫ x, residual t x
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (g t))
        (volume.restrict (_root_.Set.Ioc a' c')) ∧
      (∫ t in _root_.Set.Ioc a' c', ∫ x, residual t x
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (g t)) = 0 := by
  have ha' : 1 ≤ a' := ha.le.trans haa.le
  have hbaseSelected : ∀ᶠ k in _root_.Filter.atTop,
      redLength ((U).term (phi (co.φ k))).S 0 p (q (phi (co.φ k))) 1 ≤ A :=
    Eventually.of_forall fun k => hbase (phi (co.φ k))
  have hconvPointwise : ∀ y : P.M, ∀ t ∈ _root_.Set.Icc a c,
      _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (psi k)))).S 0 p
        (Phi.map (co.φ (psi k)) y) t) _root_.Filter.atTop (𝓝 (ell (y, t))) := by
    intro y t ht
    have htOne : 1 ≤ t := ha.le.trans ht.1
    have hpt := hconv.tendstoLocallyUniformlyOn.tendsto_at
      (_root_.Set.mem_univ (y, (⟨t, htOne⟩ : _root_.Set.Ici (1 : ℝ))))
    rw [hagree y t htOne]
    exact hpt
  have hK : IsCompact (Prod.fst '' tsupport ψ) := hψc.image continuous_fst
  have hKac : Prod.fst '' tsupport ψ ⊆ _root_.Set.Ioo a' c' := by
    rintro t ⟨q, hq, rfl⟩
    exact (hψsupp hq).1
  obtain ⟨η, hη, hηc, hηone, hηsupp, hηrange⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact hK isOpen_Ioo hKac
  have hηC1 : ContDiff ℝ 1 η := hη.of_le (by simp)
  have hηnonneg : ∀ t, 0 ≤ η t := fun t => (hηrange ⟨t, rfl⟩).1
  have hηoneOn : ∀ z ∈ tsupport ψ, η z.1 = 1 :=
    fun z hz => hηone.self_of_nhdsSet ⟨z, hz, rfl⟩
  let radii : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hradii : _root_.Filter.Tendsto radii _root_.Filter.atTop atTop :=
    _root_.Filter.tendsto_atTop_mono (fun n : ℕ =>
      (show (n : ℝ) ≤ (n : ℝ) + 1 from le_add_of_nonneg_right zero_le_one))
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hqref : RiemannianMetricComplete (co.gInf (1 - a')) :=
    ⟨hcompleteOn a' ⟨le_rfl, hac⟩⟩
  have hagreeOn (s : _root_.Set.Ioo a' c') (y : P.M) :
      ell (y, (s : ℝ)) = ellC (y, ⟨(s : ℝ), ha'.trans s.property.1.le⟩) :=
    hagree y s (ha'.trans s.property.1.le)
  have hcutoff := co.tendsto_integral_poleEndpoint_radialDistanceCutoff_residual_of_const_mass
    F hcar hreg b hbmem tau q hsigma Phi kappa hF p hbase psi hpsi ellC hconv
    ha' hac hcompleteOn ell hagreeOn m hmass P.basepoint η hηC1 hηsupp hradii
  exact co.integral_poleEndpoint_redDensity_limit_residual_eq_zero_of_radial_cutoff_limit
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt
    hcomplete hboundary kappa hF p ha hbaseSelected psi hpsi.tendsto_atTop
    ell hconvPointwise hlog haa hac hcc ψ hψ hψc hψsupp
    η hηC1 hηc hηsupp hηnonneg hηoneOn (co.gInf (1 - a')) hqref P.basepoint
    hradii hcutoff.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_redDensity_limit_residual_eq_zero_of_const_mass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_redDensity_limit_residual_eq_zero_of_const_mass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_redDensity_limit_residual_eq_zero_of_const_mass ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_redDensity_limit_residual_eq_zero_of_const_mass

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness

end
