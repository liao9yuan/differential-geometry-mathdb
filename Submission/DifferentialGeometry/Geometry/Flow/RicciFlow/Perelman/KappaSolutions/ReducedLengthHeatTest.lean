import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.HeatTest
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedLengthHamiltonJacobi
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Coordinates
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Coordinates
import Submission.DifferentialGeometry.Geometry.Metric.Family.Regularity.JointDifferentialOperator
import Submission.DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthBaseTime
import Submission.DifferentialGeometry.Analysis.Viscosity.Stability
import Submission.DifferentialGeometry.Topology.LocallyUniformConvergence
import Mathlib.Analysis.Calculus.Deriv.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates

section RegularBase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData (I := I) D)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem ancient_redLength_time_deriv_add_laplacian_lower_test_of_regular_base
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {T tau : ℝ} (hT : T < 0) (htau : 0 < tau)
    (p q : F.M) (phi : ℝ × F.M → ℝ) (d : ℝ)
    (hphi : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y => phi (tau, y)) q)
    (hdt : HasDerivAt (fun t => phi (t, q)) d tau)
    (hmin : IsLocalMin (fun z : ℝ × F.M => redLength F.S T p z.2 z.1 - phi z) (tau, q)) :
    d + laplacian (I := I) (LeviCivita (I := I) (F.S.base.metric (T - tau)))
        (F.S.base.metric (T - tau)) (fun y => phi (tau, y)) q ≤
      ((Module.finrank ℝ E : ℝ) / 2 - redLength F.S T p q tau) / tau := by
  let _ : ConnectedSpace F.M := hF.connected
  have hTc : T ∈ D.carrier := by simpa only [hF.carrier_eq, _root_.Set.mem_Iic] using hT.le
  have hg : RiemannianMetricComplete (I := I) (F.S.base.metric T) := ⟨hF.complete T hTc⟩
  obtain ⟨K, hK⟩ := ancientKappa_rmNormSqBounded_finrank F hF
  apply redLength_time_deriv_add_laplacian_lower_test F.S F.isSolution K T (tau + 1) tau
    hg htau (by linarith) ?_ ?_ p q phi d hphi hdt hmin
  · intro t ht
    simpa only [hF.regular_eq, _root_.Set.mem_Iio] using ht.2.trans_lt hT
  · intro t ht y
    exact hK t (by simpa only [hF.carrier_eq, _root_.Set.mem_Iic] using ht.2.trans hT.le) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_time_deriv_add_laplacian_lower_test_of_regular_base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_time_deriv_add_laplacian_lower_test_of_regular_base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_time_deriv_add_laplacian_lower_test_of_regular_base ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_time_deriv_add_laplacian_lower_test_of_regular_base

end RegularBase


section Ancient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData (I := I) ancientTimeInterval)
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private theorem redLength_heat_lower_test_in_chart_of_regular_base
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) {T tau : ℝ} (hT : T < 0) (htau : 0 < tau)
    (p a q : F.M) (hq : q ∈ (chartAt H a).source) (phi : ℝ × E → ℝ)
    (hphi : ContDiffAt ℝ 2 phi (tau, extChartAt I a q))
    (hmin : IsLocalMin (fun z : ℝ × E => redLength F.S T p ((extChartAt I a).symm z.2) z.1 - phi z)
      (tau, extChartAt I a q)) :
    fderiv ℝ phi (tau, extChartAt I a q) (1, 0) +
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (F.S.base.metric (T - tau)) a i j (extChartAt I a q) *
          (fderiv ℝ (fderiv ℝ phi) (tau, extChartAt I a q) (0, chartModelBasis E i) (0, chartModelBasis E j) -
            ∑ k : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) (F.S.base.metric (T - tau)) a i j k (extChartAt I a q) *
                fderiv ℝ phi (tau, extChartAt I a q) (0, chartModelBasis E k))) ≤
      ((Module.finrank ℝ E : ℝ) / 2 - redLength F.S T p q tau) / tau := by
  have hqs : q ∈ (extChartAt I a).source := by simpa only [extChartAt_source] using hq
  have hmap : ContinuousAt (fun z : ℝ × F.M => (z.1, extChartAt I a z.2)) (tau, q) :=
    continuousAt_fst.prodMk ((mdifferentiableAt_extChartAt (I := I) hq).continuousAt.comp continuousAt_snd)
  have htest : IsLocalMin (fun z : ℝ × F.M => redLength F.S T p z.2 z.1 - phi (z.1, extChartAt I a z.2))
      (tau, q) := by
    have hsrc : ∀ᶠ z : ℝ × F.M in 𝓝 (tau, q), z.2 ∈ (extChartAt I a).source :=
      continuous_snd.continuousAt.eventually (by
        change (extChartAt I a).source ∈ 𝓝 q
        simpa only [extChartAt_source] using (chartAt H a).open_source.mem_nhds hq)
    filter_upwards [hmap.tendsto.eventually hmin, hsrc] with z hz hzs
    simpa only [(extChartAt I a).left_inv hzs, (extChartAt I a).left_inv hqs] using hz
  have hs : ContDiffAt ℝ 2 (fun y => phi (tau, y)) (extChartAt I a q) :=
    hphi.comp (extChartAt I a q) (contDiffAt_const.prodMk contDiffAt_id)
  have hsM : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y => phi (tau, extChartAt I a y)) q :=
    hs.contMDiffAt.comp q (contMDiffAt_extChartAt' hq)
  have ht := (hphi.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt tau
    ((hasDerivAt_id tau).prodMk (hasDerivAt_const tau (extChartAt I a q)))
  have h := ancient_redLength_time_deriv_add_laplacian_lower_test_of_regular_base F hF hT htau p q
    (fun z => phi (z.1, extChartAt I a z.2)) (fderiv ℝ phi (tau, extChartAt I a q) (1, 0))
    hsM (by simpa only [Function.comp_def, id_eq] using ht) htest
  rwa [laplacian_time_slice_comp_extChartAt (F.S.base.metric (T - tau)) a hq phi hphi] at h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.redLength_heat_lower_test_in_chart_of_regular_base
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.redLength_heat_lower_test_in_chart_of_regular_base target :: scope.openDecls } }

private def reducedLengthHeatOperatorInChart (a : F.M) (T : ℝ) (z : ℝ × E) (r : ℝ)
    (P : (ℝ × E) →L[ℝ] ℝ) (A : (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) : ℝ :=
  ((Module.finrank ℝ E : ℝ) / 2 - r) / z.1 - P (1, 0) -
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) (F.S.base.metric (T - z.1)) a i j z.2 *
        (A (0, chartModelBasis E i) (0, chartModelBasis E j) -
          ∑ k : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) (F.S.base.metric (T - z.1)) a i j k z.2 * P (0, chartModelBasis E k))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reducedLengthHeatOperatorInChart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reducedLengthHeatOperatorInChart target :: scope.openDecls } }

omit [I.Boundaryless] in
private theorem ancient_metric_joint_smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun z : ℝ × F.M => (⟨z.2, (F.S.base.metric z.1).inner z.2⟩ :
      Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
    (_root_.Set.Iio 0 ×ˢ _root_.Set.univ) := by
  intro z hz
  exact (F.isSolution.smoothMetric.metricCLMSmoothAt
    (ancientTimeInterval.regular_isOpen.mem_nhds hz.1)).contMDiffWithinAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_metric_joint_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_metric_joint_smooth target :: scope.openDecls } }

private theorem reducedLengthHeatOperatorInChart_continuousOn (a : F.M) :
    ContinuousOn (fun w : ℝ × ((ℝ × E) × ℝ × ((ℝ × E) →L[ℝ] ℝ) ×
        ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ)) =>
      reducedLengthHeatOperatorInChart F a w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2)
      (_root_.Set.Iic 0 ×ˢ ((_root_.Set.Ioi 0 ×ˢ (extChartAt I a).target) ×ˢ _root_.Set.univ)) := by
  let _ : NormedAddCommGroup ((ℝ × E) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let _ : NormedSpace ℝ ((ℝ × E) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let _ : NormedAddCommGroup ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let Z := (ℝ × E) × ℝ × ((ℝ × E) →L[ℝ] ℝ) × ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ)
  let V : Set (ℝ × Z) := _root_.Set.Iic 0 ×ˢ ((_root_.Set.Ioi 0 ×ˢ (extChartAt I a).target) ×ˢ _root_.Set.univ)
  have hmap : ContinuousOn (fun w : ℝ × Z => (w.1 - w.2.1.1, w.2.1.2)) V := by dsimp only [Z]; fun_prop
  have hmaps : _root_.Set.MapsTo (fun w : ℝ × Z => (w.1 - w.2.1.1, w.2.1.2)) V
      (_root_.Set.Iio 0 ×ˢ interior (extChartAt I a).target) := by
    intro w hw
    change w.1 - w.2.1.1 < 0 ∧ w.2.1.2 ∈ interior (extChartAt I a).target
    exact ⟨sub_neg.mpr (show w.1 < w.2.1.1 from hw.1.trans_lt hw.2.1.1),
      by simpa only [(isOpen_extChartAt_target (I := I) a).interior_eq] using hw.2.1.2⟩
  have hA (i j : Fin (Module.finrank ℝ E)) : ContinuousOn
      (fun w : ℝ × Z => chartInvGramOnE (I := I) (F.S.base.metric (w.1 - w.2.1.1)) a i j w.2.1.2) V := by
    have hh := (chartInvGramOnE_continuousOn_of_contMDiffOn F.S.base.metric (ancient_metric_joint_smooth F) a i j).comp hmap hmaps
    exact hh
  have hC (i j k : Fin (Module.finrank ℝ E)) : ContinuousOn
      (fun w : ℝ × Z => chartChristoffel (I := I) (F.S.base.metric (w.1 - w.2.1.1)) a i j k w.2.1.2) V := by
    have hh := (chartChristoffelOnE_continuousOn_of_contMDiffOn F.S.base.metric (ancient_metric_joint_smooth F) (uniqueDiffOn_Iio 0) a i j k).comp hmap hmaps
    exact hh
  change ContinuousOn (fun w : ℝ × Z =>
    ((Module.finrank ℝ E : ℝ) / 2 - w.2.2.1) / w.2.1.1 - w.2.2.2.1 (1, 0) -
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (F.S.base.metric (w.1 - w.2.1.1)) a i j w.2.1.2 *
          (w.2.2.2.2 (0, chartModelBasis E i) (0, chartModelBasis E j) -
            ∑ k : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) (F.S.base.metric (w.1 - w.2.1.1)) a i j k w.2.1.2 *
                w.2.2.2.1 (0, chartModelBasis E k))) V
  refine ContinuousOn.sub (ContinuousOn.sub ?_ (by dsimp only [Z]; fun_prop)) ?_
  · exact ContinuousOn.div (by dsimp only [Z]; fun_prop) (by dsimp only [Z]; fun_prop) (fun w hw => hw.2.1.1.ne')
  · refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    refine (hA i j).mul (ContinuousOn.sub (by dsimp only [Z]; fun_prop) ?_)
    exact continuousOn_finsetSum _ fun k _ => (hC i j k).mul (by dsimp only [Z]; fun_prop)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reducedLengthHeatOperatorInChart_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reducedLengthHeatOperatorInChart_continuousOn target :: scope.openDecls } }


theorem ancient_redLength_time_deriv_add_laplacian_lower_test_in_chart
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) {tau : ℝ} (htau : 0 < tau)
    (p a q : F.M) (hq : q ∈ (chartAt H a).source) (phi : ℝ × E → ℝ)
    (hphi : ContDiffAt ℝ 2 phi (tau, extChartAt I a q))
    (hmin : IsLocalMin (fun z : ℝ × E => redLength F.S 0 p ((extChartAt I a).symm z.2) z.1 - phi z)
      (tau, extChartAt I a q)) :
    fderiv ℝ phi (tau, extChartAt I a q) (1, 0) +
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (F.S.base.metric (-tau)) a i j (extChartAt I a q) *
          (fderiv ℝ (fderiv ℝ phi) (tau, extChartAt I a q) (0, chartModelBasis E i) (0, chartModelBasis E j) -
            ∑ k : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) (F.S.base.metric (-tau)) a i j k (extChartAt I a q) *
                fderiv ℝ phi (tau, extChartAt I a q) (0, chartModelBasis E k))) ≤
      ((Module.finrank ℝ E : ℝ) / 2 - redLength F.S 0 p q tau) / tau := by
  let U : Set (ℝ × E) := _root_.Set.Ioi 0 ×ˢ (extChartAt I a).target
  let f : ℝ → (ℝ × E) → ℝ := fun T z => redLength F.S T p ((extChartAt I a).symm z.2) z.1
  have hU : IsOpen U := isOpen_Ioi.prod (isOpen_extChartAt_target (I := I) a)
  have hle : (𝓝[<] (0 : ℝ)) ≤ 𝓝[≤] (0 : ℝ) := nhdsWithin_mono _ _root_.Set.Iio_subset_Iic_self
  have hmap : ContinuousOn (fun z : ℝ × E => (z.1, (extChartAt I a).symm z.2)) U :=
    continuousOn_fst.prodMk ((continuousOn_extChartAt_symm a).comp continuousOn_snd (fun _ hz => hz.2))
  have hmaps : _root_.Set.MapsTo (fun z : ℝ × E => (z.1, (extChartAt I a).symm z.2)) U (_root_.Set.Ioi 0 ×ˢ _root_.Set.univ) :=
    fun _ hz => ⟨hz.1, _root_.Set.mem_univ _⟩
  have hf : ∀ᶠ T in 𝓝[<] (0 : ℝ), ContinuousOn (f T) U := by
    filter_upwards [(eventually_continuousOn_redLength_space_time_of_ancient F hF p).filter_mono hle] with T hT
    have hh := hT.comp hmap hmaps
    exact hh
  have hconv : TendstoLocallyUniformlyOn f (f 0) (𝓝[<] (0 : ℝ)) U :=
    ((tendstoLocallyUniformlyOn_redLength_terminal_base_time F hF p).comp _ hmaps hmap).mono_left hle
  let Z := (ℝ × E) × ℝ × ((ℝ × E) →L[ℝ] ℝ) × ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ)
  have hH : ContinuousOn (fun z : Z => reducedLengthHeatOperatorInChart F a 0 z.1 z.2.1 z.2.2.1 z.2.2.2)
      (U ×ˢ _root_.Set.univ) := by
    have hM : ContinuousOn (fun z : Z => ((0 : ℝ), z)) (U ×ˢ _root_.Set.univ) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have hmapsH : _root_.Set.MapsTo (fun z : Z => ((0 : ℝ), z)) (U ×ˢ _root_.Set.univ) (_root_.Set.Iic 0 ×ˢ (U ×ˢ _root_.Set.univ)) :=
      fun _ hz => ⟨mem_Iic.mpr le_rfl, hz⟩
    have hh := (reducedLengthHeatOperatorInChart_continuousOn F a).comp hM hmapsH
    exact hh
  have hHconv : TendstoLocallyUniformlyOn
      (fun T (z : Z) => reducedLengthHeatOperatorInChart F a T z.1 z.2.1 z.2.2.1 z.2.2.2)
      (fun z => reducedLengthHeatOperatorInChart F a 0 z.1 z.2.1 z.2.2.1 z.2.2.2)
      (𝓝[<] (0 : ℝ)) (U ×ˢ _root_.Set.univ) := by
    have hh := ContinuousOn.tendstoLocallyUniformlyOn
      (F := fun T (z : Z) => reducedLengthHeatOperatorInChart F a T z.1 z.2.1 z.2.2.1 z.2.2.2)
      (s := _root_.Set.Iic 0) (u := U ×ˢ _root_.Set.univ) (a := (0 : ℝ))
      (reducedLengthHeatOperatorInChart_continuousOn F a) (mem_Iic.mpr le_rfl)
    exact hh.mono_left hle
  have htests : ∀ᶠ T in 𝓝[<] (0 : ℝ), ∀ z ∈ U, ∀ psi : ℝ × E → ℝ, ContDiffAt ℝ 2 psi z →
      IsLocalMin (fun y => f T y - psi y) z →
        0 ≤ reducedLengthHeatOperatorInChart F a T z (f T z) (fderiv ℝ psi z) (fderiv ℝ (fderiv ℝ psi) z) := by
    have htime : ∀ᶠ T in 𝓝[<] (0 : ℝ), T < 0 := self_mem_nhdsWithin
    filter_upwards [htime] with T hT
    intro z hz psi hpsi htest
    have hzs : (extChartAt I a).symm z.2 ∈ (chartAt H a).source := by
      simpa only [extChartAt_source] using (extChartAt I a).map_target hz.2
    have hright := (extChartAt I a).right_inv hz.2
    have hh := redLength_heat_lower_test_in_chart_of_regular_base F hF hT hz.1 p a
      ((extChartAt I a).symm z.2) hzs psi
      (by simpa only [hright, Prod.mk.eta] using hpsi)
      (by simpa only [hright, Prod.mk.eta, f] using htest)
    simp only [hright, Prod.mk.eta] at hh
    dsimp only [reducedLengthHeatOperatorInChart, f]
    linarith only [hh]
  have hqs : q ∈ (extChartAt I a).source := by simpa only [extChartAt_source] using hq
  have hx : (tau, extChartAt I a q) ∈ U := ⟨htau, (extChartAt I a).map_source hqs⟩
  have hh := DifferentialGeometry.Analysis.Viscosity.lower_test_ge_of_tendstoLocallyUniformlyOn
    hU hf hconv hH hHconv htests hx phi hphi hmin
  simp only [reducedLengthHeatOperatorInChart, f, (extChartAt I a).left_inv hqs, zero_sub] at hh
  linarith only [hh]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_time_deriv_add_laplacian_lower_test_in_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_time_deriv_add_laplacian_lower_test_in_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_time_deriv_add_laplacian_lower_test_in_chart ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_time_deriv_add_laplacian_lower_test_in_chart

theorem ancient_redLength_time_deriv_add_laplacian_lower_test
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) {tau : ℝ} (htau : 0 < tau)
    (p q : F.M) (phi : ℝ × F.M → ℝ)
    (hphi : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 phi (tau, q))
    (hmin : IsLocalMin (fun z : ℝ × F.M => redLength F.S 0 p z.2 z.1 - phi z) (tau, q)) :
    deriv (fun t => phi (t, q)) tau +
      laplacian (I := I) (LeviCivita (I := I) (F.S.base.metric (-tau))) (F.S.base.metric (-tau))
        (fun y => phi (tau, y)) q ≤
      ((Module.finrank ℝ E : ℝ) / 2 - redLength F.S 0 p q tau) / tau := by
  let psi : ℝ × E → ℝ := fun z => phi (z.1, (extChartAt I q).symm z.2)
  have hq : q ∈ (chartAt H q).source := mem_chart_source H q
  have hqs : q ∈ (extChartAt I q).source := by simpa only [extChartAt_source] using hq
  have hqt : extChartAt I q q ∈ (extChartAt I q).target := (extChartAt I q).map_source hqs
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I q).symm (extChartAt I q q) :=
    (contMDiffOn_extChartAt_symm q).contMDiffAt ((isOpen_extChartAt_target (I := I) q).mem_nhds hqt)
  have hmap : ContMDiffAt 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod I) 2
      (fun z : ℝ × E => (z.1, (extChartAt I q).symm z.2)) (tau, extChartAt I q q) :=
    contDiffAt_fst.contMDiffAt.prodMk (hsymm.comp (tau, extChartAt I q q) contDiffAt_snd.contMDiffAt)
  have hpsi : ContDiffAt ℝ 2 psi (tau, extChartAt I q q) := by
    have hphi' : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 phi
        (tau, (extChartAt I q).symm (extChartAt I q q)) := by
      simpa only [(extChartAt I q).left_inv hqs] using hphi
    exact (hphi'.comp (tau, extChartAt I q q) hmap).contDiffAt
  have hcontact : IsLocalMin (fun z : ℝ × E =>
      redLength F.S 0 p ((extChartAt I q).symm z.2) z.1 - psi z) (tau, extChartAt I q q) := by
    have ht : _root_.Filter.Tendsto (fun z : ℝ × E => (z.1, (extChartAt I q).symm z.2))
        (𝓝 (tau, extChartAt I q q)) (𝓝 (tau, q)) := by
      simpa only [(extChartAt I q).left_inv hqs] using hmap.continuousAt.tendsto
    change ∀ᶠ z : ℝ × E in 𝓝 (tau, extChartAt I q q),
      redLength F.S 0 p ((extChartAt I q).symm (extChartAt I q q)) tau - psi (tau, extChartAt I q q) ≤
        redLength F.S 0 p ((extChartAt I q).symm z.2) z.1 - psi z
    simpa only [psi, (extChartAt I q).left_inv hqs] using ht.eventually hmin
  have htest := ancient_redLength_time_deriv_add_laplacian_lower_test_in_chart F hF htau p q q hq psi hpsi hcontact
  have hdt : deriv (fun t => phi (t, q)) tau = fderiv ℝ psi (tau, extChartAt I q q) (1, 0) := by
    have ht := (hpsi.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt tau
      ((hasDerivAt_id tau).prodMk (hasDerivAt_const tau (extChartAt I q q)))
    simpa only [Function.comp_def, id_eq, psi, (extChartAt I q).left_inv hqs] using ht.deriv
  have hspace : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y => phi (tau, y)) q :=
    hphi.comp q (contMDiffAt_const.prodMk contMDiffAt_id)
  have hspacepsi : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y => psi (tau, extChartAt I q y)) q :=
    ((hpsi.comp (extChartAt I q q) (contDiffAt_const.prodMk contDiffAt_id)).contMDiffAt).comp q
      (contMDiffAt_extChartAt' hq)
  have heq : (fun y => phi (tau, y)) =ᶠ[𝓝 q] (fun y => psi (tau, extChartAt I q y)) := by
    have hsrc : (extChartAt I q).source ∈ 𝓝 q := by
      simpa only [extChartAt_source] using (chartAt H q).open_source.mem_nhds hq
    filter_upwards [hsrc] with y hy
    exact (congrArg (fun z => phi (tau, z)) ((extChartAt I q).left_inv hy)).symm
  have heq0 : phi (tau, q) = psi (tau, extChartAt I q q) := heq.self_of_nhds
  have hcov : IsMetricCompatible (I := I) (LeviCivita (I := I) (F.S.base.metric (-tau)))
      (F.S.base.metric (-tau)) := by
    simpa only [LeviCivita] using
      leviCivitaConnectionOfMetric_isMetricCompatible (I := I) (F.S.base.metric (-tau))
  have hminEq : IsLocalMin (fun y => phi (tau, y) - psi (tau, extChartAt I q y)) q := by
    filter_upwards [heq] with y hy
    change phi (tau, q) - psi (tau, extChartAt I q q) ≤ phi (tau, y) - psi (tau, extChartAt I q y)
    rw [heq0, hy, sub_self, sub_self]
  have hminEq' : IsLocalMin (fun y => psi (tau, extChartAt I q y) - phi (tau, y)) q := by
    filter_upwards [heq] with y hy
    change psi (tau, extChartAt I q q) - phi (tau, q) ≤ psi (tau, extChartAt I q y) - phi (tau, y)
    rw [heq0, hy, sub_self, sub_self]
  have hlap := le_antisymm
    (laplacian_le_of_isLocalMin_sub (LeviCivita (I := I) (F.S.base.metric (-tau)))
      (F.S.base.metric (-tau)) hcov BoundarylessManifold.isInteriorPoint hspacepsi hspace hminEq')
    (laplacian_le_of_isLocalMin_sub (LeviCivita (I := I) (F.S.base.metric (-tau)))
      (F.S.base.metric (-tau)) hcov BoundarylessManifold.isInteriorPoint hspace hspacepsi hminEq)
  rw [hdt, hlap, laplacian_time_slice_comp_extChartAt (F.S.base.metric (-tau)) q hq psi hpsi]
  exact htest

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_time_deriv_add_laplacian_lower_test then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_time_deriv_add_laplacian_lower_test"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_time_deriv_add_laplacian_lower_test ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_time_deriv_add_laplacian_lower_test

theorem ancient_redLength_conjugate_heat_lower_test
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) {tau : ℝ} (htau : 0 < tau)
    (p q : F.M) (phi : ℝ × F.M → ℝ)
    (hphi : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 phi (tau, q))
    (hmin : IsLocalMin (fun z : ℝ × F.M => redLength F.S 0 p z.2 z.1 - phi z) (tau, q)) :
    0 ≤ deriv (fun t => phi (t, q)) tau -
      laplacian (I := I) (LeviCivita (I := I) (F.S.base.metric (-tau))) (F.S.base.metric (-tau))
        (fun y => phi (tau, y)) q +
      (F.S.base.metric (-tau)).inner q
        (gradientFun (F.S.base.metric (-tau)) (fun y => phi (tau, y)) q)
        (gradientFun (F.S.base.metric (-tau)) (fun y => phi (tau, y)) q) -
      F.S.scalar (-tau) q + (Module.finrank ℝ E : ℝ) / (2 * tau) := by
  let c := redLength F.S 0 p q tau - phi (tau, q)
  let psi : ℝ → F.M → ℝ := fun t y => phi (t, y) + c
  have hd : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) phi (tau, q) :=
    hphi.mdifferentiableAt (by norm_num)
  have hpsi : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun z : ℝ × F.M => psi z.1 z.2) (tau, q) := hd.add mdifferentiableAt_const
  have heq : redLength F.S 0 p q tau = psi tau q := by dsimp [psi, c]; ring
  have hlower : ∀ᶠ z : ℝ × F.M in 𝓝 (tau, q), psi z.1 z.2 ≤ redLength F.S 0 p z.2 z.1 := by
    filter_upwards [hmin] with z hz
    change redLength F.S 0 p q tau - phi (tau, q) ≤ redLength F.S 0 p z.2 z.1 - phi z at hz
    dsimp [psi, c]
    linarith
  have hHJ := ancient_redLength_hamilton_jacobi_lower_test_terminal F hF htau p q psi hpsi heq hlower
  have hdt : deriv (fun t => psi t q) tau = deriv (fun t => phi (t, q)) tau := by
    exact deriv_add_const c
  have hspace : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => phi (tau, y)) q :=
    hd.comp q (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have hgrad : gradientFun (F.S.base.metric (-tau)) (psi tau) q =
      gradientFun (F.S.base.metric (-tau)) (fun y => phi (tau, y)) q := by
    dsimp [psi]
    rw [gradientFun_add (F.S.base.metric (-tau)) hspace mdifferentiableAt_const,
      gradientFun_const, add_zero]
  rw [hdt, hgrad, ← heq] at hHJ
  have hheat := ancient_redLength_time_deriv_add_laplacian_lower_test F hF htau p q phi hphi hmin
  have halgebra : ((Module.finrank ℝ E : ℝ) / 2 - redLength F.S 0 p q tau) / tau +
      2 * (redLength F.S 0 p q tau / (2 * tau)) = (Module.finrank ℝ E : ℝ) / (2 * tau) := by ring
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_conjugate_heat_lower_test then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_conjugate_heat_lower_test"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_conjugate_heat_lower_test ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_conjugate_heat_lower_test

theorem ancient_redLength_conjugate_heat_lower_test_in_chart
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) {tau : ℝ} (htau : 0 < tau)
    (p a q : F.M) (hq : q ∈ (chartAt H a).source) (phi : ℝ × E → ℝ)
    (hphi : ContDiffAt ℝ 2 phi (tau, extChartAt I a q))
    (hmin : IsLocalMin (fun z : ℝ × E => redLength F.S 0 p ((extChartAt I a).symm z.2) z.1 - phi z)
      (tau, extChartAt I a q)) :
    0 ≤ fderiv ℝ phi (tau, extChartAt I a q) (1, 0) -
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (F.S.base.metric (-tau)) a i j (extChartAt I a q) *
          (fderiv ℝ (fderiv ℝ phi) (tau, extChartAt I a q) (0, chartModelBasis E i) (0, chartModelBasis E j) -
            ∑ k : Fin (Module.finrank ℝ E),
              chartChristoffel (F.S.base.metric (-tau)) a i j k (extChartAt I a q) *
                fderiv ℝ phi (tau, extChartAt I a q) (0, chartModelBasis E k))) +
      (∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (F.S.base.metric (-tau)) a k j (extChartAt I a q) *
          fderiv ℝ phi (tau, extChartAt I a q) (0, chartModelBasis E j) *
          fderiv ℝ phi (tau, extChartAt I a q) (0, chartModelBasis E k)) -
      F.S.scalar (-tau) q + (Module.finrank ℝ E : ℝ) / (2 * tau) := by
  have hqs : q ∈ (extChartAt I a).source := by simpa only [extChartAt_source] using hq
  have hchart : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) 2
      (fun z : ℝ × F.M => (z.1, extChartAt I a z.2)) (tau, q) :=
    (contMDiffAt_prod_module_iff _).mpr ⟨contMDiffAt_fst,
      (contMDiffAt_extChartAt' hq).comp (tau, q) (f := Prod.snd) contMDiffAt_snd⟩
  have hphiM : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2
      (fun z : ℝ × F.M => phi (z.1, extChartAt I a z.2)) (tau, q) :=
    hphi.contMDiffAt.comp (tau, q) hchart
  have htest : IsLocalMin (fun z : ℝ × F.M =>
      redLength F.S 0 p z.2 z.1 - phi (z.1, extChartAt I a z.2)) (tau, q) := by
    have hsrc : ∀ᶠ z : ℝ × F.M in 𝓝 (tau, q), z.2 ∈ (extChartAt I a).source :=
      continuous_snd.continuousAt.eventually (by
        change (extChartAt I a).source ∈ 𝓝 q
        simpa only [extChartAt_source] using (chartAt H a).open_source.mem_nhds hq)
    filter_upwards [hchart.continuousAt.tendsto.eventually hmin, hsrc] with z hz hzs
    simpa only [(extChartAt I a).left_inv hqs, (extChartAt I a).left_inv hzs] using hz
  have hh := ancient_redLength_conjugate_heat_lower_test F hF htau p q
    (fun z => phi (z.1, extChartAt I a z.2)) hphiM htest
  have hd := (hphi.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt tau
    ((hasDerivAt_id tau).prodMk (hasDerivAt_const tau (extChartAt I a q)))
  have hdt : deriv (fun t => phi (t, extChartAt I a q)) tau =
      fderiv ℝ phi (tau, extChartAt I a q) (1, 0) := by
    simpa only [Function.comp_def, id_eq] using hd.deriv
  have hs := (hphi.differentiableAt (by norm_num)).hasFDerivAt.comp (extChartAt I a q)
    ((hasFDerivAt_const tau (extChartAt I a q)).prodMk (hasFDerivAt_id (extChartAt I a q)))
  have hp (v : E) : fderiv ℝ (fun y => phi (tau, y)) (extChartAt I a q) v =
      fderiv ℝ phi (tau, extChartAt I a q) (0, v) := by
    have he := congrArg (fun L : E →L[ℝ] ℝ => L v) hs.fderiv
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, zero_apply, ContinuousLinearMap.id_apply] using he
  have hqi : extChartAt I a q ∈ interior (extChartAt I a).target := by
    rw [(isOpen_extChartAt_target (I := I) a).interior_eq]
    exact (extChartAt I a).map_source hqs
  have hgrad := normGradSqFun_comp_extChartAt (F.S.base.metric (-tau)) a
    (f := fun y => phi (tau, y)) hq hqi
  simp_rw [hp] at hgrad
  dsimp only [Function.comp_def] at hgrad
  change 0 ≤ deriv (fun t => phi (t, extChartAt I a q)) tau -
      laplacian (LeviCivita (F.S.base.metric (-tau))) (F.S.base.metric (-tau))
        (fun y => phi (tau, extChartAt I a y)) q +
      normGradSqFun (F.S.base.metric (-tau)) (fun y => phi (tau, extChartAt I a y)) q -
      F.S.scalar (-tau) q + (Module.finrank ℝ E : ℝ) / (2 * tau) at hh
  rwa [hdt, laplacian_time_slice_comp_extChartAt (F.S.base.metric (-tau)) a hq phi hphi,
    hgrad] at hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_conjugate_heat_lower_test_in_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_conjugate_heat_lower_test_in_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_conjugate_heat_lower_test_in_chart ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_conjugate_heat_lower_test_in_chart

end Ancient
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
