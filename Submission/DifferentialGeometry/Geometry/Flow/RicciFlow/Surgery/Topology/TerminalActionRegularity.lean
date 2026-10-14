import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalAction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CarrierC1Regularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.PrefixMinimality
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Sequences
import Mathlib.Topology.ContinuousMap.Ordered
import Submission.DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.CarrierLowerSemicontinuity
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.CurveCompactness
import Mathlib.Topology.UniformSpace.CompactConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Boundary
import Submission.DifferentialGeometry.Geometry.Metric.Family.QuadraticBounds
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.CarrierDensity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalClosedSolution
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.LocalPullback
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import Submission.DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuous
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CarrierC1RegularityJointMetric
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.PrefixMinimalityAbsolutelyContinuous

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
noncomputable section

open _root_.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Interval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private theorem closedSolution_lagrangian_ae_eq_of_projection
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c T u d : ℝ} (hcs : c ≤ s) (hu : 0 ≤ u) (hTu : T - u ^ 2 = s)
    (η : ℝ → W) (γ : ℝ → P.Carrier)
    (hdiff : ∀ᵐ r ∂volume.restrict (_root_.Set.Icc u d), MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel η r)
    (hproj : _root_.Set.EqOn (fun r => (η r).val.val) γ (_root_.Set.Icc u d)) :
    lRegularizedLagrangian (L.closedSolution W hcs) T η =ᵐ[volume.restrict (_root_.Set.Icc u d)]
      lRegularizedLagrangian G.flow T γ := by
  rw [← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc] at hdiff ⊢
  filter_upwards [hdiff, _root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with r hdr hr
  have hr0 : 0 ≤ r := hu.trans hr.1.le
  have htr : T - r ^ 2 < s := by nlinarith [sq_lt_sq₀ hu hr0 |>.2 hr.1]
  let p : W → P.Carrier := fun z => z.val.val
  let hp := isLocalDiffeomorph_comp
    (isLocalDiffeomorph_subtype_val (I := ThreeModel) G.terminalRegularOpen)
    (isLocalDiffeomorph_subtype_val (I := ThreeModel) W)
  have hm : (L.closedSolution W hcs).base.metric (T - r ^ 2) =
      (G.flow.localPullback p hp).base.metric (T - r ^ 2) := by
    change (L.closedSolution W hcs).base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) p hp
    rw [L.closedSolution_before W hcs htr,
      ← localPullMetric_subtype_val, ← localPullMetric_subtype_val, localPullMetric_comp]
    rfl
  have heq : p ∘ η =ᶠ[𝓝 r] γ := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
    exact hproj ⟨hx.1.le, hx.2.le⟩
  have hvel : lVelocity (I := ThreeModel) (p ∘ η) r = lVelocity (I := ThreeModel) γ r := by
    exact congrArg (fun L => L (1 : ℝ))
      (heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel))
  calc
    _ = lRegularizedLagrangian (G.flow.localPullback p hp) T η r := by
      unfold lRegularizedLagrangian SolutionOn.scalar SolutionFamily.scalar
      rw [hm]
    _ = lRegularizedLagrangian G.flow T (p ∘ η) r :=
      lRegularizedLagrangian_localPullback G.flow p hp T hdr
    _ = _ := by
      simp only [lRegularizedLagrangian]
      rw [heq.self_of_nhds, hvel]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.closedSolution_lagrangian_ae_eq_of_projection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.closedSolution_lagrangian_ae_eq_of_projection target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Interval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe uIncomingC1
variable {P : OrientedThreeStage.{uIncomingC1}} {a s : ℝ} {G : P.IncomingSlab a s}

private theorem TerminalLimitMetric.exists_contMDiffOn_one_terminal_collar_of_action_minimal
    (L : G.TerminalLimitMetric) {T u v : ℝ} {α : ℝ → P.Carrier}
    (hu : 0 ≤ u) (huv : u < v) (hTu : T - u ^ 2 = s) (ha : a ≤ T - v ^ 2)
    (hα : Manifold.absolutelyContinuousOnInterval ThreeModel α u v)
    (hint : IntervalIntegrable (lRegularizedLagrangian G.flow T α) _root_.MeasureTheory.MeasureSpace.volume u v)
    (hterminal : α u ∈ G.terminalRegularOpen)
    (hmin : ∀ β : ℝ → P.Carrier,
      Manifold.absolutelyContinuousOnInterval ThreeModel β u v →
      IntervalIntegrable (lRegularizedLagrangian G.flow T β) _root_.MeasureTheory.MeasureSpace.volume u v →
      β u = α u → β v = α v →
      lRegularizedAction G.flow T α u v ≤ lRegularizedAction G.flow T β u v) :
    ∃ d ∈ _root_.Set.Ioo u v, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 α (_root_.Set.Icc u d) := by
  obtain ⟨d, hd, hds, η, hη, hproj, had, hS, hclock, _, hact, _, hηint⟩ :=
    L.exists_absolutelyContinuous_closedSolution_collar hu huv hTu ha hα hterminal
  let W : TopologicalSpace.Opens G.terminalRegularOpen := ⊤
  let S := L.closedSolution W hds.le
  let : SigmaCompactSpace G.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)
  let : SigmaCompactSpace W :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)
  let : TopologicalSpace.MetrizableSpace W := Manifold.metrizableSpace ThreeModel W
  have hreg (r : ℝ) (hr : r ∈ _root_.Set.Ioo u d) :
      T - r ^ 2 ∈ (RealTimeInterval.closed (T - d ^ 2) s hds.le).regular := by
    change T - d ^ 2 < T - r ^ 2 ∧ T - r ^ 2 < s
    have hr0 := hu.trans hr.1.le
    constructor
    · nlinarith [sq_lt_sq₀ hr0 (hr0.trans hr.2.le) |>.2 hr.2]
    · nlinarith [sq_lt_sq₀ hu hr0 |>.2 hr.1]
  have hg := L.extendedMetric_restrictOpen_jointContMDiffOn W had hds
  have hminη : ∀ δ : ℝ → W, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 δ →
      δ u = η u → δ d = η d →
      lRegularizedAction S T η u d ≤ lRegularizedAction S T δ u d := by
    intro δ hδ hδu hδd
    let β : ℝ → P.Carrier := fun r => (δ r).val.val
    have hβ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β :=
      contMDiff_subtype_val.comp (contMDiff_subtype_val.comp hδ)
    have hδint : IntervalIntegrable (lRegularizedLagrangian S T δ) _root_.MeasureTheory.MeasureSpace.volume u d := by
      have hc := lRegularizedLagrangian_continuousOn_carrier S hS δ hδ
      exact (hc.comp (f := fun r : ℝ => (T, r))
        (continuous_const.prodMk continuous_id).continuousOn hclock).intervalIntegrable_of_Icc hd.1.le
    have hlag := closedSolution_lagrangian_ae_eq_of_projection L W (d := d) hds.le hu hTu δ β
      (Filter.Eventually.of_forall fun r => hδ.mdifferentiable one_ne_zero r)
      (fun _ _ => rfl)
    have hlag' : lRegularizedLagrangian S T δ =ᵐ[volume.restrict (Ι u d)]
        lRegularizedLagrangian G.flow T β := by
      rw [_root_.Set.uIoc_of_le hd.1.le]
      exact _root_.MeasureTheory.ae_mono (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume _root_.Set.Ioc_subset_Icc_self) hlag
    have hβint := (intervalIntegrable_congr_ae hlag').mp hδint
    have hδact : lRegularizedAction S T δ u d = lRegularizedAction G.flow T β u d :=
      intervalIntegral.integral_congr_ae_restrict hlag'
    have hβu : β u = α u := by
      dsimp only [β]
      rw [hδu]
      exact hproj ⟨le_rfl, hd.1.le⟩
    have hβd : β d = α d := by
      dsimp only [β]
      rw [hδd]
      exact hproj ⟨hd.1.le, le_rfl⟩
    rw [hact, hδact]
    exact lRegularizedAction_minimal_on_subinterval_of_absolutelyContinuousOnInterval
      G.flow T u u d v le_rfl hd.1.le hd.2.le α hα hint hmin β
      (Manifold.absolutelyContinuousOnInterval_of_contMDiffOn hβ.contMDiffOn)
      hβint hβu hβd
  have hηC1 := lMinCurve_c1_of_absolutelyContinuousOnInterval_of_jointContMDiffOn_metric
    S hS T u d hd.1 η hη (hηint hint) (_root_.Set.Icc (T - d ^ 2) s)
    Subset.rfl hclock hreg hg hminη
  have hprojC1 : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1
      (fun r => (η r).val.val) (_root_.Set.Icc u d) :=
    contMDiff_subtype_val.comp_contMDiffOn
      (contMDiff_subtype_val.comp_contMDiffOn hηC1)
  exact ⟨d, hd, hprojC1.congr hproj.symm⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_contMDiffOn_one_terminal_collar_of_action_minimal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_contMDiffOn_one_terminal_collar_of_action_minimal target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe uIncomingClosedC1
variable {P : OrientedThreeStage.{uIncomingClosedC1}} {a s : ℝ}

theorem contMDiffOn_one_of_action_minimal
    (G : P.IncomingSlab a s) {T u v : ℝ} {alpha : ℝ → P.Carrier}
    (huv : u < v)
    (hclock : ∀ r ∈ _root_.Set.Icc u v, T - r ^ 2 ∈ _root_.Set.Ico a s)
    (halpha : Manifold.absolutelyContinuousOnInterval ThreeModel alpha u v)
    (hint : IntervalIntegrable (lRegularizedLagrangian G.flow T alpha) _root_.MeasureTheory.MeasureSpace.volume u v)
    (hmin : ∀ beta : ℝ → P.Carrier,
      Manifold.absolutelyContinuousOnInterval ThreeModel beta u v →
      IntervalIntegrable (lRegularizedLagrangian G.flow T beta) _root_.MeasureTheory.MeasureSpace.volume u v →
      beta u = alpha u → beta v = alpha v →
      lRegularizedAction G.flow T alpha u v ≤ lRegularizedAction G.flow T beta u v) :
    ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 alpha (_root_.Set.Icc u v) := by
  let : TopologicalSpace.MetrizableSpace P.Carrier := Manifold.metrizableSpace ThreeModel P.Carrier
  have hreg (r : ℝ) (hr : r ∈ _root_.Set.Ioo u v) :
      T - r ^ 2 ∈ (RealTimeInterval.closedOpen a s G.lt).regular := by
    change a < T - r ^ 2 ∧ T - r ^ 2 < s
    have hlower : a < T - r ^ 2 := by
      by_cases hr0 : 0 ≤ r
      · have hsq := (sq_lt_sq₀ hr0 (hr0.trans hr.2.le)).mpr hr.2
        have hv := hclock v ⟨huv.le, le_rfl⟩
        linarith only [hsq, hv.1]
      · have hu0 := hr.1.trans (lt_of_not_ge hr0)
        have hsq : r ^ 2 < u ^ 2 := by
          simpa only [neg_sq] using
            (sq_lt_sq₀ (neg_nonneg.mpr (lt_of_not_ge hr0).le)
              (neg_nonneg.mpr hu0.le)).mpr (neg_lt_neg hr.1)
        have hu := hclock u ⟨le_rfl, huv.le⟩
        linarith only [hsq, hu.1]
    exact ⟨hlower, (hclock r (_root_.Set.Ioo_subset_Icc_self hr)).2⟩
  apply lMinCurve_c1_of_absolutelyContinuousOnInterval_of_jointContMDiffOn_metric
    G.flow G.equation T u v huv alpha halpha hint (_root_.Set.Ico a s) Subset.rfl
    hclock hreg G.smoothUpTo.jointContMDiffOn
  intro beta hbeta hbu hbv
  have hbetaInt : IntervalIntegrable (lRegularizedLagrangian G.flow T beta) _root_.MeasureTheory.MeasureSpace.volume u v := by
    have hc := lRegularizedLagrangian_continuousOn_carrier G.flow G.equation beta hbeta
    exact (hc.comp (f := fun r : ℝ => (T, r))
      (continuous_const.prodMk continuous_id).continuousOn hclock).intervalIntegrable_of_Icc huv.le
  exact hmin beta (Manifold.absolutelyContinuousOnInterval_of_contMDiffOn hbeta.contMDiffOn)
    hbetaInt hbu hbv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.contMDiffOn_one_of_action_minimal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.contMDiffOn_one_of_action_minimal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.contMDiffOn_one_of_action_minimal ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.contMDiffOn_one_of_action_minimal

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe uIncomingFullC1
variable {P : OrientedThreeStage.{uIncomingFullC1}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.contMDiffOn_one_of_action_minimal
    (L : G.TerminalLimitMetric) {T u v : ℝ} {alpha : ℝ → P.Carrier}
    (hu : 0 ≤ u) (huv : u < v) (hTu : T - u ^ 2 = s) (ha : a ≤ T - v ^ 2)
    (halpha : Manifold.absolutelyContinuousOnInterval ThreeModel alpha u v)
    (hint : IntervalIntegrable (lRegularizedLagrangian G.flow T alpha) _root_.MeasureTheory.MeasureSpace.volume u v)
    (hterminal : alpha u ∈ G.terminalRegularOpen)
    (hmin : ∀ beta : ℝ → P.Carrier,
      Manifold.absolutelyContinuousOnInterval ThreeModel beta u v →
      IntervalIntegrable (lRegularizedLagrangian G.flow T beta) _root_.MeasureTheory.MeasureSpace.volume u v →
      beta u = alpha u → beta v = alpha v →
      lRegularizedAction G.flow T alpha u v ≤ lRegularizedAction G.flow T beta u v) :
    ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 alpha (_root_.Set.Icc u v) := by
  obtain ⟨d, hd, hprefix⟩ :=
    L.exists_contMDiffOn_one_terminal_collar_of_action_minimal hu huv hTu ha halpha hint hterminal hmin
  obtain ⟨c, huc, hcd⟩ := exists_between hd.1
  have hcv : c < v := hcd.trans hd.2
  have hclock (r : ℝ) (hr : r ∈ _root_.Set.Icc c v) : T - r ^ 2 ∈ _root_.Set.Ico a s := by
    have hr0 := hu.trans (huc.le.trans hr.1)
    have hsqv := (sq_le_sq₀ hr0 (hr0.trans hr.2)).mpr hr.2
    have hsqu := (sq_lt_sq₀ hu hr0).mpr (huc.trans_le hr.1)
    exact ⟨by linarith only [ha, hsqv], by linarith only [hTu, hsqu]⟩
  have halphaTail : Manifold.absolutelyContinuousOnInterval ThreeModel alpha c v :=
    Manifold.absolutelyContinuousOnInterval_mono halpha (by
      simpa only [_root_.Set.uIcc_of_le hcv.le, _root_.Set.uIcc_of_le huv.le] using _root_.Set.Icc_subset_Icc huc.le le_rfl)
  have hintTail : IntervalIntegrable (lRegularizedLagrangian G.flow T alpha) _root_.MeasureTheory.MeasureSpace.volume c v :=
    hint.mono_set (by
      simpa only [_root_.Set.uIcc_of_le hcv.le, _root_.Set.uIcc_of_le huv.le] using _root_.Set.Icc_subset_Icc huc.le le_rfl)
  have hminTail := lRegularizedAction_minimal_on_subinterval_of_absolutelyContinuousOnInterval
    G.flow T u c v v huc.le hcv.le le_rfl alpha halpha hint hmin
  have htail := G.contMDiffOn_one_of_action_minimal hcv
    hclock halphaTail hintTail hminTail
  intro r hr
  by_cases hrd : r < d
  · apply (hprefix r ⟨hr.1, hrd.le⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hrd)] with x hx hxd
    exact ⟨hx.1, hxd.le⟩
  · have hcr : c < r := hcd.trans_le (not_lt.mp hrd)
    apply (htail r ⟨hcr.le, hr.2⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hcr)] with x hx hcx
    exact ⟨hcx.le, hx.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.contMDiffOn_one_of_action_minimal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.contMDiffOn_one_of_action_minimal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.contMDiffOn_one_of_action_minimal ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.contMDiffOn_one_of_action_minimal

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end
