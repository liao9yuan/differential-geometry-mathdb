import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.Density
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.AbsoluteContinuityStage
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.C1Attainment

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Interval _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uHistoryCostLsc

theorem lowerSemicontinuous_regularizedC1Cost_past_endpoint
    (H : ObservedHistory.{uHistoryCostLsc})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ r ∈ _root_.Set.Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x)
    (p : (H.stage last).Carrier) :
    LowerSemicontinuous (fun q => H.regularizedC1Cost first last hle T u v p q) := by
  classical
  let : TopologicalSpace.MetrizableSpace (H.stage first).Carrier :=
    Manifold.metrizableSpace ThreeModel (H.stage first).Carrier
  have hupperIcc : T - u ^ 2 ∈ _root_.Set.Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro bound
  cases bound using WithTop.recTopCoe with
  | top => simpa only [_root_.Set.Iic_top, _root_.Set.preimage_univ] using (isClosed_univ : IsClosed (_root_.Set.univ : Set (H.stage first).Carrier))
  | coe bound =>
    apply IsSeqClosed.isClosed
    intro qseq q hqseq hq
    have hfinite (n : ℕ) : H.regularizedC1Cost first last hle T u v p (qseq n) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (hqseq n)
    choose alpha halpha hint hstart hend hnodes hminimum using fun n =>
      H.exists_regularizedC1Cost_minimizer_of_ne_top first last hle T B u v
        hupper hscalar p (qseq n) (hfinite n)
    let action (n : ℕ) := ∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val T (alpha n j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)
    have hmember (n : ℕ) : action n ∈ H.regularizedC1ActionValues first last hle T u v p (qseq n) :=
      ⟨hu, huv, hupperIcc, hpast, alpha n, halpha n, hint n, hstart n, hend n, hnodes n, rfl⟩
    have hbound (n : ℕ) : action n ∈ _root_.Set.Icc (-(2 * B / 3) * (v ^ 3 - u ^ 3)) bound := by
      refine ⟨H.regularizedC1ActionValues_ge_of_scalar_lower first last hle T u v B
        hscalar p (qseq n) (hmember n), ?_⟩
      exact WithTop.coe_le_coe.mp ((hminimum n).trans_le (hqseq n))
    obtain ⟨ell, hell, phi, hphi, haction⟩ := isCompact_Icc.tendsto_subseq hbound
    have hendLimit : _root_.Filter.Tendsto (fun n => alpha (phi n) ⟨first, le_rfl, hle⟩ v) _root_.Filter.atTop (𝓝 q) := by
      simpa only [hend, Function.comp_def] using hq.comp hphi.tendsto_atTop
    obtain ⟨_, gamma, _, _, _, hgammaAC, hgammaInt, hgammaU, hgammaV, hgammaNodes, hgammaAction⟩ :=
      H.exists_subsequence_sum_stageRegularizedAction_le_of_tendsto_action_of_tendsto_endpoint
        first last hle hu huv hupper hpast p q bound B ell (fun n => alpha (phi n))
        (fun n j => (halpha (phi n) j).contMDiffOn) (fun n => hint (phi n))
        (fun n => hstart (phi n)) hendLimit (fun n => hnodes (phi n))
        (fun n j r hr => hscalar j r hr (alpha (phi n) j r))
        (fun n => (hbound (phi n)).2) haction
    have hext := H.regularizedExtendedAction_eq_sum_action first last hu huv hupperIcc hpast
      gamma hgammaInt (fun j => by
        filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with r hr
        exact hscalar j r hr (gamma j r))
    have hgammaMember : H.regularizedExtendedAction first last T B u v gamma ∈
        H.regularizedActionValues first last hle T B u v p q :=
      ⟨hu, huv, hupperIcc, hpast, gamma, hgammaAC, hgammaU, hgammaV, hgammaNodes, rfl⟩
    change H.regularizedC1Cost first last hle T u v p q ≤ (bound : WithTop ℝ)
    rw [← H.regularizedCost_eq_regularizedC1Cost first last hle T B u v hupper hscalar p q]
    refine (H.regularizedCost_le_of_competitor first last hle T B u v p q hgammaMember).trans ?_
    rw [hext]
    exact WithTop.coe_le_coe.mpr (hgammaAction.trans hell.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.lowerSemicontinuous_regularizedC1Cost_past_endpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.lowerSemicontinuous_regularizedC1Cost_past_endpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.lowerSemicontinuous_regularizedC1Cost_past_endpoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.lowerSemicontinuous_regularizedC1Cost_past_endpoint

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
