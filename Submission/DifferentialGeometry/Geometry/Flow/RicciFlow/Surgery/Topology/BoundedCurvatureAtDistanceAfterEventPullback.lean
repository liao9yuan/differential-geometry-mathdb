import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFlow
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingScalar
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature
import Submission.DifferentialGeometry.Geometry.Metric.DistancePullback
import Submission.DifferentialGeometry.Geometry.Metric.BilinearPerturbation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen target :: scope.openDecls } }

theorem eventually_backwardSurvivor_scalar_close_and_edist_le (H : ObservedHistory.{u})
    (j : Fin H.eventCount) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ σ in 𝓝[<] H.time j.succ,
      (∀ x : H.backwardSurvivorDomain j.castSucc j.succ j.castSucc_lt_succ.le,
        |metricScalarAt ((H.event j).incoming.flow.base.metric σ)
            (H.backwardSurvivorMap j.castSucc j.succ j.castSucc_lt_succ.le j.castSucc le_rfl
              j.castSucc_lt_succ.le x) -
          metricScalarAt (H.initialMetric j.succ) x.val| < δ) ∧
      ∀ x z : H.backwardSurvivorDomain j.castSucc j.succ j.castSucc_lt_succ.le,
        riemannianEDistOf ((H.event j).incoming.flow.base.metric σ)
            (H.backwardSurvivorMap j.castSucc j.succ j.castSucc_lt_succ.le j.castSucc le_rfl
              j.castSucc_lt_succ.le x)
            (H.backwardSurvivorMap j.castSucc j.succ j.castSucc_lt_succ.le j.castSucc le_rfl
              j.castSucc_lt_succ.le z) ≤
          ENNReal.ofReal (Real.sqrt 2) *
            riemannianEDistOf ((H.initialMetric j.succ).restrictOpen
              (H.backwardSurvivorDomain j.castSucc j.succ j.castSucc_lt_succ.le)) x z := by
  have hle : j.castSucc ≤ j.succ := j.castSucc_lt_succ.le
  let U := H.backwardSurvivorDomain j.castSucc j.succ hle
  let E := H.event j
  let T := H.backwardSurvivorTerminalMap j.castSucc j.succ hle j le_rfl le_rfl
  let K : Set E.incoming.terminalRegularOpen := _root_.Set.range E.oldTerminal
  have hK : IsCompact K := by
    have : CompactSpace E.old := isCompact_iff_compactSpace.mp E.old_compact
    exact isCompact_range E.oldTerminal.continuous
  have hTK (x : U) : T x ∈ K := by
    obtain ⟨w, -, hw, -⟩ :=
      H.backwardSurvivorMap_crossing j.castSucc j.succ hle j le_rfl le_rfl x
    exact ⟨w, Subtype.ext ((E.oldTerminal_eq w).trans hw)⟩
  have hΨ : H.backwardSurvivorMap j.castSucc j.succ hle j.succ hle le_rfl = Subtype.val :=
    funext (H.backwardSurvivorMap_last j.castSucc j.succ hle)
  obtain ⟨d0, hd0, hb0⟩ := E.terminal.converges K hK 0 1 one_pos
  filter_upwards [E.terminal.eventually_scalar_close_on_compact hK hδ,
    Ioo_mem_nhdsLT hd0.2] with σ hσ hσd
  refine ⟨fun x => ?_, fun x z => ?_⟩
  · have hcr := H.backwardSurvivorMap_crossing j.castSucc j.succ hle j le_rfl le_rfl x
    have hΨx : H.backwardSurvivorMap j.castSucc j.succ hle j.succ hle le_rfl x = x.val :=
      H.backwardSurvivorMap_last j.castSucc j.succ hle x
    rw [hΨx] at hcr
    have hc : metricScalarAt E.terminal.metric (T x) =
        metricScalarAt (H.initialMetric j.succ) x.val := by
      rw [← H.event_output j]
      exact MetricCutCapEvent.RegularCrossing.scalar_eq E (p := T x) hcr
    rw [← hc]
    exact hσ (T x) (hTK x)
  · have hquad : ∀ (w : U) (v : TangentSpace ThreeModel w),
        ((E.incoming.flow.base.metric σ).restrictOpen E.incoming.terminalRegularOpen).inner (T w)
            (mfderiv ThreeModel ThreeModel T w v) (mfderiv ThreeModel ThreeModel T w v) ≤
          2 * ((H.initialMetric j.succ).restrictOpen U).inner w v v := by
      intro w v
      have hn := hb0 σ hσd (T w) (hTK w)
      have hb := (Geometry.Metric.inner_bounds_of_metricDerivNorm_le E.terminal.metric
        ((E.incoming.flow.base.metric σ).restrictOpen E.incoming.terminalRegularOpen) (T w)
        hn.le (mfderiv ThreeModel ThreeModel T w v)).2
      have hm := H.backwardSurvivorMap_metric_crossing j.castSucc j.succ hle j le_rfl le_rfl w v v
      rw [hΨ, mfderiv_subtype_val_apply] at hm
      change _ ≤ 2 * (H.initialMetric j.succ).inner w.val v v
      rw [hm, show (2 : ℝ) = 1 + 1 by norm_num]
      exact hb
    have h1 := Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph
      ((H.initialMetric j.succ).restrictOpen U)
      ((E.incoming.flow.base.metric σ).restrictOpen E.incoming.terminalRegularOpen) T
      (H.backwardSurvivorTerminalMap_isLocalDiffeomorph j.castSucc j.succ hle j le_rfl le_rfl)
      two_pos hquad x z
    exact (riemannianEDistOf_le_restrictOpen (E.incoming.flow.base.metric σ)
      E.incoming.terminalRegularOpen (T x) (T z)).trans h1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventually_backwardSurvivor_scalar_close_and_edist_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventually_backwardSurvivor_scalar_close_and_edist_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventually_backwardSurvivor_scalar_close_and_edist_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventually_backwardSurvivor_scalar_close_and_edist_le

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
