import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAt
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryHorizonExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

variable {P₀ : OrientedThreeStage.{u}}

theorem extendAt_stageAt_iff (H : RetainedCoreHistory P₀)
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {t : ℝ}
    (hat : H.time (Fin.last H.eventCount) < t) (hts : t < s)
    (Q : ∀ K : OrientedThreeStage.{u},
      SmoothRiemannianMetric ThreeModel K.Carrier → K.Carrier → Prop)
    (y : (H.stage (Fin.last H.eventCount)).Carrier)
    (yh : ((H.extendAt hend G hG hat hts).toHistory.stageAt
      (H.extendAtTime hend G hG hat hts)).Carrier) (hy : HEq yh y) :
    Q ((H.extendAt hend G hG hat hts).toHistory.stageAt (H.extendAtTime hend G hG hat hts))
        ((H.extendAt hend G hG hat hts).toHistory.stageMetric
          ((H.extendAt hend G hG hat hts).toHistory.activeStage
            (H.extendAtTime hend G hG hat hts)) (H.extendAtTime hend G hG hat hts)) yh ↔
      Q (H.stage (Fin.last H.eventCount)) (G.flow.base.metric t) y := by
  have hlast : (H.extendAt hend G hG hat hts).toHistory.activeStage
      (H.extendAtTime hend G hG hat hts) = Fin.last H.eventCount :=
    H.activeStage_extendHorizon_eq_last (hend ▸ hat.le) (G.closedPrefix t hat hts) hG
      (H.extendAtTime hend G hG hat hts) hat.le
  have hmet : (H.extendAt hend G hG hat hts).toHistory.stageMetric (Fin.last H.eventCount)
      (H.extendAtTime hend G hG hat hts) = G.flow.base.metric t :=
    H.stageMetric_extendHorizon_last_of_mem_Icc (hend ▸ hat.le) (G.closedPrefix t hat hts) hG
      ⟨hat.le, le_rfl⟩
  revert yh
  change ∀ yh : ((H.extendAt hend G hG hat hts).toHistory.stage
      ((H.extendAt hend G hG hat hts).toHistory.activeStage
        (H.extendAtTime hend G hG hat hts))).Carrier, HEq yh y →
    (Q ((H.extendAt hend G hG hat hts).toHistory.stage
        ((H.extendAt hend G hG hat hts).toHistory.activeStage
          (H.extendAtTime hend G hG hat hts)))
      ((H.extendAt hend G hG hat hts).toHistory.stageMetric
        ((H.extendAt hend G hG hat hts).toHistory.activeStage
          (H.extendAtTime hend G hG hat hts)) (H.extendAtTime hend G hG hat hts)) yh ↔ _)
  generalize (H.extendAt hend G hG hat hts).toHistory.activeStage
    (H.extendAtTime hend G hG hat hts) = k at hlast ⊢
  subst hlast
  intro yh hy
  obtain rfl := eq_of_heq hy
  rw [hmet]
  exact Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.extendAt_stageAt_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.extendAt_stageAt_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.extendAt_stageAt_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.extendAt_stageAt_iff

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

end
