import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem oldTerminal_isSmoothEmbedding :
    letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ E.oldTerminal := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  refine DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen (𝓡∂ 3) ThreeModel
    _ E.oldTerminal ?_
  convert E.old_induced using 1
  funext x
  exact E.oldTerminal_eq x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.oldTerminal_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.oldTerminal_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.oldTerminal_isSmoothEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.oldTerminal_isSmoothEmbedding

theorem contMDiff_oldInclusion :
    letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
    letI : ChartedSpace (EuclideanHalfSpace 3) E.transition.trace.tubes.core :=
      E.transition.coreCharts
    ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (fun x : E.old => x.1) := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  let : ChartedSpace (EuclideanHalfSpace 3) E.transition.trace.tubes.core :=
    E.transition.coreCharts
  intro x
  have hcore := E.transition.core_induced.isImmersion.isImmersionAt x.1
  rw [ContMDiffAt.iff_comp_isImmersionAt hcore]
  exact ⟨continuous_subtype_val.continuousAt, E.old_induced.contMDiff.contMDiffAt⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.contMDiff_oldInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.contMDiff_oldInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.contMDiff_oldInclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.contMDiff_oldInclusion

theorem contMDiff_oldOutput :
    letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
    ContMDiff (𝓡∂ 3) ThreeModel ∞ E.oldOutput := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  let : ChartedSpace (EuclideanHalfSpace 3) E.transition.trace.tubes.core :=
    E.transition.coreCharts
  have hcomp : ContMDiff (𝓡∂ 3) ThreeModel ∞
      (fun x : E.old =>
        E.transition.presentation (E.transition.trace.capping.coreInclusion x.1)) :=
    E.transition.presentation.contMDiff.comp
      (E.transition.core_inclusion_smooth.contMDiff.comp E.contMDiff_oldInclusion)
  have hfun : ((Sum.inl : Q.Carrier → Q.Carrier ⊕ E.discarded.Carrier) ∘ E.oldOutput) =
      (fun x : E.old =>
        E.transition.presentation (E.transition.trace.capping.coreInclusion x.1)) := by
    funext x
    rw [Function.comp_apply, E.transition.presentation_eq, E.oldOutput_eq]
  intro x
  rw [ContMDiffAt.iff_comp_isImmersionAt
    ((IsSmoothEmbedding.sumInl (I := ThreeModel) (M := Q.Carrier)
      (M' := E.discarded.Carrier)).isImmersion.isImmersionAt (E.oldOutput x))]
  exact ⟨E.oldOutput.continuous.continuousAt, hfun ▸ hcomp.contMDiffAt⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.contMDiff_oldOutput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.contMDiff_oldOutput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.contMDiff_oldOutput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.contMDiff_oldOutput

theorem oldTerminal_mfderiv_bijective (x : E.old) :
    letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
    Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel E.oldTerminal x) := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  exact DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt
    (𝓡∂ 3) ThreeModel E.oldTerminal x
    (E.oldTerminal_isSmoothEmbedding.isImmersion.isImmersionAt x) rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.oldTerminal_mfderiv_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.oldTerminal_mfderiv_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.oldTerminal_mfderiv_bijective ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.oldTerminal_mfderiv_bijective

theorem oldOutput_mfderiv_bijective (x : E.old) :
    letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
    Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel E.oldOutput x) := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  let D := mfderiv (𝓡∂ 3) ThreeModel E.oldOutput x
  have hinj : Function.Injective D := by
    intro v w hvw
    have hv : D (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have heq := E.old_metric_eq x (v - w) (v - w)
    change D (v - w) = 0 at hv
    rw [hv] at heq
    have hzero : mfderiv (𝓡∂ 3) ThreeModel E.oldTerminal x (v - w) = 0 := by
      by_contra hne
      have hpos := E.terminal.metric.pos (E.oldTerminal x)
        (mfderiv (𝓡∂ 3) ThreeModel E.oldTerminal x (v - w)) hne
      simp only [map_zero] at heq
      exact (ne_of_gt hpos) heq
    exact sub_eq_zero.mp ((E.oldTerminal_mfderiv_bijective x).injective
      (hzero.trans (map_zero _).symm))
  exact D.toLinearMap.linearEquivOfInjective hinj rfl |>.bijective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.oldOutput_mfderiv_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.oldOutput_mfderiv_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.oldOutput_mfderiv_bijective ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.oldOutput_mfderiv_bijective

theorem oldOutput_isClosedEmbedding : _root_.Topology.IsClosedEmbedding E.oldOutput := by
  let : CompactSpace E.old := isCompact_iff_compactSpace.mp E.old_compact
  exact E.oldOutput.continuous.isClosedEmbedding E.oldOutput_injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.oldOutput_isClosedEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.oldOutput_isClosedEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.oldOutput_isClosedEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.oldOutput_isClosedEmbedding

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
