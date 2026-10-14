import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ObservedComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Assembly
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventBridge
import Submission.DifferentialGeometry.Topology.Manifold.CollarFamily
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandard
import Submission.DifferentialGeometry.Topology.VanKampen.FullGroupoid

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Topology _root_.Submission.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem disjointBoundaryCollarFamily_holds :
    disjointBoundaryCollarFamily.{u} := by
  intro X _ _ ι _ S _ _ e c hc h0 hdisj
  exact DifferentialGeometry.Topology.Collar.disjointBoundaryCollarFamily hc h0 hdisj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.disjointBoundaryCollarFamily_holds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.disjointBoundaryCollarFamily_holds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.disjointBoundaryCollarFamily_holds ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.disjointBoundaryCollarFamily_holds

theorem seifertVanKampenPushout_holds :
    seifertVanKampenPushout.{u} := by
  intro X _ U V hU hV hcover
  exact DifferentialGeometry.Topology.VanKampen.seifertVanKampen U V hU hV hcover

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.seifertVanKampenPushout_holds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.seifertVanKampenPushout_holds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.seifertVanKampenPushout_holds ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.seifertVanKampenPushout_holds

theorem boundaryCollarGeometry_iff :
    boundaryCollarGeometry.{u} ↔ relativeCollarUniqueness.{u} :=
  ⟨fun h => h.2, fun h => ⟨disjointBoundaryCollarFamily_holds, h⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.boundaryCollarGeometry_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.boundaryCollarGeometry_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.boundaryCollarGeometry_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.boundaryCollarGeometry_iff

theorem geometricReconstructionBackground_iff :
    geometricReconstructionBackground.{u} ↔
      relativeCollarUniqueness.{u} ∧ ballEmbeddingIsotopy.{u} ∧
        sphereDiffeomorphismIsotopyConnected :=
  ⟨fun h => ⟨h.1.2, h.2.1, h.2.2.1⟩,
    fun h => ⟨⟨disjointBoundaryCollarFamily_holds, h.1⟩, h.2.1, h.2.2,
      seifertVanKampenPushout_holds⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.geometricReconstructionBackground_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.geometricReconstructionBackground_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.geometricReconstructionBackground_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.geometricReconstructionBackground_iff

theorem globalMetricStep_iff_globalStepConclusion
    (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ) (a₀ : ℝ)
    (DiscardedCutOpen : Type u → Prop)
    (inputs : GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen) :
    globalMetricStep p τ ε d k a₀ DiscardedCutOpen inputs ↔
      GlobalStepConclusion.{u} p τ ε d k a₀ DiscardedCutOpen inputs :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.globalMetricStep_iff_globalStepConclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.globalMetricStep_iff_globalStepConclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.globalMetricStep_iff_globalStepConclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.globalMetricStep_iff_globalStepConclusion

theorem globalMetricStep_scale_positive
    (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ) (a₀ : ℝ)
    (DiscardedCutOpen : Type u → Prop)
    (inputs : GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen)
    (h : globalMetricStep p τ ε d k a₀ DiscardedCutOpen inputs) :
    ∃ hstar : ℝ, 0 < hstar ∧ 2 * hstar ^ 2 < τ := by
  obtain ⟨hstar, hpos, hlt, _⟩ := h
  exact ⟨hstar, hpos, hlt⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.globalMetricStep_scale_positive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.globalMetricStep_scale_positive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.globalMetricStep_scale_positive ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.globalMetricStep_scale_positive

def TangentOrientationSection.toManifoldOrientation {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (o : TangentOrientationSection M) : ManifoldOrientation ThreeModel M 3 where
  dimension_eq := by simp
  orientation := o.orientation
  locally_constant := o.locally_constant

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.toManifoldOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.toManifoldOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.toManifoldOrientation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.toManifoldOrientation

theorem mfderivToContinuousLinearEquiv_toLinearEquiv_eq_ofBijective
    {M N : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N]
    (f : M ≃ₘ⟮ThreeModel, ThreeModel⟯ N) (x : M)
    (hf : Function.Bijective (mfderiv ThreeModel ThreeModel f x)) :
    (f.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv =
      LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel f x).toLinearMap hf := by
  ext v
  rw [LinearEquiv.ofBijective_apply]
  change (f.mfderivToContinuousLinearEquiv (by simp) x :
    TangentSpace ThreeModel x → TangentSpace ThreeModel (f x)) v =
    mfderiv ThreeModel ThreeModel f x v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.mfderivToContinuousLinearEquiv_toLinearEquiv_eq_ofBijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.mfderivToContinuousLinearEquiv_toLinearEquiv_eq_ofBijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.mfderivToContinuousLinearEquiv_toLinearEquiv_eq_ofBijective ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.mfderivToContinuousLinearEquiv_toLinearEquiv_eq_ofBijective

theorem preservesOrientation_of_preservesTangentOrientation
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (oM : TangentOrientationSection M)
    {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] (oN : TangentOrientationSection N)
    (f : M ≃ₘ⟮ThreeModel, ThreeModel⟯ N)
    (h : PreservesTangentOrientation oM oN f) :
    f.preservesOrientation oM.toManifoldOrientation oN.toManifoldOrientation := by
  intro x
  obtain ⟨hf, hfx⟩ := h.2 x
  rw [mfderivToContinuousLinearEquiv_toLinearEquiv_eq_ofBijective f x hf]
  exact hfx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.preservesOrientation_of_preservesTangentOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.preservesOrientation_of_preservesTangentOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.preservesOrientation_of_preservesTangentOrientation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.preservesOrientation_of_preservesTangentOrientation

theorem OrientedThreeStage.preservesOrientation_toClosedOrientedManifold
    {P Q : OrientedThreeStage.{u}} {f : P.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ Q.Carrier}
    (h : PreservesTangentOrientation P.orientation Q.orientation f) :
    f.preservesOrientation P.toClosedOrientedManifold.orientation
      Q.toClosedOrientedManifold.orientation := by
  intro x
  exact preservesOrientation_of_preservesTangentOrientation
    P.orientation Q.orientation f h x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.preservesOrientation_toClosedOrientedManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.preservesOrientation_toClosedOrientedManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.preservesOrientation_toClosedOrientedManifold ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.preservesOrientation_toClosedOrientedManifold

def InitialIdentification.toFiniteSurgeryHistory
    {P : OrientedThreeStage.{u}} {g : P.Metric} {H : ObservedHistory.{u}}
    (A : InitialIdentification P g H) (hn : 0 < H.eventCount)
    (bridge : (i : Fin H.eventCount) →
      DifferentialGeometry.PDE.RicciFlow.Surgery.MetricCutCapEvent
        (H.stage i.castSucc).toClosedOrientedManifold
        (H.stage i.succ).toClosedOrientedManifold
        (H.time i.castSucc) (H.time i.succ))
    (hbridge_initial : ∀ i : Fin H.eventCount,
      (bridge i).incoming.flow.base.metric (H.time i.castSucc) = H.initialMetric i.castSucc)
    (hbridge_output : ∀ i : Fin H.eventCount,
      (bridge i).outputMetric = H.initialMetric i.succ) :
    (H.toSurgeryFiniteSurgeryHistory hn bridge hbridge_initial hbridge_output).InitialIdentification
      P.toClosedOrientedManifold g where
  diffeomorph := A.map
  orientation_preserving :=
    OrientedThreeStage.preservesOrientation_toClosedOrientedManifold A.positive
  metric_eq := A.metric_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.toFiniteSurgeryHistory then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.toFiniteSurgeryHistory"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.toFiniteSurgeryHistory ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.toFiniteSurgeryHistory

theorem exists_poincare_controlled_extinction_of_observedHistory
    (P : OrientedThreeStage.{u}) (g : P.Metric) (H : ObservedHistory.{u})
    (A : InitialIdentification P g H) [Nonempty P.Carrier]
    (hc : (i : Fin H.eventCount) → SmoothCutCapCompletion (H.event i).transition)
    (hout : (i : Fin H.eventCount) →
      letI : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
      _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : (H.event i).old => (H.event i).transition.trace.capping.coreInclusion x.1))
    (hctrl : ∀ i : Fin H.eventCount, ∀ c : ConnectedComponents (H.event i).discarded.Carrier,
      DifferentialGeometry.Topology.isPoincareStandard
        ((H.event i).discarded.toClosedOrientedManifold.component c).Carrier)
    (hempty : IsEmpty (H.stage (Fin.last H.eventCount)).Carrier) :
    Nonempty (PoincareControlledExtinction P.toClosedOrientedManifold g) := by
  have hn : 0 < H.eventCount :=
    @ObservedHistory.eventCount_pos_of_final_empty H A.initial_nonempty hempty
  refine ⟨{ history := H.toSurgeryFiniteSurgeryHistory_of_cutCapCompletion hn hc hout
            time := H.time (Fin.last H.eventCount)
            time_pos := H.last_time_pos hn
            initial := A.toFiniteSurgeryHistory hn (H.toSurgeryEvents hc hout)
              (H.toSurgeryEvents_initial hc hout) (H.toSurgeryEvents_output hc hout)
            controlled := ?_
            extinct := ?_ }⟩
  · intro i
    exact SphericalCutCapTransition.ofSmoothCutCapTransition_poincareControlled
      (H.event i).transition (hc i) (hctrl i)
  · exact ⟨rfl, hempty⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_observedHistory then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_observedHistory"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_observedHistory ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_observedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
