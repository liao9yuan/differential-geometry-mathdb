import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryCapPreservation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent.PresentedStaticCap

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
  (S : E.PresentedStaticCap fixed D m ε b)

def window : C(standardCapWindow D, Q.Carrier) := S.inclusion.comp S.witness.window

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.window ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.window

theorem window_smooth : _root_.Manifold.IsSmoothEmbedding ThreeModel ThreeModel ∞ S.window :=
  S.inclusion_smooth.comp S.witness.window_smooth (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.window_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.window_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.window_smooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.window_smooth

theorem window_inner (x : standardCapWindow D) (v w : TangentSpace ThreeModel x) :
    S.witness.windowMetric.inner x v w = S.neck.scale *
      E.outputMetric.inner (S.window x)
        (mfderiv ThreeModel ThreeModel S.window x v)
        (mfderiv ThreeModel ThreeModel S.window x w) := by
  rw [S.witness.window_inner, S.inclusion_metric]
  change _ = S.neck.scale * E.outputMetric.inner _
    (mfderiv ThreeModel ThreeModel (S.inclusion ∘ S.witness.window) x v)
    (mfderiv ThreeModel ThreeModel (S.inclusion ∘ S.witness.window) x w)
  rw [mfderiv_comp x (S.inclusion_smooth.contMDiff.mdifferentiableAt (by simp))
    (S.witness.window_smooth.contMDiff.mdifferentiableAt (by simp))]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.window_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.window_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.window_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.window_inner

def toRetained (hOld : E.old = E.transition.trace.retainedCore) :
    (E.toRetainedCoreEvent hOld).toMetricCutCapEvent.PresentedStaticCap fixed D m ε b where
  delta := S.delta
  order := S.order
  neck := S.neck
  witness := S.witness
  inclusion := S.inclusion
  inclusion_smooth := S.inclusion_smooth
  inclusion_metric := S.inclusion_metric
  cap_eq := S.cap_eq
  attaching_eq := S.attaching_eq
  retainedPoint := S.retainedPoint
  retained_point_eq := S.retained_point_eq
  retained_eq := S.retained_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.toRetained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.toRetained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.toRetained ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.toRetained

@[simp] theorem toRetained_window (hOld : E.old = E.transition.trace.retainedCore) :
    (S.toRetained hOld).window = S.window := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.toRetained_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.toRetained_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.toRetained_window ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.toRetained_window

end MetricCutCapEvent.PresentedStaticCap

theorem MetricCutCapEvent.range_oldOutput_toRetainedCoreEvent
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) :
    range (E.toRetainedCoreEvent hOld).toMetricCutCapEvent.oldOutput = _root_.Set.range E.oldOutput := by
  let e := E.retainedOldDiffeomorph hOld
  change _root_.Set.range (E.oldOutput ∘ e) = _root_.Set.range E.oldOutput
  exact e.surjective.range_comp E.oldOutput

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.range_oldOutput_toRetainedCoreEvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.range_oldOutput_toRetainedCoreEvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.range_oldOutput_toRetainedCoreEvent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.range_oldOutput_toRetainedCoreEvent

private theorem exists_static_family_of_event_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (E : MetricCutCapEvent P Q a s) (E' : MetricCutCapEvent P' Q' a' s')
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s)
    (hE : HEq E' E)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b) :
    ∃ (e : E'.RetainedBoundaryIndex ≃ E.RetainedBoundaryIndex)
      (S' : ∀ b : E'.RetainedBoundaryIndex, E'.PresentedStaticCap fixed D m ε b),
      (∀ b, HEq b.val (e b).val) ∧
      (∀ b, HEq (S' b).neck (S (e b)).neck) ∧
      (∀ b, (S' b).neck.scale = (S (e b)).neck.scale) ∧
      (∀ b, HEq (S' b).witness (S (e b)).witness) ∧
      (∀ b, HEq (S' b).inclusion (S (e b)).inclusion) ∧
      (∀ b, HEq (S' b).window (S (e b)).window) ∧
      HEq E'.outputMetric E.outputMetric ∧
      HEq (_root_.Set.range E'.oldOutput) (_root_.Set.range E.oldOutput) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact ⟨Equiv.refl _, S, fun _ => HEq.rfl, fun _ => HEq.rfl, fun _ => rfl,
    fun _ => HEq.rfl, fun _ => HEq.rfl, fun _ => HEq.rfl, HEq.rfl, HEq.rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_static_family_of_event_heq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_static_family_of_event_heq target :: scope.openDecls } }

private theorem exists_static_family_of_retainedEvent_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (E : MetricCutCapEvent P Q a s) (hOld : E.old = E.transition.trace.retainedCore)
    (E' : RetainedCoreEvent P' Q' a' s')
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s)
    (hE : HEq E' (E.toRetainedCoreEvent hOld))
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b) :
    ∃ (e : E'.toMetricCutCapEvent.RetainedBoundaryIndex ≃ E.RetainedBoundaryIndex)
      (S' : ∀ b : E'.toMetricCutCapEvent.RetainedBoundaryIndex,
        E'.toMetricCutCapEvent.PresentedStaticCap fixed D m ε b),
      (∀ b, HEq b.val (e b).val) ∧
      (∀ b, HEq (S' b).neck (S (e b)).neck) ∧
      (∀ b, (S' b).neck.scale = (S (e b)).neck.scale) ∧
      (∀ b, HEq (S' b).witness (S (e b)).witness) ∧
      (∀ b, HEq (S' b).inclusion (S (e b)).inclusion) ∧
      (∀ b, HEq (S' b).window (S (e b)).window) ∧
      HEq E'.outputMetric E.outputMetric ∧
      HEq (_root_.Set.range E'.toMetricCutCapEvent.oldOutput) (_root_.Set.range E.oldOutput) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact ⟨Equiv.refl _, fun b => (S b).toRetained hOld,
    fun _ => HEq.rfl, fun _ => HEq.rfl, fun _ => rfl, fun _ => HEq.rfl, fun _ => HEq.rfl,
    fun _ => HEq.rfl, HEq.rfl, heq_of_eq (E.range_oldOutput_toRetainedCoreEvent hOld)⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_static_family_of_retainedEvent_heq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_static_family_of_retainedEvent_heq target :: scope.openDecls } }

private theorem exists_window_of_stage_metric_heq
    {P Q : OrientedThreeStage.{u}} (hP : P = Q)
    (gP : P.Metric) (gQ : Q.Metric) (hg : HEq gP gQ)
    {D q : ℝ} (g : SmoothRiemannianMetric ThreeModel (standardCapWindow D))
    (J : C(standardCapWindow D, Q.Carrier))
    (hJ : _root_.Manifold.IsSmoothEmbedding ThreeModel ThreeModel ∞ J)
    (hmetric : ∀ x v w, g.inner x v w = q * gQ.inner (J x)
      (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x w)) :
    ∃ K : C(standardCapWindow D, P.Carrier), HEq K J ∧
      _root_.Manifold.IsSmoothEmbedding ThreeModel ThreeModel ∞ K ∧
      ∀ x v w, g.inner x v w = q * gP.inner (K x)
        (mfderiv ThreeModel ThreeModel K x v) (mfderiv ThreeModel ThreeModel K x w) := by
  cases hP
  cases eq_of_heq hg
  exact ⟨J, HEq.rfl, hJ, hmetric⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_window_of_stage_metric_heq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_window_of_stage_metric_heq target :: scope.openDecls } }

theorem RetainedCoreHistory.exists_window_at_appendEvent
    {P Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory P) {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {D q : ℝ} (g : SmoothRiemannianMetric ThreeModel (standardCapWindow D))
    (J : C(standardCapWindow D, Q.Carrier))
    (hJ : _root_.Manifold.IsSmoothEmbedding ThreeModel ThreeModel ∞ J)
    (hmetric : ∀ x v w, g.inner x v w = q * E.outputMetric.inner (J x)
      (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x w)) :
    let K := H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit
    ∃ J' : C(standardCapWindow D, (K.stage (Fin.last K.eventCount)).Carrier),
      HEq J' J ∧ _root_.Manifold.IsSmoothEmbedding ThreeModel ThreeModel ∞ J' ∧
      ∀ x v w, g.inner x v w = q *
        (K.initialMetric (Fin.last K.eventCount)).inner (J' x)
          (mfderiv ThreeModel ThreeModel J' x v) (mfderiv ThreeModel ThreeModel J' x w) := by
  exact exists_window_of_stage_metric_heq
    (H.appendEvent_stage_last E.incoming.lt (E.toRetainedCoreEvent hOld) hinit)
    _ E.outputMetric
    (H.appendEvent_initialMetric_last_heq E.incoming.lt (E.toRetainedCoreEvent hOld) hinit)
    g J hJ hmetric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_window_at_appendEvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_window_at_appendEvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_window_at_appendEvent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_window_at_appendEvent

theorem RetainedCoreHistory.exists_static_window_at_appendEvent
    {P Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory P) {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b) :
    let K := H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit
    ∃ J : C(standardCapWindow D, (K.stage (Fin.last K.eventCount)).Carrier),
      HEq J S.window ∧ _root_.Manifold.IsSmoothEmbedding ThreeModel ThreeModel ∞ J ∧
      ∀ x v w, S.witness.windowMetric.inner x v w = S.neck.scale *
        (K.initialMetric (Fin.last K.eventCount)).inner (J x)
          (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x w) := by
  exact H.exists_window_at_appendEvent E hOld hinit
    S.witness.windowMetric S.window S.window_smooth S.window_inner

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_static_window_at_appendEvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_static_window_at_appendEvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_static_window_at_appendEvent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_static_window_at_appendEvent

theorem RetainedCoreHistory.exists_static_cap_family_at_appendEvent
    {P Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory P) {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b) :
    let K := H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit
    let i : Fin K.eventCount := Fin.last H.eventCount
    ∃ (e : (K.toHistory.event i).RetainedBoundaryIndex ≃ E.RetainedBoundaryIndex)
      (S' : ∀ b : (K.toHistory.event i).RetainedBoundaryIndex,
        (K.toHistory.event i).PresentedStaticCap fixed D m ε b),
      HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
      (∀ b, HEq b.val (e b).val) ∧
      (∀ b, HEq (S' b).neck (S (e b)).neck) ∧
      (∀ b, (S' b).neck.scale = (S (e b)).neck.scale) ∧
      (∀ b, HEq (S' b).witness (S (e b)).witness) ∧
      (∀ b, HEq (S' b).inclusion (S (e b)).inclusion) ∧
      (∀ b, HEq (S' b).window (S (e b)).window) ∧
      HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
      HEq (_root_.Set.range (K.toHistory.event i).oldOutput) (_root_.Set.range E.oldOutput) := by
  let F := E.toRetainedCoreEvent hOld
  let K := H.appendEvent E.incoming.lt F hinit
  let i : Fin K.eventCount := Fin.last H.eventCount
  have hE : HEq (K.coreEvent i) F := by
    change HEq ((H.appendEvent E.incoming.lt F hinit).coreEvent (Fin.last H.eventCount)) F
    refine (heq_of_eq (H.appendEvent_coreEvent_last E.incoming.lt F hinit)).trans ?_
    change HEq (H.extendCoreEventLast F) F
    unfold RetainedCoreHistory.extendCoreEventLast
    have ht {P₁ Q₁ P₂ Q₂ : OrientedThreeStage.{u}} {a₁ s₁ a₂ s₂ : ℝ}
        (hP : P₁ = P₂) (hQ : Q₁ = Q₂) (ha : a₁ = a₂) (hs : s₁ = s₂)
        (T : RetainedCoreEvent P₁ Q₁ a₁ s₁) :
        HEq (RetainedCoreEvent.transport hP hQ ha hs T) T := by
      cases hP
      cases hQ
      cases ha
      cases hs
      exact HEq.rfl
    exact ht _ _ _ _ _
  obtain ⟨e, S', hlabel, hneck, hscale, hwitness, hinclusion, hwindow, _, hold⟩ :=
    exists_static_family_of_retainedEvent_heq E hOld (K.coreEvent i)
      (H.appendEvent_stage_castSucc E.incoming.lt F hinit (Fin.last H.eventCount))
      (H.appendEvent_stage_last E.incoming.lt F hinit)
      (H.appendEvent_time_castSucc E.incoming.lt F hinit (Fin.last H.eventCount))
      (H.appendEvent_time_last E.incoming.lt F hinit) hE S
  exact ⟨e, S', hE, hlabel, hneck, hscale, hwitness, hinclusion, hwindow,
    H.appendEvent_initialMetric_last_heq E.incoming.lt F hinit, hold⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_static_cap_family_at_appendEvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_static_cap_family_at_appendEvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_static_cap_family_at_appendEvent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_static_cap_family_at_appendEvent

theorem RetainedCoreHistory.exists_static_cap_family_before_appendEvent
    {P Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory P) {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (i : Fin H.eventCount)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ b : (H.toHistory.event i).RetainedBoundaryIndex,
      (H.toHistory.event i).PresentedStaticCap fixed D m ε b) :
    let K := H.appendEvent hs E hinit
    ∃ (e : (K.toHistory.event i.castSucc).RetainedBoundaryIndex ≃
        (H.toHistory.event i).RetainedBoundaryIndex)
      (S' : ∀ b : (K.toHistory.event i.castSucc).RetainedBoundaryIndex,
        (K.toHistory.event i.castSucc).PresentedStaticCap fixed D m ε b),
      HEq (K.toHistory.event i.castSucc) (H.toHistory.event i) ∧
      (∀ b, HEq b.val (e b).val) ∧
      (∀ b, HEq (S' b).neck (S (e b)).neck) ∧
      (∀ b, (S' b).neck.scale = (S (e b)).neck.scale) ∧
      (∀ b, HEq (S' b).witness (S (e b)).witness) ∧
      (∀ b, HEq (S' b).inclusion (S (e b)).inclusion) ∧
      (∀ b, HEq (S' b).window (S (e b)).window) ∧
      HEq (K.toHistory.event i.castSucc).outputMetric (H.toHistory.event i).outputMetric ∧
      HEq (_root_.Set.range (K.toHistory.event i.castSucc).oldOutput)
        (_root_.Set.range (H.toHistory.event i).oldOutput) := by
  let K := H.appendEvent hs E hinit
  have hE : HEq (K.toHistory.event i.castSucc) (H.toHistory.event i) := by
    change HEq ((H.extendCoreEventFamily E i.castSucc).toMetricCutCapEvent) (H.toHistory.event i)
    rw [H.extendCoreEventFamily_toMetricCutCapEvent]
    exact H.toHistory.appendEvent_event_castSucc_heq hs E.toMetricCutCapEvent hinit i
  obtain ⟨e, S', hrest⟩ := exists_static_family_of_event_heq (H.toHistory.event i)
    (K.toHistory.event i.castSucc)
    (H.appendEvent_stage_castSucc hs E hinit i.castSucc)
    (H.appendEvent_stage_castSucc hs E hinit i.succ)
    (H.appendEvent_time_castSucc hs E hinit i.castSucc)
    (H.appendEvent_time_castSucc hs E hinit i.succ) hE S
  exact ⟨e, S', hE, hrest⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_static_cap_family_before_appendEvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_static_cap_family_before_appendEvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_static_cap_family_before_appendEvent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_static_cap_family_before_appendEvent


theorem RetainedCoreHistory.exists_static_cap_families_at_appendEvent
    {P Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory P) {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ i : Fin H.eventCount, ∀ b : (H.toHistory.event i).RetainedBoundaryIndex,
      (H.toHistory.event i).PresentedStaticCap fixed D m ε b)
    (T : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b) :
    let K := H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit
    ∃ S' : ∀ i : Fin K.eventCount, ∀ b : (K.toHistory.event i).RetainedBoundaryIndex,
        (K.toHistory.event i).PresentedStaticCap fixed D m ε b,
      (∀ i : Fin H.eventCount,
        ∃ e : (K.toHistory.event i.castSucc).RetainedBoundaryIndex ≃
            (H.toHistory.event i).RetainedBoundaryIndex,
          HEq (K.toHistory.event i.castSucc) (H.toHistory.event i) ∧
          (∀ b, HEq b.val (e b).val) ∧
          (∀ b, HEq (S' i.castSucc b).neck (S i (e b)).neck) ∧
          (∀ b, (S' i.castSucc b).neck.scale = (S i (e b)).neck.scale) ∧
          (∀ b, HEq (S' i.castSucc b).witness (S i (e b)).witness) ∧
          (∀ b, HEq (S' i.castSucc b).inclusion (S i (e b)).inclusion) ∧
          (∀ b, HEq (S' i.castSucc b).window (S i (e b)).window) ∧
          HEq (K.toHistory.event i.castSucc).outputMetric (H.toHistory.event i).outputMetric ∧
          HEq (_root_.Set.range (K.toHistory.event i.castSucc).oldOutput)
            (_root_.Set.range (H.toHistory.event i).oldOutput)) ∧
      ∃ e : (K.toHistory.event (Fin.last H.eventCount)).RetainedBoundaryIndex ≃ E.RetainedBoundaryIndex,
        HEq (K.coreEvent (Fin.last H.eventCount)) (E.toRetainedCoreEvent hOld) ∧
        (∀ b, HEq b.val (e b).val) ∧
        (∀ b, HEq (S' (Fin.last H.eventCount) b).neck (T (e b)).neck) ∧
        (∀ b, (S' (Fin.last H.eventCount) b).neck.scale = (T (e b)).neck.scale) ∧
        (∀ b, HEq (S' (Fin.last H.eventCount) b).witness (T (e b)).witness) ∧
        (∀ b, HEq (S' (Fin.last H.eventCount) b).inclusion (T (e b)).inclusion) ∧
        (∀ b, HEq (S' (Fin.last H.eventCount) b).window (T (e b)).window) ∧
        HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
        HEq (_root_.Set.range (K.toHistory.event (Fin.last H.eventCount)).oldOutput) (_root_.Set.range E.oldOutput) := by
  classical
  let F := E.toRetainedCoreEvent hOld
  let K := H.appendEvent E.incoming.lt F hinit
  obtain ⟨eNew, T', hnew⟩ := H.exists_static_cap_family_at_appendEvent E hOld hinit T
  have hex (i : Fin H.eventCount) := H.exists_static_cap_family_before_appendEvent
    E.incoming.lt F hinit i (S i)
  choose eOld S₀ hold using hex
  let S' : ∀ i : Fin (H.eventCount + 1), ∀ b : (K.toHistory.event i).RetainedBoundaryIndex,
      (K.toHistory.event i).PresentedStaticCap fixed D m ε b := Fin.lastCases T' S₀
  have hOldFamily (i : Fin H.eventCount) : S' i.castSucc = S₀ i :=
    Fin.lastCases_castSucc i
  have hNewFamily : S' (Fin.last H.eventCount) = T' :=
    Fin.lastCases_last
  refine ⟨S', ?_, ?_⟩
  · intro i
    refine ⟨eOld i, ?_⟩
    rw [hOldFamily]
    exact hold i
  · refine ⟨eNew, ?_⟩
    rw [hNewFamily]
    exact hnew

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_static_cap_families_at_appendEvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_static_cap_families_at_appendEvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_static_cap_families_at_appendEvent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_static_cap_families_at_appendEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
