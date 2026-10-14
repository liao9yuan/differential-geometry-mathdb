import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckRecenteringFields

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem mem_neckBuffer_of_pos_of_lt_one {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1)
    (x : TubeDomain) : (x.1, x.2.1) ∈ neckBuffer δ := by
  have hinv : 1 < δ⁻¹ := by
    exact (one_lt_inv₀ h0).mpr h1
  obtain ⟨hlo, hhi⟩ := x.2.2
  exact ⟨by linarith, by linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.mem_neckBuffer_of_pos_of_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.mem_neckBuffer_of_pos_of_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.mem_neckBuffer_of_pos_of_lt_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.mem_neckBuffer_of_pos_of_lt_one

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}

local instance frontierTerminalSecondCountable (H : ObservedHistory.{u}) (i : Fin H.eventCount) :
    SecondCountableTopology (H.event i).incoming.terminalRegularOpen := by
  let : SecondCountableTopology (H.stage i.castSucc).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (H.stage i.castSucc).Carrier
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.frontierTerminalSecondCountable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.frontierTerminalSecondCountable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.frontierTerminalSecondCountable ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.frontierTerminalSecondCountable

local instance frontierTerminalLocallyCompact (H : ObservedHistory.{u}) (i : Fin H.eventCount) :
    LocallyCompactSpace (H.event i).incoming.terminalRegularOpen :=
  ChartedSpace.locallyCompactSpace ThreeSpace (H.event i).incoming.terminalRegularOpen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.frontierTerminalLocallyCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.frontierTerminalLocallyCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.frontierTerminalLocallyCompact ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.frontierTerminalLocallyCompact

theorem tube_in_buffer_of_normalizedNeck
    {delta : (H.event i).transition.trace.tubes.Index → ℝ}
    {order : (H.event i).transition.trace.tubes.Index → ℕ}
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (delta α) (order α)) :
    ∀ α, ∀ x : TubeDomain, (x.1, x.2.1) ∈ neckBuffer (delta α) :=
  fun α x => mem_neckBuffer_of_pos_of_lt_one (neck α).delta_pos (neck α).delta_lt_one x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tube_in_buffer_of_normalizedNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tube_in_buffer_of_normalizedNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tube_in_buffer_of_normalizedNeck ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tube_in_buffer_of_normalizedNeck

theorem delta_pos_of_normalizedNeck
    {delta : (H.event i).transition.trace.tubes.Index → ℝ}
    {order : (H.event i).transition.trace.tubes.Index → ℕ}
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (delta α) (order α)) :
    ∀ α, 0 < delta α :=
  fun α => (neck α).delta_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.delta_pos_of_normalizedNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.delta_pos_of_normalizedNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.delta_pos_of_normalizedNeck ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.delta_pos_of_normalizedNeck

theorem nominal_pos_of_incomingBackwardNeck
    {nominalRadius : Nonempty (H.event i).transition.trace.tubes.Index → ℝ}
    {delta : (H.event i).transition.trace.tubes.Index → ℝ}
    {order : (H.event i).transition.trace.tubes.Index → ℕ}
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (delta α) (order α))
    (backward : ∀ α, IncomingBackwardNeck H i (neck α) (nominalRadius ⟨α⟩)) :
    ∀ h, 0 < nominalRadius h := by
  intro h
  cases h with
  | intro α => exact (backward α).radius_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nominal_pos_of_incomingBackwardNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nominal_pos_of_incomingBackwardNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nominal_pos_of_incomingBackwardNeck ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nominal_pos_of_incomingBackwardNeck

theorem retained_terminal_of_old_eq_retained {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) (h : E.old = E.transition.trace.retainedCore) :
    ∀ x ∈ E.transition.trace.retainedCore, x.1 ∈ E.incoming.terminalRegularRegion := by
  intro x hx
  rw [← h] at hx
  rw [← E.oldTerminal_eq ⟨x, hx⟩]
  exact (E.oldTerminal ⟨x, hx⟩).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.retained_terminal_of_old_eq_retained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.retained_terminal_of_old_eq_retained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.retained_terminal_of_old_eq_retained ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.retained_terminal_of_old_eq_retained

theorem recenter_scale_of_presentedStaticCap
    (static : ∀ b : (H.event i).RetainedBoundaryIndex,
      PresentedStaticCap H i parameters.fixed parameters.modelRadius parameters.modelOrder
        parameters.modelAccuracy b) :
    ∀ b : (H.event i).RetainedBoundaryIndex,
      (static b).neck.scale =
        metricScalarAt (H.event i).terminal.metric ((static b).neck.center) :=
  fun b => (static b).neck.scale_scalar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.recenter_scale_of_presentedStaticCap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.recenter_scale_of_presentedStaticCap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.recenter_scale_of_presentedStaticCap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.recenter_scale_of_presentedStaticCap

theorem no_cuts_discard_iff_retainedCore_ne_univ
    [IsEmpty (H.event i).transition.trace.tubes.Index] :
    (∃ x : (H.event i).transition.trace.tubes.core,
        x ∉ (H.event i).transition.trace.retainedCore) ↔
      (H.event i).transition.trace.retainedCore ≠ Set.univ :=
  (Set.ne_univ_iff_exists_notMem _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.no_cuts_discard_iff_retainedCore_ne_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.no_cuts_discard_iff_retainedCore_ne_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.no_cuts_discard_iff_retainedCore_ne_univ ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.no_cuts_discard_iff_retainedCore_ne_univ

def HasRecenterConstants (q : CutoffParameters) : Prop :=
  ∃ (c : ℝ) (δ₀ : ℝ), 4 ≤ c ∧ 0 < δ₀ ∧ q.recenterConstant = c ∧
    (∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
      (g : SmoothRiemannianMetric ThreeModel M) (k : ℕ), 2 ≤ k →
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ N : NormalizedNeck g δ k, ∀ side : Bool,
        Nonempty (NeckRecenteringFields g k δ c N side)) ∧
    ∀ t, 0 ≤ t → q.delta t ≤ δ₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasRecenterConstants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasRecenterConstants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasRecenterConstants ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasRecenterConstants

theorem exists_recenterConstants :
    ∃ (c : ℝ) (δ₀ : ℝ), 4 ≤ c ∧ 0 < δ₀ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
        (g : SmoothRiemannianMetric ThreeModel M) (k : ℕ), 2 ≤ k →
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ N : NormalizedNeck g δ k, ∀ side : Bool,
          Nonempty (NeckRecenteringFields g k δ c N side) := by
  obtain ⟨c, hc, δ₀, hδ₀, h⟩ := exists_neckRecenteringFields
  refine ⟨c, δ₀, hc, hδ₀, ?_⟩
  intro M _ _ _ _ _ g k hk δ hδ hδle N side
  exact h M g k hk δ hδ hδle N side

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_recenterConstants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_recenterConstants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_recenterConstants ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_recenterConstants

theorem exists_cutoffParameters_hasRecenterConstants (q₀ : CutoffParameters) :
    ∃ q : CutoffParameters, HasRecenterConstants q := by
  obtain ⟨c, δ₀, hc, hδ₀, huniv⟩ := exists_recenterConstants
  have hhalf : 0 < δ₀ / 2 := by linarith
  refine ⟨{ delta := fun _ => _root_.Min.min (δ₀ / 2) (1 / 2)
            neckRadius := fun _ => 1
            protectedRadius := fun _ => 1
            delta_pos := fun _ _ => lt_min hhalf (by norm_num)
            delta_lt_one := fun _ _ => lt_of_le_of_lt (min_le_right _ _) (by norm_num)
            neckRadius_pos := fun _ _ => one_pos
            protectedRadius_pos := fun _ _ => one_pos
            fixed := q₀.fixed
            modelRadius := q₀.modelRadius
            modelRadius_pos := q₀.modelRadius_pos
            modelOrder := q₀.modelOrder
            modelAccuracy := q₀.modelAccuracy
            modelAccuracy_pos := q₀.modelAccuracy_pos
            recenterConstant := c
            recenterConstant_ge_four := hc },
    c, δ₀, hc, hδ₀, rfl, huniv, fun _ _ => (min_le_left _ _).trans (by linarith)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_cutoffParameters_hasRecenterConstants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_cutoffParameters_hasRecenterConstants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_cutoffParameters_hasRecenterConstants ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_cutoffParameters_hasRecenterConstants

theorem recenter_fields_of_recenterConstants (h : HasRecenterConstants.{u} parameters)
    {delta : (H.event i).transition.trace.tubes.Index → ℝ}
    {order : (H.event i).transition.trace.tubes.Index → ℕ}
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (delta α) (order α))
    (horder : ∀ α, 2 ≤ order α)
    (hdelta : ∀ α, delta α ≤ parameters.delta (H.time i.succ)) :
    ∀ b : (H.event i).RetainedBoundaryIndex,
      ∃ hbuffer : ∀ x : neckBuffer (parameters.recenterConstant * delta b.1.1),
          (x.1.1, (if b.1.2 then (1 : ℝ) else -1) * (1 + x.1.2)) ∈ neckBuffer (delta b.1.1),
      ∃ N' : NormalizedNeck (H.event i).terminal.metric
          (parameters.recenterConstant * delta b.1.1) (order b.1.1),
        N'.sphereMark = (neck b.1.1).sphereMark ∧
        (∀ x : neckBuffer (parameters.recenterConstant * delta b.1.1),
          N'.chart x = (neck b.1.1).chart
            ⟨(x.1.1, (if b.1.2 then (1 : ℝ) else -1) * (1 + x.1.2)), hbuffer x⟩) ∧
        |N'.scale / (neck b.1.1).scale - 1| ≤ parameters.recenterConstant * delta b.1.1 := by
  obtain ⟨c, δ₀, _hc, _hδ₀, hconst, huniv, hsmall⟩ := h
  intro b
  have htime : 0 ≤ H.time i.succ := by
    simpa [H.time_zero] using H.time_strictMono.monotone (Fin.zero_le i.succ)
  have hle : delta b.1.1 ≤ δ₀ := (hdelta b.1.1).trans (hsmall (H.time i.succ) htime)
  obtain ⟨R⟩ :=
    huniv (M := (H.event i).incoming.terminalRegularOpen) (g := (H.event i).terminal.metric)
      (k := order b.1.1) (horder b.1.1) (delta b.1.1) (neck b.1.1).delta_pos hle
      (neck b.1.1) b.1.2
  obtain ⟨hbuffer, N', hmark, hchart, _hcenter, hscale⟩ := R
  rw [hconst]
  exact ⟨hbuffer, N', hmark, hchart, hscale⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.recenter_fields_of_recenterConstants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.recenter_fields_of_recenterConstants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.recenter_fields_of_recenterConstants ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.recenter_fields_of_recenterConstants

structure GeometricCutoffFrontier (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (parameters : CutoffParameters) where
  singular : (H.event i).incoming.SingularEndpoint
  nominalRadius : Nonempty (H.event i).transition.trace.tubes.Index → ℝ
  nominal_small : ∀ h, nominalRadius h <
    (parameters.delta (H.time i.succ))^2 * parameters.neckRadius (H.time i.succ)
  nominal_time : ∀ h, (nominalRadius h)^2 ≤ H.time i.succ
  delta : (H.event i).transition.trace.tubes.Index → ℝ
  delta_le : ∀ α, delta α ≤ parameters.delta (H.time i.succ)
  order : (H.event i).transition.trace.tubes.Index → ℕ
  order_lower : ∀ α, _root_.Max.max (parameters.modelOrder + 6)
    (2 * ⌊(delta α)⁻¹⌋₊ + 4) ≤ order α
  neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (delta α) (order α)
  scale_eq : ∀ α, (neck α).scale = ((nominalRadius ⟨α⟩) ^ 2)⁻¹
  buffer_disjoint : Pairwise fun α β =>
    Disjoint (Set.range (neck α).chart) (Set.range (neck β).chart)
  tube_eq : ∀ α, ∀ x : TubeDomain, ∀ hx : (x.1, x.2.1) ∈ neckBuffer (delta α),
    (H.event i).transition.trace.tubes.tube α x = ((neck α).chart ⟨(x.1, x.2.1), hx⟩).1
  backward : ∀ α, IncomingBackwardNeck H i (neck α) (nominalRadius ⟨α⟩)
  protected_interior : ∀ x : (H.event i).incoming.terminalRegularOpen,
    metricScalarAt (H.event i).terminal.metric x ≤
      ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
    x.1 ∈ interior (Subtype.val '' (H.event i).transition.trace.retainedCore)
  retained_meets_protected : ∀ c : ConnectedComponents (H.event i).transition.trace.tubes.core,
    (∃ x : (H.event i).transition.trace.tubes.core,
      ConnectedComponents.mk x = c ∧ x ∈ (H.event i).transition.trace.retainedCore) →
    ∃ x : (H.event i).incoming.terminalRegularOpen,
      ∃ hx : x.1 ∈ (H.event i).transition.trace.tubes.core,
        ConnectedComponents.mk ⟨x.1, hx⟩ = c ∧
          metricScalarAt (H.event i).terminal.metric x ≤
            ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹
  one_retained_side : ∀ α,
    (H.event i).RetainedBoundary (α, _root_.Bool.true) ↔ ¬ (H.event i).RetainedBoundary (α, _root_.Bool.false)
  no_cuts_discard : IsEmpty (H.event i).transition.trace.tubes.Index →
    ∃ x : (H.event i).transition.trace.tubes.core, x ∉ (H.event i).transition.trace.retainedCore
  static : ∀ b : (H.event i).RetainedBoundaryIndex,
    PresentedStaticCap H i parameters.fixed parameters.modelRadius parameters.modelOrder
      parameters.modelAccuracy b
  recenter_mark : ∀ b : (H.event i).RetainedBoundaryIndex,
    (static b).neck.sphereMark = (neck b.1.1).sphereMark
  recenter_delta : ∀ b : (H.event i).RetainedBoundaryIndex,
    (static b).delta = parameters.recenterConstant * delta b.1.1
  recenter_scale_comparison : ∀ b : (H.event i).RetainedBoundaryIndex,
    |(static b).neck.scale / (neck b.1.1).scale - 1| ≤
      parameters.recenterConstant * delta b.1.1
  recenter_chart : ∀ b : (H.event i).RetainedBoundaryIndex,
    ∀ x : neckBuffer (static b).delta,
    ∀ hx : (x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)) ∈ neckBuffer (delta b.1.1),
      (static b).neck.chart x = (neck b.1.1).chart
        ⟨(x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)), hx⟩
  recenter_in_buffer : ∀ b : (H.event i).RetainedBoundaryIndex,
    ∀ x : neckBuffer (static b).delta,
      (x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)) ∈ neckBuffer (delta b.1.1)
  old_eq_retained : (H.event i).old = (H.event i).transition.trace.retainedCore
  curvature_preserving : ∀ a : ℝ, 0 < a →
    (∀ x : (H.event i).incoming.terminalRegularOpen,
      InFixedHamiltonIveyRegion (H.event i).terminal.metric a x) →
    ∀ x : (H.stage i.succ).Carrier, InFixedHamiltonIveyRegion (H.event i).outputMetric a x
  scalar_preserving : ∀ L : ℝ, L ≤ 0 →
    (∀ x : (H.event i).incoming.terminalRegularOpen,
      L ≤ metricScalarAt (H.event i).terminal.metric x) →
    ∀ x : (H.stage i.succ).Carrier, L ≤ metricScalarAt (H.event i).outputMetric x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffFrontier

def GeometricCutoffRecord.ofFrontier
    (F : GeometricCutoffFrontier H i parameters) : GeometricCutoffRecord H i parameters where
  singular := F.singular
  nominalRadius := F.nominalRadius
  nominal_pos := nominal_pos_of_incomingBackwardNeck (nominalRadius := F.nominalRadius)
    (delta := F.delta) (order := F.order) F.neck F.backward
  nominal_small := F.nominal_small
  nominal_time := F.nominal_time
  delta := F.delta
  delta_pos := delta_pos_of_normalizedNeck F.neck
  delta_le := F.delta_le
  order := F.order
  order_lower := F.order_lower
  neck := F.neck
  scale_eq := F.scale_eq
  buffer_disjoint := F.buffer_disjoint
  tube_eq := F.tube_eq
  tube_in_buffer := tube_in_buffer_of_normalizedNeck F.neck
  backward := F.backward
  retained_terminal := retained_terminal_of_old_eq_retained (H.event i) F.old_eq_retained
  protected_interior := F.protected_interior
  retained_meets_protected := F.retained_meets_protected
  one_retained_side := F.one_retained_side
  no_cuts_discard := F.no_cuts_discard
  static := F.static
  recenter_scale := recenter_scale_of_presentedStaticCap F.static
  recenter_mark := F.recenter_mark
  recenter_delta := F.recenter_delta
  recenter_scale_comparison := F.recenter_scale_comparison
  recenter_chart := F.recenter_chart
  recenter_in_buffer := F.recenter_in_buffer
  old_eq_retained := F.old_eq_retained
  curvature_preserving := F.curvature_preserving
  scalar_preserving := F.scalar_preserving

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ofFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ofFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ofFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ofFrontier

def GeometricCutoffRecord.toFrontier
    (R : GeometricCutoffRecord H i parameters) : GeometricCutoffFrontier H i parameters where
  singular := R.singular
  nominalRadius := R.nominalRadius
  nominal_small := R.nominal_small
  nominal_time := R.nominal_time
  delta := R.delta
  delta_le := R.delta_le
  order := R.order
  order_lower := R.order_lower
  neck := R.neck
  scale_eq := R.scale_eq
  buffer_disjoint := R.buffer_disjoint
  tube_eq := R.tube_eq
  backward := R.backward
  protected_interior := R.protected_interior
  retained_meets_protected := R.retained_meets_protected
  one_retained_side := R.one_retained_side
  no_cuts_discard := R.no_cuts_discard
  static := R.static
  recenter_mark := R.recenter_mark
  recenter_delta := R.recenter_delta
  recenter_scale_comparison := R.recenter_scale_comparison
  recenter_chart := R.recenter_chart
  recenter_in_buffer := R.recenter_in_buffer
  old_eq_retained := R.old_eq_retained
  curvature_preserving := R.curvature_preserving
  scalar_preserving := R.scalar_preserving

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.toFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.toFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.toFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.toFrontier

theorem nonempty_geometricCutoffFrontier_iff_nonempty_record :
    Nonempty (GeometricCutoffFrontier H i parameters) ↔
      Nonempty (GeometricCutoffRecord H i parameters) :=
  ⟨fun ⟨F⟩ => ⟨GeometricCutoffRecord.ofFrontier F⟩, fun ⟨R⟩ => ⟨R.toFrontier⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_geometricCutoffFrontier_iff_nonempty_record then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_geometricCutoffFrontier_iff_nonempty_record"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_geometricCutoffFrontier_iff_nonempty_record ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_geometricCutoffFrontier_iff_nonempty_record

theorem pairwise_disjoint_range_of_isEmpty_index [IsEmpty (H.event i).transition.trace.tubes.Index]
    {Z Y : Type*} (f : (H.event i).transition.trace.tubes.Index → Z → Y) :
    _root_.Pairwise fun a b => Disjoint (Set.range (f a)) (Set.range (f b)) := by
  intro a
  exact isEmptyElim a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pairwise_disjoint_range_of_isEmpty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pairwise_disjoint_range_of_isEmpty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pairwise_disjoint_range_of_isEmpty_index ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pairwise_disjoint_range_of_isEmpty_index

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
