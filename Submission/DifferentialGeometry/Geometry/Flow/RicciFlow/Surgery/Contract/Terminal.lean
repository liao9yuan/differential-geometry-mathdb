import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricEvent
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedOrientedStage
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryExtension
import Submission.DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollar
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapReconstruction
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandard
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscarded
import Submission.DifferentialGeometry.Topology.ThreeManifold.StandardFactors
import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Function _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure OneStepIncoming where
  stage : OrientedThreeStage.{u}
  startTime : ℝ
  endTime : ℝ
  startTime_nonneg : 0 ≤ startTime
  startTime_lt_endTime : startTime < endTime
  slab : stage.IncomingSlab startTime endTime
  terminal : slab.TerminalLimitMetric
  singular : slab.SingularEndpoint
  parameters : CutoffParameters

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OneStepIncoming then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OneStepIncoming"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OneStepIncoming ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OneStepIncoming

namespace OneStepIncoming

def ofRecord {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) : OneStepIncoming.{u} where
  stage := H.stage i.castSucc
  startTime := H.time i.castSucc
  endTime := H.time i.succ
  startTime_nonneg := by
    simpa [H.time_zero] using H.time_strictMono.le_iff_le.mpr (Fin.zero_le i.castSucc)
  startTime_lt_endTime := H.time_strictMono i.castSucc_lt_succ
  slab := (H.event i).incoming
  terminal := (H.event i).terminal
  singular := R.singular
  parameters := p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OneStepIncoming.ofRecord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OneStepIncoming.ofRecord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OneStepIncoming.ofRecord ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OneStepIncoming.ofRecord

end OneStepIncoming

abbrev HalfNeckCylinder := {p : NeckCylinder // 0 ≤ p.2}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HalfNeckCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HalfNeckCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HalfNeckCylinder ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HalfNeckCylinder

structure TerminalCorePresentation (D : OneStepIncoming.{u}) (ε Λ : ℝ) where
  epsilon_pos : 0 < ε
  Lambda_ge_one : 1 ≤ Λ
  coreRadius : ℝ
  coreRadius_pos : 0 < coreRadius
  coreRadius_eq : coreRadius =
    D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime
  component : Set (ConnectedComponents ↥D.slab.terminalRegularOpen)
  component_finite : component.Finite
  core : ConnectedComponents ↥D.slab.terminalRegularOpen →
    Set ↥D.slab.terminalRegularOpen
  core_isCompact : ∀ c ∈ component, IsCompact (core c)
  core_isConnected : ∀ c ∈ component, IsConnected (core c)
  core_empty : ∀ c, c ∉ component → core c = ∅
  coreCharts : ∀ c, c ∈ component → ChartedSpace (EuclideanHalfSpace 3) (core c)
  core_smooth : ∀ c (hc : c ∈ component),
    letI := coreCharts c hc
    IsManifold (𝓡∂ 3) ∞ (core c)
  core_induced : ∀ c (hc : c ∈ component),
    letI := coreCharts c hc
    _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
      (Subtype.val : core c → ↥D.slab.terminalRegularOpen)
  core_interior_eq : ∀ c (hc : c ∈ component),
    letI := coreCharts c hc
    (Subtype.val : core c → ↥D.slab.terminalRegularOpen) ''
      (𝓡∂ 3).interior (core c) = interior (core c)
  core_boundary_eq : ∀ c (hc : c ∈ component),
    letI := coreCharts c hc
    (Subtype.val : core c → ↥D.slab.terminalRegularOpen) ''
      (𝓡∂ 3).boundary (core c) = frontier (core c)
  component_iff_meets_low : ∀ c : ConnectedComponents ↥D.slab.terminalRegularOpen,
    c ∈ component ↔ ∃ x : ↥D.slab.terminalRegularOpen, ConnectedComponents.mk x = c ∧
      metricScalarAt D.terminal.metric x ≤ (coreRadius ^ 2)⁻¹
  low_mem_interior_core : ∀ c ∈ component, ∀ x : ↥D.slab.terminalRegularOpen,
    ConnectedComponents.mk x = c →
    metricScalarAt D.terminal.metric x ≤ (coreRadius ^ 2)⁻¹ →
      x ∈ interior (core c)
  hornIndex : ConnectedComponents ↥D.slab.terminalRegularOpen → Type u
  hornIndex_finite : ∀ c, Finite (hornIndex c)
  hornIndex_empty : ∀ c, c ∉ component → IsEmpty (hornIndex c)
  horn : ∀ c, hornIndex c → NeckCylinder → ↥D.slab.terminalRegularOpen
  horn_smooth : ∀ c e, ContMDiffOn NeckCylinderModel ThreeModel ∞ (horn c e)
    (Set.univ ×ˢ Set.Ici (0 : ℝ))
  horn_interior_embedding : ∀ c e,
    let U : TopologicalSpace.Opens NeckCylinder :=
      ⟨Set.univ ×ˢ Set.Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
    _root_.Manifold.IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ (fun p : U => horn c e p)
  horn_injOn : ∀ c e, Set.InjOn (horn c e) (Set.univ ×ˢ Set.Ici (0 : ℝ))
  horn_proper : ∀ c e, IsProperMap fun p : HalfNeckCylinder => horn c e p.1
  horn_range_disjoint : ∀ c e e', e ≠ e' →
    Disjoint (Set.range fun p : HalfNeckCylinder => horn c e p.1)
      (Set.range fun p : HalfNeckCylinder => horn c e' p.1)
  horn_meets_core : ∀ c e,
    (Set.range fun p : HalfNeckCylinder => horn c e p.1) ∩ core c =
      Set.range fun y : Sphere 2 => horn c e (y, 0)
  horn_base_covers_boundary : ∀ c ∈ component,
    frontier (core c) = ⋃ e : hornIndex c, Set.range fun y : Sphere 2 => horn c e (y, 0)
  hornCollar : ∀ c (e : hornIndex c),
    SmoothTwoSidedCollar (𝓡 2) ThreeModel (fun y : Sphere 2 => horn c e (y, 0))
  horn_collar_core_side : ∀ c e (p : Sphere 2 × symmetricOpenInterval (hornCollar c e).radius),
    (hornCollar c e).toFun p ∈ core c ↔ (p.2 : ℝ) ≤ 0
  horn_collar_eq : ∀ c e (p : Sphere 2 × symmetricOpenInterval (hornCollar c e).radius),
    0 ≤ (p.2 : ℝ) → (hornCollar c e).toFun p = horn c e (p.1, p.2)
  horn_covers_component : ∀ c ∈ component,
    {x : ↥D.slab.terminalRegularOpen | ConnectedComponents.mk x = c} =
      core c ∪ ⋃ e : hornIndex c, Set.range fun p : HalfNeckCylinder => horn c e p.1
  horn_scalar_large : ∀ c e y u, 0 ≤ u →
    (coreRadius ^ 2)⁻¹ < metricScalarAt D.terminal.metric (horn c e (y, u))
  horn_base_scalar : ∀ c e y,
    metricScalarAt D.terminal.metric (horn c e (y, 0)) ≤ Λ * (coreRadius ^ 2)⁻¹
  horn_scalar_diverges : ∀ (c : ConnectedComponents ↥D.slab.terminalRegularOpen)
    (e : hornIndex c) (L : ℝ), ∃ u_L : ℝ, ∀ y u, u_L ≤ u →
    L < metricScalarAt D.terminal.metric (horn c e (y, u))
  horn_spatial_neck : ∀ (c : ConnectedComponents ↥D.slab.terminalRegularOpen)
    (e : hornIndex c) (x : ↥D.slab.terminalRegularOpen),
    x ∈ interior (Set.range fun p : HalfNeckCylinder => horn c e p.1) →
    ∃ (δ : ℝ) (k : ℕ) (neck : NormalizedNeck D.terminal.metric δ k),
      neck.center = x ∧ δ ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

namespace TerminalCorePresentation

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

theorem core_subset_component (c : ConnectedComponents ↥D.slab.terminalRegularOpen)
    (hc : c ∈ P.component) :
    P.core c ⊆ {x | ConnectedComponents.mk x = c} := by
  intro x hx
  have h : x ∈ P.core c ∪ ⋃ e : P.hornIndex c,
      Set.range fun p : HalfNeckCylinder => P.horn c e p.1 := Or.inl hx
  rw [← P.horn_covers_component c hc] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.core_subset_component then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.core_subset_component"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.core_subset_component ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.core_subset_component

theorem horn_base_mem_core (c : ConnectedComponents ↥D.slab.terminalRegularOpen)
    (e : P.hornIndex c) (y : Sphere 2) : P.horn c e (y, 0) ∈ P.core c := by
  have h : P.horn c e (y, 0) ∈
      (Set.range fun p : HalfNeckCylinder => P.horn c e p.1) ∩ P.core c := by
    rw [P.horn_meets_core]
    exact ⟨y, rfl⟩
  exact h.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.horn_base_mem_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.horn_base_mem_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.horn_base_mem_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.horn_base_mem_core

theorem horn_pos_notMem_core (c : ConnectedComponents ↥D.slab.terminalRegularOpen)
    (e : P.hornIndex c) (y : Sphere 2) {t : ℝ} (ht : 0 < t) :
    P.horn c e (y, t) ∉ P.core c := by
  intro hx
  have h : P.horn c e (y, t) ∈
      (Set.range fun p : HalfNeckCylinder => P.horn c e p.1) ∩ P.core c :=
    ⟨⟨⟨(y, t), ht.le⟩, rfl⟩, hx⟩
  rw [P.horn_meets_core] at h
  obtain ⟨z, hz⟩ := h
  have hzmem : (z, (0 : ℝ)) ∈ Set.univ ×ˢ Set.Ici (0 : ℝ) :=
    ⟨Set.mem_univ _, show (0 : ℝ) ≤ 0 from le_rfl⟩
  have hymem : (y, t) ∈ Set.univ ×ˢ Set.Ici (0 : ℝ) := ⟨Set.mem_univ _, ht.le⟩
  have he := P.horn_injOn c e hzmem hymem hz
  exact (ne_of_gt ht) (congrArg Prod.snd he).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.horn_pos_notMem_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.horn_pos_notMem_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.horn_pos_notMem_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.horn_pos_notMem_core

theorem frontier_scalar_le (c : ConnectedComponents ↥D.slab.terminalRegularOpen)
    (hc : c ∈ P.component) {x : ↥D.slab.terminalRegularOpen}
    (hx : x ∈ frontier (P.core c)) :
    metricScalarAt D.terminal.metric x ≤ Λ * (P.coreRadius ^ 2)⁻¹ := by
  rw [P.horn_base_covers_boundary c hc] at hx
  obtain ⟨e, y, rfl⟩ := Set.mem_iUnion.mp hx
  exact P.horn_base_scalar c e y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.frontier_scalar_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.frontier_scalar_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.frontier_scalar_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.frontier_scalar_le

theorem nonempty_hornIndex_of_not_isCompact_component
    (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (hc : c ∈ P.component)
    (h : ¬ IsCompact {x : ↥D.slab.terminalRegularOpen | ConnectedComponents.mk x = c}) :
    Nonempty (P.hornIndex c) := by
  by_contra he
  let : IsEmpty (P.hornIndex c) := not_nonempty_iff.mp he
  apply h
  rw [P.horn_covers_component c hc, Set.iUnion_of_empty, Set.union_empty]
  exact P.core_isCompact c hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.nonempty_hornIndex_of_not_isCompact_component then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.nonempty_hornIndex_of_not_isCompact_component"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.nonempty_hornIndex_of_not_isCompact_component ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.nonempty_hornIndex_of_not_isCompact_component

end TerminalCorePresentation

structure TerminalCorePresentationInput (τ ε : ℝ) where
  tau_pos : 0 < τ
  epsilon_pos : 0 < ε
  epsilon_lt_one : ε < 1
  lambda : ℝ
  one_le_lambda : 1 ≤ lambda
  presentation : ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
    Nonempty (TerminalCorePresentation D ε lambda)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentationInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentationInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentationInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentationInput

structure AdaptedHistoricalNeck (D : OneStepIncoming.{u})
    (horn : NeckCylinder → ↥D.slab.terminalRegularOpen) (d h : ℝ) (k : ℕ) where
  d_pos : 0 < d
  d_lt_quarter : d < 1 / 4
  h_pos : 0 < h
  order_lower : 2 * ⌊d⁻¹⌋₊ + 4 ≤ k
  depth_ge : D.startTime ≤ D.endTime - 2 * h ^ 2
  chart : NeckCylinder → ↥D.slab.terminalRegularOpen
  chart_agrees_horn : ∃ W : Set NeckCylinder,
    IsOpen W ∧ Set.range (fun y : Sphere 2 => (y, (0 : ℝ))) ⊆ W ∧ Set.EqOn chart horn W
  shift : ℝ
  shift_lower : d⁻¹ + 1 < shift
  neck : NormalizedNeck D.terminal.metric d k
  chart_eq_neck : ∀ p : neckBuffer d, chart (p.1.1, shift - p.1.2) = neck.chart p
  scale_eq : neck.scale = (h ^ 2)⁻¹
  pastMetric : ℝ → SmoothRiemannianMetric NeckCylinderModel (neckBuffer d)
  pastMetric_inner : ∀ t ∈ Set.Icc (D.endTime - 2 * h ^ 2) D.endTime,
    ∀ (x : neckBuffer d) (V W : TangentSpace NeckCylinderModel x),
      (pastMetric t).inner x V W = neck.scale *
        (D.slab.flow.base.metric t).inner (neck.chart x).1
          (mfderiv NeckCylinderModel ThreeModel
            (fun y : neckBuffer d => (neck.chart y).1) x V)
          (mfderiv NeckCylinderModel ThreeModel
            (fun y : neckBuffer d => (neck.chart y).1) x W)
  past_closeness : ∀ t ∈ Set.Icc (D.endTime - 2 * h ^ 2) D.endTime, ∀ m : ℕ, m ≤ k →
    metricDerivNormSupOn (neckClosedTest d) m (pastMetric t)
      (roundCylinderMetric.restrictOpen (neckBuffer d))
      (roundCylinderMetric.restrictOpen (neckBuffer d)) < d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdaptedHistoricalNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdaptedHistoricalNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdaptedHistoricalNeck ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdaptedHistoricalNeck

def historicalNeckRecognition (τ ε d : ℝ) (k : ℕ) (Λ : ℝ) : Prop :=
  0 < d ∧ d < 1 / 4 ∧ 2 * ⌊d⁻¹⌋₊ + 4 ≤ k ∧
    ∃ H : ℝ, 0 < H ∧
      ∀ (D : OneStepIncoming.{u}) (P : TerminalCorePresentation D ε Λ)
        (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c)
        (h : ℝ),
        0 < h → h ≤ H → 2 * h ^ 2 < τ → Λ * (P.coreRadius ^ 2)⁻¹ < (h ^ 2)⁻¹ →
          Nonempty (AdaptedHistoricalNeck D (P.horn c e) d h k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historicalNeckRecognition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historicalNeckRecognition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historicalNeckRecognition ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historicalNeckRecognition

def cylinderSlab (N : ℝ) : TopologicalSpace.Opens NeckCylinder :=
  ⟨{x : NeckCylinder | x.2 ∈ Set.Ioo (-N) N},
    isOpen_Ioo.preimage continuous_snd⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cylinderSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cylinderSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cylinderSlab ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cylinderSlab

def backwardCylinderMetric (N : ℝ) (v : Set.Icc (-1 : ℝ) 0) :
    SmoothRiemannianMetric NeckCylinderModel (↥(cylinderSlab N)) :=
  (shrinkingCylinderMetric ⟨(v : ℝ), Set.mem_Iio.mpr (by
      have hv : (v : ℝ) ≤ 0 := v.2.2
      linarith)⟩).restrictOpen
    (cylinderSlab N)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.backwardCylinderMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.backwardCylinderMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.backwardCylinderMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.backwardCylinderMetric

def normalizedFlowMetricAt (D : OneStepIncoming.{u}) (Q v : ℝ) :
    SmoothRiemannianMetric ThreeModel ↥D.slab.terminalRegularOpen :=
  if v = 0 then D.terminal.metric
  else (D.slab.flow.base.metric (D.endTime + v / Q)).restrictOpen
    D.slab.terminalRegularOpen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.normalizedFlowMetricAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.normalizedFlowMetricAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.normalizedFlowMetricAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.normalizedFlowMetricAt

def hornCylinderLimit (ε Λ : ℝ) : Prop :=
  ∀ (D : OneStepIncoming.{u}) (P : TerminalCorePresentation D ε Λ)
    (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (x : ℕ → ↥D.slab.terminalRegularOpen),
    (∀ n, x n ∈ Set.range fun p : HalfNeckCylinder => P.horn c e p.1) →
    _root_.Filter.Tendsto (fun n => metricScalarAt D.terminal.metric (x n)) _root_.Filter.atTop _root_.Filter.atTop →
    ∃ block : ℕ → ℕ, StrictMono block ∧
      ∀ (N : ℝ) (_hN : 0 < N) (order : ℕ) (η : ℝ), 0 < η →
        ∀ᶠ n in _root_.Filter.atTop,
          ∃ (chart : C(↥(cylinderSlab N), ↥D.slab.terminalRegularOpen))
            (scaled : Set.Icc (-1 : ℝ) 0 →
              SmoothRiemannianMetric NeckCylinderModel (↥(cylinderSlab N))),
            (∀ (v : Set.Icc (-1 : ℝ) 0) (z : ↥(cylinderSlab N))
                (V W : TangentSpace NeckCylinderModel z),
              (scaled v).inner z V W = metricScalarAt D.terminal.metric (x (block n)) *
                (normalizedFlowMetricAt D (metricScalarAt D.terminal.metric (x (block n)))
                  (z.1.2)).inner (chart z)
                  (mfderiv NeckCylinderModel ThreeModel chart z V)
                  (mfderiv NeckCylinderModel ThreeModel chart z W)) ∧
            (∀ v : Set.Icc (-1 : ℝ) 0,
              metricDerivNormSupOn (Set.univ : Set ↥(cylinderSlab N)) order (scaled v)
                (backwardCylinderMetric N v) (backwardCylinderMetric N v) < η)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hornCylinderLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hornCylinderLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hornCylinderLimit ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hornCylinderLimit

def IsConstantPositiveSectionalCurvature {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ x (v w : TangentSpace ThreeModel x),
    LinearIndependent ℝ ![v, w] →
      DifferentialGeometry.Geometry.Riemannian.sectionalCurvature g x v w = κ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsConstantPositiveSectionalCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsConstantPositiveSectionalCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsConstantPositiveSectionalCurvature ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsConstantPositiveSectionalCurvature

def IsPositiveSpaceFormModel (M : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∃ g : SmoothRiemannianMetric ThreeModel M.Carrier,
    IsConstantPositiveSectionalCurvature g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsPositiveSpaceFormModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsPositiveSpaceFormModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsPositiveSpaceFormModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsPositiveSpaceFormModel

def sphericalSpaceFormCovering : Prop :=
  ∀ (M : ConnectedClosedOrientedManifold.{u} 3) (g : SmoothRiemannianMetric ThreeModel M.Carrier),
    IsConstantPositiveSectionalCurvature g →
    ∃ G : DifferentialGeometry.Topology.SphericalSpaceFormGroup,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
        G.manifold.toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalSpaceFormCovering then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalSpaceFormCovering"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalSpaceFormCovering ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalSpaceFormCovering

structure RelativeDiscardPresentation (C : Type u) [TopologicalSpace C]
    [ChartedSpace ThreeSpace C] [IsManifold ThreeModel ∞ C] [T2Space C] [CompactSpace C] where
  vertexCount : ℕ
  vertex : Fin vertexCount → ConnectedClosedOrientedManifold.{u} 3
  vertex_elementary : ∀ i,
    DifferentialGeometry.Topology.isStandardFactor (vertex i) ∨ IsPositiveSpaceFormModel (vertex i)
  edgeCount : ℕ
  edgeSource : Fin edgeCount → Fin vertexCount
  edgeTarget : Fin edgeCount → Fin vertexCount
  graph_connected : ∀ i i' : Fin vertexCount,
    Relation.ReflTransGen (fun a b : Fin vertexCount =>
      ∃ e : Fin edgeCount,
        (edgeSource e = a ∧ edgeTarget e = b) ∨ (edgeSource e = b ∧ edgeTarget e = a)) i i'
  externalCount : ℕ
  externalSphere : Fin externalCount → C(Sphere 2, C)
  externalSphere_smooth : ∀ b, _root_.Manifold.IsSmoothEmbedding (𝓡 2) ThreeModel ∞ (externalSphere b)
  externalSphere_pairwise : Pairwise fun b b' =>
    Disjoint (Set.range (externalSphere b)) (Set.range (externalSphere b'))
  edgeCollar : Fin edgeCount → C(Sphere 2 × Set.Icc (-2 : ℝ) 2, C)
  edgeCollar_smooth : ∀ e,
    letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
    _root_.Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (edgeCollar e)
  edgeCollar_pairwise : Pairwise fun e e' =>
    Disjoint (Set.range (edgeCollar e)) (Set.range (edgeCollar e'))
  edgeCollar_disjoint_sphere : ∀ e b,
    Disjoint (Set.range (edgeCollar e)) (Set.range (externalSphere b))
  region : Fin vertexCount → Set C
  region_compact : ∀ i, IsCompact (region i)
  region_connected : ∀ i, IsConnected (region i)
  region_frontier : ∀ i, frontier (region i) ⊆
    (⋃ b, Set.range (externalSphere b)) ∪ (⋃ e, Set.range (edgeCollar e))
  cover : ∀ x : C, (∃ i, x ∈ region i) ∨ (∃ e, x ∈ Set.range (edgeCollar e)) ∨
    (∃ b, x ∈ Set.range (externalSphere b))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RelativeDiscardPresentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RelativeDiscardPresentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RelativeDiscardPresentation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RelativeDiscardPresentation

def HasElementaryDiscardDecomposition (C : Type u) [TopologicalSpace C]
    [ChartedSpace ThreeSpace C] [IsManifold ThreeModel ∞ C] [T2Space C] [CompactSpace C] : Prop :=
  Nonempty (RelativeDiscardPresentation C)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasElementaryDiscardDecomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasElementaryDiscardDecomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasElementaryDiscardDecomposition ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasElementaryDiscardDecomposition

structure ProtectedIncomingWitness (D : OneStepIncoming.{u})
    (X : Set ↥D.slab.terminalRegularOpen) (x : ↥D.slab.terminalRegularOpen) where
  region : Set ↥D.slab.terminalRegularOpen
  region_open : IsOpen region
  x_mem : x ∈ region
  radius : ℝ
  radius_pos : 0 < radius
  buffer : Set ↥D.slab.terminalRegularOpen
  buffer_open : IsOpen buffer
  region_subset_buffer : region ⊆ buffer
  buffer_subset_core : buffer ⊆ interior X
  bufferRadius : ℝ
  bufferRadius_gt : 2 * radius < bufferRadius
  ball_compact : IsCompact (riemannianClosedBallOf D.terminal.metric x bufferRadius)
  ball_subset_buffer : riemannianClosedBallOf D.terminal.metric x bufferRadius ⊆ buffer
  scale_pos : 0 < metricScalarAt D.terminal.metric x
  scalar_comparable : ∀ y ∈ region,
    metricScalarAt D.terminal.metric x / 2 ≤ metricScalarAt D.terminal.metric y ∧
      metricScalarAt D.terminal.metric y ≤ 2 * metricScalarAt D.terminal.metric x
  neckCount : ℕ
  neckPrecision : Fin neckCount → ℝ
  neckOrder : Fin neckCount → ℕ
  neckChart : (i : Fin neckCount) → C(neckBuffer (neckPrecision i),
    ↥D.slab.terminalRegularOpen)
  neckChart_smooth : ∀ i, _root_.Manifold.IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ (neckChart i)
  neck_range_subset : ∀ i, Set.range (neckChart i) ⊆ buffer
  neck_backward : ∀ i, ∃ (θ : NeckCylinder → ↥D.slab.terminalRegularOpen) (h : ℝ),
    0 < h ∧ Set.range θ ⊆ buffer ∧
      Nonempty (AdaptedHistoricalNeck D θ (neckPrecision i) h (neckOrder i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ProtectedIncomingWitness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ProtectedIncomingWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ProtectedIncomingWitness ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ProtectedIncomingWitness

def precutCanonicalCoverage (D : OneStepIncoming.{u})
    (X : Set ↥D.slab.terminalRegularOpen) (rTest : ℝ)
    (ι : Type u) (collar : ι → Set ↥D.slab.terminalRegularOpen) : Prop :=
  ∀ x ∈ X, (rTest ^ 2)⁻¹ ≤ metricScalarAt D.terminal.metric x →
    (∃ i, x ∈ collar i) ∨ Nonempty (ProtectedIncomingWitness D X x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.precutCanonicalCoverage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.precutCanonicalCoverage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.precutCanonicalCoverage ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.precutCanonicalCoverage

def protectionInput (τ ε Λ : ℝ) : Prop :=
  ∀ (D : OneStepIncoming.{u}) (P : TerminalCorePresentation D ε Λ)
    (X : Set ↥D.slab.terminalRegularOpen) (rTest : ℝ)
    (collar : (c : ConnectedComponents ↥D.slab.terminalRegularOpen) →
      P.hornIndex c → Set ↥D.slab.terminalRegularOpen),
    τ ≤ D.endTime → 0 < rTest → IsCompact X →
    (∀ c, c ∈ P.component → P.core c ⊆ X) →
    (∀ x ∈ X, (∀ c, c ∈ P.component → x ∉ P.core c) →
      ∃ (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c),
        x ∈ collar c e) →
    (∀ c e, collar c e ⊆ P.core c) →
    precutCanonicalCoverage D X rTest
      ((c : ConnectedComponents ↥D.slab.terminalRegularOpen) × P.hornIndex c)
      (fun ie => collar ie.1 ie.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.protectionInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.protectionInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.protectionInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.protectionInput

structure OneStepPrecision (p : CutoffParameters) (B dCap glob : ℝ) where
  precision : ℝ
  order : ℕ
  precision_pos : 0 < precision
  precision_shorter : precision < _root_.Min.min (1 / 4) (_root_.Min.min (p.delta B) (_root_.Min.min dCap glob))
  order_lower : _root_.Max.max (p.modelOrder + 6) (2 * ⌊precision⁻¹⌋₊ + 4) ≤ order

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OneStepPrecision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OneStepPrecision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OneStepPrecision ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OneStepPrecision

structure GlobalStepInputs (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ)
    (DiscardedCutOpen : Type u → Prop) where
  endInput : TerminalCorePresentationInput.{u} τ ε
  neckInput : historicalNeckRecognition.{u} τ ε d k endInput.lambda
  pieceInput : ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount),
    GeometricCutoffRecord H i p → DiscardedCutOpen (H.event i).discarded.Carrier →
    (H.event i).discarded.toClosedOrientedManifold.componentwiseConnectedSumStandardFactor
  roundInput : sphericalSpaceFormCovering.{u}
  cylinderInput : hornCylinderLimit.{u} ε endInput.lambda
  protectInput : protectionInput.{u} τ ε endInput.lambda

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GlobalStepInputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GlobalStepInputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GlobalStepInputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GlobalStepInputs

def GlobalStepConclusion (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ) (a₀ : ℝ)
    (DiscardedCutOpen : Type u → Prop)
    (inputs : GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen) : Prop :=
  ∃ hstar : ℝ, 0 < hstar ∧ 2 * hstar ^ 2 < τ ∧
    ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount),
      τ ≤ H.time i.succ →
      Nonempty (GeometricCutoffRecord H i p) →
      ∃ (K : ObservedHistory.{u}) (j : Fin K.eventCount) (R : GeometricCutoffRecord K j p),
        j.val = H.eventCount ∧ ObservedHistory.IsPrefixOf H K ∧
        K.eventCount = H.eventCount + 1 ∧
        τ ≤ K.time (Fin.succ j) ∧
        Nonempty (TerminalCorePresentation (OneStepIncoming.ofRecord R) ε
          inputs.endInput.lambda) ∧
        (∀ α : (K.event j).transition.trace.tubes.Index,
          R.nominalRadius ⟨α⟩ = hstar) ∧
        DiscardedCutOpen (K.event j).discarded.Carrier ∧
        (∀ C : ConnectedComponents (K.event j).discarded.Carrier,
          componentIsPoincareStandard (K.event j).discarded.toClosedOrientedManifold C) ∧
        (∀ x : (K.stage (Fin.succ j)).Carrier,
          -3 / (a₀ + 2 * K.time (Fin.succ j)) ≤ metricScalarAt (K.event j).outputMetric x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GlobalStepConclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GlobalStepConclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GlobalStepConclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GlobalStepConclusion

def globalMetricStep (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ) (a₀ : ℝ)
    (DiscardedCutOpen : Type u → Prop)
    (inputs : GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen) : Prop :=
  GlobalStepConclusion.{u} p τ ε d k a₀ DiscardedCutOpen inputs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.globalMetricStep then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.globalMetricStep"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.globalMetricStep ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.globalMetricStep

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
