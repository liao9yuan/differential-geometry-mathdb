import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import Submission.DifferentialGeometry.Geometry.Curvature.RoundCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.Function _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Topology

open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {D : OneStepIncoming.{u}}

def TerminalCorePresentation.monoLambda {ε Λ Λ' : ℝ}
    (P : TerminalCorePresentation D ε Λ) (hΛ : Λ ≤ Λ') :
    TerminalCorePresentation D ε Λ' where
  epsilon_pos := P.epsilon_pos
  Lambda_ge_one := le_trans P.Lambda_ge_one hΛ
  coreRadius := P.coreRadius
  coreRadius_pos := P.coreRadius_pos
  coreRadius_eq := P.coreRadius_eq
  component := P.component
  component_finite := P.component_finite
  core := P.core
  core_isCompact := P.core_isCompact
  core_isConnected := P.core_isConnected
  core_empty := P.core_empty
  coreCharts := P.coreCharts
  core_smooth := P.core_smooth
  core_induced := P.core_induced
  core_interior_eq := P.core_interior_eq
  core_boundary_eq := P.core_boundary_eq
  component_iff_meets_low := P.component_iff_meets_low
  low_mem_interior_core := P.low_mem_interior_core
  hornIndex := P.hornIndex
  hornIndex_finite := P.hornIndex_finite
  hornIndex_empty := P.hornIndex_empty
  horn := P.horn
  horn_smooth := P.horn_smooth
  horn_interior_embedding := P.horn_interior_embedding
  horn_injOn := P.horn_injOn
  horn_proper := P.horn_proper
  horn_range_disjoint := P.horn_range_disjoint
  horn_meets_core := P.horn_meets_core
  horn_base_covers_boundary := P.horn_base_covers_boundary
  hornCollar := P.hornCollar
  horn_collar_core_side := P.horn_collar_core_side
  horn_collar_eq := P.horn_collar_eq
  horn_covers_component := P.horn_covers_component
  horn_scalar_large := P.horn_scalar_large
  horn_base_scalar := fun c e y =>
    (P.horn_base_scalar c e y).trans
      (mul_le_mul_of_nonneg_right hΛ (inv_nonneg.mpr (sq_nonneg P.coreRadius)))
  horn_scalar_diverges := P.horn_scalar_diverges
  horn_spatial_neck := P.horn_spatial_neck

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.monoLambda then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.monoLambda"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.monoLambda ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.monoLambda

def TerminalCorePresentation.monoEpsilon {ε ε' Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ) (hε : ε ≤ ε') :
    TerminalCorePresentation D ε' Λ where
  epsilon_pos := lt_of_lt_of_le P.epsilon_pos hε
  Lambda_ge_one := P.Lambda_ge_one
  coreRadius := P.coreRadius
  coreRadius_pos := P.coreRadius_pos
  coreRadius_eq := P.coreRadius_eq
  component := P.component
  component_finite := P.component_finite
  core := P.core
  core_isCompact := P.core_isCompact
  core_isConnected := P.core_isConnected
  core_empty := P.core_empty
  coreCharts := P.coreCharts
  core_smooth := P.core_smooth
  core_induced := P.core_induced
  core_interior_eq := P.core_interior_eq
  core_boundary_eq := P.core_boundary_eq
  component_iff_meets_low := P.component_iff_meets_low
  low_mem_interior_core := P.low_mem_interior_core
  hornIndex := P.hornIndex
  hornIndex_finite := P.hornIndex_finite
  hornIndex_empty := P.hornIndex_empty
  horn := P.horn
  horn_smooth := P.horn_smooth
  horn_interior_embedding := P.horn_interior_embedding
  horn_injOn := P.horn_injOn
  horn_proper := P.horn_proper
  horn_range_disjoint := P.horn_range_disjoint
  horn_meets_core := P.horn_meets_core
  horn_base_covers_boundary := P.horn_base_covers_boundary
  hornCollar := P.hornCollar
  horn_collar_core_side := P.horn_collar_core_side
  horn_collar_eq := P.horn_collar_eq
  horn_covers_component := P.horn_covers_component
  horn_scalar_large := P.horn_scalar_large
  horn_base_scalar := P.horn_base_scalar
  horn_scalar_diverges := P.horn_scalar_diverges
  horn_spatial_neck := fun c e x hx => by
    obtain ⟨δ, k, neck, hcenter, hδε, hk⟩ := P.horn_spatial_neck c e x hx
    exact ⟨δ, k, neck, hcenter, hδε.trans hε,
      le_trans (Nat.add_le_add_right
        (Nat.floor_mono (inv_anti₀ P.epsilon_pos hε)) 1) hk⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.monoEpsilon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.monoEpsilon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.monoEpsilon ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.monoEpsilon

theorem TerminalCorePresentation.lowComponents_finite {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ) :
    {c : ConnectedComponents ↥D.slab.terminalRegularOpen |
      ∃ x : ↥D.slab.terminalRegularOpen, ConnectedComponents.mk x = c ∧
        metricScalarAt D.terminal.metric x ≤ (P.coreRadius ^ 2)⁻¹}.Finite :=
  P.component_finite.subset fun _ hc => (P.component_iff_meets_low _).mpr hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.lowComponents_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.lowComponents_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.lowComponents_finite ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.lowComponents_finite

theorem TerminalCorePresentation.low_mem_core {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ) {x : ↥D.slab.terminalRegularOpen}
    (hx : metricScalarAt D.terminal.metric x ≤ (P.coreRadius ^ 2)⁻¹) :
    ∃ c ∈ P.component, x ∈ P.core c := by
  have hc : ConnectedComponents.mk x ∈ P.component :=
    (P.component_iff_meets_low (ConnectedComponents.mk x)).mpr ⟨x, rfl, hx⟩
  exact ⟨_, hc, interior_subset (P.low_mem_interior_core _ hc x rfl hx)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.low_mem_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.low_mem_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.low_mem_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.low_mem_core

theorem TerminalCorePresentation.lowSet_subset_iUnion_core {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ) :
    {x : ↥D.slab.terminalRegularOpen |
        metricScalarAt D.terminal.metric x ≤ (P.coreRadius ^ 2)⁻¹} ⊆
      ⋃ c ∈ P.component, P.core c := by
  intro x hx
  obtain ⟨c, hc, hxc⟩ := P.low_mem_core hx
  exact Set.mem_biUnion hc hxc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.lowSet_subset_iUnion_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.lowSet_subset_iUnion_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.lowSet_subset_iUnion_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.lowSet_subset_iUnion_core

def TerminalCorePresentationInput.monoEpsilon {τ ε ε' : ℝ}
    (P : TerminalCorePresentationInput.{u} τ ε) (hε : ε ≤ ε') (hε' : ε' < 1) :
    TerminalCorePresentationInput.{u} τ ε' where
  tau_pos := P.tau_pos
  epsilon_pos := lt_of_lt_of_le P.epsilon_pos hε
  epsilon_lt_one := hε'
  lambda := P.lambda
  one_le_lambda := P.one_le_lambda
  presentation := fun D hτ => (P.presentation D hτ).map (fun Q => Q.monoEpsilon hε)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentationInput.monoEpsilon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentationInput.monoEpsilon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentationInput.monoEpsilon ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentationInput.monoEpsilon

def TerminalCorePresentationInput.monoLambda {τ ε : ℝ}
    (P : TerminalCorePresentationInput.{u} τ ε) {Λ' : ℝ}
    (hΛ : P.lambda ≤ Λ') (hΛ' : 1 ≤ Λ') :
    TerminalCorePresentationInput.{u} τ ε where
  tau_pos := P.tau_pos
  epsilon_pos := P.epsilon_pos
  epsilon_lt_one := P.epsilon_lt_one
  lambda := Λ'
  one_le_lambda := hΛ'
  presentation := fun D hτ => (P.presentation D hτ).map (fun Q => Q.monoLambda hΛ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentationInput.monoLambda then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentationInput.monoLambda"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentationInput.monoLambda ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentationInput.monoLambda

def TerminalCorePresentationInput.monoParams {τ ε ε' : ℝ}
    (P : TerminalCorePresentationInput.{u} τ ε) {Λ' : ℝ}
    (hε : ε ≤ ε') (hε' : ε' < 1) (hΛ : P.lambda ≤ Λ') (hΛ' : 1 ≤ Λ') :
    TerminalCorePresentationInput.{u} τ ε' where
  tau_pos := P.tau_pos
  epsilon_pos := lt_of_lt_of_le P.epsilon_pos hε
  epsilon_lt_one := hε'
  lambda := Λ'
  one_le_lambda := hΛ'
  presentation := fun D hτ =>
    (P.presentation D hτ).map (fun Q => (Q.monoEpsilon hε).monoLambda hΛ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentationInput.monoParams then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentationInput.monoParams"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentationInput.monoParams ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentationInput.monoParams

section MetricMonotonicity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem metricDerivNormSupOn_mono {K : Set M} (hK : IsCompact K) {j k : ℕ} (hjk : j ≤ k)
    (gk gInf gRef : SmoothRiemannianMetric I M) :
    metricDerivNormSupOn (I := I) K j gk gInf gRef ≤
      metricDerivNormSupOn (I := I) K k gk gInf gRef := by
  refine metricDerivNormSupOn_le_of_forall (I := I) K j gk gInf gRef
    (metricDerivNormSupOn (I := I) K k gk gInf gRef)
    (metricDerivNormSupOn_nonneg K k gk gInf gRef) ?_
  intro a ha x hx
  exact derivNorm_le_sup (I := I) hK (ha.trans hjk) gk gInf gRef hx

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.metricDerivNormSupOn_mono
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.metricDerivNormSupOn_mono target :: scope.openDecls } }

end MetricMonotonicity

section NeckDatum

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

def NormalizedNeck.lowerOrder {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k j : ℕ}
    (N : NormalizedNeck g δ k) (hjk : j ≤ k) : NormalizedNeck g δ j :=
  { N with
    closeness := lt_of_le_of_lt
      (metricDerivNormSupOn_mono (isCompact_neckClosedTest δ) hjk
        N.normalizedMetric (roundCylinderMetric.restrictOpen (neckBuffer δ))
        (roundCylinderMetric.restrictOpen (neckBuffer δ)))
      N.closeness }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.lowerOrder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.lowerOrder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.lowerOrder ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.lowerOrder

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.scale_eq_inv_sq_of_scalar {g : SmoothRiemannianMetric ThreeModel M}
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck g δ k) {h : ℝ}
    (hcenter : metricScalarAt g N.center = (h ^ 2)⁻¹) :
    N.scale = (h ^ 2)⁻¹ :=
  N.scale_scalar.trans hcenter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.scale_eq_inv_sq_of_scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.scale_eq_inv_sq_of_scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.scale_eq_inv_sq_of_scalar ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.scale_eq_inv_sq_of_scalar

end NeckDatum

private theorem metricScalarAt_roundCylinderMetric_eq_one (x : NeckCylinder) :
    metricScalarAt roundCylinderMetric x = 1 := by
  rw [roundCylinderMetric_eq_geometry]
  rw [metricScalarAt_roundCylinder]
  norm_num

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.metricScalarAt_roundCylinderMetric_eq_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.metricScalarAt_roundCylinderMetric_eq_one target :: scope.openDecls } }

theorem exists_center_scalar_inv_sq_roundCylinder :
    ∃ h : ℝ, 0 < h ∧ ∀ x : NeckCylinder, metricScalarAt roundCylinderMetric x = (h ^ 2)⁻¹ :=
  ⟨1, by norm_num, fun x => by rw [metricScalarAt_roundCylinderMetric_eq_one]; norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_center_scalar_inv_sq_roundCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_center_scalar_inv_sq_roundCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_center_scalar_inv_sq_roundCylinder ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_center_scalar_inv_sq_roundCylinder

def AdaptedHistoricalNeck.lowerOrder {d h : ℝ} {k j : ℕ}
    {horn : NeckCylinder → ↥D.slab.terminalRegularOpen}
    (A : AdaptedHistoricalNeck D horn d h k) (hjk : j ≤ k)
    (hlow : 2 * ⌊d⁻¹⌋₊ + 4 ≤ j) :
    AdaptedHistoricalNeck D horn d h j where
  d_pos := A.d_pos
  d_lt_quarter := A.d_lt_quarter
  h_pos := A.h_pos
  order_lower := hlow
  depth_ge := A.depth_ge
  chart := A.chart
  chart_agrees_horn := A.chart_agrees_horn
  shift := A.shift
  shift_lower := A.shift_lower
  neck := A.neck.lowerOrder hjk
  chart_eq_neck := A.chart_eq_neck
  scale_eq := A.scale_eq
  pastMetric := A.pastMetric
  pastMetric_inner := A.pastMetric_inner
  past_closeness := fun t ht m hm => A.past_closeness t ht m (le_trans hm hjk)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdaptedHistoricalNeck.lowerOrder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdaptedHistoricalNeck.lowerOrder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdaptedHistoricalNeck.lowerOrder ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdaptedHistoricalNeck.lowerOrder

theorem AdaptedHistoricalNeck.center_scalar_eq {d h : ℝ} {k : ℕ}
    {horn : NeckCylinder → ↥D.slab.terminalRegularOpen}
    (A : AdaptedHistoricalNeck D horn d h k) :
    metricScalarAt D.terminal.metric A.neck.center = (h ^ 2)⁻¹ :=
  A.neck.scale_scalar.symm.trans A.scale_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdaptedHistoricalNeck.center_scalar_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdaptedHistoricalNeck.center_scalar_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdaptedHistoricalNeck.center_scalar_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdaptedHistoricalNeck.center_scalar_eq

theorem historicalNeckRecognition.mono_order {τ ε d Λ : ℝ} {k j : ℕ}
    (H : historicalNeckRecognition.{u} τ ε d k Λ) (hjk : j ≤ k)
    (hlow : 2 * ⌊d⁻¹⌋₊ + 4 ≤ j) :
    historicalNeckRecognition.{u} τ ε d j Λ := by
  obtain ⟨hd0, hd1, -, H0, hH0, hrec⟩ := H
  refine ⟨hd0, hd1, hlow, H0, hH0, fun D P c e h hh0 hhH hτ hscale => ?_⟩
  obtain ⟨A⟩ := hrec D P c e h hh0 hhH hτ hscale
  exact ⟨A.lowerOrder hjk hlow⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historicalNeckRecognition
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historicalNeckRecognition.mono_order then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historicalNeckRecognition.mono_order"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historicalNeckRecognition.mono_order ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historicalNeckRecognition.mono_order

def GlobalStepInputs.monoOrder {p : CutoffParameters} {τ ε d : ℝ} {k j : ℕ}
    {DiscardedCutOpen : Type u → Prop}
    (G : GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen) (hjk : j ≤ k)
    (hlow : 2 * ⌊d⁻¹⌋₊ + 4 ≤ j) :
    GlobalStepInputs.{u} p τ ε d j DiscardedCutOpen where
  endInput := G.endInput
  neckInput := G.neckInput.mono_order hjk hlow
  pieceInput := G.pieceInput
  roundInput := G.roundInput
  cylinderInput := G.cylinderInput
  protectInput := G.protectInput

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GlobalStepInputs.monoOrder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GlobalStepInputs.monoOrder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GlobalStepInputs.monoOrder ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GlobalStepInputs.monoOrder

theorem exists_precision_order_witness :
    ∃ d : ℝ, ∃ k : ℕ, 0 < d ∧ d < 1 / 4 ∧ 2 * ⌊d⁻¹⌋₊ + 4 ≤ k :=
  ⟨1 / 8, 20, by norm_num, by norm_num, by norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_precision_order_witness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_precision_order_witness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_precision_order_witness ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_precision_order_witness

theorem not_order_threshold_nineteen :
    ¬ 2 * ⌊(1 / 8 : ℝ)⁻¹⌋₊ + 4 ≤ 19 := by
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_order_threshold_nineteen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_order_threshold_nineteen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_order_threshold_nineteen ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_order_threshold_nineteen

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
