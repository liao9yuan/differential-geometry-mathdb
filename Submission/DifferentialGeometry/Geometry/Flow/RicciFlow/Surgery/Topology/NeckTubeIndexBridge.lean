import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CappingCover
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Function

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem mem_neckBuffer_iff {δ : ℝ} {z : NeckCylinder} :
    z ∈ neckBuffer δ ↔ -δ⁻¹ - 1 < z.2 ∧ z.2 < δ⁻¹ + 1 := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.mem_neckBuffer_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.mem_neckBuffer_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.mem_neckBuffer_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.mem_neckBuffer_iff

theorem inv_add_one_le_two_iff {δ : ℝ} (hδ : 0 < δ) :
    δ⁻¹ + 1 ≤ 2 ↔ 1 ≤ δ := by
  rw [show (2 : ℝ) = 1 + 1 by norm_num, add_le_add_iff_right]
  exact inv_le_one₀ hδ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.inv_add_one_le_two_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.inv_add_one_le_two_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.inv_add_one_le_two_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.inv_add_one_le_two_iff

theorem not_exists_precision_lt_one_and_buffer_le_two :
    ¬ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ⁻¹ + 1 ≤ 2 := by
  rintro ⟨δ, h0, h1, hle⟩
  exact absurd ((inv_add_one_le_two_iff h0).mp hle) (not_le.mpr h1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_exists_precision_lt_one_and_buffer_le_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_exists_precision_lt_one_and_buffer_le_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_exists_precision_lt_one_and_buffer_le_two ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_exists_precision_lt_one_and_buffer_le_two

theorem exists_neckBuffer_two_lt_abs_snd {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    ∃ z : NeckCylinder, z ∈ neckBuffer δ ∧ 2 < |z.2| := by
  have hinv : 1 < δ⁻¹ := (one_lt_inv₀ h0).mpr h1
  refine ⟨(sphereNorth, (2 + (δ⁻¹ + 1)) / 2), ?_, ?_⟩
  · rw [mem_neckBuffer_iff]
    constructor <;> linarith
  · rw [abs_of_pos (show (0 : ℝ) < (2 + (δ⁻¹ + 1)) / 2 by linarith)]
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_neckBuffer_two_lt_abs_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_neckBuffer_two_lt_abs_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_neckBuffer_two_lt_abs_snd ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_neckBuffer_two_lt_abs_snd

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}

def neckChartCentralOf (δ : (H.event i).transition.trace.tubes.Index → ℝ)
    (k : (H.event i).transition.trace.tubes.Index → ℕ)
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (δ α) (k α))
    (α : (H.event i).transition.trace.tubes.Index) :
    Set ↥(H.event i).incoming.terminalRegularOpen :=
  (neck α).chart '' {z : neckBuffer (δ α) | |z.1.2| ≤ 2}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChartCentralOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChartCentralOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChartCentralOf ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChartCentralOf

def neckChartTailOf (δ : (H.event i).transition.trace.tubes.Index → ℝ)
    (k : (H.event i).transition.trace.tubes.Index → ℕ)
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (δ α) (k α))
    (α : (H.event i).transition.trace.tubes.Index) :
    Set ↥(H.event i).incoming.terminalRegularOpen :=
  (neck α).chart '' {z : neckBuffer (δ α) | 2 < |z.1.2|}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChartTailOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChartTailOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChartTailOf ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChartTailOf

theorem neckChart_eq_central_union_tail_of
    (δ : (H.event i).transition.trace.tubes.Index → ℝ)
    (k : (H.event i).transition.trace.tubes.Index → ℕ)
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (δ α) (k α))
    (α : (H.event i).transition.trace.tubes.Index) :
    Set.range (neck α).chart =
      neckChartCentralOf δ k neck α ∪ neckChartTailOf δ k neck α := by
  have huniv : (Set.univ : Set (neckBuffer (δ α))) =
      {z : neckBuffer (δ α) | |z.1.2| ≤ 2} ∪ {z | 2 < |z.1.2|} := by
    ext z
    simp only [_root_.Set.mem_univ, _root_.Set.mem_union, Set.mem_ofPred_eq]
    exact ⟨fun _ => (lt_or_ge (2 : ℝ) |z.1.2|).symm, fun _ => trivial⟩
  rw [neckChartCentralOf, neckChartTailOf, ← Set.image_univ, huniv, Set.image_union]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChart_eq_central_union_tail_of then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChart_eq_central_union_tail_of"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChart_eq_central_union_tail_of ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChart_eq_central_union_tail_of

theorem val_image_neckChartCentral_eq_tube_range_of
    (δ : (H.event i).transition.trace.tubes.Index → ℝ)
    (k : (H.event i).transition.trace.tubes.Index → ℕ)
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (δ α) (k α))
    (tube_eq : ∀ (α : (H.event i).transition.trace.tubes.Index) (x : TubeDomain),
      ∀ hx : (x.1, x.2.1) ∈ neckBuffer (δ α),
      (H.event i).transition.trace.tubes.tube α x = ((neck α).chart ⟨(x.1, x.2.1), hx⟩).1)
    (tube_in_buffer : ∀ (α : (H.event i).transition.trace.tubes.Index)
      (x : TubeDomain), (x.1, x.2.1) ∈ neckBuffer (δ α))
    (α : (H.event i).transition.trace.tubes.Index) :
    Subtype.val '' neckChartCentralOf δ k neck α =
      Set.range ((H.event i).transition.trace.tubes.tube α) := by
  rw [neckChartCentralOf]
  ext p
  constructor
  · rintro ⟨q, hq, hqp⟩
    obtain ⟨z, hz, rfl⟩ := hq
    obtain ⟨hz1, hz2⟩ := abs_le.mp (show |z.1.2| ≤ 2 from hz)
    let w : TubeDomain := (z.1.1, ⟨z.1.2, hz1, hz2⟩)
    have hw : (⟨(w.1, w.2.1), tube_in_buffer α w⟩ : neckBuffer (δ α)) = z :=
      Subtype.ext rfl
    refine ⟨w, ?_⟩
    rw [tube_eq α w (tube_in_buffer α w), hw]
    exact hqp
  · rintro ⟨w, rfl⟩
    refine ⟨(neck α).chart ⟨(w.1, w.2.1), tube_in_buffer α w⟩, ?_,
      (tube_eq α w (tube_in_buffer α w)).symm⟩
    exact ⟨⟨(w.1, w.2.1), tube_in_buffer α w⟩, abs_le.mpr ⟨w.2.2.1, w.2.2.2⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.val_image_neckChartCentral_eq_tube_range_of then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.val_image_neckChartCentral_eq_tube_range_of"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.val_image_neckChartCentral_eq_tube_range_of ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.val_image_neckChartCentral_eq_tube_range_of

theorem tube_range_subset_val_image_chart_range_of
    (δ : (H.event i).transition.trace.tubes.Index → ℝ)
    (k : (H.event i).transition.trace.tubes.Index → ℕ)
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (δ α) (k α))
    (tube_eq : ∀ (α : (H.event i).transition.trace.tubes.Index) (x : TubeDomain),
      ∀ hx : (x.1, x.2.1) ∈ neckBuffer (δ α),
      (H.event i).transition.trace.tubes.tube α x = ((neck α).chart ⟨(x.1, x.2.1), hx⟩).1)
    (tube_in_buffer : ∀ (α : (H.event i).transition.trace.tubes.Index)
      (x : TubeDomain), (x.1, x.2.1) ∈ neckBuffer (δ α))
    (α : (H.event i).transition.trace.tubes.Index) :
    Set.range ((H.event i).transition.trace.tubes.tube α) ⊆
      Subtype.val '' Set.range (neck α).chart := by
  rw [← val_image_neckChartCentral_eq_tube_range_of δ k neck tube_eq tube_in_buffer α]
  exact Set.image_mono (Set.image_subset_range _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tube_range_subset_val_image_chart_range_of then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tube_range_subset_val_image_chart_range_of"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tube_range_subset_val_image_chart_range_of ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tube_range_subset_val_image_chart_range_of

theorem neckChartCentral_pairwise_disjoint_of
    (δ : (H.event i).transition.trace.tubes.Index → ℝ)
    (k : (H.event i).transition.trace.tubes.Index → ℕ)
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (δ α) (k α))
    (tube_eq : ∀ (α : (H.event i).transition.trace.tubes.Index) (x : TubeDomain),
      ∀ hx : (x.1, x.2.1) ∈ neckBuffer (δ α),
      (H.event i).transition.trace.tubes.tube α x = ((neck α).chart ⟨(x.1, x.2.1), hx⟩).1)
    (tube_in_buffer : ∀ (α : (H.event i).transition.trace.tubes.Index)
      (x : TubeDomain), (x.1, x.2.1) ∈ neckBuffer (δ α))
    {α β : (H.event i).transition.trace.tubes.Index} (h : α ≠ β) :
    Disjoint (neckChartCentralOf δ k neck α) (neckChartCentralOf δ k neck β) := by
  refine Set.disjoint_left.mpr fun p hp hq => ?_
  have hd := (H.event i).transition.trace.tubes.disjoint h
  have hp' : p.1 ∈ Set.range ((H.event i).transition.trace.tubes.tube α) := by
    rw [← val_image_neckChartCentral_eq_tube_range_of δ k neck tube_eq tube_in_buffer α]
    exact ⟨p, hp, rfl⟩
  have hq' : p.1 ∈ Set.range ((H.event i).transition.trace.tubes.tube β) := by
    rw [← val_image_neckChartCentral_eq_tube_range_of δ k neck tube_eq tube_in_buffer β]
    exact ⟨p, hq, rfl⟩
  exact Set.disjoint_left.mp hd hp' hq'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChartCentral_pairwise_disjoint_of then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChartCentral_pairwise_disjoint_of"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChartCentral_pairwise_disjoint_of ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChartCentral_pairwise_disjoint_of

theorem buffer_disjoint_iff_neckChartTail_disjoint_of
    (δ : (H.event i).transition.trace.tubes.Index → ℝ)
    (k : (H.event i).transition.trace.tubes.Index → ℕ)
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (δ α) (k α))
    (tube_eq : ∀ (α : (H.event i).transition.trace.tubes.Index) (x : TubeDomain),
      ∀ hx : (x.1, x.2.1) ∈ neckBuffer (δ α),
      (H.event i).transition.trace.tubes.tube α x = ((neck α).chart ⟨(x.1, x.2.1), hx⟩).1)
    (tube_in_buffer : ∀ (α : (H.event i).transition.trace.tubes.Index)
      (x : TubeDomain), (x.1, x.2.1) ∈ neckBuffer (δ α)) :
    (∀ α β, α ≠ β →
        Disjoint (Set.range (neck α).chart) (Set.range (neck β).chart)) ↔
      ∀ α β, α ≠ β →
        Disjoint (neckChartTailOf δ k neck α) (Set.range (neck β).chart) := by
  constructor
  · intro h α β hab
    exact (h α β hab).mono_left (Set.image_subset_range _ _)
  · intro h α β hab
    rw [neckChart_eq_central_union_tail_of δ k neck α,
      neckChart_eq_central_union_tail_of δ k neck β]
    refine disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨?_, ?_⟩,
      disjoint_union_right.mpr ⟨?_, ?_⟩⟩
    · exact neckChartCentral_pairwise_disjoint_of δ k neck tube_eq tube_in_buffer hab
    · exact ((h β α (Ne.symm hab)).mono_right (Set.image_subset_range _ _)).symm
    · exact (h α β hab).mono_right (Set.image_subset_range _ _)
    · exact (h α β hab).mono_right (Set.image_subset_range _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.buffer_disjoint_iff_neckChartTail_disjoint_of then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.buffer_disjoint_iff_neckChartTail_disjoint_of"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.buffer_disjoint_iff_neckChartTail_disjoint_of ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.buffer_disjoint_iff_neckChartTail_disjoint_of

theorem neckChartTail_nonempty_of
    (δ : (H.event i).transition.trace.tubes.Index → ℝ)
    (k : (H.event i).transition.trace.tubes.Index → ℕ)
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (δ α) (k α))
    (α : (H.event i).transition.trace.tubes.Index) :
    (neckChartTailOf δ k neck α).Nonempty := by
  obtain ⟨z, hz, hz₂⟩ :=
    exists_neckBuffer_two_lt_abs_snd (neck α).delta_pos (neck α).delta_lt_one
  exact ⟨(neck α).chart ⟨z, hz⟩, ⟨⟨z, hz⟩, hz₂, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChartTail_nonempty_of then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChartTail_nonempty_of"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChartTail_nonempty_of ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckChartTail_nonempty_of

private def bridgeTestChart (k : ℝ) (z : neckBuffer (1 / 2)) : ℝ :=
  if |z.1.2| ≤ 2 then k else z.1.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bridgeTestChart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bridgeTestChart target :: scope.openDecls } }

theorem exists_chartCentral_disjoint_not_chartTail_disjoint :
    ∃ f g : neckBuffer (1 / 2) → ℝ,
      Disjoint (f '' {z : neckBuffer (1 / 2) | |z.1.2| ≤ 2})
        (g '' {z : neckBuffer (1 / 2) | |z.1.2| ≤ 2}) ∧
      ¬ Disjoint (f '' {z : neckBuffer (1 / 2) | 2 < |z.1.2|})
        (g '' {z : neckBuffer (1 / 2) | 2 < |z.1.2|}) := by
  refine ⟨bridgeTestChart 0, bridgeTestChart 1, ?_, ?_⟩
  · refine Set.disjoint_left.mpr fun x hx hx' => ?_
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', hzx⟩ := hx'
    have hz1 : |z.1.2| ≤ 2 := hz
    have hz2 : |z'.1.2| ≤ 2 := hz'
    simp only [bridgeTestChart, if_pos hz1, if_pos hz2] at hzx
    norm_num at hzx
  · let z₀ : neckBuffer (1 / 2) := ⟨(sphereNorth, 5 / 2), by
      rw [mem_neckBuffer_iff]
      constructor <;> norm_num⟩
    have hzt : z₀ ∈ {z : neckBuffer (1 / 2) | 2 < |z.1.2|} := by
      change 2 < |z₀.1.2|
      rw [show z₀.1.2 = 5 / 2 from rfl, abs_of_pos (show (0 : ℝ) < 5 / 2 by norm_num)]
      norm_num
    have hzle : ¬ |z₀.1.2| ≤ 2 := by
      rw [show z₀.1.2 = 5 / 2 from rfl, abs_of_pos (show (0 : ℝ) < 5 / 2 by norm_num)]
      norm_num
    have hf : bridgeTestChart 0 z₀ = 5 / 2 := by
      rw [bridgeTestChart, if_neg hzle]
    have hg : bridgeTestChart 1 z₀ = 5 / 2 := by
      rw [bridgeTestChart, if_neg hzle]
    intro hd
    exact (Set.disjoint_left.mp hd ⟨z₀, hzt, hf⟩) ⟨z₀, hzt, hg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_chartCentral_disjoint_not_chartTail_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_chartCentral_disjoint_not_chartTail_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_chartCentral_disjoint_not_chartTail_disjoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_chartCentral_disjoint_not_chartTail_disjoint

namespace GeometricCutoffRecord

abbrev neckChartCentral (G : GeometricCutoffRecord H i parameters)
    (α : (H.event i).transition.trace.tubes.Index) :
    Set ↥(H.event i).incoming.terminalRegularOpen :=
  neckChartCentralOf G.delta G.order G.neck α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartCentral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartCentral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartCentral ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartCentral

abbrev neckChartTail (G : GeometricCutoffRecord H i parameters)
    (α : (H.event i).transition.trace.tubes.Index) :
    Set ↥(H.event i).incoming.terminalRegularOpen :=
  neckChartTailOf G.delta G.order G.neck α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartTail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartTail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartTail ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartTail

theorem neckChart_eq_central_union_tail (G : GeometricCutoffRecord H i parameters)
    (α : (H.event i).transition.trace.tubes.Index) :
    Set.range (G.neck α).chart = neckChartCentral G α ∪ neckChartTail G α :=
  neckChart_eq_central_union_tail_of G.delta G.order G.neck α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChart_eq_central_union_tail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChart_eq_central_union_tail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChart_eq_central_union_tail ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChart_eq_central_union_tail

theorem val_image_neckChartCentral_eq_tube_range (G : GeometricCutoffRecord H i parameters)
    (α : (H.event i).transition.trace.tubes.Index) :
    Subtype.val '' neckChartCentral G α =
      Set.range ((H.event i).transition.trace.tubes.tube α) :=
  val_image_neckChartCentral_eq_tube_range_of G.delta G.order G.neck G.tube_eq
    G.tube_in_buffer α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.val_image_neckChartCentral_eq_tube_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.val_image_neckChartCentral_eq_tube_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.val_image_neckChartCentral_eq_tube_range ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.val_image_neckChartCentral_eq_tube_range

theorem tube_range_subset_val_image_chart_range (G : GeometricCutoffRecord H i parameters)
    (α : (H.event i).transition.trace.tubes.Index) :
    Set.range ((H.event i).transition.trace.tubes.tube α) ⊆
      Subtype.val '' Set.range (G.neck α).chart :=
  tube_range_subset_val_image_chart_range_of G.delta G.order G.neck G.tube_eq
    G.tube_in_buffer α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tube_range_subset_val_image_chart_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tube_range_subset_val_image_chart_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tube_range_subset_val_image_chart_range ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tube_range_subset_val_image_chart_range

theorem neckChartCentral_pairwise_disjoint (G : GeometricCutoffRecord H i parameters)
    {α β : (H.event i).transition.trace.tubes.Index} (h : α ≠ β) :
    Disjoint (neckChartCentral G α) (neckChartCentral G β) :=
  neckChartCentral_pairwise_disjoint_of G.delta G.order G.neck G.tube_eq G.tube_in_buffer h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartCentral_pairwise_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartCentral_pairwise_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartCentral_pairwise_disjoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartCentral_pairwise_disjoint

theorem buffer_disjoint_iff_neckChartTail_disjoint (G : GeometricCutoffRecord H i parameters) :
    (∀ α β, α ≠ β →
        Disjoint (Set.range (G.neck α).chart) (Set.range (G.neck β).chart)) ↔
      ∀ α β, α ≠ β → Disjoint (neckChartTail G α) (Set.range (G.neck β).chart) :=
  buffer_disjoint_iff_neckChartTail_disjoint_of G.delta G.order G.neck G.tube_eq
    G.tube_in_buffer

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.buffer_disjoint_iff_neckChartTail_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.buffer_disjoint_iff_neckChartTail_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.buffer_disjoint_iff_neckChartTail_disjoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.buffer_disjoint_iff_neckChartTail_disjoint

theorem neckChartTail_nonempty (G : GeometricCutoffRecord H i parameters)
    (α : (H.event i).transition.trace.tubes.Index) : (neckChartTail G α).Nonempty :=
  neckChartTail_nonempty_of G.delta G.order G.neck α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartTail_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartTail_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartTail_nonempty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartTail_nonempty

end GeometricCutoffRecord

namespace TerminalCorePresentation

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ}

def hornHalfRange (P : TerminalCorePresentation D ε Λ)
    (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c) :
    Set ↥D.slab.terminalRegularOpen :=
  Set.range fun p : HalfNeckCylinder => P.horn c e p.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange

theorem hornHalfRange_mk_eq (P : TerminalCorePresentation D ε Λ)
    (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {x : ↥D.slab.terminalRegularOpen} (hx : x ∈ hornHalfRange P c e) :
    ConnectedComponents.mk x = c := by
  obtain ⟨p, rfl⟩ := hx
  by_cases hc : c ∈ P.component
  · have hcov := P.horn_covers_component c hc
    change P.horn c e p.1 ∈ ({x | ConnectedComponents.mk x = c} : Set _)
    rw [hcov]
    exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨e, Set.mem_range_self p⟩)
  · exact (P.hornIndex_empty c hc).elim e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange_mk_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange_mk_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange_mk_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange_mk_eq

theorem hornHalfRange_disjoint_of_same (P : TerminalCorePresentation D ε Λ)
    {c : ConnectedComponents ↥D.slab.terminalRegularOpen} {e e' : P.hornIndex c}
    (h : e ≠ e') :
    Disjoint (hornHalfRange P c e) (hornHalfRange P c e') := by
  simpa only [hornHalfRange] using P.horn_range_disjoint c e e' h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange_disjoint_of_same then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange_disjoint_of_same"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange_disjoint_of_same ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange_disjoint_of_same

theorem hornHalfRange_disjoint_of_ne (P : TerminalCorePresentation D ε Λ)
    {c c' : ConnectedComponents ↥D.slab.terminalRegularOpen} (h : c ≠ c')
    (e : P.hornIndex c) (e' : P.hornIndex c') :
    Disjoint (hornHalfRange P c e) (hornHalfRange P c' e') := by
  refine Set.disjoint_left.mpr fun x hx hx' => h ?_
  rw [← hornHalfRange_mk_eq P c e hx, ← hornHalfRange_mk_eq P c' e' hx']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange_disjoint_of_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange_disjoint_of_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange_disjoint_of_ne ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange_disjoint_of_ne

theorem hornHalfRange_pairwise_disjoint (P : TerminalCorePresentation D ε Λ) :
    Pairwise fun ce ce' :
        (c : ConnectedComponents ↥D.slab.terminalRegularOpen) × P.hornIndex c =>
      Disjoint (hornHalfRange P ce.1 ce.2) (hornHalfRange P ce'.1 ce'.2) := by
  intro ce ce' hne
  obtain ⟨c, e⟩ := ce
  obtain ⟨c', e'⟩ := ce'
  by_cases hcc : c = c'
  · subst hcc
    refine hornHalfRange_disjoint_of_same P (fun h => hne ?_)
    cases h
    rfl
  · exact hornHalfRange_disjoint_of_ne P hcc e e'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange_pairwise_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange_pairwise_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange_pairwise_disjoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.hornHalfRange_pairwise_disjoint

end TerminalCorePresentation

namespace GeometricCutoffRecord

structure NeckTubeIndexBridge (G : GeometricCutoffRecord H i parameters)
    {ε Λ : ℝ} (P : TerminalCorePresentation (OneStepIncoming.ofRecord G) ε Λ) where
  indexEquiv : (H.event i).transition.trace.tubes.Index ≃
    (c : ConnectedComponents ↥(H.event i).incoming.terminalRegularOpen) × P.hornIndex c
  chartTail_subset_horn : ∀ α,
    neckChartTail G α ⊆
      TerminalCorePresentation.hornHalfRange P (indexEquiv α).1 (indexEquiv α).2
  chartTail_disjoint_central : ∀ α β, α ≠ β →
    Disjoint (neckChartTail G α) (neckChartCentral G β)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.NeckTubeIndexBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.NeckTubeIndexBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.NeckTubeIndexBridge ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.NeckTubeIndexBridge

theorem neckChartTail_pairwise_disjoint_of_indexBridge {G : GeometricCutoffRecord H i parameters}
    {ε Λ : ℝ} {P : TerminalCorePresentation (OneStepIncoming.ofRecord G) ε Λ}
    (B : NeckTubeIndexBridge G P) :
    ∀ α β, α ≠ β → Disjoint (neckChartTail G α) (neckChartTail G β) := by
  intro α β h
  have hne : B.indexEquiv α ≠ B.indexEquiv β := fun hh => h (B.indexEquiv.injective hh)
  exact (TerminalCorePresentation.hornHalfRange_pairwise_disjoint P hne).mono
    (B.chartTail_subset_horn α) (B.chartTail_subset_horn β)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartTail_pairwise_disjoint_of_indexBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartTail_pairwise_disjoint_of_indexBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartTail_pairwise_disjoint_of_indexBridge ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.neckChartTail_pairwise_disjoint_of_indexBridge

theorem buffer_disjoint_of_indexBridge {G : GeometricCutoffRecord H i parameters}
    {ε Λ : ℝ} {P : TerminalCorePresentation (OneStepIncoming.ofRecord G) ε Λ}
    (B : NeckTubeIndexBridge G P) :
    Pairwise fun α β => Disjoint (Set.range (G.neck α).chart) (Set.range (G.neck β).chart) := by
  refine (buffer_disjoint_iff_neckChartTail_disjoint G).mpr fun α β hab => ?_
  rw [neckChart_eq_central_union_tail G β]
  exact disjoint_union_right.mpr ⟨B.chartTail_disjoint_central α β hab,
    neckChartTail_pairwise_disjoint_of_indexBridge B α β hab⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.buffer_disjoint_of_indexBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.buffer_disjoint_of_indexBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.buffer_disjoint_of_indexBridge ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.buffer_disjoint_of_indexBridge

theorem nonempty_neckTubeIndexBridge_of_isEmpty {G : GeometricCutoffRecord H i parameters}
    {ε Λ : ℝ} {P : TerminalCorePresentation (OneStepIncoming.ofRecord G) ε Λ}
    [IsEmpty (H.event i).transition.trace.tubes.Index]
    [IsEmpty ((c : ConnectedComponents ↥(H.event i).incoming.terminalRegularOpen) ×
      P.hornIndex c)] :
    Nonempty (NeckTubeIndexBridge G P) :=
  ⟨{ indexEquiv := Equiv.equivOfIsEmpty _ _
     chartTail_subset_horn := fun α => isEmptyElim α
     chartTail_disjoint_central := fun α => isEmptyElim α }⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.nonempty_neckTubeIndexBridge_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.nonempty_neckTubeIndexBridge_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.nonempty_neckTubeIndexBridge_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.nonempty_neckTubeIndexBridge_of_isEmpty

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
