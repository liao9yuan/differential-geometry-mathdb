import Submission.DifferentialGeometry.Topology.Attachment.Defs
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Constructions
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Maps.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology

universe u v w t

open _root_.Filter _root_.Function _root_.Set

instance _root_.Submission.DifferentialGeometry.Topology.instCompactSpaceClosedCell (n : ℕ) : CompactSpace (ClosedCell n) := by
  have h : IsCompact ({x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ 1} : Set (EuclideanSpace ℝ (Fin n))) := by
    have heq : ({x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ 1} : Set _) =
        Metric.closedBall 0 1 := by
      ext x
      simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
    rw [heq]
    exact _root_.ProperSpace.isCompact_closedBall (x := (0 : EuclideanSpace ℝ (Fin n))) (r := 1)
  exact isCompact_iff_compactSpace.mp h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.instCompactSpaceClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.instCompactSpaceClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.instCompactSpaceClosedCell ``Submission.DifferentialGeometry.Topology.instCompactSpaceClosedCell

instance _root_.Submission.DifferentialGeometry.Topology.instCompactSpaceCellBoundary (n : ℕ) : CompactSpace (CellBoundary n) := by
  have h : IsCompact ({x : EuclideanSpace ℝ (Fin n) | ‖x‖ = 1} : Set (EuclideanSpace ℝ (Fin n))) := by
    have heq : ({x : EuclideanSpace ℝ (Fin n) | ‖x‖ = 1} : Set _) =
        Metric.sphere 0 1 := by
      ext x
      simp only [Set.mem_ofPred_eq, Metric.mem_sphere, dist_zero_right]
    rw [heq]
    exact isCompact_sphere (x := (0 : EuclideanSpace ℝ (Fin n))) (r := 1)
  exact isCompact_iff_compactSpace.mp h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.instCompactSpaceCellBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.instCompactSpaceCellBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.instCompactSpaceCellBoundary ``Submission.DifferentialGeometry.Topology.instCompactSpaceCellBoundary

theorem continuous_cellBoundaryInclusion (n : ℕ) : Continuous (cellBoundaryInclusion n) := by
  exact continuous_subtype_val.subtype_mk (p := fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ≤ 1)
    (fun x : CellBoundary n => le_of_eq x.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_cellBoundaryInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_cellBoundaryInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_cellBoundaryInclusion ``Submission.DifferentialGeometry.Topology.continuous_cellBoundaryInclusion

theorem injective_cellBoundaryInclusion (n : ℕ) : Function.Injective (cellBoundaryInclusion n) := by
  intro x y h
  have hval : (x : EuclideanSpace ℝ (Fin n)) = (y : EuclideanSpace ℝ (Fin n)) := by
    simpa [cellBoundaryInclusion] using
      congrArg (fun z : ClosedCell n => (z : EuclideanSpace ℝ (Fin n))) h
  apply Subtype.ext
  exact hval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.injective_cellBoundaryInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.injective_cellBoundaryInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.injective_cellBoundaryInclusion ``Submission.DifferentialGeometry.Topology.injective_cellBoundaryInclusion

theorem range_closedCell (n : ℕ) :
    Set.range (fun x : ClosedCell n => (x : EuclideanSpace ℝ (Fin n))) =
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp [Metric.closedBall]
  · intro hx
    exact ⟨⟨x, by simpa [Metric.closedBall] using hx⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.range_closedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.range_closedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.range_closedCell ``Submission.DifferentialGeometry.Topology.range_closedCell

theorem range_cellBoundary (n : ℕ) :
    Set.range (fun x : CellBoundary n => (x : EuclideanSpace ℝ (Fin n))) =
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp [Metric.sphere]
  · intro hx
    exact ⟨⟨x, by simpa [Metric.sphere] using hx⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.range_cellBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.range_cellBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.range_cellBoundary ``Submission.DifferentialGeometry.Topology.range_cellBoundary

section AdjunctionSpace

variable {A : Type v} {B : Type w} [TopologicalSpace B] {X : Type u} [TopologicalSpace X]

theorem continuous_adjunctionMk (i : A → B) (φ : A → X) : Continuous (adjunctionMk i φ) :=
  continuous_quot_mk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_adjunctionMk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_adjunctionMk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_adjunctionMk ``Submission.DifferentialGeometry.Topology.continuous_adjunctionMk

theorem continuous_adjunctionLower (i : A → B) (φ : A → X) :
    Continuous (adjunctionLower (i := i) φ) :=
  continuous_quot_mk.comp continuous_inr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_adjunctionLower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_adjunctionLower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_adjunctionLower ``Submission.DifferentialGeometry.Topology.continuous_adjunctionLower

theorem continuous_adjunctionCell (i : A → B) (φ : A → X) : Continuous (adjunctionCell i φ) :=
  continuous_quot_mk.comp continuous_inl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_adjunctionCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_adjunctionCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_adjunctionCell ``Submission.DifferentialGeometry.Topology.continuous_adjunctionCell

theorem isQuotientMap_adjunctionMk (i : A → B) (φ : A → X) :
    Topology.IsQuotientMap (adjunctionMk i φ) :=
  isQuotientMap_quot_mk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isQuotientMap_adjunctionMk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isQuotientMap_adjunctionMk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isQuotientMap_adjunctionMk ``Submission.DifferentialGeometry.Topology.isQuotientMap_adjunctionMk

theorem continuous_adjunction_lift (i : A → B) (φ : A → X) {Y : Type t} [TopologicalSpace Y]
    {f : B ⊕ X → Y}
    (hr : ∀ a b : B ⊕ X, adjunctionRel i φ a b → f a = f b) (hf : Continuous f) :
    Continuous (Quot.lift f hr : AdjunctionSpace i φ → Y) :=
  continuous_quot_lift hr hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_adjunction_lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_adjunction_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_adjunction_lift ``Submission.DifferentialGeometry.Topology.continuous_adjunction_lift

theorem adjunction_cell_eq_lower_iff {A : Type v} {B : Type w} {X : Type u}
    (i : A → B) (φ : A → X) (hφ : Function.Injective φ) (b : B) (x : X) :
    adjunctionCell i φ b = adjunctionLower φ x ↔ ∃ a, i a = b ∧ φ a = x := by
  have key : ∀ a : A, (i a = b) = (∃ a', i a' = b ∧ φ a' = φ a) := by
    intro a
    apply propext
    constructor
    · intro h
      exact ⟨a, h, rfl⟩
    · rintro ⟨a', ha', hφ'⟩
      exact ((congrArg i (hφ hφ')).symm).trans ha'
  constructor
  · intro h
    let f : B ⊕ X → Prop := Sum.elim (fun b' => b' = b)
      (fun x' => ∃ a, i a = b ∧ φ a = x')
    have hf : ∀ u v, adjunctionRel i φ u v → f u = f v := by
      rintro u v ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact key a
      · exact (key a).symm
    let g : AdjunctionSpace i φ → Prop := Quot.lift f hf
    have hh := congrArg g h
    change f (Sum.inl b) = f (Sum.inr x) at hh
    change (b = b) = (∃ a, i a = b ∧ φ a = x) at hh
    exact Eq.mp hh rfl
  · rintro ⟨a, rfl, rfl⟩
    exact adjunction_coherence i φ a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunction_cell_eq_lower_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunction_cell_eq_lower_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunction_cell_eq_lower_iff ``Submission.DifferentialGeometry.Topology.adjunction_cell_eq_lower_iff

theorem connectedSpace_adjunctionSpace {A : Type*} {B : Type*} {X : Type*}
    [TopologicalSpace B] [TopologicalSpace X] [ConnectedSpace B] [ConnectedSpace X] [Nonempty A]
    (i : A → B) (φ : A → X) : ConnectedSpace (AdjunctionSpace i φ) := by
  have hcov : Set.range (adjunctionCell i φ) ∪ Set.range (adjunctionLower (i := i) φ) = univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    exact Quot.induction_on q fun s => by
      cases s with
      | inl b => exact Or.inl ⟨b, rfl⟩
      | inr x => exact Or.inr ⟨x, rfl⟩
  obtain ⟨z⟩ := ‹Nonempty A›
  have hne : (Set.range (adjunctionCell i φ) ∩
      Set.range (adjunctionLower (i := i) φ)).Nonempty :=
    ⟨adjunctionCell i φ (i z),
      ⟨⟨i z, rfl⟩, ⟨φ z, (adjunction_coherence i φ z).symm⟩⟩⟩
  rw [connectedSpace_iff_univ, ← hcov]
  exact IsConnected.union hne (isConnected_range (continuous_adjunctionCell i φ))
    (isConnected_range (continuous_adjunctionLower i φ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSpace_adjunctionSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSpace_adjunctionSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSpace_adjunctionSpace ``Submission.DifferentialGeometry.Topology.connectedSpace_adjunctionSpace

theorem pathConnectedSpace_adjunctionSpace {A : Type*} {B : Type*} {X : Type*}
    [TopologicalSpace B] [TopologicalSpace X] [PathConnectedSpace B] [PathConnectedSpace X]
    [Nonempty A] (i : A → B) (φ : A → X) : PathConnectedSpace (AdjunctionSpace i φ) := by
  have hcov : Set.range (adjunctionCell i φ) ∪ Set.range (adjunctionLower (i := i) φ) = univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    exact Quot.induction_on q fun s => by
      cases s with
      | inl b => exact Or.inl ⟨b, rfl⟩
      | inr x => exact Or.inr ⟨x, rfl⟩
  obtain ⟨z⟩ := ‹Nonempty A›
  have hne : (Set.range (adjunctionCell i φ) ∩
      Set.range (adjunctionLower (i := i) φ)).Nonempty :=
    ⟨adjunctionCell i φ (i z),
      ⟨⟨i z, rfl⟩, ⟨φ z, (adjunction_coherence i φ z).symm⟩⟩⟩
  rw [pathConnectedSpace_iff_univ, ← hcov]
  exact IsPathConnected.union (isPathConnected_range (continuous_adjunctionCell i φ))
    (isPathConnected_range (continuous_adjunctionLower i φ)) hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathConnectedSpace_adjunctionSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathConnectedSpace_adjunctionSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathConnectedSpace_adjunctionSpace ``Submission.DifferentialGeometry.Topology.pathConnectedSpace_adjunctionSpace

end AdjunctionSpace

end DifferentialGeometry.Topology
