import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Constructions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology

universe u v w

abbrev ClosedCell (n : ℕ) : Type :=
  {x : EuclideanSpace ℝ (Fin n) // ‖x‖ ≤ 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedCell ``Submission.DifferentialGeometry.Topology.ClosedCell

abbrev CellBoundary (n : ℕ) : Type :=
  {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.CellBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.CellBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.CellBoundary ``Submission.DifferentialGeometry.Topology.CellBoundary

abbrev CellInterior (n : ℕ) : Type :=
  {x : EuclideanSpace ℝ (Fin n) // ‖x‖ < 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.CellInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.CellInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.CellInterior ``Submission.DifferentialGeometry.Topology.CellInterior

def cellBoundaryInclusion (n : ℕ) : CellBoundary n → ClosedCell n :=
  fun x => ⟨x, le_of_eq x.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cellBoundaryInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cellBoundaryInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cellBoundaryInclusion ``Submission.DifferentialGeometry.Topology.cellBoundaryInclusion

def closedCellCenter (n : ℕ) : ClosedCell n :=
  ⟨0, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.closedCellCenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.closedCellCenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.closedCellCenter ``Submission.DifferentialGeometry.Topology.closedCellCenter

def cellInteriorInclusion (n : ℕ) : CellInterior n → ClosedCell n :=
  fun x => ⟨x, le_of_lt x.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cellInteriorInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cellInteriorInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cellInteriorInclusion ``Submission.DifferentialGeometry.Topology.cellInteriorInclusion

def adjunctionRel {A : Type v} {B : Type w} {X : Type u} (i : A → B) (φ : A → X) :
    B ⊕ X → B ⊕ X → Prop :=
  fun a b =>
    ∃ x : A,
      (a = Sum.inl (i x) ∧ b = Sum.inr (φ x)) ∨
        (b = Sum.inl (i x) ∧ a = Sum.inr (φ x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionRel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionRel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionRel ``Submission.DifferentialGeometry.Topology.adjunctionRel

abbrev AdjunctionSpace {A : Type v} {B : Type w} {X : Type u} (i : A → B) (φ : A → X) :
    Type (max w u) :=
  Quot (adjunctionRel i φ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.AdjunctionSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.AdjunctionSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.AdjunctionSpace ``Submission.DifferentialGeometry.Topology.AdjunctionSpace

def adjunctionMk {A : Type v} {B : Type w} {X : Type u} (i : A → B) (φ : A → X) :
    B ⊕ X → AdjunctionSpace i φ :=
  Quot.mk (adjunctionRel i φ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionMk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionMk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionMk ``Submission.DifferentialGeometry.Topology.adjunctionMk

def adjunctionLower {A : Type v} {B : Type w} {X : Type u} {i : A → B} (φ : A → X) :
    X → AdjunctionSpace i φ :=
  fun x => adjunctionMk i φ (Sum.inr x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionLower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionLower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionLower ``Submission.DifferentialGeometry.Topology.adjunctionLower

def adjunctionCell {A : Type v} {B : Type w} {X : Type u} (i : A → B) (φ : A → X) :
    B → AdjunctionSpace i φ :=
  fun d => adjunctionMk i φ (Sum.inl d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionCell ``Submission.DifferentialGeometry.Topology.adjunctionCell

theorem adjunction_coherence {A : Type v} {B : Type w} {X : Type u} (i : A → B) (φ : A → X)
    (x : A) :
    adjunctionCell i φ (i x) = adjunctionLower φ (φ x) :=
  Quot.sound ⟨x, Or.inl ⟨rfl, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunction_coherence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunction_coherence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunction_coherence ``Submission.DifferentialGeometry.Topology.adjunction_coherence

abbrev CellAdjunctionSpace {X : Type u} (n : ℕ) (φ : CellBoundary n → X) : Type u :=
  AdjunctionSpace (cellBoundaryInclusion n) φ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.CellAdjunctionSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.CellAdjunctionSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.CellAdjunctionSpace ``Submission.DifferentialGeometry.Topology.CellAdjunctionSpace

end DifferentialGeometry.Topology
