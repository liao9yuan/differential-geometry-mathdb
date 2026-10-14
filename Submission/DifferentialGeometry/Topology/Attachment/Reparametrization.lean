import Submission.DifferentialGeometry.Topology.Attachment.Basic
import Mathlib.Topology.Homeomorph.Quotient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.Topology

universe u v w t

variable {A : Type u} {A' : Type v} {B : Type w} {X : Type t}

theorem adjunctionRel_comp_equiv (i : A → B) (φ : A → X) (e : A' ≃ A) (x y : B ⊕ X) :
    adjunctionRel (i ∘ e) (φ ∘ e) x y ↔ adjunctionRel i φ x y := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨e a, h⟩
  · rintro ⟨a, h⟩
    refine ⟨e.symm a, ?_⟩
    simpa only [Function.comp_apply, e.apply_symm_apply] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionRel_comp_equiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionRel_comp_equiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionRel_comp_equiv ``Submission.DifferentialGeometry.Topology.adjunctionRel_comp_equiv

variable [TopologicalSpace B] [TopologicalSpace X]

def adjunctionHomeomorphOfBoundaryEquiv (i : A → B) (φ : A → X) (e : A' ≃ A) :
    AdjunctionSpace (i ∘ e) (φ ∘ e) ≃ₜ AdjunctionSpace i φ :=
  Homeomorph.Quot.congrRight (adjunctionRel_comp_equiv i φ e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionHomeomorphOfBoundaryEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionHomeomorphOfBoundaryEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionHomeomorphOfBoundaryEquiv ``Submission.DifferentialGeometry.Topology.adjunctionHomeomorphOfBoundaryEquiv

@[simp] theorem adjunctionHomeomorphOfBoundaryEquiv_cell
    (i : A → B) (φ : A → X) (e : A' ≃ A) (b : B) :
    adjunctionHomeomorphOfBoundaryEquiv i φ e (adjunctionCell (i ∘ e) (φ ∘ e) b) =
      adjunctionCell i φ b := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionHomeomorphOfBoundaryEquiv_cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionHomeomorphOfBoundaryEquiv_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionHomeomorphOfBoundaryEquiv_cell ``Submission.DifferentialGeometry.Topology.adjunctionHomeomorphOfBoundaryEquiv_cell

@[simp] theorem adjunctionHomeomorphOfBoundaryEquiv_lower
    (i : A → B) (φ : A → X) (e : A' ≃ A) (x : X) :
    adjunctionHomeomorphOfBoundaryEquiv i φ e (adjunctionLower (i := i ∘ e) (φ ∘ e) x) =
      adjunctionLower (i := i) φ x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionHomeomorphOfBoundaryEquiv_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionHomeomorphOfBoundaryEquiv_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionHomeomorphOfBoundaryEquiv_lower ``Submission.DifferentialGeometry.Topology.adjunctionHomeomorphOfBoundaryEquiv_lower

variable {B' : Type*} [TopologicalSpace B']

def adjunctionHomeomorphOfCellEquiv (i : A → B) (φ : A → X) (h : B ≃ₜ B') :
    AdjunctionSpace i φ ≃ₜ AdjunctionSpace (h ∘ i) φ :=
  Homeomorph.Quot.congr (h.sumCongr (Homeomorph.refl X)) (fun x y => by
    cases x <;> cases y <;> simp [adjunctionRel, Homeomorph.sumCongr, h.injective.eq_iff])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv ``Submission.DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv

@[simp] theorem adjunctionHomeomorphOfCellEquiv_cell
    (i : A → B) (φ : A → X) (h : B ≃ₜ B') (b : B) :
    adjunctionHomeomorphOfCellEquiv i φ h (adjunctionCell i φ b) =
      adjunctionCell (h ∘ i) φ (h b) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv_cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv_cell ``Submission.DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv_cell

@[simp] theorem adjunctionHomeomorphOfCellEquiv_lower
    (i : A → B) (φ : A → X) (h : B ≃ₜ B') (x : X) :
    adjunctionHomeomorphOfCellEquiv i φ h (adjunctionLower (i := i) φ x) =
      adjunctionLower (i := h ∘ i) φ x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv_lower ``Submission.DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv_lower

@[simp] theorem adjunctionHomeomorphOfCellEquiv_symm_cell
    (i : A → B) (φ : A → X) (h : B ≃ₜ B') (b : B') :
    (adjunctionHomeomorphOfCellEquiv i φ h).symm (adjunctionCell (h ∘ i) φ b) =
      adjunctionCell i φ (h.symm b) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv_symm_cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv_symm_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv_symm_cell ``Submission.DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv_symm_cell

@[simp] theorem adjunctionHomeomorphOfCellEquiv_symm_lower
    (i : A → B) (φ : A → X) (h : B ≃ₜ B') (x : X) :
    (adjunctionHomeomorphOfCellEquiv i φ h).symm (adjunctionLower (i := h ∘ i) φ x) =
      adjunctionLower (i := i) φ x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv_symm_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv_symm_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv_symm_lower ``Submission.DifferentialGeometry.Topology.adjunctionHomeomorphOfCellEquiv_symm_lower

end DifferentialGeometry.Topology
