import Submission.DifferentialGeometry.Topology.Attachment.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.Topology.Manifold.Attachment
variable {A B X : Type*}

private def representative (i : A → B) (φ : A → X) : B ⊕ X → B ⊕ X := by
  classical
  exact fun p => match p with
    | Sum.inl b => if h : ∃ a, i a = b then Sum.inr (φ (Classical.choose h)) else Sum.inl b
    | Sum.inr x => Sum.inr x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.representative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.representative target :: scope.openDecls } }
private theorem representative_boundary (i : A → B) (φ : A → X) (hi : _root_.Function.Injective i) (a : A) :
    representative i φ (Sum.inl (i a)) = Sum.inr (φ a) := by
  have h : ∃ b, i b = i a := ⟨a, rfl⟩
  simp only [representative, dif_pos h]
  exact congrArg (fun b => Sum.inr (φ b)) (hi (Classical.choose_spec h))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.representative_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.representative_boundary target :: scope.openDecls } }
private theorem representative_rel (i : A → B) (φ : A → X) (hi : _root_.Function.Injective i)
    (x y : B ⊕ X) (h : adjunctionRel i φ x y) : representative i φ x = representative i φ y := by
  obtain ⟨a, h | h⟩ := h
  · rcases h with ⟨rfl, rfl⟩
    exact representative_boundary i φ hi a
  · rcases h with ⟨rfl, rfl⟩
    exact (representative_boundary i φ hi a).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.representative_rel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.representative_rel target :: scope.openDecls } }
private def quotientRepresentative (i : A → B) (φ : A → X) (hi : _root_.Function.Injective i) :
    AdjunctionSpace i φ → B ⊕ X := Quot.lift (representative i φ) (representative_rel i φ hi)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.quotientRepresentative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.quotientRepresentative target :: scope.openDecls } }

theorem adjunctionLower_injective (i : A → B) (φ : A → X) (hi : _root_.Function.Injective i) :
    Injective (adjunctionLower (i := i) φ) := by
  intro x y he
  have hh := congrArg (quotientRepresentative i φ hi) he
  exact Sum.inr_injective hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.adjunctionLower_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.adjunctionLower_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.adjunctionLower_injective ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.adjunctionLower_injective

theorem adjunctionCell_eq_lower_iff (i : A → B) (φ : A → X) (hi : _root_.Function.Injective i) (b : B) (x : X) :
    adjunctionCell i φ b = adjunctionLower φ x ↔ ∃ a : A, i a = b ∧ φ a = x := by
  classical
  constructor
  · intro he
    have hh := congrArg (quotientRepresentative i φ hi) he
    change representative i φ (Sum.inl b) = Sum.inr x at hh
    by_cases hb : ∃ a, i a = b
    · rw [representative, dif_pos hb] at hh
      exact ⟨Classical.choose hb, Classical.choose_spec hb, Sum.inr_injective hh⟩
    · rw [representative, dif_neg hb] at hh
      cases hh
  · rintro ⟨a, rfl, rfl⟩
    exact adjunction_coherence i φ a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.adjunctionCell_eq_lower_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.adjunctionCell_eq_lower_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.adjunctionCell_eq_lower_iff ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.adjunctionCell_eq_lower_iff

theorem adjunctionCell_injective (i : A → B) (φ : A → X) (hi : _root_.Function.Injective i) (hφ : _root_.Function.Injective φ) :
    Injective (adjunctionCell i φ) := by
  classical
  intro b c he
  have hh := congrArg (quotientRepresentative i φ hi) he
  change representative i φ (Sum.inl b) = representative i φ (Sum.inl c) at hh
  by_cases hb : ∃ a, i a = b
  · by_cases hc : ∃ a, i a = c
    · rw [representative, dif_pos hb, representative, dif_pos hc] at hh
      have ha := hφ (Sum.inr_injective hh)
      exact (Classical.choose_spec hb).symm.trans ((congrArg i ha).trans (Classical.choose_spec hc))
    · rw [representative, dif_pos hb, representative, dif_neg hc] at hh
      cases hh
  · by_cases hc : ∃ a, i a = c
    · rw [representative, dif_neg hb, representative, dif_pos hc] at hh
      cases hh
    · rw [representative, dif_neg hb, representative, dif_neg hc] at hh
      exact Sum.inl_injective hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.adjunctionCell_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.adjunctionCell_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.adjunctionCell_injective ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.adjunctionCell_injective

theorem adjunction_inclusions_cover (i : A → B) (φ : A → X) :
    range (adjunctionCell i φ) ∪ _root_.Set.range (adjunctionLower (i := i) φ) = univ := by
  apply _root_.Set.eq_univ_of_forall
  intro q
  induction q using Quot.inductionOn with
  | h p =>
    cases p with
    | inl b => exact Or.inl ⟨b, rfl⟩
    | inr x => exact Or.inr ⟨x, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.adjunction_inclusions_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.adjunction_inclusions_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.adjunction_inclusions_cover ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.adjunction_inclusions_cover

theorem adjunction_inclusions_inter (i : A → B) (φ : A → X) (hi : _root_.Function.Injective i) :
    range (adjunctionCell i φ) ∩ _root_.Set.range (adjunctionLower (i := i) φ) =
      range (adjunctionCell i φ ∘ i) := by
  ext q
  constructor
  · rintro ⟨⟨b, rfl⟩, ⟨x, hx⟩⟩
    obtain ⟨a, ha, _⟩ := (adjunctionCell_eq_lower_iff i φ hi b x).mp hx.symm
    exact ⟨a, congrArg (adjunctionCell i φ) ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨i a, rfl⟩, ⟨φ a, (adjunction_coherence i φ a).symm⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.adjunction_inclusions_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.adjunction_inclusions_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.adjunction_inclusions_inter ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.adjunction_inclusions_inter
end DifferentialGeometry.Topology.Manifold.Attachment
