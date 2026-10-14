import Submission.DifferentialGeometry.Topology.Manifold.Attachment.AdjunctionSeparation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function

namespace DifferentialGeometry.Topology

universe uA uB uX

variable {A : Type uA} {B : Type uB} {X : Type uX}

private def adjunctionRestrictionMap (i : A → B) (φ : A → X)
    (T : Set X) (hφT : ∀ a, φ a ∈ T) :
    AdjunctionSpace i (fun a => (⟨φ a, hφT a⟩ : T)) → AdjunctionSpace i φ :=
  Quot.lift (Sum.elim (adjunctionCell i φ) (fun x : T => adjunctionLower (i := i) φ x.val)) (by
    rintro _ _ ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact adjunction_coherence i φ a
    · exact (adjunction_coherence i φ a).symm)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.adjunctionRestrictionMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.adjunctionRestrictionMap target :: scope.openDecls } }

private theorem adjunctionRestrictionMap_not_mem
    (i : A → B) (φ : A → X) (hi : _root_.Function.Injective i)
    (T : Set X) (hφT : ∀ a, φ a ∈ T)
    (q : AdjunctionSpace i (fun a => (⟨φ a, hφT a⟩ : T))) :
    adjunctionRestrictionMap i φ T hφT q ∉ adjunctionLower (i := i) φ '' Tᶜ := by
  induction q using Quot.inductionOn with
  | h p =>
    cases p with
    | inl b =>
      rintro ⟨x, hx, he⟩
      obtain ⟨a, _, ha⟩ :=
        (Manifold.Attachment.adjunctionCell_eq_lower_iff i φ hi b x).mp he.symm
      exact hx (ha ▸ hφT a)
    | inr x =>
      rintro ⟨y, hy, he⟩
      have hyx := Manifold.Attachment.adjunctionLower_injective i φ hi he
      exact hy (hyx.symm ▸ x.property)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.adjunctionRestrictionMap_not_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.adjunctionRestrictionMap_not_mem target :: scope.openDecls } }

private theorem adjunctionRestrictionMap_injective
    (i : A → B) (φ : A → X) (hi : _root_.Function.Injective i) (hφ : _root_.Function.Injective φ)
    (T : Set X) (hφT : ∀ a, φ a ∈ T) :
    Injective (adjunctionRestrictionMap i φ T hφT) := by
  intro q r
  induction q using Quot.inductionOn with
  | h p =>
    induction r using Quot.inductionOn with
    | h s =>
      cases p with
      | inl b =>
        cases s with
        | inl b' =>
          intro h
          exact congrArg (adjunctionCell i (fun a => (⟨φ a, hφT a⟩ : T)))
            (Manifold.Attachment.adjunctionCell_injective i φ hi hφ h)
        | inr x =>
          intro h
          obtain ⟨a, ha, hx⟩ :=
            (Manifold.Attachment.adjunctionCell_eq_lower_iff i φ hi b x.val).mp h
          have he : (⟨φ a, hφT a⟩ : T) = x := Subtype.ext hx
          rw [← ha, ← he]
          exact adjunction_coherence i (fun a => (⟨φ a, hφT a⟩ : T)) a
      | inr x =>
        cases s with
        | inl b =>
          intro h
          obtain ⟨a, ha, hx⟩ :=
            (Manifold.Attachment.adjunctionCell_eq_lower_iff i φ hi b x.val).mp h.symm
          have he : (⟨φ a, hφT a⟩ : T) = x := Subtype.ext hx
          rw [← ha, ← he]
          exact (adjunction_coherence i (fun a => (⟨φ a, hφT a⟩ : T)) a).symm
        | inr y =>
          intro h
          exact congrArg (adjunctionLower (i := i) (fun a => (⟨φ a, hφT a⟩ : T)))
            (Subtype.ext (Manifold.Attachment.adjunctionLower_injective i φ hi h))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.adjunctionRestrictionMap_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.adjunctionRestrictionMap_injective target :: scope.openDecls } }

private def adjunctionRestrictionToSubtype
    (i : A → B) (φ : A → X) (hi : _root_.Function.Injective i)
    (T : Set X) (hφT : ∀ a, φ a ∈ T) :
    AdjunctionSpace i (fun a => (⟨φ a, hφT a⟩ : T)) →
      {q : AdjunctionSpace i φ // q ∉ adjunctionLower (i := i) φ '' Tᶜ} :=
  fun q => ⟨adjunctionRestrictionMap i φ T hφT q,
    adjunctionRestrictionMap_not_mem i φ hi T hφT q⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.adjunctionRestrictionToSubtype
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.adjunctionRestrictionToSubtype target :: scope.openDecls } }

private theorem adjunctionRestrictionToSubtype_surjective
    (i : A → B) (φ : A → X) (hi : _root_.Function.Injective i)
    (T : Set X) (hφT : ∀ a, φ a ∈ T) :
    Surjective (adjunctionRestrictionToSubtype i φ hi T hφT) := by
  intro q
  obtain ⟨p, hp⟩ := Quot.exists_rep q.val
  cases p with
  | inl b =>
    refine ⟨adjunctionCell i (fun a => (⟨φ a, hφT a⟩ : T)) b, ?_⟩
    exact Subtype.ext hp
  | inr x =>
    have hx : x ∈ T := by
      by_contra h
      exact q.property ⟨x, h, hp⟩
    refine ⟨adjunctionLower (i := i) (fun a => (⟨φ a, hφT a⟩ : T)) ⟨x, hx⟩, ?_⟩
    exact Subtype.ext hp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.adjunctionRestrictionToSubtype_surjective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.adjunctionRestrictionToSubtype_surjective target :: scope.openDecls } }

variable [TopologicalSpace B] [TopologicalSpace X]

private theorem continuous_adjunctionRestrictionToSubtype
    (i : A → B) (φ : A → X) (hi : _root_.Function.Injective i)
    (T : Set X) (hφT : ∀ a, φ a ∈ T) :
    Continuous (adjunctionRestrictionToSubtype i φ hi T hφT) := by
  apply Continuous.subtype_mk
  exact continuous_adjunction_lift i (fun a => (⟨φ a, hφT a⟩ : T)) _
    (Continuous.sumElim (continuous_adjunctionCell i φ)
      ((continuous_adjunctionLower i φ).comp continuous_subtype_val))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.continuous_adjunctionRestrictionToSubtype
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.continuous_adjunctionRestrictionToSubtype target :: scope.openDecls } }

variable [TopologicalSpace A] [CompactSpace A] [CompactSpace B] [CompactSpace X]
  [T2Space B] [T2Space X]

def adjunctionClosedRestrictionHomeomorph
    (i : A → B) (φ : A → X) (hi : _root_.Function.Injective i) (hφ : _root_.Function.Injective φ)
    (hci : Continuous i) (hcφ : Continuous φ)
    (T : Set X) (hT : IsClosed T) (hφT : ∀ a, φ a ∈ T) :
    AdjunctionSpace i (fun a => (⟨φ a, hφT a⟩ : T)) ≃ₜ
      {q : AdjunctionSpace i φ // q ∉ adjunctionLower (i := i) φ '' Tᶜ} := by
  let _ : CompactSpace T := isCompact_iff_compactSpace.mp hT.isCompact
  let _ : T2Space (AdjunctionSpace i φ) :=
    Manifold.Attachment.adjunction_t2Space i φ hi hφ hci hcφ
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (adjunctionRestrictionToSubtype i φ hi T hφT)
      ⟨fun q r h => adjunctionRestrictionMap_injective i φ hi hφ T hφT
        (congrArg Subtype.val h), adjunctionRestrictionToSubtype_surjective i φ hi T hφT⟩)
    (continuous_adjunctionRestrictionToSubtype i φ hi T hφT)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph ``Submission.DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph

@[simp] theorem adjunctionClosedRestrictionHomeomorph_cell
    (i : A → B) (φ : A → X) (hi : _root_.Function.Injective i) (hφ : _root_.Function.Injective φ)
    (hci : Continuous i) (hcφ : Continuous φ)
    (T : Set X) (hT : IsClosed T) (hφT : ∀ a, φ a ∈ T) (b : B) :
    (adjunctionClosedRestrictionHomeomorph i φ hi hφ hci hcφ T hT hφT
      (adjunctionCell i (fun a => (⟨φ a, hφT a⟩ : T)) b)).val = adjunctionCell i φ b := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph_cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph_cell ``Submission.DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph_cell

@[simp] theorem adjunctionClosedRestrictionHomeomorph_lower
    (i : A → B) (φ : A → X) (hi : _root_.Function.Injective i) (hφ : _root_.Function.Injective φ)
    (hci : Continuous i) (hcφ : Continuous φ)
    (T : Set X) (hT : IsClosed T) (hφT : ∀ a, φ a ∈ T) (x : T) :
    (adjunctionClosedRestrictionHomeomorph i φ hi hφ hci hcφ T hT hφT
      (adjunctionLower (i := i) (fun a => (⟨φ a, hφT a⟩ : T)) x)).val =
      adjunctionLower (i := i) φ x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph_lower ``Submission.DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph_lower

@[simp] theorem adjunctionClosedRestrictionHomeomorph_symm_cell
    (i : A → B) (φ : A → X) (hi : _root_.Function.Injective i) (hφ : _root_.Function.Injective φ)
    (hci : Continuous i) (hcφ : Continuous φ)
    (T : Set X) (hT : IsClosed T) (hφT : ∀ a, φ a ∈ T) (b : B)
    (hb : adjunctionCell i φ b ∉ adjunctionLower (i := i) φ '' Tᶜ) :
    (adjunctionClosedRestrictionHomeomorph i φ hi hφ hci hcφ T hT hφT).symm
        ⟨adjunctionCell i φ b, hb⟩ =
      adjunctionCell i (fun a => (⟨φ a, hφT a⟩ : T)) b := by
  apply (adjunctionClosedRestrictionHomeomorph i φ hi hφ hci hcφ T hT hφT).injective
  rw [Homeomorph.apply_symm_apply]
  exact Subtype.ext rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph_symm_cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph_symm_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph_symm_cell ``Submission.DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph_symm_cell

@[simp] theorem adjunctionClosedRestrictionHomeomorph_symm_lower
    (i : A → B) (φ : A → X) (hi : _root_.Function.Injective i) (hφ : _root_.Function.Injective φ)
    (hci : Continuous i) (hcφ : Continuous φ)
    (T : Set X) (hT : IsClosed T) (hφT : ∀ a, φ a ∈ T) (x : T)
    (hx : adjunctionLower (i := i) φ x.val ∉ adjunctionLower (i := i) φ '' Tᶜ) :
    (adjunctionClosedRestrictionHomeomorph i φ hi hφ hci hcφ T hT hφT).symm
        ⟨adjunctionLower (i := i) φ x.val, hx⟩ =
      adjunctionLower (i := i) (fun a => (⟨φ a, hφT a⟩ : T)) x := by
  apply (adjunctionClosedRestrictionHomeomorph i φ hi hφ hci hcφ T hT hφT).injective
  rw [Homeomorph.apply_symm_apply]
  exact Subtype.ext rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph_symm_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph_symm_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph_symm_lower ``Submission.DifferentialGeometry.Topology.adjunctionClosedRestrictionHomeomorph_symm_lower

end DifferentialGeometry.Topology
