import Submission.DifferentialGeometry.Topology.SphereSeparation.BicollarComponents
import Mathlib.Topology.Algebra.Group.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions


def bicollarLowerSide {A M : Type*} [TopologicalSpace M]
    (φ : A × ℝ → M) (a : A) (c : ℝ) : Set M :=
  connectedComponentIn (_root_.Set.range (fun y => φ (y, c)))ᶜ (φ (a, c - 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLowerSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLowerSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLowerSide ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLowerSide


def bicollarUpperSide {A M : Type*} [TopologicalSpace M]
    (φ : A × ℝ → M) (a : A) (c : ℝ) : Set M :=
  connectedComponentIn (_root_.Set.range (fun y => φ (y, c)))ᶜ (φ (a, c + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarUpperSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarUpperSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarUpperSide ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarUpperSide

private theorem bicollar_slice_components_of_sides
    {A M : Type*} [TopologicalSpace M]
    (φ : A × ℝ → M) (a : A) (c : ℝ)
    (B E : Set M)
    (hB : IsConnected B) (hE : IsConnected E) (hBop : IsOpen B) (hEop : IsOpen E)
    (hBE : Disjoint B E) (hcover : B ∪ E = (_root_.Set.range (fun y => φ (y, c)))ᶜ)
    (hBfr : frontier B = _root_.Set.range (fun y => φ (y, c)))
    (hEfr : frontier E = _root_.Set.range (fun y => φ (y, c)))
    (hBcl : closure B = B ∪ _root_.Set.range (fun y => φ (y, c)))
    (hEcl : closure E = E ∪ _root_.Set.range (fun y => φ (y, c)))
    (hcomponents : ∀ x ∈ (_root_.Set.range (fun y => φ (y, c)))ᶜ,
      connectedComponentIn (_root_.Set.range (fun y => φ (y, c)))ᶜ x = B ∨
      connectedComponentIn (_root_.Set.range (fun y => φ (y, c)))ᶜ x = E)
    (hnegative : ∀ y z, z < c → φ (y, z) ∈ B)
    (hpositive : ∀ y z, c < z → φ (y, z) ∈ E) :
    IsConnected (bicollarLowerSide φ a c) ∧ IsConnected (bicollarUpperSide φ a c) ∧
      IsOpen (bicollarLowerSide φ a c) ∧ IsOpen (bicollarUpperSide φ a c) ∧
      Disjoint (bicollarLowerSide φ a c) (bicollarUpperSide φ a c) ∧
      bicollarLowerSide φ a c ∪ bicollarUpperSide φ a c =
        (_root_.Set.range (fun y => φ (y, c)))ᶜ ∧
      frontier (bicollarLowerSide φ a c) = _root_.Set.range (fun y => φ (y, c)) ∧
      frontier (bicollarUpperSide φ a c) = _root_.Set.range (fun y => φ (y, c)) ∧
      closure (bicollarLowerSide φ a c) =
        bicollarLowerSide φ a c ∪ _root_.Set.range (fun y => φ (y, c)) ∧
      closure (bicollarUpperSide φ a c) =
        bicollarUpperSide φ a c ∪ _root_.Set.range (fun y => φ (y, c)) ∧
      (∀ y z, z < c → φ (y, z) ∈ bicollarLowerSide φ a c) ∧
      (∀ y z, c < z → φ (y, z) ∈ bicollarUpperSide φ a c) := by
  have hBlo : φ (a, c - 1) ∈ B := hnegative a (c - 1) (by linarith)
  have hEhi : φ (a, c + 1) ∈ E := hpositive a (c + 1) (by linarith)
  have hloAvoid : φ (a, c - 1) ∈ (_root_.Set.range (fun y => φ (y, c)))ᶜ := by
    rw [← hcover]
    exact Or.inl hBlo
  have hhiAvoid : φ (a, c + 1) ∈ (_root_.Set.range (fun y => φ (y, c)))ᶜ := by
    rw [← hcover]
    exact Or.inr hEhi
  have hlower : bicollarLowerSide φ a c = B := by
    rcases hcomponents _ hloAvoid with hcomp | hcomp
    · exact hcomp
    · have hmem := mem_connectedComponentIn hloAvoid
      rw [hcomp] at hmem
      exact False.elim (Set.disjoint_left.mp hBE hBlo hmem)
  have hupper : bicollarUpperSide φ a c = E := by
    rcases hcomponents _ hhiAvoid with hcomp | hcomp
    · have hmem := mem_connectedComponentIn hhiAvoid
      rw [hcomp] at hmem
      exact False.elim (Set.disjoint_left.mp hBE hmem hEhi)
    · exact hcomp
  rw [hlower, hupper]
  exact ⟨hB, hE, hBop, hEop, hBE, hcover, hBfr, hEfr, hBcl, hEcl,
    hnegative, hpositive⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollar_slice_components_of_sides
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollar_slice_components_of_sides target :: scope.openDecls } }

theorem bicollar_slice_components
    {A M : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
    [TopologicalSpace M] [T2Space M] [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
    (φ : A × ℝ → M) (hφ : _root_.Topology.IsOpenEmbedding φ) (a : A) (c : ℝ) :
    IsConnected (bicollarLowerSide φ a c) ∧ IsConnected (bicollarUpperSide φ a c) ∧
      IsOpen (bicollarLowerSide φ a c) ∧ IsOpen (bicollarUpperSide φ a c) ∧
      Disjoint (bicollarLowerSide φ a c) (bicollarUpperSide φ a c) ∧
      bicollarLowerSide φ a c ∪ bicollarUpperSide φ a c =
        (_root_.Set.range (fun y => φ (y, c)))ᶜ ∧
      frontier (bicollarLowerSide φ a c) = _root_.Set.range (fun y => φ (y, c)) ∧
      frontier (bicollarUpperSide φ a c) = _root_.Set.range (fun y => φ (y, c)) ∧
      closure (bicollarLowerSide φ a c) =
        bicollarLowerSide φ a c ∪ _root_.Set.range (fun y => φ (y, c)) ∧
      closure (bicollarUpperSide φ a c) =
        bicollarUpperSide φ a c ∪ _root_.Set.range (fun y => φ (y, c)) ∧
      (∀ y z, z < c → φ (y, z) ∈ bicollarLowerSide φ a c) ∧
      (∀ y z, c < z → φ (y, z) ∈ bicollarUpperSide φ a c) := by
  let τ : A × ℝ ≃ₜ A × ℝ := (Homeomorph.refl A).prodCongr (Homeomorph.addRight c)
  let ψ : A × ℝ → M := fun p => φ (p.1, p.2 + c)
  have hψ : _root_.Topology.IsOpenEmbedding ψ := hφ.comp τ.isOpenEmbedding
  obtain ⟨B, E, hB, hE, hBop, hEop, hBE, hcover, hBfr, hEfr, hBcl, hEcl,
    hcomponents, hneg, hpos⟩ := bicollar_complement_components ψ hψ
  have hcenter : _root_.Set.range (fun y => ψ (y, 0)) = _root_.Set.range (fun y => φ (y, c)) := by
    simp only [ψ, zero_add]
  rw [hcenter] at hcover hBfr hEfr hBcl hEcl hcomponents
  have hnegative (y : A) (z : ℝ) (hz : z < c) : φ (y, z) ∈ B := by
    have h := hneg y (z - c) (sub_neg.mpr hz)
    simpa only [ψ, sub_add_cancel] using h
  have hpositive (y : A) (z : ℝ) (hz : c < z) : φ (y, z) ∈ E := by
    have h := hpos y (z - c) (sub_pos.mpr hz)
    simpa only [ψ, sub_add_cancel] using h
  exact bicollar_slice_components_of_sides φ a c B E hB hE hBop hEop hBE hcover
    hBfr hEfr hBcl hEcl hcomponents hnegative hpositive

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollar_slice_components then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollar_slice_components"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollar_slice_components ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollar_slice_components

theorem bicollar_slice_components_of_homotopic_disjoint
    {A M : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
    [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [LocallyConnectedSpace M]
    (φ : A × ℝ → M) (hφ : _root_.Topology.IsOpenEmbedding φ)
    (r : C(M, M)) (hr : ContinuousMap.Homotopic r (ContinuousMap.id M))
    (hdisjoint : Disjoint (_root_.Set.range r) (_root_.Set.range (fun y => φ (y, 0)))) (a : A) (c : ℝ) :
    IsConnected (bicollarLowerSide φ a c) ∧ IsConnected (bicollarUpperSide φ a c) ∧
      IsOpen (bicollarLowerSide φ a c) ∧ IsOpen (bicollarUpperSide φ a c) ∧
      Disjoint (bicollarLowerSide φ a c) (bicollarUpperSide φ a c) ∧
      bicollarLowerSide φ a c ∪ bicollarUpperSide φ a c =
        (_root_.Set.range (fun y => φ (y, c)))ᶜ ∧
      frontier (bicollarLowerSide φ a c) = _root_.Set.range (fun y => φ (y, c)) ∧
      frontier (bicollarUpperSide φ a c) = _root_.Set.range (fun y => φ (y, c)) ∧
      closure (bicollarLowerSide φ a c) =
        bicollarLowerSide φ a c ∪ _root_.Set.range (fun y => φ (y, c)) ∧
      closure (bicollarUpperSide φ a c) =
        bicollarUpperSide φ a c ∪ _root_.Set.range (fun y => φ (y, c)) ∧
      (∀ y z, z < c → φ (y, z) ∈ bicollarLowerSide φ a c) ∧
      (∀ y z, c < z → φ (y, z) ∈ bicollarUpperSide φ a c) := by
  obtain ⟨B, E, hB, hE, hBop, hEop, hBE, hcover, hBfr, hEfr, hBcl, hEcl,
    hcomponents, hnegative, hpositive⟩ :=
      bicollar_slice_complement_components_of_homotopic_disjoint φ hφ r hr hdisjoint c
  exact bicollar_slice_components_of_sides φ a c B E hB hE hBop hEop hBE hcover
    hBfr hEfr hBcl hEcl hcomponents hnegative hpositive

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollar_slice_components_of_homotopic_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollar_slice_components_of_homotopic_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollar_slice_components_of_homotopic_disjoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollar_slice_components_of_homotopic_disjoint

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
