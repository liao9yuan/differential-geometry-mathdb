import Submission.DifferentialGeometry.Topology.OpenCoverInduction
import Submission.DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.Vanishing
import Submission.DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.Homeomorph
import Mathlib.Topology.Homeomorph.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.TopologicalSpace _root_.Submission.TopologicalSpace

universe u v

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X]

private theorem integralCompactlySupportedCohomology_subsingleton_sUnion_of_directed
    (n : ℕ) (S : Set (Set X)) (hdir : DirectedOn (· ⊆ ·) S)
    (hopen : ∀ U ∈ S, IsOpen U)
    (hvan : ∀ U ∈ S, Subsingleton (integralCompactlySupportedCohomology n U)) :
    Subsingleton (integralCompactlySupportedCohomology n ↥(⋃₀ S)) := by
  let W := ⋃₀ S
  let V : S → Set W := fun U => Subtype.val ⁻¹' (U : Set X)
  apply integralCompactlySupportedCohomology_subsingleton_of_directed_open_cover n V
  · intro U
    exact (hopen U U.property).preimage continuous_subtype_val
  · intro U V
    obtain ⟨T, hT, hUT, hVT⟩ := hdir U U.property V V.property
    exact ⟨⟨T, hT⟩, _root_.Set.preimage_mono hUT, _root_.Set.preimage_mono hVT⟩
  · apply _root_.Set.eq_univ_of_forall
    intro x
    obtain ⟨U, hU, hx⟩ := mem_sUnion.mp x.property
    exact mem_iUnion.mpr ⟨⟨U, hU⟩, hx⟩
  · intro U
    let e : V U ≃ₜ (U : Set X) :=
      (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (Subtype.val : W → X)).homeomorphOfSubsetRange
        (by
          intro x hx
          exact ⟨⟨x, mem_sUnion.mpr ⟨U, U.property, hx⟩⟩, rfl⟩)
    let _ := hvan U U.property
    exact (integralCompactlySupportedCohomologyPushforward_homeomorph_bijective n e).injective.subsingleton

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_sUnion_of_directed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_sUnion_of_directed target :: scope.openDecls } }

theorem integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_basis
    {B : Set (Set X)} (hB : _root_.TopologicalSpace.IsTopologicalBasis B)
    (hinter : ∀ U ∈ B, ∀ V ∈ B, U ∩ V ∈ B ∨ U ∩ V = ∅)
    (d : ℕ) (hseed : ∀ U ∈ B, ∀ n, d < n →
      Subsingleton (integralCompactlySupportedCohomology n U))
    {W : Set X} (hW : IsOpen W) (n : ℕ) (hn : d < n) :
    Subsingleton (integralCompactlySupportedCohomology n W) := by
  let P : Set X → Prop := fun U => ∀ n, d < n →
    Subsingleton (integralCompactlySupportedCohomology n U)
  have hP : P W := hB.isOpen_induction_of_union_of_directed_sUnion
      (P := P) hinter
      (fun n _ => integralCompactlySupportedCohomology_subsingleton_of_isEmpty n)
      hseed
      (fun U V hU hV hPU hPV hPuv n hn => by
        let _ := hPU n hn
        let _ := hPV n hn
        let _ := hPuv (n + 1) (hn.trans (Nat.lt_succ_self n))
        exact integralCompactlySupportedCohomology_subsingleton_union n U V hU hV)
      (fun S hSne hdir hS n hn =>
        integralCompactlySupportedCohomology_subsingleton_sUnion_of_directed n S hdir
          (fun U hU => (hS U hU).1) (fun U hU => (hS U hU).2 n hn)) hW
  exact hP n hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_basis ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_basis

end DifferentialGeometry.Topology

end
