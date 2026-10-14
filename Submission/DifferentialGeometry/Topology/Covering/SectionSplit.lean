import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Connected.Clopen

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.Covering

variable {B C : Type*} [TopologicalSpace B] [TopologicalSpace C]


theorem isOpenEmbedding_section {p : C → B} (hp : IsLocalHomeomorph p)
    (s : C(B, C)) (hs : Function.RightInverse s p) : _root_.Topology.IsOpenEmbedding s := by
  apply hp.isOpenEmbedding_of_comp _ s.continuous
  have heq : p ∘ s = id := funext hs
  rw [heq]
  exact (Homeomorph.refl B).isOpenEmbedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Covering.isOpenEmbedding_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Covering.isOpenEmbedding_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Covering.isOpenEmbedding_section ``Submission.DifferentialGeometry.Topology.Covering.isOpenEmbedding_section

theorem not_connected_of_double_cover_section [Nonempty B]
    {p : C → B} (hp : IsCoveringMap p) (τ : C → C) (hτ : Continuous τ)
    (hdeck : ∀ z, p (τ z) = p z) (hfree : ∀ z, τ z ≠ z)
    (hfiber : ∀ x y, p y = p x → y = x ∨ y = τ x)
    (s : C(B, C)) (hs : Function.RightInverse s p) : ¬ ConnectedSpace C := by
  let s' : C(B, C) := ⟨τ ∘ s, hτ.comp s.continuous⟩
  have hs' : Function.RightInverse s' p := fun b => (hdeck (s b)).trans (hs b)
  have hout (b : B) : s' b ∉ _root_.Set.range s := by
    rintro ⟨b', hb'⟩
    have hbb : b' = b := (hs b').symm.trans ((congrArg p hb').trans (hs' b))
    subst b'
    exact hfree (s b) hb'.symm
  have hcompl : (_root_.Set.range s)ᶜ = _root_.Set.range s' := by
    ext z
    constructor
    · intro hz
      rcases hfiber (s (p z)) z (hs (p z)).symm with he | he
      · exact False.elim (hz ⟨p z, he.symm⟩)
      · exact ⟨p z, he.symm⟩
    · rintro ⟨b, rfl⟩
      exact hout b
  have hcl : IsClopen (_root_.Set.range s) := by
    refine ⟨?_, (isOpenEmbedding_section hp.isLocalHomeomorph s hs).isOpen_range⟩
    rw [← isOpen_compl_iff, hcompl]
    exact (isOpenEmbedding_section hp.isLocalHomeomorph s' hs').isOpen_range
  intro hconn
  let := hconn
  let b : B := Classical.choice inferInstance
  rcases isClopen_iff.mp hcl with h | h
  · have hh : s b ∈ _root_.Set.range s := _root_.Set.mem_range_self b
    rw [h] at hh
    exact hh
  · exact hout b (h.symm ▸ _root_.Set.mem_univ (s' b))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Covering.not_connected_of_double_cover_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Covering.not_connected_of_double_cover_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Covering.not_connected_of_double_cover_section ``Submission.DifferentialGeometry.Topology.Covering.not_connected_of_double_cover_section

end DifferentialGeometry.Topology.Covering
