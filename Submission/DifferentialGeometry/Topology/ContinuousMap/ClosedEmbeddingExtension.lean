import Mathlib.Topology.ContinuousOn

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set

namespace Topology.IsClosedEmbedding
open _root_.Topology _root_.Topology.IsClosedEmbedding

universe u v w

variable {C : Type u} {X : Type v} {Y : Type w}
  [TopologicalSpace C] [TopologicalSpace X] [TopologicalSpace Y]

open _root_.Topology _root_.Topology.IsClosedEmbedding in
theorem continuous_extend_of_isOpen_image
    {c : C → X} (hc : _root_.Topology.IsClosedEmbedding c) {U : Set C}
    (hU : IsOpen (c '' U)) {f : C → Y} {g : X → Y}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ p, p ∉ U → f p = g (c p)) :
    Continuous (Function.extend c f g) := by
  have hcomp : ContinuousOn (Function.extend c f g ∘ c) univ := by
    rw [Function.extend_comp hc.injective f g]
    exact hf.continuousOn
  have hrange : ContinuousOn (Function.extend c f g) (_root_.Set.range c) := by
    simpa only [_root_.Set.image_univ] using
      (hc.isInducing.continuousOn_image_iff (s := _root_.Set.univ)).mpr hcomp
  have houtside : _root_.Set.EqOn (Function.extend c f g) g (c '' U)ᶜ := by
    intro x hx
    by_cases hcx : x ∈ _root_.Set.range c
    · obtain ⟨p, rfl⟩ := hcx
      rw [hc.injective.extend_apply f g p]
      exact hfg p (fun hp => hx ⟨p, hp, rfl⟩)
    · exact Function.extend_apply' f g x hcx
  have hcover : _root_.Set.range c ∪ (c '' U)ᶜ = univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ _root_.Set.range c
    · exact Or.inl hx
    · exact Or.inr (fun ⟨p, _, hp⟩ => hx ⟨p, hp⟩)
  have hcont := hrange.union_of_isClosed (hg.continuousOn.congr houtside)
    hc.isClosed_range hU.isClosed_compl
  rw [hcover] at hcont
  exact continuousOn_univ.mp hcont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Topology.IsClosedEmbedding.continuous_extend_of_isOpen_image then
    throwError "Refusing to shadow existing declaration Topology.IsClosedEmbedding.continuous_extend_of_isOpen_image"
  Lean.modifyEnv fun env => Lean.addAlias env `Topology.IsClosedEmbedding.continuous_extend_of_isOpen_image ``Submission.Topology.IsClosedEmbedding.continuous_extend_of_isOpen_image

open _root_.Topology _root_.Topology.IsClosedEmbedding in
theorem exists_continuous_extension_of_isOpen_image
    {c : C → X} (hc : _root_.Topology.IsClosedEmbedding c) {U : Set C}
    (hU : IsOpen (c '' U)) {f : C → Y} {g : X → Y}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ p, p ∉ U → f p = g (c p)) :
    ∃ F : X → Y, Continuous F ∧ (∀ p, F (c p) = f p) ∧
      ∀ x, x ∉ _root_.Set.range c → F x = g x := by
  exact ⟨Function.extend c f g, hc.continuous_extend_of_isOpen_image hU hf hg hfg,
    hc.injective.extend_apply f g, fun x hx => Function.extend_apply' f g x hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Topology.IsClosedEmbedding.exists_continuous_extension_of_isOpen_image then
    throwError "Refusing to shadow existing declaration Topology.IsClosedEmbedding.exists_continuous_extension_of_isOpen_image"
  Lean.modifyEnv fun env => Lean.addAlias env `Topology.IsClosedEmbedding.exists_continuous_extension_of_isOpen_image ``Submission.Topology.IsClosedEmbedding.exists_continuous_extension_of_isOpen_image

end Topology.IsClosedEmbedding
