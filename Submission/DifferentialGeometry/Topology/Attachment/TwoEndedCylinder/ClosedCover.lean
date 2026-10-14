import Submission.DifferentialGeometry.Topology.Attachment.AdjunctionHomeomorph
import Mathlib.Topology.Instances.Real.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Function

namespace DifferentialGeometry.Topology

variable {S L R M : Type*} [TopologicalSpace S] [TopologicalSpace L]
  [TopologicalSpace R] [TopologicalSpace M]

theorem exists_adjunction_homeomorph_of_two_cap_cylinder_cover
    (b₀ : S → L) (b₁ : S → R)
    (f₀ : C(L, M)) (f₁ : C(R, M)) (T : C(S × _root_.Set.Icc (0 : ℝ) 1, M))
    (hf₀ : _root_.Topology.IsClosedEmbedding f₀)
    (hf₁ : _root_.Topology.IsClosedEmbedding f₁)
    (hT : _root_.Topology.IsClosedEmbedding T)
    (hdisj : Disjoint (_root_.Set.range f₀) (_root_.Set.range f₁))
    (hzero : ∀ z, T (z, 0) = f₀ (b₀ z))
    (hone : ∀ z, T (z, 1) = f₁ (b₁ z))
    (hcross₀ : ∀ q x, T q = f₀ x → q.2 = 0 ∧ b₀ q.1 = x)
    (hcross₁ : ∀ q x, T q = f₁ x → q.2 = 1 ∧ b₁ q.1 = x)
    (hcover : _root_.Set.range T ∪ (_root_.Set.range f₀ ∪ _root_.Set.range f₁) = _root_.Set.univ) :
    let endMap : S ⊕ S → S × _root_.Set.Icc (0 : ℝ) 1 :=
      Sum.elim (fun z => (z, 0)) (fun z => (z, 1))
    let attaching : S ⊕ S → L ⊕ R := Sum.map b₀ b₁
    ∃ H : AdjunctionSpace endMap attaching ≃ₜ M,
      (∀ q, H (adjunctionCell endMap attaching q) = T q) ∧
      (∀ x, H (adjunctionLower (i := endMap) attaching (Sum.inl x)) = f₀ x) ∧
      ∀ x, H (adjunctionLower (i := endMap) attaching (Sum.inr x)) = f₁ x := by
  let endMap : S ⊕ S → S × _root_.Set.Icc (0 : ℝ) 1 :=
    Sum.elim (fun z => (z, 0)) (fun z => (z, 1))
  let attaching : S ⊕ S → L ⊕ R := Sum.map b₀ b₁
  let caps : L ⊕ R → M := Sum.elim f₀ f₁
  let F : (S × _root_.Set.Icc (0 : ℝ) 1) ⊕ (L ⊕ R) → M := Sum.elim T caps
  have hcapc : Continuous caps := f₀.continuous.sumElim f₁.continuous
  have hcapclosed : IsClosedMap caps := hf₀.isClosedMap.sumElim hf₁.isClosedMap
  have hcapinj : _root_.Function.Injective caps := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (hf₀.injective h)
      | inr y => exact False.elim (hdisj.le_bot ⟨mem_range_self x, y, h.symm⟩)
    | inr x =>
      cases y with
      | inl y => exact False.elim (hdisj.le_bot ⟨⟨y, h.symm⟩, _root_.Set.mem_range_self x⟩)
      | inr y => exact congrArg Sum.inr (hf₁.injective h)
  have hsurj : _root_.Function.Surjective F := by
    intro x
    have hx : x ∈ _root_.Set.range T ∪ (_root_.Set.range f₀ ∪ _root_.Set.range f₁) := hcover.symm ▸ _root_.Set.mem_univ x
    rcases hx with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩
    · exact ⟨Sum.inl q, rfl⟩
    · exact ⟨Sum.inr (Sum.inl q), rfl⟩
    · exact ⟨Sum.inr (Sum.inr q), rfl⟩
  have hquot : _root_.Topology.IsQuotientMap F :=
    (hT.isClosedMap.sumElim hcapclosed).isQuotientMap (T.continuous.sumElim hcapc) hsurj
  have hcross : ∀ q x, F (Sum.inl q) = F (Sum.inr x) ↔
      ∃ z, endMap z = q ∧ attaching z = x := by
    intro q x
    cases x with
    | inl x =>
      constructor
      · intro h
        obtain ⟨ht, hx⟩ := hcross₀ q x h
        exact ⟨Sum.inl q.1, Prod.ext rfl ht.symm, congrArg Sum.inl hx⟩
      · rintro ⟨z, hz, hx⟩
        cases z with
        | inl z =>
          cases hz
          have hb : b₀ z = x := Sum.inl.inj hx
          change T (z, 0) = f₀ x
          rw [hzero, hb]
        | inr z => cases hx
    | inr x =>
      constructor
      · intro h
        obtain ⟨ht, hx⟩ := hcross₁ q x h
        exact ⟨Sum.inr q.1, Prod.ext rfl ht.symm, congrArg Sum.inr hx⟩
      · rintro ⟨z, hz, hx⟩
        cases z with
        | inl z => cases hx
        | inr z =>
          cases hz
          have hb : b₁ z = x := Sum.inr.inj hx
          change T (z, 1) = f₁ x
          rw [hone, hb]
  exact ⟨adjunctionHomeomorphOfFibers endMap attaching F hquot hT.injective hcapinj hcross,
    fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_adjunction_homeomorph_of_two_cap_cylinder_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_adjunction_homeomorph_of_two_cap_cylinder_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_adjunction_homeomorph_of_two_cap_cylinder_cover ``Submission.DifferentialGeometry.Topology.exists_adjunction_homeomorph_of_two_cap_cylinder_cover

end DifferentialGeometry.Topology
