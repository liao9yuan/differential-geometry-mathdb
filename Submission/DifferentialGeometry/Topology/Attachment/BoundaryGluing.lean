import Mathlib.Data.Setoid.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Regular
import Submission.DifferentialGeometry.Topology.Attachment.QuotientIteration

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function _root_.Topology

namespace DifferentialGeometry.Topology

universe u v

theorem isClosed_range_of_continuous_of_compactSpace {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space Y] {f : X → Y} (hf : Continuous f) :
    IsClosed (_root_.Set.range f) := by
  simpa [Set.image_univ] using (isCompact_univ (X := X)).image hf |>.isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isClosed_range_of_continuous_of_compactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isClosed_range_of_continuous_of_compactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isClosed_range_of_continuous_of_compactSpace ``Submission.DifferentialGeometry.Topology.isClosed_range_of_continuous_of_compactSpace

theorem isClosed_class_of_isClosed_rel {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] {r : Setoid X} (hr : IsClosed {p : X × X | r p.1 p.2}) (a : X) :
    IsClosed {y : X | r a y} := by
  have hset : {y : X | r a y}
      = Prod.snd '' ({p : X × X | r p.1 p.2} ∩ ({a} ×ˢ _root_.Set.univ)) := by
    ext y
    constructor
    · intro hy
      exact ⟨(a, y), ⟨hy, ⟨rfl, trivial⟩⟩, rfl⟩
    · rintro ⟨⟨c, b⟩, ⟨hrc, hca, -⟩, hb⟩
      change r c b at hrc
      have hca' : c = a := hca
      have hb' : b = y := hb
      rw [hca', hb'] at hrc
      exact hrc
  rw [hset]
  exact ((hr.inter (isClosed_singleton.prod isClosed_univ)).isCompact.image continuous_snd).isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isClosed_class_of_isClosed_rel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isClosed_class_of_isClosed_rel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isClosed_class_of_isClosed_rel ``Submission.DifferentialGeometry.Topology.isClosed_class_of_isClosed_rel

theorem isClosedMap_quotient_mk_of_isClosed_rel {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] {r : Setoid X} (hr : IsClosed {p : X × X | r p.1 p.2}) :
    IsClosedMap (Quotient.mk' : X → Quotient r) := by
  intro C hC
  rw [← (isQuotientMap_quotient_mk' (s := r)).isCoinducing.isClosed_preimage]
  have hset : (Quotient.mk' : X → Quotient r) ⁻¹'
        ((Quotient.mk' : X → Quotient r) '' C)
      = Prod.snd '' ({p : X × X | r p.1 p.2} ∩ C ×ˢ _root_.Set.univ) := by
    ext x
    constructor
    · rintro ⟨c, hc, hcx⟩
      exact ⟨(c, x), ⟨(Quotient.eq' (s₁ := r)).mp hcx, hc, trivial⟩, rfl⟩
    · rintro ⟨⟨c, y⟩, ⟨hrc, hc, -⟩, hy⟩
      change r c y at hrc
      have hy' : y = x := hy
      rw [hy'] at hrc
      exact ⟨c, hc, Quotient.sound' hrc⟩
  rw [hset]
  exact ((hr.inter (hC.prod isClosed_univ)).isCompact.image continuous_snd).isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isClosedMap_quotient_mk_of_isClosed_rel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isClosedMap_quotient_mk_of_isClosed_rel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isClosedMap_quotient_mk_of_isClosed_rel ``Submission.DifferentialGeometry.Topology.isClosedMap_quotient_mk_of_isClosed_rel

theorem isOpen_quotient_mk_image_of_saturated {X : Type*} [TopologicalSpace X] {r : Setoid X}
    {W : Set X} (hW : ∀ x y, r x y → (x ∈ W ↔ y ∈ W)) (ho : IsOpen W) :
    IsOpen ((Quotient.mk' : X → Quotient r) '' W) := by
  rw [← (isQuotientMap_quotient_mk' (s := r)).isCoinducing.isOpen_preimage]
  have hpre : (Quotient.mk' : X → Quotient r) ⁻¹'
      ((Quotient.mk' : X → Quotient r) '' W) = W := by
    ext x
    constructor
    · rintro ⟨w, hw, hwx⟩
      exact (hW w x ((Quotient.eq' (s₁ := r)).mp hwx)).mp hw
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [hpre]
  exact ho

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isOpen_quotient_mk_image_of_saturated then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isOpen_quotient_mk_image_of_saturated"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isOpen_quotient_mk_image_of_saturated ``Submission.DifferentialGeometry.Topology.isOpen_quotient_mk_image_of_saturated

theorem t2Space_quotient_of_isClosed_rel {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] {r : Setoid X} (hr : IsClosed {p : X × X | r p.1 p.2}) :
    T2Space (Quotient r) := by
  have hclosed : IsClosedMap (Quotient.mk' : X → Quotient r) :=
    isClosedMap_quotient_mk_of_isClosed_rel hr
  rw [t2Space_iff]
  intro q₁ q₂ hne
  obtain ⟨x₁, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨x₂, rfl⟩ := Quotient.exists_rep q₂
  have hc₁ : IsClosed {y : X | r x₁ y} := isClosed_class_of_isClosed_rel hr x₁
  have hc₂ : IsClosed {y : X | r x₂ y} := isClosed_class_of_isClosed_rel hr x₂
  have hdj : Disjoint {y : X | r x₁ y} {y : X | r x₂ y} := by
    rw [Set.disjoint_left]
    intro y hy hz
    exact hne (Quotient.sound' (r.trans hy (r.symm hz)))
  obtain ⟨U₁, U₂, hU₁, hU₂, hs₁, hs₂, hdjU⟩ := normal_separation hc₁ hc₂ hdj
  have hW₁ : IsOpen {z : X | ∀ y : X, r z y → y ∈ U₁} := by
    have hcl : IsClosed ((Quotient.mk' : X → Quotient r) '' U₁ᶜ) :=
      hclosed U₁ᶜ hU₁.isClosed_compl
    have hpre : (Quotient.mk' : X → Quotient r) ⁻¹' ((Quotient.mk' : X → Quotient r) '' U₁ᶜ)
        = {z : X | ∃ y : X, y ∉ U₁ ∧ r z y} := by
      ext z
      constructor
      · rintro ⟨y, hy, hzy⟩
        exact ⟨y, hy, r.symm ((Quotient.eq' (s₁ := r)).mp hzy)⟩
      · rintro ⟨y, hy, hzy⟩
        exact ⟨y, hy, Quotient.sound' (r.symm hzy)⟩
    have hset : {z : X | ∀ y : X, r z y → y ∈ U₁}
        = ((Quotient.mk' : X → Quotient r) ⁻¹' ((Quotient.mk' : X → Quotient r) '' U₁ᶜ))ᶜ := by
      ext z
      rw [hpre]
      change (∀ y : X, r z y → y ∈ U₁) ↔ ¬ (∃ y : X, y ∉ U₁ ∧ r z y)
      exact ⟨fun h hc => by obtain ⟨y, hy, hry⟩ := hc; exact hy (h y hry),
        fun h y hry => by by_contra hy; exact h ⟨y, hy, hry⟩⟩
    rw [hset]
    exact hcl.isOpen_compl.preimage continuous_quotient_mk'
  have hW₂ : IsOpen {z : X | ∀ y : X, r z y → y ∈ U₂} := by
    have hcl : IsClosed ((Quotient.mk' : X → Quotient r) '' U₂ᶜ) :=
      hclosed U₂ᶜ hU₂.isClosed_compl
    have hpre : (Quotient.mk' : X → Quotient r) ⁻¹' ((Quotient.mk' : X → Quotient r) '' U₂ᶜ)
        = {z : X | ∃ y : X, y ∉ U₂ ∧ r z y} := by
      ext z
      constructor
      · rintro ⟨y, hy, hzy⟩
        exact ⟨y, hy, r.symm ((Quotient.eq' (s₁ := r)).mp hzy)⟩
      · rintro ⟨y, hy, hzy⟩
        exact ⟨y, hy, Quotient.sound' (r.symm hzy)⟩
    have hset : {z : X | ∀ y : X, r z y → y ∈ U₂}
        = ((Quotient.mk' : X → Quotient r) ⁻¹' ((Quotient.mk' : X → Quotient r) '' U₂ᶜ))ᶜ := by
      ext z
      rw [hpre]
      change (∀ y : X, r z y → y ∈ U₂) ↔ ¬ (∃ y : X, y ∉ U₂ ∧ r z y)
      exact ⟨fun h hc => by obtain ⟨y, hy, hry⟩ := hc; exact hy (h y hry),
        fun h y hry => by by_contra hy; exact h ⟨y, hy, hry⟩⟩
    rw [hset]
    exact hcl.isOpen_compl.preimage continuous_quotient_mk'
  have hsat₁ : ∀ x y, r x y →
      (x ∈ {z : X | ∀ w : X, r z w → w ∈ U₁} ↔
        y ∈ {z : X | ∀ w : X, r z w → w ∈ U₁}) := by
    intro x y hxy
    exact ⟨fun h w hw => h w (r.trans hxy hw), fun h w hw => h w (r.trans (r.symm hxy) hw)⟩
  have hsat₂ : ∀ x y, r x y →
      (x ∈ {z : X | ∀ w : X, r z w → w ∈ U₂} ↔
        y ∈ {z : X | ∀ w : X, r z w → w ∈ U₂}) := by
    intro x y hxy
    exact ⟨fun h w hw => h w (r.trans hxy hw), fun h w hw => h w (r.trans (r.symm hxy) hw)⟩
  have hdjW : Disjoint {z : X | ∀ y : X, r z y → y ∈ U₁}
      {z : X | ∀ y : X, r z y → y ∈ U₂} := by
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    exact hdjU.le_bot ⟨hz₁ z (r.refl z), hz₂ z (r.refl z)⟩
  refine ⟨_, _, isOpen_quotient_mk_image_of_saturated hsat₁ hW₁,
    isOpen_quotient_mk_image_of_saturated hsat₂ hW₂, ⟨x₁, fun y hy => hs₁ hy, rfl⟩,
    ⟨x₂, fun y hy => hs₂ hy, rfl⟩, ?_⟩
  rw [Set.disjoint_left] at hdjW ⊢
  rintro q ⟨z, hz₁, rfl⟩ ⟨z', hz₂, hzq⟩
  have hz'z : r z' z := (Quotient.eq' (s₁ := r)).mp hzq
  exact hdjW hz₁ (fun y hy => hz₂ y (r.trans hz'z hy))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.t2Space_quotient_of_isClosed_rel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.t2Space_quotient_of_isClosed_rel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.t2Space_quotient_of_isClosed_rel ``Submission.DifferentialGeometry.Topology.t2Space_quotient_of_isClosed_rel

structure BoundaryGluing (X : Type u) [TopologicalSpace X] (ι : Type v) [Finite ι] where
  left : ι → Set X
  right : ι → Set X
  attaching : ∀ i, (left i) ≃ₜ (right i)
  isClosed_left : ∀ i, IsClosed (left i)
  isClosed_right : ∀ i, IsClosed (right i)
  disjoint_left_right : ∀ i, Disjoint (left i) (right i)
  disjoint_blocks : ∀ i j, i ≠ j → Disjoint (left i ∪ right i) (left j ∪ right j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing ``Submission.DifferentialGeometry.Topology.BoundaryGluing

namespace BoundaryGluing

variable {X : Type u} {X' : Type v} {ι : Type*} [Finite ι]
variable [TopologicalSpace X] [TopologicalSpace X']

def block (G : BoundaryGluing X ι) (i : ι) : Set X := G.left i ∪ G.right i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.block then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.block"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.block ``Submission.DifferentialGeometry.Topology.BoundaryGluing.block

theorem isClosed_block (G : BoundaryGluing X ι) (i : ι) : IsClosed (G.block i) :=
  (G.isClosed_left i).union (G.isClosed_right i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.isClosed_block then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.isClosed_block"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.isClosed_block ``Submission.DifferentialGeometry.Topology.BoundaryGluing.isClosed_block

open _root_.Classical in
def flip (G : BoundaryGluing X ι) (i : ι) : X → X := fun x =>
  if hx : x ∈ G.left i then G.attaching i ⟨x, hx⟩
  else if hx : x ∈ G.right i then (G.attaching i).symm ⟨x, hx⟩ else x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.flip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.flip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.flip ``Submission.DifferentialGeometry.Topology.BoundaryGluing.flip

theorem flip_of_mem_left (G : BoundaryGluing X ι) {i : ι} {x : X} (hx : x ∈ G.left i) :
    G.flip i x = G.attaching i ⟨x, hx⟩ := by
  rw [flip, dif_pos hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.flip_of_mem_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.flip_of_mem_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.flip_of_mem_left ``Submission.DifferentialGeometry.Topology.BoundaryGluing.flip_of_mem_left

theorem flip_of_mem_right (G : BoundaryGluing X ι) {i : ι} {x : X} (hx : x ∈ G.right i) :
    G.flip i x = (G.attaching i).symm ⟨x, hx⟩ := by
  rw [flip, dif_neg (fun h => (G.disjoint_left_right i).le_bot ⟨h, hx⟩), dif_pos hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.flip_of_mem_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.flip_of_mem_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.flip_of_mem_right ``Submission.DifferentialGeometry.Topology.BoundaryGluing.flip_of_mem_right

theorem flip_of_notMem (G : BoundaryGluing X ι) {i : ι} {x : X} (hx : x ∉ G.block i) :
    G.flip i x = x := by
  rw [flip, dif_neg (fun h => hx (Or.inl h)), dif_neg (fun h => hx (Or.inr h))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.flip_of_notMem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.flip_of_notMem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.flip_of_notMem ``Submission.DifferentialGeometry.Topology.BoundaryGluing.flip_of_notMem

theorem flip_mem_block (G : BoundaryGluing X ι) {i : ι} {x : X} (hx : x ∈ G.block i) :
    G.flip i x ∈ G.block i := by
  rcases hx with hx | hx
  · rw [G.flip_of_mem_left hx]
    exact Or.inr (G.attaching i ⟨x, hx⟩).2
  · rw [G.flip_of_mem_right hx]
    exact Or.inl ((G.attaching i).symm ⟨x, hx⟩).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.flip_mem_block then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.flip_mem_block"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.flip_mem_block ``Submission.DifferentialGeometry.Topology.BoundaryGluing.flip_mem_block

theorem flip_attaching (G : BoundaryGluing X ι) (i : ι) (z : G.left i) :
    G.flip i ((G.attaching i z : X)) = (z : X) := by
  rw [G.flip_of_mem_right (G.attaching i z).2]
  have h : (⟨((G.attaching i) z : X), (G.attaching i z).2⟩ : ↥(G.right i)) = G.attaching i z :=
    Subtype.ext rfl
  exact congrArg Subtype.val (by rw [h, Homeomorph.symm_apply_apply])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.flip_attaching then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.flip_attaching"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.flip_attaching ``Submission.DifferentialGeometry.Topology.BoundaryGluing.flip_attaching

theorem flip_symm_attaching (G : BoundaryGluing X ι) (i : ι) (w : G.right i) :
    G.flip i (((G.attaching i).symm w : X)) = (w : X) := by
  rw [G.flip_of_mem_left ((G.attaching i).symm w).2]
  have h : (⟨(((G.attaching i).symm w : X)), ((G.attaching i).symm w).2⟩ : ↥(G.left i))
      = (G.attaching i).symm w := Subtype.ext rfl
  exact congrArg Subtype.val (by rw [h, Homeomorph.apply_symm_apply])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.flip_symm_attaching then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.flip_symm_attaching"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.flip_symm_attaching ``Submission.DifferentialGeometry.Topology.BoundaryGluing.flip_symm_attaching

theorem flip_involutive (G : BoundaryGluing X ι) (i : ι) : Function.Involutive (G.flip i) := by
  intro x
  rcases em (x ∈ G.left i) with hx | hx
  · rw [G.flip_of_mem_left hx, G.flip_attaching]
  · rcases em (x ∈ G.right i) with hx' | hx'
    · rw [G.flip_of_mem_right hx', G.flip_symm_attaching]
    · rw [G.flip_of_notMem (fun h => h.elim hx hx'), G.flip_of_notMem (fun h => h.elim hx hx')]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.flip_involutive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.flip_involutive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.flip_involutive ``Submission.DifferentialGeometry.Topology.BoundaryGluing.flip_involutive

def rel (G : BoundaryGluing X ι) (x y : X) : Prop :=
  x = y ∨ ∃ i, x ∈ G.block i ∧ y = G.flip i x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.rel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.rel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.rel ``Submission.DifferentialGeometry.Topology.BoundaryGluing.rel

private theorem isEquivalence_of_blocks {Y : Type*} {κ : Type*} {block : κ → Set Y}
    (hdisj : Pairwise fun i j => Disjoint (block i) (block j)) {f : κ → Y → Y}
    (hflip : ∀ i, Function.Involutive (f i)) (hmem : ∀ i, ∀ x ∈ block i, f i x ∈ block i) :
    Equivalence fun x y => x = y ∨ ∃ i, x ∈ block i ∧ y = f i x := by
  refine ⟨fun x => Or.inl rfl, ?_, ?_⟩
  · rintro x y (rfl | ⟨i, hx, hy⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨i, hy ▸ hmem i x hx, by rw [hy, hflip i x]⟩
  · rintro x y z hxy hyz
    rcases hxy with rfl | ⟨i, hx, hy⟩
    · exact hyz
    rcases hyz with rfl | ⟨j, hx', hz⟩
    · exact Or.inr ⟨i, hx, hy⟩
    · have hyi : y ∈ block i := by rw [hy]; exact hmem i x hx
      have hij : i = j := by
        by_contra h
        exact (hdisj h).le_bot ⟨hyi, hx'⟩
      subst hij
      exact Or.inl (by rw [hz, hy, hflip i x])

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.BoundaryGluing.isEquivalence_of_blocks
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.BoundaryGluing.isEquivalence_of_blocks target :: scope.openDecls } }

theorem isEquivalence_rel (G : BoundaryGluing X ι) : Equivalence G.rel :=
  isEquivalence_of_blocks (block := G.block) (fun _ _ hij => G.disjoint_blocks _ _ hij)
    (fun i => G.flip_involutive i) (fun _ _ hx => G.flip_mem_block hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.isEquivalence_rel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.isEquivalence_rel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.isEquivalence_rel ``Submission.DifferentialGeometry.Topology.BoundaryGluing.isEquivalence_rel

def setoid (G : BoundaryGluing X ι) : Setoid X := ⟨G.rel, G.isEquivalence_rel⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.setoid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.setoid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.setoid ``Submission.DifferentialGeometry.Topology.BoundaryGluing.setoid

theorem rel_of_mem_left (G : BoundaryGluing X ι) {i : ι} {x : X} (hx : x ∈ G.left i) :
    G.rel x (G.attaching i ⟨x, hx⟩) :=
  Or.inr ⟨i, Or.inl hx, (G.flip_of_mem_left hx).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.rel_of_mem_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.rel_of_mem_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.rel_of_mem_left ``Submission.DifferentialGeometry.Topology.BoundaryGluing.rel_of_mem_left

theorem rel_of_mem_right (G : BoundaryGluing X ι) {i : ι} {x : X} (hx : x ∈ G.right i) :
    G.rel x ((G.attaching i).symm ⟨x, hx⟩) :=
  Or.inr ⟨i, Or.inr hx, (G.flip_of_mem_right hx).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.rel_of_mem_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.rel_of_mem_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.rel_of_mem_right ``Submission.DifferentialGeometry.Topology.BoundaryGluing.rel_of_mem_right

theorem rel_of_attaching (G : BoundaryGluing X ι) (i : ι) (z : G.left i) :
    G.rel ((G.attaching i z : X)) (z : X) :=
  Or.inr ⟨i, Or.inr (G.attaching i z).2, (G.flip_attaching i z).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.rel_of_attaching then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.rel_of_attaching"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.rel_of_attaching ``Submission.DifferentialGeometry.Topology.BoundaryGluing.rel_of_attaching

theorem isClosed_setOf_rel (G : BoundaryGluing X ι) [T2Space X] [CompactSpace X] :
    IsClosed {p : X × X | G.rel p.1 p.2} := by
  have hgraph : ∀ i, IsClosed (_root_.Set.range fun z : (G.left i) =>
      ((z : X), (G.attaching i z : X))) := fun i => by
    have hc : CompactSpace (G.left i) := isCompact_iff_compactSpace.mp (G.isClosed_left i).isCompact
    exact isClosed_range_of_continuous_of_compactSpace
      (continuous_subtype_val.prodMk (continuous_subtype_val.comp (G.attaching i).continuous))
  have hgraph' : ∀ i, IsClosed (_root_.Set.range fun z : (G.left i) =>
      ((G.attaching i z : X), (z : X))) := fun i => by
    have hc : CompactSpace (G.left i) := isCompact_iff_compactSpace.mp (G.isClosed_left i).isCompact
    exact isClosed_range_of_continuous_of_compactSpace
      ((continuous_subtype_val.comp (G.attaching i).continuous).prodMk continuous_subtype_val)
  have hset : {p : X × X | G.rel p.1 p.2} = _root_.Set.diagonal X ∪ ⋃ i,
      (_root_.Set.range fun z : (G.left i) => ((z : X), (G.attaching i z : X)))
        ∪ (_root_.Set.range fun z : (G.left i) => ((G.attaching i z : X), (z : X))) := by
    ext p
    constructor
    · intro hp
      rcases hp with hxy | ⟨i, hx, hy⟩
      · exact Or.inl (Set.mem_diagonal_iff.mpr hxy)
      · refine Or.inr (mem_iUnion.mpr ⟨i, ?_⟩)
        rcases hx with hx | hx
        · refine Or.inl ⟨⟨p.1, hx⟩, ?_⟩
          rw [G.flip_of_mem_left hx] at hy
          exact Prod.ext rfl hy.symm
        · refine Or.inr ⟨(G.attaching i).symm ⟨p.1, hx⟩, ?_⟩
          rw [G.flip_of_mem_right hx] at hy
          exact Prod.ext
            (congrArg Subtype.val ((G.attaching i).apply_symm_apply ⟨p.1, hx⟩)) hy.symm
    · intro hp
      rcases hp with h | h
      · exact Or.inl (Set.mem_diagonal_iff.mp h)
      · obtain ⟨i, h | h⟩ := mem_iUnion.mp h
        · obtain ⟨z, hz⟩ := h
          rw [← hz]
          exact G.rel_of_mem_left z.2
        · obtain ⟨z, hz⟩ := h
          rw [← hz]
          exact G.rel_of_attaching i z
  rw [hset]
  exact isClosed_diagonal.union (isClosed_iUnion_of_finite fun i => (hgraph i).union (hgraph' i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.isClosed_setOf_rel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.isClosed_setOf_rel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.isClosed_setOf_rel ``Submission.DifferentialGeometry.Topology.BoundaryGluing.isClosed_setOf_rel

instance instT2SpaceQuotient (G : BoundaryGluing X ι) [T2Space X] [CompactSpace X] :
    T2Space (Quotient G.setoid) :=
  t2Space_quotient_of_isClosed_rel G.isClosed_setOf_rel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.instT2SpaceQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.instT2SpaceQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.instT2SpaceQuotient ``Submission.DifferentialGeometry.Topology.BoundaryGluing.instT2SpaceQuotient

theorem eq_of_rel_of_notMem (G : BoundaryGluing X ι) {x y : X}
    (hx : ∀ i, x ∉ G.block i) (h : G.rel x y) : x = y := by
  rcases h with rfl | ⟨i, hx', -⟩
  · rfl
  · exact absurd hx' (hx i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.eq_of_rel_of_notMem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.eq_of_rel_of_notMem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.eq_of_rel_of_notMem ``Submission.DifferentialGeometry.Topology.BoundaryGluing.eq_of_rel_of_notMem

theorem injOn_quotientMk (G : BoundaryGluing X ι) :
    InjOn (Quotient.mk'' : X → Quotient G.setoid) {x : X | ∀ i, x ∉ G.block i} := by
  intro x hx y hy hxy
  exact G.eq_of_rel_of_notMem hx ((Quotient.eq' (s₁ := G.setoid)).mp hxy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.injOn_quotientMk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.injOn_quotientMk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.injOn_quotientMk ``Submission.DifferentialGeometry.Topology.BoundaryGluing.injOn_quotientMk

def congrHomeomorph (G : BoundaryGluing X ι) (G' : BoundaryGluing X' ι) (e : X ≃ₜ X')
    (h : ∀ x y, G.rel x y ↔ G'.rel (e x) (e y)) :
    Quotient G.setoid ≃ₜ Quotient G'.setoid :=
  Homeomorph.Quotient.congr e h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.congrHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.congrHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.congrHomeomorph ``Submission.DifferentialGeometry.Topology.BoundaryGluing.congrHomeomorph

def restrict (G : BoundaryGluing X ι) (s : Set ι) : BoundaryGluing X s where
  left i := G.left i.1
  right i := G.right i.1
  attaching i := G.attaching i.1
  isClosed_left i := G.isClosed_left i.1
  isClosed_right i := G.isClosed_right i.1
  disjoint_left_right i := G.disjoint_left_right i.1
  disjoint_blocks i j hij := G.disjoint_blocks i.1 j.1 fun h => hij (Subtype.ext h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.restrict ``Submission.DifferentialGeometry.Topology.BoundaryGluing.restrict

theorem block_restrict (G : BoundaryGluing X ι) (s : Set ι) (i : s) :
    (G.restrict s).block i = G.block i.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.block_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.block_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.block_restrict ``Submission.DifferentialGeometry.Topology.BoundaryGluing.block_restrict

theorem flip_restrict (G : BoundaryGluing X ι) (s : Set ι) (i : s) :
    (G.restrict s).flip i = G.flip i.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.flip_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.flip_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.flip_restrict ``Submission.DifferentialGeometry.Topology.BoundaryGluing.flip_restrict

theorem rel_restrict_iff (G : BoundaryGluing X ι) (s : Set ι) (x y : X) :
    (G.restrict s).rel x y ↔
      x = y ∨ ∃ i : s, x ∈ G.block i.1 ∧ y = G.flip i.1 x :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.rel_restrict_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.rel_restrict_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.rel_restrict_iff ``Submission.DifferentialGeometry.Topology.BoundaryGluing.rel_restrict_iff

theorem rel_restrict_imp (G : BoundaryGluing X ι) (s : Set ι) {x y : X}
    (h : (G.restrict s).rel x y) : G.rel x y := by
  rcases h with h | ⟨i, hx, hy⟩
  · exact Or.inl h
  · exact Or.inr ⟨i.1, hx, hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.rel_restrict_imp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.rel_restrict_imp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.rel_restrict_imp ``Submission.DifferentialGeometry.Topology.BoundaryGluing.rel_restrict_imp

theorem setoid_restrict_le (G : BoundaryGluing X ι) (s : Set ι) :
    (G.restrict s).setoid ≤ G.setoid :=
  fun _ _ h => G.rel_restrict_imp s h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.setoid_restrict_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.setoid_restrict_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.setoid_restrict_le ``Submission.DifferentialGeometry.Topology.BoundaryGluing.setoid_restrict_le

theorem rel_restrict_univ_iff (G : BoundaryGluing X ι) (x y : X) :
    (G.restrict _root_.Set.univ).rel x y ↔ G.rel x y := by
  refine ⟨G.rel_restrict_imp _root_.Set.univ, fun h => ?_⟩
  rcases h with h | ⟨i, hx, hy⟩
  · exact Or.inl h
  · exact Or.inr ⟨⟨i, trivial⟩, hx, hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.rel_restrict_univ_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.rel_restrict_univ_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.rel_restrict_univ_iff ``Submission.DifferentialGeometry.Topology.BoundaryGluing.rel_restrict_univ_iff

theorem setoid_restrict_univ (G : BoundaryGluing X ι) :
    (G.restrict _root_.Set.univ).setoid = G.setoid :=
  Setoid.ext (G.rel_restrict_univ_iff · ·)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.setoid_restrict_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.setoid_restrict_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.setoid_restrict_univ ``Submission.DifferentialGeometry.Topology.BoundaryGluing.setoid_restrict_univ

theorem setoid_restrict_empty (G : BoundaryGluing X ι) :
    (G.restrict (∅ : Set ι)).setoid = ⊥ := by
  refine Setoid.ext fun x y => ?_
  change (G.restrict (∅ : Set ι)).rel x y ↔ x = y
  refine ⟨fun h => ?_, fun h => Or.inl h⟩
  rcases h with h | ⟨i, -⟩
  · exact h
  · exact absurd i.2 (Set.notMem_empty i.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.setoid_restrict_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.setoid_restrict_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.setoid_restrict_empty ``Submission.DifferentialGeometry.Topology.BoundaryGluing.setoid_restrict_empty

def successiveQuotientHomeomorph (G : BoundaryGluing X ι) (s : Set ι) :
    Quotient (Setoid.ker (Quot.mapRight (G.setoid_restrict_le s))) ≃ₜ Quotient G.setoid :=
  quotientQuotientHomeomorph (G.setoid_restrict_le s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.successiveQuotientHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.successiveQuotientHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.successiveQuotientHomeomorph ``Submission.DifferentialGeometry.Topology.BoundaryGluing.successiveQuotientHomeomorph

def isEmpty (X : Type u) [TopologicalSpace X] : BoundaryGluing X Empty where
  left i := nomatch i
  right i := nomatch i
  attaching i := nomatch i
  isClosed_left i := nomatch i
  isClosed_right i := nomatch i
  disjoint_left_right i := nomatch i
  disjoint_blocks i := nomatch i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.isEmpty ``Submission.DifferentialGeometry.Topology.BoundaryGluing.isEmpty

theorem rel_isEmpty (X : Type u) [TopologicalSpace X] (x y : X) :
    (isEmpty X).rel x y ↔ x = y := by
  refine ⟨fun h => ?_, fun h => Or.inl h⟩
  rcases h with h | ⟨i, -⟩
  · exact h
  · exact isEmptyElim i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.rel_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.rel_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.rel_isEmpty ``Submission.DifferentialGeometry.Topology.BoundaryGluing.rel_isEmpty

theorem setoid_isEmpty (X : Type u) [TopologicalSpace X] : (isEmpty X).setoid = ⊥ := by
  refine Setoid.ext fun x y => ?_
  change (isEmpty X).rel x y ↔ x = y
  exact rel_isEmpty X x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.setoid_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.setoid_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.setoid_isEmpty ``Submission.DifferentialGeometry.Topology.BoundaryGluing.setoid_isEmpty

def quotientHomeomorph_isEmpty (X : Type u) [TopologicalSpace X] :
    Quotient (isEmpty X).setoid ≃ₜ X :=
  (Homeomorph.Quotient.congrRight (fun x y => by rw [setoid_isEmpty])).trans
    Homeomorph.quotientBot

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoundaryGluing.quotientHomeomorph_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoundaryGluing.quotientHomeomorph_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoundaryGluing.quotientHomeomorph_isEmpty ``Submission.DifferentialGeometry.Topology.BoundaryGluing.quotientHomeomorph_isEmpty

end BoundaryGluing

end DifferentialGeometry.Topology
