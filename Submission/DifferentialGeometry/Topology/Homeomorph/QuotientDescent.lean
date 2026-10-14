import Mathlib.Topology.Homeomorph.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Topology

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

def quotientHomeomorphOfRelations
    (F : X → Y) (hF : _root_.Topology.IsQuotientMap F)
    (r : X → X → Prop) (s : Y → Y → Prop)
    (hforward : ∀ x x', r x x' → Relation.EqvGen s (F x) (F x'))
    (hbackward : ∀ x x', s (F x) (F x') → Relation.EqvGen r x x')
    (hkernel : ∀ x x', F x = F x' → Relation.EqvGen r x x') :
    Quot r ≃ₜ Quot s := by
  have hlift : ∀ y y', Relation.EqvGen s y y' →
      ∀ x x', F x = y → F x' = y' → Relation.EqvGen r x x' := by
    intro y y' h
    induction h with
    | rel y y' h =>
      intro x x' hx hx'
      exact hbackward x x' (by simpa only [hx, hx'] using h)
    | refl y =>
      intro x x' hx hx'
      exact hkernel x x' (hx.trans hx'.symm)
    | symm y y' h ih =>
      intro x x' hx hx'
      exact Relation.EqvGen.symm x' x (ih x' x hx' hx)
    | trans y y' y'' h h' ih ih' =>
      intro x x' hx hx'
      obtain ⟨z, hz⟩ := hF.surjective y'
      exact Relation.EqvGen.trans x z x' (ih x z hx hz) (ih' z x' hz hx')
  let G : Quot r → Quot s :=
    Quot.lift (fun x => Quot.mk s (F x))
      (fun x x' h => Quot.eqvGen_sound (hforward x x' h))
  have hGinjective : Function.Injective G := by
    intro q q' hqq'
    obtain ⟨x, rfl⟩ := Quot.exists_rep q
    obtain ⟨x', rfl⟩ := Quot.exists_rep q'
    change Quot.mk s (F x) = Quot.mk s (F x') at hqq'
    exact Quot.eqvGen_sound (hlift (F x) (F x') (Quot.eqvGen_exact hqq') x x' rfl rfl)
  have hGcomp : _root_.Topology.IsQuotientMap (G ∘ Quot.mk r) :=
    (isQuotientMap_quot_mk (r := s)).comp hF
  have hGquotient : _root_.Topology.IsQuotientMap G :=
    (isQuotientMap_quot_mk (r := r)).of_comp_isQuotientMap hGcomp
  exact IsHomeomorph.homeomorph G
    ((isHomeomorph_iff_isQuotientMap_injective).mpr ⟨hGquotient, hGinjective⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.quotientHomeomorphOfRelations then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.quotientHomeomorphOfRelations"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.quotientHomeomorphOfRelations ``Submission.DifferentialGeometry.Topology.quotientHomeomorphOfRelations

@[simp]
theorem quotientHomeomorphOfRelations_apply_mk
    (F : X → Y) (hF : _root_.Topology.IsQuotientMap F)
    (r : X → X → Prop) (s : Y → Y → Prop)
    (hforward : ∀ x x', r x x' → Relation.EqvGen s (F x) (F x'))
    (hbackward : ∀ x x', s (F x) (F x') → Relation.EqvGen r x x')
    (hkernel : ∀ x x', F x = F x' → Relation.EqvGen r x x')
    (x : X) :
    quotientHomeomorphOfRelations F hF r s hforward hbackward hkernel (Quot.mk r x) =
      Quot.mk s (F x) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.quotientHomeomorphOfRelations_apply_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.quotientHomeomorphOfRelations_apply_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.quotientHomeomorphOfRelations_apply_mk ``Submission.DifferentialGeometry.Topology.quotientHomeomorphOfRelations_apply_mk

end DifferentialGeometry.Topology

namespace Homeomorph.Quot
open _root_.Homeomorph

variable {X Y I : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def indexedRelationStep (r : I → X → X → Prop) (i : I) (H : Quot (r i) ≃ₜ Y) :
    Quot (fun x y => ∃ j, r j x y) ≃ₜ
      Quot (fun y y' => ∃ j : {j // j ≠ i},
        Relation.Map (r j.val) (H ∘ Quot.mk (r i)) (H ∘ Quot.mk (r i)) y y') := by
  classical
  let F := H ∘ Quot.mk (r i)
  let R := fun x y => ∃ j, r j x y
  let S := fun y y' => ∃ j : {j // j ≠ i}, Relation.Map (r j.val) F F y y'
  have hF : _root_.Topology.IsQuotientMap F := H.isQuotientMap.comp isQuotientMap_quot_mk
  have hkernel (x x' : X) (h : F x = F x') : Relation.EqvGen R x x' := by
    have hri : Relation.EqvGen (r i) x x' := Quot.eqvGen_exact (H.injective h)
    clear h
    induction hri with
    | rel x y hxy => exact Relation.EqvGen.rel x y ⟨i, hxy⟩
    | refl x => exact Relation.EqvGen.refl x
    | symm x y _ ih => exact Relation.EqvGen.symm x y ih
    | trans x y z _ _ ih ih' => exact Relation.EqvGen.trans x y z ih ih'
  have hforward (x x' : X) (h : R x x') : Relation.EqvGen S (F x) (F x') := by
    obtain ⟨j, hj⟩ := h
    by_cases hji : j = i
    · subst j
      have hFxy : F x = F x' := congrArg H (Quot.sound hj)
      rw [hFxy]
      exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ ⟨⟨j, hji⟩, x, x', hj, rfl, rfl⟩
  have hbackward (x x' : X) (h : S (F x) (F x')) : Relation.EqvGen R x x' := by
    obtain ⟨j, a, b, hab, hax, hbx'⟩ := h
    exact Relation.EqvGen.trans x a x' (hkernel x a hax.symm)
      (Relation.EqvGen.trans a b x' (Relation.EqvGen.rel a b ⟨j.val, hab⟩)
        (hkernel b x' hbx'))
  exact DifferentialGeometry.Topology.quotientHomeomorphOfRelations F hF R S
    hforward hbackward hkernel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.Quot.indexedRelationStep then
    throwError "Refusing to shadow existing declaration Homeomorph.Quot.indexedRelationStep"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.Quot.indexedRelationStep ``Submission.Homeomorph.Quot.indexedRelationStep

@[simp] theorem indexedRelationStep_mk (r : I → X → X → Prop) (i : I)
    (H : Quot (r i) ≃ₜ Y) (x : X) :
    indexedRelationStep r i H (Quot.mk _ x) = Quot.mk _ (H (Quot.mk (r i) x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.Quot.indexedRelationStep_mk then
    throwError "Refusing to shadow existing declaration Homeomorph.Quot.indexedRelationStep_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.Quot.indexedRelationStep_mk ``Submission.Homeomorph.Quot.indexedRelationStep_mk

end Homeomorph.Quot

namespace Homeomorph.Quot
open _root_.Homeomorph

variable {X : Type*} [TopologicalSpace X]

def emptyRelation (r : X → X → Prop) (hr : ∀ x y, ¬ r x y) : Quot r ≃ₜ X where
  toFun := Quot.lift id (fun x y h => (hr x y h).elim)
  invFun := Quot.mk r
  left_inv q := Quot.inductionOn q fun _ => rfl
  right_inv _ := rfl
  continuous_toFun := continuous_quot_lift _ continuous_id
  continuous_invFun := continuous_quot_mk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.Quot.emptyRelation then
    throwError "Refusing to shadow existing declaration Homeomorph.Quot.emptyRelation"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.Quot.emptyRelation ``Submission.Homeomorph.Quot.emptyRelation

@[simp] theorem emptyRelation_mk (r : X → X → Prop) (hr : ∀ x y, ¬ r x y) (x : X) :
    emptyRelation r hr (Quot.mk r x) = x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.Quot.emptyRelation_mk then
    throwError "Refusing to shadow existing declaration Homeomorph.Quot.emptyRelation_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.Quot.emptyRelation_mk ``Submission.Homeomorph.Quot.emptyRelation_mk

@[simp] theorem emptyRelation_symm_apply (r : X → X → Prop) (hr : ∀ x y, ¬ r x y) (x : X) :
    (emptyRelation r hr).symm x = Quot.mk r x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.Quot.emptyRelation_symm_apply then
    throwError "Refusing to shadow existing declaration Homeomorph.Quot.emptyRelation_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.Quot.emptyRelation_symm_apply ``Submission.Homeomorph.Quot.emptyRelation_symm_apply

end Homeomorph.Quot
