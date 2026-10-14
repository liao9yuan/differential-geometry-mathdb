import Submission.DifferentialGeometry.Topology.Attachment.MappingCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Topology
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Topology

variable {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]


def mappingCylinderDesc (f : C(A, X)) (g : C(A × _root_.Set.Icc (0 : ℝ) 1, Y)) (j : C(X, Y))
    (hseam : ∀ a, g (a, 0) = j (f a)) : C(MappingCylinder f, Y) := by
  let r : (A × _root_.Set.Icc (0 : ℝ) 1) ⊕ X → Y := Sum.elim g j
  have hr : ∀ a b, DifferentialGeometry.Topology.adjunctionRel
      (fun a : A => (a, (0 : _root_.Set.Icc (0 : ℝ) 1))) f a b → r a = r b := by
    rintro a b ⟨p, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact hseam p
    · exact (hseam p).symm
  exact ⟨Quot.lift r hr, DifferentialGeometry.Topology.continuous_adjunction_lift _ _ hr
    (Continuous.sumElim g.continuous j.continuous)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mappingCylinderDesc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mappingCylinderDesc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mappingCylinderDesc ``Submission.DifferentialGeometry.Topology.mappingCylinderDesc

@[simp] theorem mappingCylinderDesc_original (f : C(A, X))
    (g : C(A × _root_.Set.Icc (0 : ℝ) 1, Y)) (j : C(X, Y)) (hseam : ∀ a, g (a, 0) = j (f a)) (x : X) :
    mappingCylinderDesc f g j hseam (mappingCylinderOriginal f x) = j x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mappingCylinderDesc_original then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mappingCylinderDesc_original"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mappingCylinderDesc_original ``Submission.DifferentialGeometry.Topology.mappingCylinderDesc_original

@[simp] theorem mappingCylinderDesc_product (f : C(A, X))
    (g : C(A × _root_.Set.Icc (0 : ℝ) 1, Y)) (j : C(X, Y)) (hseam : ∀ a, g (a, 0) = j (f a))
    (p : A × _root_.Set.Icc (0 : ℝ) 1) :
    mappingCylinderDesc f g j hseam (mappingCylinderProduct f p) = g p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mappingCylinderDesc_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mappingCylinderDesc_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mappingCylinderDesc_product ``Submission.DifferentialGeometry.Topology.mappingCylinderDesc_product

theorem isClosedMap_mappingCylinderDesc (f : C(A, X))
    (g : C(A × _root_.Set.Icc (0 : ℝ) 1, Y)) (j : C(X, Y)) (hseam : ∀ a, g (a, 0) = j (f a))
    (hg : IsClosedMap g) (hj : IsClosedMap j) :
    IsClosedMap (mappingCylinderDesc f g j hseam) := by
  intro S hS
  have heq : mappingCylinderDesc f g j hseam '' S =
      g '' ((mappingCylinderProduct f) ⁻¹' S) ∪ j '' ((mappingCylinderOriginal f) ⁻¹' S) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨q, rfl⟩ := Quot.exists_rep z
      cases q with
      | inl p => exact Or.inl ⟨p, hz, rfl⟩
      | inr x => exact Or.inr ⟨x, hz, rfl⟩
    · rintro (⟨p, hp, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact ⟨mappingCylinderProduct f p, hp, rfl⟩
      · exact ⟨mappingCylinderOriginal f x, hx, rfl⟩
  rw [heq]
  exact (hg _ (hS.preimage (mappingCylinderProduct f).continuous)).union
    (hj _ (hS.preimage (mappingCylinderOriginal f).continuous))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isClosedMap_mappingCylinderDesc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isClosedMap_mappingCylinderDesc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isClosedMap_mappingCylinderDesc ``Submission.DifferentialGeometry.Topology.isClosedMap_mappingCylinderDesc

def mappingCylinderHomeomorphOfClosedCover (f : C(A, X))
    (g : C(A × _root_.Set.Icc (0 : ℝ) 1, Y)) (j : C(X, Y)) (hseam : ∀ a, g (a, 0) = j (f a))
    (hg : _root_.Topology.IsClosedEmbedding g) (hj : _root_.Topology.IsClosedEmbedding j)
    (hcross : ∀ p x, g p = j x → p.2 = 0 ∧ f p.1 = x)
    (hcover : _root_.Set.range g ∪ _root_.Set.range j = _root_.Set.univ) : MappingCylinder f ≃ₜ Y := by
  let d := mappingCylinderDesc f g j hseam
  have hdinj : _root_.Function.Injective d := by
    intro z z' h
    obtain ⟨q, rfl⟩ := Quot.exists_rep z
    obtain ⟨q', rfl⟩ := Quot.exists_rep z'
    cases q with
    | inl p =>
      cases q' with
      | inl p' => exact congrArg (mappingCylinderProduct f) (hg.injective h)
      | inr x => exact (mappingCylinder_product_eq_original_iff f p x).mpr (hcross p x h)
    | inr x =>
      cases q' with
      | inl p => exact ((mappingCylinder_product_eq_original_iff f p x).mpr (hcross p x h.symm)).symm
      | inr x' => exact congrArg (mappingCylinderOriginal f) (hj.injective h)
  have hdsurj : _root_.Function.Surjective d := by
    intro y
    have hy : y ∈ _root_.Set.range g ∪ _root_.Set.range j := hcover ▸ _root_.Set.mem_univ y
    rcases hy with ⟨p, rfl⟩ | ⟨x, rfl⟩
    · exact ⟨mappingCylinderProduct f p, rfl⟩
    · exact ⟨mappingCylinderOriginal f x, rfl⟩
  exact (isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨d.continuous, isClosedMap_mappingCylinderDesc f g j hseam hg.isClosedMap hj.isClosedMap,
      hdinj, hdsurj⟩).homeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mappingCylinderHomeomorphOfClosedCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mappingCylinderHomeomorphOfClosedCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mappingCylinderHomeomorphOfClosedCover ``Submission.DifferentialGeometry.Topology.mappingCylinderHomeomorphOfClosedCover

@[simp] theorem mappingCylinderHomeomorphOfClosedCover_original (f : C(A, X))
    (g : C(A × _root_.Set.Icc (0 : ℝ) 1, Y)) (j : C(X, Y)) (hseam : ∀ a, g (a, 0) = j (f a))
    (hg : _root_.Topology.IsClosedEmbedding g) (hj : _root_.Topology.IsClosedEmbedding j)
    (hcross : ∀ p x, g p = j x → p.2 = 0 ∧ f p.1 = x)
    (hcover : _root_.Set.range g ∪ _root_.Set.range j = _root_.Set.univ) (x : X) :
    mappingCylinderHomeomorphOfClosedCover f g j hseam hg hj hcross hcover
      (mappingCylinderOriginal f x) = j x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mappingCylinderHomeomorphOfClosedCover_original then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mappingCylinderHomeomorphOfClosedCover_original"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mappingCylinderHomeomorphOfClosedCover_original ``Submission.DifferentialGeometry.Topology.mappingCylinderHomeomorphOfClosedCover_original

@[simp] theorem mappingCylinderHomeomorphOfClosedCover_product (f : C(A, X))
    (g : C(A × _root_.Set.Icc (0 : ℝ) 1, Y)) (j : C(X, Y)) (hseam : ∀ a, g (a, 0) = j (f a))
    (hg : _root_.Topology.IsClosedEmbedding g) (hj : _root_.Topology.IsClosedEmbedding j)
    (hcross : ∀ p x, g p = j x → p.2 = 0 ∧ f p.1 = x)
    (hcover : _root_.Set.range g ∪ _root_.Set.range j = _root_.Set.univ) (p : A × _root_.Set.Icc (0 : ℝ) 1) :
    mappingCylinderHomeomorphOfClosedCover f g j hseam hg hj hcross hcover
      (mappingCylinderProduct f p) = g p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mappingCylinderHomeomorphOfClosedCover_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mappingCylinderHomeomorphOfClosedCover_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mappingCylinderHomeomorphOfClosedCover_product ``Submission.DifferentialGeometry.Topology.mappingCylinderHomeomorphOfClosedCover_product

end DifferentialGeometry.Topology
