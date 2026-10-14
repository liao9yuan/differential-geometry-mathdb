import Submission.DifferentialGeometry.Topology.Attachment.Basic
import Mathlib.Topology.UnitInterval

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Topology
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Topology

variable {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]


abbrev MappingCylinder (f : C(A, X)) :=
  DifferentialGeometry.Topology.AdjunctionSpace
    (fun a : A => (a, (0 : _root_.Set.Icc (0 : ℝ) 1))) f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MappingCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MappingCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MappingCylinder ``Submission.DifferentialGeometry.Topology.MappingCylinder


def mappingCylinderOriginal (f : C(A, X)) : C(X, MappingCylinder f) :=
  ⟨DifferentialGeometry.Topology.adjunctionLower f,
    DifferentialGeometry.Topology.continuous_adjunctionLower _ _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mappingCylinderOriginal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mappingCylinderOriginal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mappingCylinderOriginal ``Submission.DifferentialGeometry.Topology.mappingCylinderOriginal


def mappingCylinderProduct (f : C(A, X)) : C(A × _root_.Set.Icc (0 : ℝ) 1, MappingCylinder f) :=
  ⟨DifferentialGeometry.Topology.adjunctionCell _ f,
    DifferentialGeometry.Topology.continuous_adjunctionCell _ _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mappingCylinderProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mappingCylinderProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mappingCylinderProduct ``Submission.DifferentialGeometry.Topology.mappingCylinderProduct


theorem mappingCylinder_seam (f : C(A, X)) (a : A) :
    mappingCylinderProduct f (a, 0) = mappingCylinderOriginal f (f a) :=
  DifferentialGeometry.Topology.adjunction_coherence _ _ a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mappingCylinder_seam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mappingCylinder_seam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mappingCylinder_seam ``Submission.DifferentialGeometry.Topology.mappingCylinder_seam


def mappingCylinderRetract (f : C(A, X)) : C(MappingCylinder f, X) := by
  let r : (A × _root_.Set.Icc (0 : ℝ) 1) ⊕ X → X := Sum.elim (fun p => f p.1) id
  have hr : ∀ a b, DifferentialGeometry.Topology.adjunctionRel
      (fun a : A => (a, (0 : _root_.Set.Icc (0 : ℝ) 1))) f a b → r a = r b := by
    rintro a b ⟨p, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ <;> rfl
  exact ⟨Quot.lift r hr, DifferentialGeometry.Topology.continuous_adjunction_lift _ _ hr
    (Continuous.sumElim (f.continuous.comp continuous_fst) continuous_id)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mappingCylinderRetract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mappingCylinderRetract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mappingCylinderRetract ``Submission.DifferentialGeometry.Topology.mappingCylinderRetract

def mappingCylinderHeight (f : C(A, X)) : C(MappingCylinder f, _root_.Set.Icc (0 : ℝ) 1) := by
  let r : (A × _root_.Set.Icc (0 : ℝ) 1) ⊕ X → _root_.Set.Icc (0 : ℝ) 1 := Sum.elim Prod.snd (fun _ => 0)
  have hr : ∀ a b, DifferentialGeometry.Topology.adjunctionRel
      (fun a : A => (a, (0 : _root_.Set.Icc (0 : ℝ) 1))) f a b → r a = r b := by
    rintro a b ⟨p, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ <;> rfl
  exact ⟨Quot.lift r hr, DifferentialGeometry.Topology.continuous_adjunction_lift _ _ hr
    (Continuous.sumElim continuous_snd continuous_const)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mappingCylinderHeight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mappingCylinderHeight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mappingCylinderHeight ``Submission.DifferentialGeometry.Topology.mappingCylinderHeight

@[simp] theorem mappingCylinderRetract_original (f : C(A, X)) (x : X) :
    mappingCylinderRetract f (mappingCylinderOriginal f x) = x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mappingCylinderRetract_original then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mappingCylinderRetract_original"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mappingCylinderRetract_original ``Submission.DifferentialGeometry.Topology.mappingCylinderRetract_original

@[simp] theorem mappingCylinderRetract_product (f : C(A, X)) (p : A × _root_.Set.Icc (0 : ℝ) 1) :
    mappingCylinderRetract f (mappingCylinderProduct f p) = f p.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mappingCylinderRetract_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mappingCylinderRetract_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mappingCylinderRetract_product ``Submission.DifferentialGeometry.Topology.mappingCylinderRetract_product

@[simp] theorem mappingCylinderHeight_original (f : C(A, X)) (x : X) :
    mappingCylinderHeight f (mappingCylinderOriginal f x) = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mappingCylinderHeight_original then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mappingCylinderHeight_original"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mappingCylinderHeight_original ``Submission.DifferentialGeometry.Topology.mappingCylinderHeight_original

@[simp] theorem mappingCylinderHeight_product (f : C(A, X)) (p : A × _root_.Set.Icc (0 : ℝ) 1) :
    mappingCylinderHeight f (mappingCylinderProduct f p) = p.2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mappingCylinderHeight_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mappingCylinderHeight_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mappingCylinderHeight_product ``Submission.DifferentialGeometry.Topology.mappingCylinderHeight_product


theorem isEmbedding_mappingCylinderOriginal (f : C(A, X)) :
    IsEmbedding (mappingCylinderOriginal f) :=
  (show _root_.Function.LeftInverse (mappingCylinderRetract f) (mappingCylinderOriginal f) from
    mappingCylinderRetract_original f).isEmbedding
      (mappingCylinderRetract f).continuous (mappingCylinderOriginal f).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isEmbedding_mappingCylinderOriginal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isEmbedding_mappingCylinderOriginal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isEmbedding_mappingCylinderOriginal ``Submission.DifferentialGeometry.Topology.isEmbedding_mappingCylinderOriginal

theorem mappingCylinder_product_eq_original_iff (f : C(A, X))
    (p : A × _root_.Set.Icc (0 : ℝ) 1) (x : X) :
    mappingCylinderProduct f p = mappingCylinderOriginal f x ↔ p.2 = 0 ∧ f p.1 = x := by
  constructor
  · intro h
    exact ⟨congrArg (mappingCylinderHeight f) h, congrArg (mappingCylinderRetract f) h⟩
  · rintro ⟨ht, rfl⟩
    rcases p with ⟨a, t⟩
    dsimp at ht
    subst t
    exact mappingCylinder_seam f a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mappingCylinder_product_eq_original_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mappingCylinder_product_eq_original_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mappingCylinder_product_eq_original_iff ``Submission.DifferentialGeometry.Topology.mappingCylinder_product_eq_original_iff


theorem range_mappingCylinderOriginal (f : C(A, X)) :
    range (mappingCylinderOriginal f) = (mappingCylinderHeight f) ⁻¹' {0} := by
  ext z
  refine Quot.inductionOn z ?_
  intro q
  cases q with
  | inl p =>
      change (∃ x, mappingCylinderOriginal f x = mappingCylinderProduct f p) ↔ p.2 = 0
      constructor
      · rintro ⟨x, hx⟩
        exact ((mappingCylinder_product_eq_original_iff f p x).mp hx.symm).1
      · intro ht
        exact ⟨f p.1, ((mappingCylinder_product_eq_original_iff f p (f p.1)).mpr ⟨ht, rfl⟩).symm⟩
  | inr x =>
      exact iff_of_true ⟨x, rfl⟩ (_root_.Set.mem_singleton 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.range_mappingCylinderOriginal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.range_mappingCylinderOriginal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.range_mappingCylinderOriginal ``Submission.DifferentialGeometry.Topology.range_mappingCylinderOriginal


theorem isClosedEmbedding_mappingCylinderOriginal (f : C(A, X)) :
    IsClosedEmbedding (mappingCylinderOriginal f) :=
  ⟨isEmbedding_mappingCylinderOriginal f, by
    rw [range_mappingCylinderOriginal]
    exact isClosed_singleton.preimage (mappingCylinderHeight f).continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isClosedEmbedding_mappingCylinderOriginal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isClosedEmbedding_mappingCylinderOriginal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isClosedEmbedding_mappingCylinderOriginal ``Submission.DifferentialGeometry.Topology.isClosedEmbedding_mappingCylinderOriginal


theorem isEmbedding_mappingCylinderProduct (f : C(A, X)) (hf : _root_.Topology.IsEmbedding f) :
    IsEmbedding (mappingCylinderProduct f) := by
  apply IsEmbedding.of_comp (mappingCylinderProduct f).continuous
    ((mappingCylinderRetract f).continuous.prodMk (mappingCylinderHeight f).continuous)
  exact hf.prodMap IsEmbedding.id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isEmbedding_mappingCylinderProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isEmbedding_mappingCylinderProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isEmbedding_mappingCylinderProduct ``Submission.DifferentialGeometry.Topology.isEmbedding_mappingCylinderProduct

theorem range_mappingCylinderProduct (f : C(A, X)) :
    range (mappingCylinderProduct f) = (mappingCylinderRetract f) ⁻¹' _root_.Set.range f := by
  ext z
  refine Quot.inductionOn z ?_
  intro q
  cases q with
  | inl p => exact iff_of_true ⟨p, rfl⟩ ⟨p.1, rfl⟩
  | inr x =>
      change (∃ p, mappingCylinderProduct f p = mappingCylinderOriginal f x) ↔ ∃ a, f a = x
      constructor
      · rintro ⟨p, hp⟩
        exact ⟨p.1, ((mappingCylinder_product_eq_original_iff f p x).mp hp).2⟩
      · rintro ⟨a, rfl⟩
        exact ⟨(a, 0), mappingCylinder_seam f a⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.range_mappingCylinderProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.range_mappingCylinderProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.range_mappingCylinderProduct ``Submission.DifferentialGeometry.Topology.range_mappingCylinderProduct


theorem isClosedEmbedding_mappingCylinderProduct (f : C(A, X)) (hf : _root_.Topology.IsClosedEmbedding f) :
    IsClosedEmbedding (mappingCylinderProduct f) :=
  ⟨isEmbedding_mappingCylinderProduct f hf.isEmbedding, by
    rw [range_mappingCylinderProduct]
    exact hf.isClosed_range.preimage (mappingCylinderRetract f).continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isClosedEmbedding_mappingCylinderProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isClosedEmbedding_mappingCylinderProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isClosedEmbedding_mappingCylinderProduct ``Submission.DifferentialGeometry.Topology.isClosedEmbedding_mappingCylinderProduct

end DifferentialGeometry.Topology
