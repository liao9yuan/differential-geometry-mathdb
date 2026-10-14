import Submission.DifferentialGeometry.Topology.Attachment.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.TopCat.Adjunction
universe u
variable {A B X : TopCat.{u}} (i : A ⟶ B) (φ : A ⟶ X)


def cellMap : B ⟶ TopCat.of (AdjunctionSpace i φ) :=
  TopCat.ofHom ⟨adjunctionCell i φ, continuous_adjunctionCell i φ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TopCat.Adjunction.cellMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TopCat.Adjunction.cellMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TopCat.Adjunction.cellMap ``Submission.DifferentialGeometry.TopCat.Adjunction.cellMap


def lowerMap : X ⟶ TopCat.of (AdjunctionSpace i φ) :=
  TopCat.ofHom ⟨adjunctionLower (i := i) φ, continuous_adjunctionLower i φ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TopCat.Adjunction.lowerMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TopCat.Adjunction.lowerMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TopCat.Adjunction.lowerMap ``Submission.DifferentialGeometry.TopCat.Adjunction.lowerMap


theorem isPushout : _root_.CategoryTheory.IsPushout i φ (cellMap i φ) (lowerMap i φ) := by
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · ext a
    exact adjunction_coherence i φ a
  · apply PushoutCocone.isColimitAux'
    intro s
    let f : B ⊕ X → s.pt := Sum.elim s.inl s.inr
    have hr : ∀ a b : B ⊕ X, adjunctionRel i φ a b → f a = f b := by
      rintro a b ⟨x, h | h⟩
      · rcases h with ⟨rfl, rfl⟩
        exact ConcreteCategory.congr_hom s.condition x
      · rcases h with ⟨rfl, rfl⟩
        exact (ConcreteCategory.congr_hom s.condition x).symm
    let l : TopCat.of (AdjunctionSpace i φ) ⟶ s.pt := TopCat.ofHom
      ⟨Quot.lift f hr, continuous_adjunction_lift i φ hr
        (s.inl.hom.continuous.sumElim s.inr.hom.continuous)⟩
    refine ⟨l, ?_, ?_, ?_⟩
    · ext x
      rfl
    · ext x
      rfl
    · intro m hm hb
      ext q
      induction q using Quot.inductionOn with
      | h v =>
        cases v with
        | inl v => exact ConcreteCategory.congr_hom hm v
        | inr v => exact ConcreteCategory.congr_hom hb v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TopCat.Adjunction.isPushout then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TopCat.Adjunction.isPushout"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TopCat.Adjunction.isPushout ``Submission.DifferentialGeometry.TopCat.Adjunction.isPushout

end DifferentialGeometry.TopCat.Adjunction
