import Submission.DifferentialGeometry.Topology.Attachment.AdjunctionHomeomorph
import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.DoubleCylinderMappingTorus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.DoubleCylinder

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo)
  (a c : Cylinder → M) (ha : Continuous a) (hc : Continuous c)
  (hai : Injective a) (hci : Injective c)
  (hcover : range a ∪ range c = univ)
  (hcross : ∀ p q, a p = c q ↔ ∃ z : Bool × SphereTwo,
    SelfAttachment.boundaryInclusion z = p ∧ attachingMap f z = q)

def ambientHomeomorph : Space f ≃ₜ M := by
  have hsurj : _root_.Function.Surjective (Sum.elim a c) := by
    intro y
    have hy : y ∈ _root_.Set.range a ∪ _root_.Set.range c := hcover.symm ▸ _root_.Set.mem_univ y
    rcases hy with ⟨p, rfl⟩ | ⟨q, rfl⟩
    · exact ⟨Sum.inl p, rfl⟩
    · exact ⟨Sum.inr q, rfl⟩
  have hquot : _root_.Topology.IsQuotientMap (Sum.elim a c) :=
    _root_.Topology.IsQuotientMap.of_surjective_continuous hsurj
      (continuous_sum_dom.mpr ⟨ha, hc⟩)
  exact adjunctionHomeomorphOfFibers SelfAttachment.boundaryInclusion (attachingMap f)
    (Sum.elim a c) hquot hai hci hcross

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.ambientHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.ambientHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.ambientHomeomorph ``Submission.DifferentialGeometry.Topology.DoubleCylinder.ambientHomeomorph

@[simp] theorem ambientHomeomorph_mk (p : Cylinder ⊕ Cylinder) :
    ambientHomeomorph f a c ha hc hai hci hcover hcross
      (adjunctionMk SelfAttachment.boundaryInclusion (attachingMap f) p) = Sum.elim a c p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.ambientHomeomorph_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.ambientHomeomorph_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.ambientHomeomorph_mk ``Submission.DifferentialGeometry.Topology.DoubleCylinder.ambientHomeomorph_mk

@[simp] theorem ambientHomeomorph_band (p : Cylinder) :
    ambientHomeomorph f a c ha hc hai hci hcover hcross (band f p) = a p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.ambientHomeomorph_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.ambientHomeomorph_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.ambientHomeomorph_band ``Submission.DifferentialGeometry.Topology.DoubleCylinder.ambientHomeomorph_band

@[simp] theorem ambientHomeomorph_core (p : Cylinder) :
    ambientHomeomorph f a c ha hc hai hci hcover hcross (core f p) = c p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.ambientHomeomorph_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.ambientHomeomorph_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.ambientHomeomorph_core ``Submission.DifferentialGeometry.Topology.DoubleCylinder.ambientHomeomorph_core

def ambientMappingTorusHomeomorph : M ≃ₜ SphereMappingTorus f :=
  (ambientHomeomorph f a c ha hc hai hci hcover hcross).symm.trans (mappingTorusHomeomorph f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorph ``Submission.DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorph

@[simp] theorem ambientMappingTorusHomeomorph_band (p : Cylinder) :
    ambientMappingTorusHomeomorph f a c ha hc hai hci hcover hcross (a p) =
      bandToMappingTorus f p := by
  change mappingTorusHomeomorph f
    ((ambientHomeomorph f a c ha hc hai hci hcover hcross).symm (a p)) = _
  rw [← ambientHomeomorph_band f a c ha hc hai hci hcover hcross p,
    Homeomorph.symm_apply_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorph_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorph_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorph_band ``Submission.DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorph_band

@[simp] theorem ambientMappingTorusHomeomorph_core (p : Cylinder) :
    ambientMappingTorusHomeomorph f a c ha hc hai hci hcover hcross (c p) =
      coreToMappingTorus f p := by
  change mappingTorusHomeomorph f
    ((ambientHomeomorph f a c ha hc hai hci hcover hcross).symm (c p)) = _
  rw [← ambientHomeomorph_core f a c ha hc hai hci hcover hcross p,
    Homeomorph.symm_apply_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorph_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorph_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorph_core ``Submission.DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorph_core

end DifferentialGeometry.Topology.DoubleCylinder


set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.DoubleCylinder

variable {M : Type*}
  (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) (a c : Cylinder → M)
  (hai : Injective a) (hci : Injective c)
  (hinter : range a ∩ range c ⊆
    range (fun z => c (z, ⟨0, by norm_num⟩)) ∪
      range (fun z => c (z, ⟨1, by norm_num⟩)))
  (hzero : ∀ z, a (z, ⟨0, by norm_num⟩) = c (z, ⟨0, by norm_num⟩))
  (hone : ∀ z, a (z, ⟨1, by norm_num⟩) = c (f.symm z, ⟨1, by norm_num⟩))

include hai hci hinter hzero hone in
theorem band_eq_core_iff_of_boundary_eq (p q : Cylinder) :
    a p = c q ↔ ∃ z : Bool × SphereTwo,
      SelfAttachment.boundaryInclusion z = p ∧ attachingMap f z = q := by
  constructor
  · intro hpq
    have hm : a p ∈ _root_.Set.range a ∩ _root_.Set.range c := ⟨⟨p, rfl⟩, ⟨q, hpq.symm⟩⟩
    rcases hinter hm with ⟨z, hz⟩ | ⟨z, hz⟩
    · refine ⟨(_root_.Bool.false, z), hai ((hzero z).trans hz), hci (hz.trans hpq)⟩
    · refine ⟨(_root_.Bool.true, f z), ?_, ?_⟩
      · apply hai
        change a (f z, ⟨1, by norm_num⟩) = a p
        rw [hone, f.symm_apply_apply]
        exact hz
      · apply hci
        change c (f.symm (f z), ⟨1, by norm_num⟩) = c q
        rw [f.symm_apply_apply]
        exact hz.trans hpq
  · rintro ⟨⟨b, z⟩, rfl, rfl⟩
    cases b
    · exact hzero z
    · exact hone z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.band_eq_core_iff_of_boundary_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.band_eq_core_iff_of_boundary_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.band_eq_core_iff_of_boundary_eq ``Submission.DifferentialGeometry.Topology.DoubleCylinder.band_eq_core_iff_of_boundary_eq

variable [TopologicalSpace M] [T2Space M]
  (ha : Continuous a) (hc : Continuous c) (hcover : range a ∪ range c = univ)

def ambientMappingTorusHomeomorphOfBoundaryEquations : M ≃ₜ SphereMappingTorus f :=
  ambientMappingTorusHomeomorph f a c ha hc hai hci hcover
    (band_eq_core_iff_of_boundary_eq f a c hai hci hinter hzero hone)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorphOfBoundaryEquations then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorphOfBoundaryEquations"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorphOfBoundaryEquations ``Submission.DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorphOfBoundaryEquations

@[simp] theorem ambientMappingTorusHomeomorphOfBoundaryEquations_band (p : Cylinder) :
    ambientMappingTorusHomeomorphOfBoundaryEquations f a c hai hci hinter hzero hone
      ha hc hcover (a p) = bandToMappingTorus f p :=
  ambientMappingTorusHomeomorph_band f a c ha hc hai hci hcover _ p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorphOfBoundaryEquations_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorphOfBoundaryEquations_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorphOfBoundaryEquations_band ``Submission.DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorphOfBoundaryEquations_band

@[simp] theorem ambientMappingTorusHomeomorphOfBoundaryEquations_core (p : Cylinder) :
    ambientMappingTorusHomeomorphOfBoundaryEquations f a c hai hci hinter hzero hone
      ha hc hcover (c p) = coreToMappingTorus f p :=
  ambientMappingTorusHomeomorph_core f a c ha hc hai hci hcover _ p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorphOfBoundaryEquations_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorphOfBoundaryEquations_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorphOfBoundaryEquations_core ``Submission.DifferentialGeometry.Topology.DoubleCylinder.ambientMappingTorusHomeomorphOfBoundaryEquations_core

end DifferentialGeometry.Topology.DoubleCylinder
