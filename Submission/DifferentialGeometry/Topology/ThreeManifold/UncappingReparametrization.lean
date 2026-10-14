import Submission.DifferentialGeometry.Topology.ThreeManifold.PuncturedUncapping
import Submission.DifferentialGeometry.Topology.ThreeManifold.PuncturedCappingReparametrization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

local notation "Sphere" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Annulus" => Sphere × _root_.Set.Icc (1 / 4 : ℝ) 1

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)
  (B : T.Boundary → ClosedCell 3 ≃ₜ ClosedCell 3)
  (hsmall : ∀ b (x : ClosedCell 3), ‖x.val‖ ≤ 1 / 4 → B b x = x)
  (hboundary : ∀ b (z : Sphere), B b (sphereToClosedCell z) = sphereToClosedCell z)

theorem puncturedCappingReparametrization_innerCapBoundary
    (a : T.Index) (side : Bool) (z : Sphere) :
    C.puncturedCappingReparametrization B hsmall hboundary (C.innerCapBoundary a side z) =
      C.innerCapBoundary a side z :=
  C.puncturedCappingReparametrization_inner B hsmall hboundary (a, side) z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_innerCapBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_innerCapBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_innerCapBoundary ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_innerCapBoundary

theorem puncturedCappingReparametrization_innerCapRelation_iff (x y : C.PuncturedCapping) :
    C.innerCapRelation (C.puncturedCappingReparametrization B hsmall hboundary x)
        (C.puncturedCappingReparametrization B hsmall hboundary y) ↔
      C.innerCapRelation x y := by
  let H := C.puncturedCappingReparametrization B hsmall hboundary
  have hf (a : T.Index) (side : Bool) (z : Sphere) :
      H (C.innerCapBoundary a side z) = C.innerCapBoundary a side z :=
    C.puncturedCappingReparametrization_innerCapBoundary B hsmall hboundary a side z
  constructor
  · rintro ⟨a, z, h | h⟩
    · exact ⟨a, z, Or.inl ⟨H.injective (h.1.trans (hf a _root_.Bool.false z).symm),
        H.injective (h.2.trans (hf a _root_.Bool.true z).symm)⟩⟩
    · exact ⟨a, z, Or.inr ⟨H.injective (h.1.trans (hf a _root_.Bool.false z).symm),
        H.injective (h.2.trans (hf a _root_.Bool.true z).symm)⟩⟩
  · rintro ⟨a, z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨a, z, Or.inl ⟨hf a _root_.Bool.false z, hf a _root_.Bool.true z⟩⟩
    · exact ⟨a, z, Or.inr ⟨hf a _root_.Bool.false z, hf a _root_.Bool.true z⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_innerCapRelation_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_innerCapRelation_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_innerCapRelation_iff ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_innerCapRelation_iff

def uncappingQuotientReparametrization : C.UncappingQuotient ≃ₜ C.UncappingQuotient :=
  Homeomorph.Quot.congr (C.puncturedCappingReparametrization B hsmall hboundary)
    (fun x y => (C.puncturedCappingReparametrization_innerCapRelation_iff B hsmall hboundary x y).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization ``Submission.DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization

@[simp] theorem uncappingQuotientReparametrization_mk (x : C.PuncturedCapping) :
    C.uncappingQuotientReparametrization B hsmall hboundary (Quot.mk C.innerCapRelation x) =
      Quot.mk C.innerCapRelation (C.puncturedCappingReparametrization B hsmall hboundary x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_mk ``Submission.DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_mk

@[simp] theorem uncappingQuotientReparametrization_symm_mk (x : C.PuncturedCapping) :
    (C.uncappingQuotientReparametrization B hsmall hboundary).symm (Quot.mk C.innerCapRelation x) =
      Quot.mk C.innerCapRelation ((C.puncturedCappingReparametrization B hsmall hboundary).symm x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_symm_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_symm_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_symm_mk ``Submission.DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_symm_mk

theorem uncappingQuotientReparametrization_core (x : _root_.Set.range C.coreInclusion) :
    C.uncappingQuotientReparametrization B hsmall hboundary
      (Quot.mk C.innerCapRelation (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T))
        C.capAnnuliAttachingMap x)) =
      Quot.mk C.innerCapRelation (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T))
        C.capAnnuliAttachingMap x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_core ``Submission.DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_core

theorem uncappingQuotientReparametrization_symm_core (x : _root_.Set.range C.coreInclusion) :
    (C.uncappingQuotientReparametrization B hsmall hboundary).symm
      (Quot.mk C.innerCapRelation (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T))
        C.capAnnuliAttachingMap x)) =
      Quot.mk C.innerCapRelation (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T))
        C.capAnnuliAttachingMap x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_symm_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_symm_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_symm_core ``Submission.DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_symm_core

theorem uncappingQuotientReparametrization_annulus (b : T.Boundary) (q : Annulus) :
    C.uncappingQuotientReparametrization B hsmall hboundary
      (Quot.mk C.innerCapRelation (adjunctionCell (capAnnuliBoundaryInclusion (T := T))
        C.capAnnuliAttachingMap ⟨b, q⟩)) =
      Quot.mk C.innerCapRelation (adjunctionCell (capAnnuliBoundaryInclusion (T := T))
        C.capAnnuliAttachingMap ⟨b, C.capAnnulusHomeomorph b (B b) (hsmall b) q⟩) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_annulus ``Submission.DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_annulus

theorem uncappingQuotientReparametrization_inner (a : T.Index) (side : Bool) (z : Sphere) :
    C.uncappingQuotientReparametrization B hsmall hboundary
      (Quot.mk C.innerCapRelation (C.innerCapBoundary a side z)) =
      Quot.mk C.innerCapRelation (C.innerCapBoundary a side z) := by
  rw [C.uncappingQuotientReparametrization_mk,
    C.puncturedCappingReparametrization_innerCapBoundary]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_inner ``Submission.DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_inner

theorem uncappingQuotientReparametrization_symm_inner (a : T.Index) (side : Bool) (z : Sphere) :
    (C.uncappingQuotientReparametrization B hsmall hboundary).symm
      (Quot.mk C.innerCapRelation (C.innerCapBoundary a side z)) =
      Quot.mk C.innerCapRelation (C.innerCapBoundary a side z) := by
  apply (C.uncappingQuotientReparametrization B hsmall hboundary).injective
  rw [Homeomorph.apply_symm_apply, C.uncappingQuotientReparametrization_inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_symm_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_symm_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_symm_inner ``Submission.DifferentialGeometry.Topology.SphericalCapping.uncappingQuotientReparametrization_symm_inner

end DifferentialGeometry.Topology.SphericalCapping
