import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.DoublePunctured
import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.DoubleCylinderMappingTorus
import Submission.DifferentialGeometry.Topology.ThreeManifold.SphereMappingTorusTrivialization
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.QuotientTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E4 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE4HAddOfNat : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE4HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE4HAddOfNat target :: scope.openDecls } }

def sphereSelfAttachmentMonodromy (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2 :=
  (sphereAntipodalDiffeomorph (E := E3) (n := 2)).trans a.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentMonodromy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentMonodromy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentMonodromy ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentMonodromy

abbrev SphereSelfAttachment (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) :=
  SelfAttachment.Quotient (stereographicSmallBallChart P) (oppositeStereographicSmallBallChart P)
    (stereographicSmallBallChart_disjoint P) a.toHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.SphereSelfAttachment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.SphereSelfAttachment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.SphereSelfAttachment ``Submission.DifferentialGeometry.Topology.Manifold.SphereSelfAttachment

def doubleCylinderSphereSelfAttachmentHomeomorph (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) :
    DoubleCylinder.Space (sphereSelfAttachmentMonodromy a) ≃ₜ SphereSelfAttachment P a := by
  apply adjunctionSpaceHomeomorphOfHomeomorph
    SelfAttachment.boundaryInclusion (DoubleCylinder.attachingMap (sphereSelfAttachmentMonodromy a))
    SelfAttachment.boundaryInclusion
    (SelfAttachment.attachingMap (stereographicSmallBallChart P) (oppositeStereographicSmallBallChart P)
      (stereographicSmallBallChart_disjoint P) a.toHomeomorph)
    (Homeomorph.refl _) (Homeomorph.refl _) (sphereDoublePuncturedHomeomorph P)
  · intro q
    rfl
  · rintro ⟨b, z⟩
    cases b
    · apply Subtype.ext
      exact sphereDoublePuncturedHomeomorph_lower P z
    · apply Subtype.ext
      change (sphereDoublePuncturedHomeomorph P
        ((sphereSelfAttachmentMonodromy a).symm z, ⟨1, by norm_num⟩)).val =
          (oppositeStereographicSmallBallChart P).chart (a z).val
      rw [sphereDoublePuncturedHomeomorph_upper]
      change (oppositeStereographicSmallBallChart P).chart (-(-(a z))).val = _
      rw [neg_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.doubleCylinderSphereSelfAttachmentHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.doubleCylinderSphereSelfAttachmentHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.doubleCylinderSphereSelfAttachmentHomeomorph ``Submission.DifferentialGeometry.Topology.Manifold.doubleCylinderSphereSelfAttachmentHomeomorph

theorem doubleCylinderSphereSelfAttachmentHomeomorph_core
    (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (p : DoubleCylinder.Cylinder) :
    doubleCylinderSphereSelfAttachmentHomeomorph P a
      (DoubleCylinder.core (sphereSelfAttachmentMonodromy a) p) =
        SelfAttachment.coreInclusion (stereographicSmallBallChart P)
          (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P)
          a.toHomeomorph (sphereDoublePuncturedHomeomorph P p) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.doubleCylinderSphereSelfAttachmentHomeomorph_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.doubleCylinderSphereSelfAttachmentHomeomorph_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.doubleCylinderSphereSelfAttachmentHomeomorph_core ``Submission.DifferentialGeometry.Topology.Manifold.doubleCylinderSphereSelfAttachmentHomeomorph_core

theorem doubleCylinderSphereSelfAttachmentHomeomorph_band
    (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (p : DoubleCylinder.Cylinder) :
    doubleCylinderSphereSelfAttachmentHomeomorph P a
      (DoubleCylinder.band (sphereSelfAttachmentMonodromy a) p) =
        SelfAttachment.bandInclusion (stereographicSmallBallChart P)
          (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P)
          a.toHomeomorph p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.doubleCylinderSphereSelfAttachmentHomeomorph_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.doubleCylinderSphereSelfAttachmentHomeomorph_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.doubleCylinderSphereSelfAttachmentHomeomorph_band ``Submission.DifferentialGeometry.Topology.Manifold.doubleCylinderSphereSelfAttachmentHomeomorph_band

def sphereSelfAttachmentMappingTorusHomeomorph (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) :
    SphereSelfAttachment P a ≃ₜ SphereMappingTorus (sphereSelfAttachmentMonodromy a) :=
  (doubleCylinderSphereSelfAttachmentHomeomorph P a).symm.trans
    (DoubleCylinder.mappingTorusHomeomorph (sphereSelfAttachmentMonodromy a))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentMappingTorusHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentMappingTorusHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentMappingTorusHomeomorph ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentMappingTorusHomeomorph

theorem sphereSelfAttachmentMappingTorusHomeomorph_core
    (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (p : DoubleCylinder.Cylinder) :
    sphereSelfAttachmentMappingTorusHomeomorph P a
      (SelfAttachment.coreInclusion (stereographicSmallBallChart P)
        (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P)
        a.toHomeomorph (sphereDoublePuncturedHomeomorph P p)) =
      DoubleCylinder.coreToMappingTorus (sphereSelfAttachmentMonodromy a) p := by
  rw [← doubleCylinderSphereSelfAttachmentHomeomorph_core]
  rw [sphereSelfAttachmentMappingTorusHomeomorph, Homeomorph.trans_apply,
    Homeomorph.symm_apply_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentMappingTorusHomeomorph_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentMappingTorusHomeomorph_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentMappingTorusHomeomorph_core ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentMappingTorusHomeomorph_core

theorem sphereSelfAttachmentMappingTorusHomeomorph_band
    (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (p : DoubleCylinder.Cylinder) :
    sphereSelfAttachmentMappingTorusHomeomorph P a
      (SelfAttachment.bandInclusion (stereographicSmallBallChart P)
        (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P)
        a.toHomeomorph p) =
      DoubleCylinder.bandToMappingTorus (sphereSelfAttachmentMonodromy a) p := by
  rw [← doubleCylinderSphereSelfAttachmentHomeomorph_band]
  rw [sphereSelfAttachmentMappingTorusHomeomorph, Homeomorph.trans_apply,
    Homeomorph.symm_apply_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentMappingTorusHomeomorph_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentMappingTorusHomeomorph_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentMappingTorusHomeomorph_band ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentMappingTorusHomeomorph_band

end DifferentialGeometry.Topology.Manifold
