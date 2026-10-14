import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.Smooth
import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.DoubleCylinderInterior

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Filter
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
private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.IC target :: scope.openDecls } }
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

variable (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
  (D : ℝ ≃ₘ[ℝ] ℝ) (hI : D '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1)
  (h0 : D 0 = 0) (h1 : D 1 = 1)
  (J : SphereMappingTorusIsotopy) (hJtarget : J.target = sphereSelfAttachmentMonodromy a)

private abbrev monodromyIsotopy : SphereMappingTorusIsotopy where
  target := sphereSelfAttachmentMonodromy a
  isotopy := J.isotopy
  continuous_apply := J.continuous_apply
  isotopy_zero := J.isotopy_zero
  isotopy_one := J.isotopy_one.trans hJtarget

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.monodromyIsotopy
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.monodromyIsotopy target :: scope.openDecls } }

def sphereSelfAttachmentCoreInterior (p : DoubleCylinder.Interior) : SphereSelfAttachment P a :=
  SelfAttachment.coreInclusion (stereographicSmallBallChart P)
    (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P) a.toHomeomorph
    (sphereDoublePuncturedHomeomorph P
      (p.val.1, unitIntervalRestriction D hI ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreInterior ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreInterior

def sphereSelfAttachmentBandInterior (p : DoubleCylinder.Interior) : SphereSelfAttachment P a :=
  SelfAttachment.bandInclusion (stereographicSmallBallChart P)
    (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P) a.toHomeomorph
    (p.val.1, ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentBandInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentBandInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentBandInterior ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentBandInterior

theorem sphereSelfAttachmentCoreInterior_isLocalDiffeomorph
    (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
    (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1)) :
    let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorph IC IC ∞ (sphereSelfAttachmentCoreInterior P a D hI) := by
  let J' := monodromyIsotopy a J hJtarget
  let _ := sphereMappingTorusChartedSpace J'.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (DoubleCylinder.mappingTorusHomeomorph J'.target)
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  have hbase := DoubleCylinder.interiorCore_isLocalDiffeomorph J' hJ hJi
  have hH := (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := IC) (n := ∞) (sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1).symm).symm.isLocalDiffeomorph
  have hcomp := DifferentialGeometry.isLocalDiffeomorph_comp hH hbase
  have heq : (sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1) ∘
      DoubleCylinder.interiorCore (sphereSelfAttachmentMonodromy a) =
        sphereSelfAttachmentCoreInterior P a D hI := by
    funext p
    exact sphereSelfAttachmentReparametrizedHomeomorph_core P a D hI h0 h1
      (p.val.1, ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩)
  change IsLocalDiffeomorph IC IC ∞ ((sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1) ∘
    DoubleCylinder.interiorCore (sphereSelfAttachmentMonodromy a)) at hcomp
  rwa [heq] at hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreInterior_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreInterior_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreInterior_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreInterior_isLocalDiffeomorph

theorem sphereSelfAttachmentBandInterior_isLocalDiffeomorph
    (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
    (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1)) :
    let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorph IC IC ∞ (sphereSelfAttachmentBandInterior P a) := by
  let J' := monodromyIsotopy a J hJtarget
  let _ := sphereMappingTorusChartedSpace J'.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (DoubleCylinder.mappingTorusHomeomorph J'.target)
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  have hbase := DoubleCylinder.interiorBand_isLocalDiffeomorph J' hJ hJi
  have hH := (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := IC) (n := ∞) (sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1).symm).symm.isLocalDiffeomorph
  have hcomp := DifferentialGeometry.isLocalDiffeomorph_comp hH hbase
  have heq : (sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1) ∘
      DoubleCylinder.interiorBand (sphereSelfAttachmentMonodromy a) =
        sphereSelfAttachmentBandInterior P a := by
    funext p
    exact sphereSelfAttachmentReparametrizedHomeomorph_band P a D hI h0 h1
      (p.val.1, ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩)
  change IsLocalDiffeomorph IC IC ∞ ((sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1) ∘
    DoubleCylinder.interiorBand (sphereSelfAttachmentMonodromy a)) at hcomp
  rwa [heq] at hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentBandInterior_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentBandInterior_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentBandInterior_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentBandInterior_isLocalDiffeomorph

private def cylinderReparametrization : Diffeomorph IC IC (S2 × ℝ) (S2 × ℝ) ∞ where
  toFun p := (-p.1, D p.2)
  invFun p := (-p.1, D.symm p.2)
  left_inv p := Prod.ext (neg_neg p.1) (D.symm_apply_apply p.2)
  right_inv p := Prod.ext (neg_neg p.1) (D.apply_symm_apply p.2)
  contMDiff_toFun :=
    ((sphereAntipodalDiffeomorph (E := E3) (n := 2)).contMDiff.comp contMDiff_fst).prodMk
      (D.contMDiff.comp contMDiff_snd)
  contMDiff_invFun :=
    ((sphereAntipodalDiffeomorph (E := E3) (n := 2)).contMDiff.comp contMDiff_fst).prodMk
      (D.symm.contMDiff.comp contMDiff_snd)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.cylinderReparametrization
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.cylinderReparametrization target :: scope.openDecls } }

def sphereDoublePuncturedInterior (p : DoubleCylinder.Interior) : S3 :=
  (sphereDoublePuncturedHomeomorph P
    (p.val.1, unitIntervalRestriction D hI ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩)).val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInterior ``Submission.DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInterior

theorem sphereDoublePuncturedInterior_isLocalDiffeomorph :
    IsLocalDiffeomorph IC (𝓡 3) ∞ (sphereDoublePuncturedInterior P D hI) := by
  have hres := DifferentialGeometry.isLocalDiffeomorph_restrict_open DoubleCylinder.Interior
    ((cylinderReparametrization D).isLocalDiffeomorph.isLocalDiffeomorphOn DoubleCylinder.Interior)
  intro p
  have hmem : D p.val.2 ∈ _root_.Set.Icc (0 : ℝ) 1 := by
    rw [← hI]
    exact ⟨p.val.2, ⟨p.property.2.1.le, p.property.2.2.le⟩, rfl⟩
  have hrad := stereographic_radial_isLocalDiffeomorphAt P (1 / 2) 8 (by norm_num)
    ((cylinderReparametrization D) p.val) (by change 0 < 1 / 2 + (8 - 1 / 2) * D p.val.2; nlinarith [hmem.1])
  have hcomp := (hres p).comp (K := 𝓡 3) (P := S3) hrad
  exact hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInterior_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInterior_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInterior_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInterior_isLocalDiffeomorph

theorem sphereDoublePuncturedInterior_injective : _root_.Function.Injective (sphereDoublePuncturedInterior P D hI) := by
  intro p q h
  have hq := (sphereDoublePuncturedHomeomorph P).injective (Subtype.ext h)
  apply Subtype.ext
  refine Prod.ext (congrArg (fun x : S2 × _root_.Set.Icc (0 : ℝ) 1 => x.1) hq) ?_
  have ht := congrArg (fun x : S2 × _root_.Set.Icc (0 : ℝ) 1 => x.2.val) hq
  exact D.injective ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInterior_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInterior_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInterior_injective ``Submission.DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInterior_injective

def sphereDoublePuncturedInteriorImage : TopologicalSpace.Opens S3 :=
  ⟨range (sphereDoublePuncturedInterior P D hI),
    (sphereDoublePuncturedInterior_isLocalDiffeomorph P D hI).isOpenMap.isOpen_range⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInteriorImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInteriorImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInteriorImage ``Submission.DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInteriorImage

def sphereDoublePuncturedInteriorDiffeomorph :
    Diffeomorph IC (𝓡 3) DoubleCylinder.Interior (sphereDoublePuncturedInteriorImage P D hI) ∞ := by
  have hloc : IsLocalDiffeomorph IC (𝓡 3) ∞
      (fun p : DoubleCylinder.Interior =>
        (⟨sphereDoublePuncturedInterior P D hI p, ⟨p, rfl⟩⟩ : sphereDoublePuncturedInteriorImage P D hI)) := by
    intro p
    exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
      (fun q : DoubleCylinder.Interior => show sphereDoublePuncturedInterior P D hI q ∈
        sphereDoublePuncturedInteriorImage P D hI from ⟨q, rfl⟩)
      (sphereDoublePuncturedInterior_isLocalDiffeomorph P D hI p)
  exact hloc.diffeomorphOfBijective ⟨fun p q hpq =>
    sphereDoublePuncturedInterior_injective P D hI (congrArg (fun x : sphereDoublePuncturedInteriorImage P D hI => x.val) hpq), by
      rintro ⟨q, p, hp⟩
      exact ⟨p, Subtype.ext hp⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInteriorDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInteriorDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInteriorDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInteriorDiffeomorph

theorem sphereDoublePuncturedInteriorDiffeomorph_apply (p : DoubleCylinder.Interior) :
    (sphereDoublePuncturedInteriorDiffeomorph P D hI p).val = sphereDoublePuncturedInterior P D hI p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInteriorDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInteriorDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInteriorDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedInteriorDiffeomorph_apply

def sphereSelfAttachmentCoreMap (p : sphereDoublePuncturedInteriorImage P D hI) : SphereSelfAttachment P a :=
  sphereSelfAttachmentCoreInterior P a D hI ((sphereDoublePuncturedInteriorDiffeomorph P D hI).symm p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreMap ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreMap

theorem sphereSelfAttachmentCoreMap_isLocalDiffeomorph
    (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
    (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1)) :
    let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorph (𝓡 3) IC ∞ (sphereSelfAttachmentCoreMap P a D hI) := by
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  exact DifferentialGeometry.isLocalDiffeomorph_comp
    (sphereSelfAttachmentCoreInterior_isLocalDiffeomorph P a D hI h0 h1 J hJtarget hJ hJi)
    (sphereDoublePuncturedInteriorDiffeomorph P D hI).symm.isLocalDiffeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreMap_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreMap_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreMap_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreMap_isLocalDiffeomorph

theorem sphereSelfAttachmentCoreMap_eq (p : sphereDoublePuncturedInteriorImage P D hI) :
    ∃ hp, sphereSelfAttachmentCoreMap P a D hI p =
      SelfAttachment.coreInclusion (stereographicSmallBallChart P)
        (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P)
        a.toHomeomorph ⟨p.val, hp⟩ := by
  let x := (sphereDoublePuncturedInteriorDiffeomorph P D hI).symm p
  let q := sphereDoublePuncturedHomeomorph P
    (x.val.1, unitIntervalRestriction D hI ⟨x.val.2, x.property.2.1.le, x.property.2.2.le⟩)
  have hval : q.val = p.val := by
    have h := congrArg Subtype.val
      ((sphereDoublePuncturedInteriorDiffeomorph P D hI).apply_symm_apply p)
    rw [sphereDoublePuncturedInteriorDiffeomorph_apply] at h
    exact h
  refine ⟨hval ▸ q.property, ?_⟩
  exact congrArg (SelfAttachment.coreInclusion _ _ _ _) (Subtype.ext hval)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreMap_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreMap_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreMap_eq ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentCoreMap_eq

end DifferentialGeometry.Topology.Manifold
