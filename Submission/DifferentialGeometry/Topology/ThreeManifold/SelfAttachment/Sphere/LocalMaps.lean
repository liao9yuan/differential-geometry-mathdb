import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.StandardModel
import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.LocalMaps

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
  (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
  (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1))

include hJ hJi in
theorem sphereSelfAttachmentStandard_bandInterior_isLocalDiffeomorph :
    let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorph IC (𝓡 3) ∞
      (SelfAttachment.bandInteriorInclusion (stereographicSmallBallChart P)
        (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P) a.toHomeomorph) := by
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  let F : Diffeomorph IC ((𝓡 2).prod (𝓡 1)) (SphereSelfAttachment P a) SphereTwoTimesCircle ∞ :=
    sphereSelfAttachmentDiffeomorphSphereTwoTimesCircle P a D hI h0 h1 J hJtarget
  have h := sphereSelfAttachmentBandInterior_isLocalDiffeomorph P a D hI h0 h1 J hJtarget hJ hJi
  have h1loc := DifferentialGeometry.isLocalDiffeomorph_comp F.isLocalDiffeomorph h
  have h2loc := DifferentialGeometry.isLocalDiffeomorph_comp
    sphereTwoTimesCircleModelCopy.equiv.isLocalDiffeomorph h1loc
  let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
  let G : Diffeomorph (𝓡 3) (𝓡 3) (SphereSelfAttachment P a) sphereTwoTimesCircleLift.Carrier ∞ :=
    sphereSelfAttachmentStandardDiffeomorph P a D hI h0 h1 J hJtarget
  have h3 := DifferentialGeometry.isLocalDiffeomorph_comp G.symm.isLocalDiffeomorph h2loc
  have heq : G.symm ∘ (sphereTwoTimesCircleModelCopy.equiv ∘ (F ∘ sphereSelfAttachmentBandInterior P a)) =
      sphereSelfAttachmentBandInterior P a := by
    funext y
    exact (sphereSelfAttachmentStandardHomeomorph P a D hI h0 h1 J hJtarget).symm_apply_apply _
  change IsLocalDiffeomorph IC (𝓡 3) ∞ (sphereSelfAttachmentBandInterior P a)
  intro x
  exact IsLocalDiffeomorphAt.of_eventuallyEq (Filter.EventuallyEq.of_eq heq.symm) (h3 x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_bandInterior_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_bandInterior_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_bandInterior_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_bandInterior_isLocalDiffeomorph

include hJ hJi in
theorem sphereSelfAttachmentStandard_coreInterior_isLocalDiffeomorph :
    let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (SelfAttachment.coreInteriorInclusion (stereographicSmallBallChart P)
        (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P) a.toHomeomorph) := by
  let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
  let U := SelfAttachment.coreInterior (stereographicSmallBallChart P) (oppositeStereographicSmallBallChart P)
  have hmem (x : U) : x.val ∈ sphereDoublePuncturedInteriorImage P D hI := by
    change x.val ∈ (sphereDoublePuncturedInteriorImage P D hI : Set S3)
    rw [sphereDoublePuncturedInteriorImage_eq P D hI h0 h1]
    exact x.property
  let f : U → sphereDoublePuncturedInteriorImage P D hI := fun x => ⟨x.val, hmem x⟩
  have hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f := fun x =>
    DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict hmem
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val U x)
  have hcomp := DifferentialGeometry.isLocalDiffeomorph_comp
    (sphereSelfAttachmentStandard_core_isLocalDiffeomorph P a D hI h0 h1 J hJtarget hJ hJi) hf
  have heq : sphereSelfAttachmentCoreMap P a D hI ∘ f =
      SelfAttachment.coreInteriorInclusion (stereographicSmallBallChart P)
        (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P) a.toHomeomorph := by
    funext x
    obtain ⟨hx, hval⟩ := sphereSelfAttachmentCoreMap_eq P a D hI (f x)
    exact hval
  rwa [heq] at hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_coreInterior_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_coreInterior_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_coreInterior_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_coreInterior_isLocalDiffeomorph

private def collarProductOpen : TopologicalSpace.Opens (S2 × ℝ) :=
  ⟨univ ×ˢ ConnectedSumQuotient.collarInterval, isOpen_univ.prod ConnectedSumQuotient.collarInterval.isOpen⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.collarProductOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.collarProductOpen target :: scope.openDecls } }

private def collarProductDiffeomorph :
    Diffeomorph IC IC collarProductOpen SelfAttachment.CollarDomain ∞ where
  toFun p := (p.val.1, ⟨p.val.2, p.property.2⟩)
  invFun p := ⟨(p.1, p.2.val), _root_.Set.mem_univ _, p.2.property⟩
  left_inv p := rfl
  right_inv p := rfl
  contMDiff_toFun := by
    apply ContMDiff.prodMk
    · exact contMDiff_fst.comp contMDiff_subtype_val
    · apply (ContMDiff.subtypeVal_comp_iff ConnectedSumQuotient.collarInterval _).mp
      exact contMDiff_snd.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff collarProductOpen _).mp
    exact contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.collarProductDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.collarProductDiffeomorph target :: scope.openDecls } }

private def reverseParameter (b : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (p : DoubleCylinder.seamDomain) : SelfAttachment.CollarDomain :=
  (b p.val.1, ⟨-p.val.2, by
    constructor <;> linarith [p.property.2.1, p.property.2.2]⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.reverseParameter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.reverseParameter target :: scope.openDecls } }

private theorem reverseParameter_isLocalDiffeomorph (b : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) :
    IsLocalDiffeomorph IC IC ∞ (reverseParameter b) := by
  let F := b.prodCongr (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).toDiffeomorph
  have hres := DifferentialGeometry.isLocalDiffeomorph_restrict_open DoubleCylinder.seamDomain
    (F.isLocalDiffeomorph.isLocalDiffeomorphOn DoubleCylinder.seamDomain)
  have hmem (p : DoubleCylinder.seamDomain) : F p.val ∈ collarProductOpen := by
    refine ⟨mem_univ _, ?_⟩
    change -(1 / 2 : ℝ) < -p.val.2 ∧ -p.val.2 < 1 / 2
    constructor <;> linarith [p.property.2.1, p.property.2.2]
  have hloc : IsLocalDiffeomorph IC IC ∞
      (fun p : DoubleCylinder.seamDomain => (⟨F p.val, hmem p⟩ : collarProductOpen)) := by
    intro p
    exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict hmem (hres p)
  exact DifferentialGeometry.isLocalDiffeomorph_comp collarProductDiffeomorph.isLocalDiffeomorph hloc

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.reverseParameter_isLocalDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.reverseParameter_isLocalDiffeomorph target :: scope.openDecls } }

theorem sphereSelfAttachmentStandard_lower_localDiffeomorph
    (hlow : (D : ℝ → ℝ) =ᶠ[𝓝 0] (fun t => t / 15)) (z : S2) :
    let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorphAt IC (𝓡 3) ∞
      (SelfAttachment.lowerCollar (stereographicSmallBallChart P)
        (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P) a.toHomeomorph)
      (SelfAttachment.collarZero z) := by
  let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
  let p : DoubleCylinder.seamDomain := ⟨(z, 0), _root_.Set.mem_univ _, by norm_num⟩
  have hparam := reverseParameter_isLocalDiffeomorph (Diffeomorph.refl (𝓡 2) S2 ∞) p
  have hraw := sphereSelfAttachmentStandard_lowerCollar_isLocalDiffeomorphAt
    P a D hI h0 h1 J hJtarget hlow z
  have h := DifferentialGeometry.isLocalDiffeomorphAt_of_comp
    (f := reverseParameter (Diffeomorph.refl (𝓡 2) S2 ∞))
    (g := SelfAttachment.lowerCollar (stereographicSmallBallChart P)
      (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P) a.toHomeomorph)
    hraw hparam
  have heq : reverseParameter (Diffeomorph.refl (𝓡 2) S2 ∞) p = SelfAttachment.collarZero z := by
    refine Prod.ext ?_ ?_
    · rfl
    · exact Subtype.ext (neg_zero)
  rwa [heq] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_lower_localDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_lower_localDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_lower_localDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_lower_localDiffeomorph

include hJ hJi in
theorem sphereSelfAttachmentStandard_upper_localDiffeomorph
    (hupp : (D : ℝ → ℝ) =ᶠ[𝓝 1] (fun t => (16 / (2 - t) - 1) / 15)) (z : S2) :
    let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorphAt IC (𝓡 3) ∞
      (SelfAttachment.upperCollar (stereographicSmallBallChart P)
        (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P) a.toHomeomorph)
      (SelfAttachment.collarZero z) := by
  let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
  let b := sphereSelfAttachmentMonodromy a
  let p : DoubleCylinder.seamDomain := ⟨(b.symm z, 0), _root_.Set.mem_univ _, by norm_num⟩
  have hparam := reverseParameter_isLocalDiffeomorph b p
  have hraw := sphereSelfAttachmentStandard_upperCollar_isLocalDiffeomorphAt
    P a D hI h0 h1 J hJtarget hJ hJi hupp (b.symm z)
  have h := DifferentialGeometry.isLocalDiffeomorphAt_of_comp
    (f := reverseParameter b)
    (g := SelfAttachment.upperCollar (stereographicSmallBallChart P)
      (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P) a.toHomeomorph)
    hraw hparam
  have heq : reverseParameter b p = SelfAttachment.collarZero z := by
    refine Prod.ext ?_ ?_
    · exact b.apply_symm_apply z
    · exact Subtype.ext (neg_zero)
  rwa [heq] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_upper_localDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_upper_localDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_upper_localDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_upper_localDiffeomorph

end DifferentialGeometry.Topology.Manifold
