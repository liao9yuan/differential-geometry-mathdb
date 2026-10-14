import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.Interior
import Submission.DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleLift
import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationComparison

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

theorem connectedSpace_sphereDoublePuncturedInteriorImage :
    ConnectedSpace (sphereDoublePuncturedInteriorImage P D hI) := by
  let _ : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) (0 : E3) (by norm_num))
  have hc : IsConnected (_root_.Set.univ ×ˢ _root_.Set.Ioo (0 : ℝ) 1 : Set (S2 × ℝ)) :=
    isConnected_univ.prod (isConnected_Ioo zero_lt_one)
  let _ : ConnectedSpace DoubleCylinder.Interior := isConnected_iff_connectedSpace.mp hc
  exact (sphereDoublePuncturedInteriorDiffeomorph P D hI).toHomeomorph.connectedSpace_iff.mp inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.connectedSpace_sphereDoublePuncturedInteriorImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.connectedSpace_sphereDoublePuncturedInteriorImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.connectedSpace_sphereDoublePuncturedInteriorImage ``Submission.DifferentialGeometry.Topology.Manifold.connectedSpace_sphereDoublePuncturedInteriorImage

theorem exists_sphereSelfAttachment_orientation_extending_core
    (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
    (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1))
    (o : SmoothOrientation (𝓡 3) S3) :
    let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
    let _ := sphereSelfAttachment_isManifold P a D hI h0 h1 J hJtarget
    let hc : IsLocalDiffeomorph (𝓡 3) IC ∞ (sphereSelfAttachmentCoreMap P a D hI) :=
      sphereSelfAttachmentCoreMap_isLocalDiffeomorph P a D hI h0 h1 J hJtarget hJ hJi
    ∃ O : SmoothOrientation IC (SphereSelfAttachment P a),
      ∀ x : sphereDoublePuncturedInteriorImage P D hI,
        tangentOrientationEquiv
          (hc.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv (o.val x.val) =
          O.val (sphereSelfAttachmentCoreMap P a D hI x) := by
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  let _ := sphereSelfAttachment_isManifold P a D hI h0 h1 J hJtarget
  let _ := connectedSpace_sphereDoublePuncturedInteriorImage P D hI
  let F : Diffeomorph IC ((𝓡 2).prod (𝓡 1)) (SphereSelfAttachment P a) SphereTwoTimesCircle ∞ :=
    sphereSelfAttachmentDiffeomorphSphereTwoTimesCircle P a D hI h0 h1 J hJtarget
  let OF := pullbackSmoothOrientation IC ((𝓡 2).prod (𝓡 1)) F F.contMDiff
    (fun x => (F.mfderivToContinuousLinearEquiv (by simp) x).bijective) sphereTwoTimesCircleSmoothOrientation
  let hc : IsLocalDiffeomorph (𝓡 3) IC ∞ (sphereSelfAttachmentCoreMap P a D hI) :=
    sphereSelfAttachmentCoreMap_isLocalDiffeomorph P a D hI h0 h1 J hJtarget hJ hJi
  let hbij : ∀ x, _root_.Function.Bijective (mfderiv (𝓡 3) IC (sphereSelfAttachmentCoreMap P a D hI) x) := by
    intro x
    exact (hc.mfderivToContinuousLinearEquiv (by simp) x).bijective
  let Oc := pullbackSmoothOrientation (𝓡 3) IC (sphereSelfAttachmentCoreMap P a D hI)
    hc.contMDiff hbij OF
  let oU := restrictSmoothOrientation (𝓡 3) (sphereDoublePuncturedInteriorImage P D hI) o
  have heq (x : sphereDoublePuncturedInteriorImage P D hI) :
      (differentialEquivOfBijective (𝓡 3) IC (sphereSelfAttachmentCoreMap P a D hI) hbij x).toLinearEquiv =
        (hc.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change differentialEquivOfBijective (𝓡 3) IC (sphereSelfAttachmentCoreMap P a D hI) hbij x v =
      (hc.mfderivToContinuousLinearEquiv (by simp) x) v
    exact (differentialEquivOfBijective_apply (𝓡 3) IC
      (sphereSelfAttachmentCoreMap P a D hI) hbij x v).trans rfl
  obtain ⟨x₀⟩ : Nonempty (sphereDoublePuncturedInteriorImage P D hI) := inferInstance
  rcases smoothOrientation_eq_or_eq_neg (𝓡 3) Oc oU x₀ with hpos | hneg
  · refine ⟨OF, ?_⟩
    intro x
    have h := pullbackSmoothOrientation_eq_iff (𝓡 3) IC
      (sphereSelfAttachmentCoreMap P a D hI) hc.contMDiff hbij OF oU x |>.mp (hpos x)
    rw [heq] at h
    exact h
  · refine ⟨negSmoothOrientation IC OF, ?_⟩
    intro x
    have h := pullbackSmoothOrientation_pushforward (𝓡 3) IC
      (sphereSelfAttachmentCoreMap P a D hI) hc.contMDiff hbij OF x
    change tangentOrientationEquiv
      (differentialEquivOfBijective (𝓡 3) IC (sphereSelfAttachmentCoreMap P a D hI) hbij x).toLinearEquiv
      (Oc.val x) = OF.val (sphereSelfAttachmentCoreMap P a D hI x) at h
    rw [heq, hneg x] at h
    have he := tangentOrientationEquiv_neg
      (hc.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv (oU.val x)
    have h' := he.symm.trans h
    have hn := congrArg Neg.neg h'
    have hn' := (neg_neg _).symm.trans hn
    exact hn'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_sphereSelfAttachment_orientation_extending_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_sphereSelfAttachment_orientation_extending_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_sphereSelfAttachment_orientation_extending_core ``Submission.DifferentialGeometry.Topology.Manifold.exists_sphereSelfAttachment_orientation_extending_core

end DifferentialGeometry.Topology.Manifold
