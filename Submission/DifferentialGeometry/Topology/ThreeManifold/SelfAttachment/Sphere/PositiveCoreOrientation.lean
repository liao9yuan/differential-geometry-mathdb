import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.PositiveLocalMaps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology

open _root_.Submission.DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.E4 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.S3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.instFactEqNatFinrankRealE4HAddOfNat : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.instFactEqNatFinrankRealE4HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.instFactEqNatFinrankRealE4HAddOfNat target :: scope.openDecls } }

variable (P : S3)
  (c d : OrientedBallChart standardThreeSphere.toClosedOrientedManifold)
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (B : E3 ≃ₗᵢ[ℝ] E3)
  (hc : ∀ x, c.chart x = (stereographicSmallBallChart P).chart (B x))
  (hd : ∀ x, d.chart x = (oppositeStereographicSmallBallChart P).chart (B x))
  (D : ℝ ≃ₘ[ℝ] ℝ) (hI : D '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1)
  (h0 : D 0 = 0) (h1 : D 1 = 1)

private def positiveCoreToImage
    (x : SelfAttachment.coreInterior c.toBallChart d.toBallChart) :
    sphereDoublePuncturedInteriorImage P D hI :=
  ⟨x.val, by
    change x.val ∈ (sphereDoublePuncturedInteriorImage P D hI : Set S3)
    rw [sphereDoublePuncturedInteriorImage_eq P D hI h0 h1]
    exact (positiveSphereAttachmentCoreToRaw P c d B hc hd x).property⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.positiveCoreToImage
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.positiveCoreToImage target :: scope.openDecls } }

private theorem positiveCoreToImage_isLocalDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (positiveCoreToImage P c d B hc hd D hI h0 h1) := by
  let U : TopologicalSpace.Opens S3 := SelfAttachment.coreInterior c.toBallChart d.toBallChart
  have hmem (x : U) : x.val ∈ sphereDoublePuncturedInteriorImage P D hI :=
    (positiveCoreToImage P c d B hc hd D hI h0 h1 x).property
  intro x
  exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict hmem
    (DifferentialGeometry.isLocalDiffeomorph_subtype_val U x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.positiveCoreToImage_isLocalDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.positiveCoreToImage_isLocalDiffeomorph target :: scope.openDecls } }

private theorem positiveCoreToImage_mfderiv
    (x : SelfAttachment.coreInterior c.toBallChart d.toBallChart) :
    mfderiv (𝓡 3) (𝓡 3) (positiveCoreToImage P c d B hc hd D hI h0 h1) x =
      ContinuousLinearMap.id ℝ E3 := by
  rw [← DifferentialGeometry.mfderiv_subtypeVal_comp]
  exact DifferentialGeometry.mfderiv_subtype_val _ x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.positiveCoreToImage_mfderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.positiveCoreToImage_mfderiv target :: scope.openDecls } }

theorem positiveSphereAttachment_core_preserves_orientation
    (O :
      let _ := sphereSelfAttachmentStandardCharts P antipodalAttachment D hI h0 h1
        sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target
      ManifoldOrientation (𝓡 3) (SphereSelfAttachment P antipodalAttachment) 3)
    (hor :
      let _ := sphereSelfAttachmentStandardCharts P antipodalAttachment D hI h0 h1
        sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target
      let hraw := sphereSelfAttachmentStandard_core_isLocalDiffeomorph P antipodalAttachment D hI h0 h1
        sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target contMDiff_fst contMDiff_fst
      ∀ x, Orientation.map (Fin 3) (hraw.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
        (standardThreeSphere.orientation.orientation x.val) =
        O.orientation (sphereSelfAttachmentCoreMap P antipodalAttachment D hI x)) :
    let _ := sphereSelfAttachmentStandardCharts P antipodalAttachment D hI h0 h1
      sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target
    let Q := sphereSelfAttachmentManifold P antipodalAttachment D hI h0 h1 sphereMappingTorusIsotopyRefl
      sphereMappingTorusIsotopyRefl_target O
    let H := positiveSphereAttachmentHomeomorph P c d hcd B hc hd
    let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd
        antipodalAttachment.toHomeomorph) := (Q.pullback H).charts
    let hpos := positiveSphereAttachment_core_localDiffeomorph P c d hcd B hc hd D hI h0 h1
    ∀ x, Orientation.map (Fin 3) (hpos.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (standardThreeSphere.orientation.orientation x.val) =
      (Q.pullback H).orientation.orientation
        (SelfAttachment.coreInteriorInclusion c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph x) := by
  let _ := sphereSelfAttachmentStandardCharts P antipodalAttachment D hI h0 h1
    sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target
  let Q := sphereSelfAttachmentManifold P antipodalAttachment D hI h0 h1 sphereMappingTorusIsotopyRefl
    sphereMappingTorusIsotopyRefl_target O
  let H := positiveSphereAttachmentHomeomorph P c d hcd B hc hd
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd
        antipodalAttachment.toHomeomorph) := (Q.pullback H).charts
  let G : Diffeomorph (𝓡 3) (𝓡 3)
      (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph)
      (SphereSelfAttachment P antipodalAttachment) ∞ := (Q.pullbackOrientedDiffeomorph H).val
  have hGO := (Q.pullbackOrientedDiffeomorph H).property
  let hpos := positiveSphereAttachment_core_localDiffeomorph P c d hcd B hc hd D hI h0 h1
  let hraw := sphereSelfAttachmentStandard_core_isLocalDiffeomorph P antipodalAttachment D hI h0 h1
    sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target contMDiff_fst contMDiff_fst
  let f : SelfAttachment.coreInterior c.toBallChart d.toBallChart →
      SelfAttachment.Quotient c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph :=
    SelfAttachment.coreInteriorInclusion c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph
  let r := sphereSelfAttachmentCoreMap P antipodalAttachment D hI
  let φ := positiveCoreToImage P c d B hc hd D hI h0 h1
  have hφ := positiveCoreToImage_isLocalDiffeomorph P c d B hc hd D hI h0 h1
  have heq : G ∘ f = r ∘ φ := by
    funext x
    exact positiveSphereAttachmentHomeomorph_coreImage P c d hcd B hc hd D hI x (φ x).property
  change ∀ x, Orientation.map (Fin 3) (hpos.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
    (standardThreeSphere.orientation.orientation x.val) = (Q.pullback H).orientation.orientation (f x)
  intro x
  let L := (G.mfderivToContinuousLinearEquiv (by simp) (f x)).toLinearEquiv
  apply (Orientation.map (Fin 3) L).injective
  have hG : Orientation.map (Fin 3) L ((Q.pullback H).orientation.orientation (f x)) =
      O.orientation (G (f x)) := hGO (f x)
  rw [hG]
  have hder : (hpos.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.trans L =
      (hraw.mfderivToContinuousLinearEquiv (by simp) (φ x)).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change mfderiv (𝓡 3) (𝓡 3) G (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) =
      mfderiv (𝓡 3) (𝓡 3) r (φ x) v
    rw [← mfderiv_comp_apply x (G.mdifferentiable (by simp) _) (hpos.mdifferentiable (by simp) _) v,
      heq, mfderiv_comp_apply x (hraw.mdifferentiable (by simp) _) (hφ.mdifferentiable (by simp) _) v]
    rw [positiveCoreToImage_mfderiv]
    rfl
  erw [DifferentialGeometry.VectorBundle.map_orientation_trans_between, hder]
  have h := hor (φ x)
  rw [show G (f x) = r (φ x) from congrFun heq x]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.positiveSphereAttachment_core_preserves_orientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.positiveSphereAttachment_core_preserves_orientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.positiveSphereAttachment_core_preserves_orientation ``Submission.DifferentialGeometry.Topology.positiveSphereAttachment_core_preserves_orientation

end DifferentialGeometry.Topology
