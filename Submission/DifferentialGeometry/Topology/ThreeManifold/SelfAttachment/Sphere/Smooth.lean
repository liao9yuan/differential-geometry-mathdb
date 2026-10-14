import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.Collar

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

@[instance_reducible]
def sphereSelfAttachmentChartedSpace :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (SphereSelfAttachment P a) := by
  let J' := monodromyIsotopy a J hJtarget
  let _ := sphereMappingTorusChartedSpace J'.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ)
    (DoubleCylinder.mappingTorusHomeomorph (sphereSelfAttachmentMonodromy a))
  exact DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ)
    (sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentChartedSpace ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentChartedSpace

theorem sphereSelfAttachmentLowerCollar_isLocalDiffeomorphAt
    (hlow : (D : ℝ → ℝ) =ᶠ[𝓝 0] (fun t => t / 15)) (z : S2) :
    let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorphAt IC IC ∞ (sphereSelfAttachmentLowerCollar P a)
      (⟨(z, 0), _root_.Set.mem_univ _, by norm_num⟩ : DoubleCylinder.seamDomain) := by
  let J' := monodromyIsotopy a J hJtarget
  let _ := sphereMappingTorusChartedSpace J'.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (DoubleCylinder.mappingTorusHomeomorph J'.target)
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  have hbase := DoubleCylinder.lowerSeam_isLocalDiffeomorph J'
  have hH := (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := IC) (n := ∞) (sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1).symm).symm.isLocalDiffeomorph
  have hcomp := DifferentialGeometry.isLocalDiffeomorph_comp hH hbase
  have heq := sphereSelfAttachmentReparametrizedHomeomorph_lowerSeam_eventually P a D hI h0 h1 hlow z
  exact IsLocalDiffeomorphAt.of_eventuallyEq heq.symm
    (hcomp (⟨(z, 0), _root_.Set.mem_univ _, by norm_num⟩ : DoubleCylinder.seamDomain))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentLowerCollar_isLocalDiffeomorphAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentLowerCollar_isLocalDiffeomorphAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentLowerCollar_isLocalDiffeomorphAt ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentLowerCollar_isLocalDiffeomorphAt

theorem sphereSelfAttachmentUpperCollar_isLocalDiffeomorphAt
    (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
    (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1))
    (hupp : (D : ℝ → ℝ) =ᶠ[𝓝 1] (fun t => (16 / (2 - t) - 1) / 15)) (z : S2) :
    let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorphAt IC IC ∞ (sphereSelfAttachmentUpperCollar P a)
      (⟨(z, 0), _root_.Set.mem_univ _, by norm_num⟩ : DoubleCylinder.seamDomain) := by
  let J' := monodromyIsotopy a J hJtarget
  let _ := sphereMappingTorusChartedSpace J'.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (DoubleCylinder.mappingTorusHomeomorph J'.target)
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  have hbase := DoubleCylinder.upperSeam_isLocalDiffeomorph J' hJ hJi
  have hH := (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := IC) (n := ∞) (sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1).symm).symm.isLocalDiffeomorph
  have hcomp := DifferentialGeometry.isLocalDiffeomorph_comp hH hbase
  have heq := sphereSelfAttachmentReparametrizedHomeomorph_upperSeam_eventually P a D hI h0 h1 hupp z
  exact IsLocalDiffeomorphAt.of_eventuallyEq heq.symm
    (hcomp (⟨(z, 0), _root_.Set.mem_univ _, by norm_num⟩ : DoubleCylinder.seamDomain))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentUpperCollar_isLocalDiffeomorphAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentUpperCollar_isLocalDiffeomorphAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentUpperCollar_isLocalDiffeomorphAt ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentUpperCollar_isLocalDiffeomorphAt


theorem sphereSelfAttachment_isManifold :
    let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
    IsManifold IC ∞ (SphereSelfAttachment P a) := by
  let J' := monodromyIsotopy a J hJtarget
  let _ := sphereMappingTorusChartedSpace J'.flatten
  let _ : IsManifold IC ∞ (SphereMappingTorus J'.target) :=
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
      (I := IC) (n := ∞) (sphereMappingTorusHomeomorph J'.flatten)
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (DoubleCylinder.mappingTorusHomeomorph J'.target)
  let _ : IsManifold IC ∞ (DoubleCylinder.Space J'.target) :=
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
      (I := IC) (n := ∞) (DoubleCylinder.mappingTorusHomeomorph J'.target)
  exact DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
    (I := IC) (n := ∞) (sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachment_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachment_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachment_isManifold ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachment_isManifold

def SphereSelfAttachmentDiffeomorph : Type :=
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  Diffeomorph IC ((𝓡 2).prod (𝓡 1)) (SphereSelfAttachment P a) SphereTwoTimesCircle ∞

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.SphereSelfAttachmentDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.SphereSelfAttachmentDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.SphereSelfAttachmentDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.SphereSelfAttachmentDiffeomorph

def sphereSelfAttachmentDiffeomorphSphereTwoTimesCircle :
    SphereSelfAttachmentDiffeomorph P a D hI h0 h1 J hJtarget := by
  let J' := monodromyIsotopy a J hJtarget
  let _ := sphereMappingTorusChartedSpace J'.flatten
  let _ : IsManifold IC ∞ (SphereMappingTorus J'.target) :=
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
      (I := IC) (n := ∞) (sphereMappingTorusHomeomorph J'.flatten)
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (DoubleCylinder.mappingTorusHomeomorph J'.target)
  let _ : IsManifold IC ∞ (DoubleCylinder.Space J'.target) :=
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
      (I := IC) (n := ∞) (DoubleCylinder.mappingTorusHomeomorph J'.target)
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  let F := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := IC) (n := ∞) (sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1).symm
  let G := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := IC) (n := ∞) (DoubleCylinder.mappingTorusHomeomorph J'.target)
  exact (F.trans G).trans (sphereMappingTorusDiffeomorphSphereTwoTimesCircle J'.flatten)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentDiffeomorphSphereTwoTimesCircle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentDiffeomorphSphereTwoTimesCircle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentDiffeomorphSphereTwoTimesCircle ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentDiffeomorphSphereTwoTimesCircle

end DifferentialGeometry.Topology.Manifold
