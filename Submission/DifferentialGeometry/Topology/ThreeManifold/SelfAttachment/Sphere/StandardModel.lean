import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.OrientedRetainedChart

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

def sphereSelfAttachmentStandardHomeomorph :
    SphereSelfAttachment P a ≃ₜ sphereTwoTimesCircleLift.Carrier := by
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  let F : Diffeomorph IC ((𝓡 2).prod (𝓡 1)) (SphereSelfAttachment P a) SphereTwoTimesCircle ∞ :=
    sphereSelfAttachmentDiffeomorphSphereTwoTimesCircle P a D hI h0 h1 J hJtarget
  exact F.toHomeomorph.trans sphereTwoTimesCircleModelCopy.equiv.toHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandardHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandardHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandardHomeomorph ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandardHomeomorph

@[instance_reducible]
def sphereSelfAttachmentStandardCharts : ChartedSpace E3 (SphereSelfAttachment P a) :=
  DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (sphereSelfAttachmentStandardHomeomorph P a D hI h0 h1 J hJtarget)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandardCharts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandardCharts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandardCharts ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandardCharts

theorem sphereSelfAttachmentStandard_isManifold :
    let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
    IsManifold (𝓡 3) ∞ (SphereSelfAttachment P a) :=
  DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
    (I := 𝓡 3) (n := ∞) (sphereSelfAttachmentStandardHomeomorph P a D hI h0 h1 J hJtarget)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_isManifold ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_isManifold

def SphereSelfAttachmentStandardDiffeomorph : Type :=
  let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
  Diffeomorph (𝓡 3) (𝓡 3) (SphereSelfAttachment P a) sphereTwoTimesCircleLift.Carrier ∞

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.SphereSelfAttachmentStandardDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.SphereSelfAttachmentStandardDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.SphereSelfAttachmentStandardDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.SphereSelfAttachmentStandardDiffeomorph

def sphereSelfAttachmentStandardDiffeomorph :
    SphereSelfAttachmentStandardDiffeomorph P a D hI h0 h1 J hJtarget :=
  DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := 𝓡 3) (n := ∞) (sphereSelfAttachmentStandardHomeomorph P a D hI h0 h1 J hJtarget)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandardDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandardDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandardDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandardDiffeomorph

theorem sphereSelfAttachmentStandardHomeomorph_core
    (x : sphereDoublePuncturedInteriorImage P D hI) :
    sphereSelfAttachmentStandardHomeomorph P a D hI h0 h1 J hJtarget
      (sphereSelfAttachmentCoreMap P a D hI x) =
        sphereSelfAttachmentCoreToSphereProduct P a D hI h0 h1 J hJtarget x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandardHomeomorph_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandardHomeomorph_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandardHomeomorph_core ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandardHomeomorph_core

private theorem identity_change_model_isLocalDiffeomorph
    (f : DoubleCylinder.seamDomain → SphereSelfAttachment P a)
    (x : DoubleCylinder.seamDomain)
    (hf : let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
      IsLocalDiffeomorphAt IC IC ∞ f x) :
    let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorphAt IC (𝓡 3) ∞ f x := by
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  let F : Diffeomorph IC ((𝓡 2).prod (𝓡 1)) (SphereSelfAttachment P a) SphereTwoTimesCircle ∞ :=
    sphereSelfAttachmentDiffeomorphSphereTwoTimesCircle P a D hI h0 h1 J hJtarget
  have h1loc := hf.comp (K := (𝓡 2).prod (𝓡 1)) (P := SphereTwoTimesCircle) (F.isLocalDiffeomorph _)
  have h2loc := h1loc.comp (K := 𝓡 3) (P := sphereTwoTimesCircleLift.Carrier)
    (sphereTwoTimesCircleModelCopy.equiv.isLocalDiffeomorph _)
  let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
  let G : Diffeomorph (𝓡 3) (𝓡 3) (SphereSelfAttachment P a) sphereTwoTimesCircleLift.Carrier ∞ :=
    sphereSelfAttachmentStandardDiffeomorph P a D hI h0 h1 J hJtarget
  have h3 := h2loc.comp (K := 𝓡 3) (P := SphereSelfAttachment P a) (G.symm.isLocalDiffeomorph _)
  have heq : G.symm ∘ (sphereTwoTimesCircleModelCopy.equiv ∘ (F ∘ f)) = f := by
    funext y
    exact (sphereSelfAttachmentStandardHomeomorph P a D hI h0 h1 J hJtarget).symm_apply_apply (f y)
  rwa [heq] at h3

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.identity_change_model_isLocalDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.identity_change_model_isLocalDiffeomorph target :: scope.openDecls } }

theorem sphereSelfAttachmentStandard_lowerCollar_isLocalDiffeomorphAt
    (hlow : (D : ℝ → ℝ) =ᶠ[𝓝 0] (fun t => t / 15)) (z : S2) :
    let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorphAt IC (𝓡 3) ∞ (sphereSelfAttachmentLowerCollar P a)
      (⟨(z, 0), _root_.Set.mem_univ _, by norm_num⟩ : DoubleCylinder.seamDomain) :=
  identity_change_model_isLocalDiffeomorph P a D hI h0 h1 J hJtarget _ _
    (sphereSelfAttachmentLowerCollar_isLocalDiffeomorphAt P a D hI h0 h1 J hJtarget hlow z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_lowerCollar_isLocalDiffeomorphAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_lowerCollar_isLocalDiffeomorphAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_lowerCollar_isLocalDiffeomorphAt ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_lowerCollar_isLocalDiffeomorphAt

theorem sphereSelfAttachmentStandard_upperCollar_isLocalDiffeomorphAt
    (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
    (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1))
    (hupp : (D : ℝ → ℝ) =ᶠ[𝓝 1] (fun t => (16 / (2 - t) - 1) / 15)) (z : S2) :
    let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorphAt IC (𝓡 3) ∞ (sphereSelfAttachmentUpperCollar P a)
      (⟨(z, 0), _root_.Set.mem_univ _, by norm_num⟩ : DoubleCylinder.seamDomain) :=
  identity_change_model_isLocalDiffeomorph P a D hI h0 h1 J hJtarget _ _
    (sphereSelfAttachmentUpperCollar_isLocalDiffeomorphAt P a D hI h0 h1 J hJtarget hJ hJi hupp z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_upperCollar_isLocalDiffeomorphAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_upperCollar_isLocalDiffeomorphAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_upperCollar_isLocalDiffeomorphAt ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_upperCollar_isLocalDiffeomorphAt

theorem sphereSelfAttachmentStandard_core_isLocalDiffeomorph
    (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
    (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1)) :
    let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (sphereSelfAttachmentCoreMap P a D hI) := by
  let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
  let G : Diffeomorph (𝓡 3) (𝓡 3) (SphereSelfAttachment P a) sphereTwoTimesCircleLift.Carrier ∞ :=
    sphereSelfAttachmentStandardDiffeomorph P a D hI h0 h1 J hJtarget
  have h := DifferentialGeometry.isLocalDiffeomorph_comp G.symm.isLocalDiffeomorph
    (sphereSelfAttachmentCoreToSphereProduct_isLocalDiffeomorph P a D hI h0 h1 J hJtarget hJ hJi)
  have heq : G.symm ∘ sphereSelfAttachmentCoreToSphereProduct P a D hI h0 h1 J hJtarget =
      sphereSelfAttachmentCoreMap P a D hI := by
    funext x
    exact (sphereSelfAttachmentStandardHomeomorph P a D hI h0 h1 J hJtarget).symm_apply_apply _
  rwa [heq] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_core_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_core_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_core_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.sphereSelfAttachmentStandard_core_isLocalDiffeomorph

end DifferentialGeometry.Topology.Manifold
