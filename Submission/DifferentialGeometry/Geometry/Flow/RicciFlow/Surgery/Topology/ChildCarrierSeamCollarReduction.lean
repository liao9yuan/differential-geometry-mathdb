import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCarrierCoreCapCoverFrontier
import Submission.DifferentialGeometry.Topology.Manifold.SmoothBicollar
import Submission.DifferentialGeometry.Topology.VanKampen.SmoothTwoSidedCollarBridge
import Submission.DifferentialGeometry.Topology.Embedding.Sphere
import Submission.DifferentialGeometry.Topology.Embedding.Factor
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Topology _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

noncomputable def childSeamSphere (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    C(Sphere 2, E.ChildCarrier c) :=
  (E.childCoreInclusion c).comp (E.childCapSeam c b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSeamSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSeamSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSeamSphere ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSeamSphere

def seamSphereSmoothlyEmbedded (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    Prop :=
  letI : ChartedSpace ThreeSpace (E.ChildCarrier c) := (Q.component c).charts
  letI : IsManifold ThreeModel ∞ (E.ChildCarrier c) := (Q.component c).smooth
  _root_.Manifold.IsSmoothEmbedding (𝓡 2) ThreeModel ∞ fun y : Sphere 2 => E.childSeamSphere c b y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.seamSphereSmoothlyEmbedded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.seamSphereSmoothlyEmbedded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.seamSphereSmoothlyEmbedded ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.seamSphereSmoothlyEmbedded

private theorem contMDiff_sphereToThreeBall :
    letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
    letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := E.ballSmooth
    ContMDiff (𝓡 2) (𝓡∂ 3) ∞ sphereToThreeBall := by
  let thisBall : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
  let thisSmooth : IsManifold (𝓡∂ 3) ∞ ThreeBall := E.ballSmooth
  refine (ContMDiff.iff_comp_isImmersion E.ball_induced.isImmersion).mpr ?_
  exact ⟨sphereToThreeBall.continuous,
    (isSmoothEmbedding_coe_sphere (E := ThreeSpace) (n := 2)).contMDiff⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.contMDiff_sphereToThreeBall
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.contMDiff_sphereToThreeBall target :: scope.openDecls } }

private theorem injective_mfderiv_sphereToThreeBall (x : Sphere 2) :
    letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
    letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := E.ballSmooth
    Function.Injective (mfderiv (𝓡 2) (𝓡∂ 3) sphereToThreeBall x) := by
  let thisBall : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
  let thisSmooth : IsManifold (𝓡∂ 3) ∞ ThreeBall := E.ballSmooth
  have hinj := ((isSmoothEmbedding_coe_sphere (E := ThreeSpace) (n := 2)).isImmersion.isImmersionAt
    x).injective_mfderiv (by simp)
  have heq : (Subtype.val : Sphere 2 → ThreeSpace) =
      (Subtype.val : ThreeBall → ThreeSpace) ∘ sphereToThreeBall := rfl
  rw [heq, mfderiv_comp x (E.ball_induced.contMDiff.mdifferentiableAt (by simp))
    (E.contMDiff_sphereToThreeBall.mdifferentiableAt (by simp))] at hinj
  exact Function.Injective.of_comp hinj

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.injective_mfderiv_sphereToThreeBall
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.injective_mfderiv_sphereToThreeBall target :: scope.openDecls } }

private theorem capBoundary_isSmoothEmbedding (b : E.trace.tubes.Boundary) :
    IsSmoothEmbedding (𝓡 2) ThreeModel ∞ (E.trace.capping.cap b ∘ sphereToThreeBall) := by
  let thisBall : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
  let thisSmooth : IsManifold (𝓡∂ 3) ∞ ThreeBall := E.ballSmooth
  have hsm : ContMDiff (𝓡 2) ThreeModel ∞ (E.trace.capping.cap b ∘ sphereToThreeBall) :=
    (E.cap_smooth b).contMDiff.comp E.contMDiff_sphereToThreeBall
  refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv
    (by simp) hsm ?_, ?_⟩
  · intro x
    rw [mfderiv_comp x ((E.cap_smooth b).contMDiff.mdifferentiableAt (by simp))
      (E.contMDiff_sphereToThreeBall.mdifferentiableAt (by simp))]
    exact ((E.cap_smooth b).isImmersion.isImmersionAt _).injective_mfderiv (by simp) |>.comp
      (E.injective_mfderiv_sphereToThreeBall x)
  · apply (E.cap_smooth b).isEmbedding.comp
    apply _root_.Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
    exact _root_.Topology.IsEmbedding.subtypeVal

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capBoundary_isSmoothEmbedding
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capBoundary_isSmoothEmbedding target :: scope.openDecls } }

theorem childSeamSphere_isSmoothEmbedding (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) : E.seamSphereSmoothlyEmbedded c b := by
  let thisChart : ChartedSpace ThreeSpace (E.ChildCarrier c) := (Q.component c).charts
  let thisSmooth : IsManifold ThreeModel ∞ (E.ChildCarrier c) := (Q.component c).smooth
  let inclusion : E.ChildCarrier c → Q.Carrier ⊕ D.Carrier := fun q => Sum.inl q.1
  have heq : inclusion ∘ E.childSeamSphere c b =
      E.presentation ∘ (E.trace.capping.cap b.1 ∘ sphereToThreeBall) := by
    funext y
    change Sum.inl (E.childSeamSphere c b y).1 =
      E.presentation (E.trace.capping.cap b.1 (sphereToThreeBall y))
    rw [E.presentation_eq]
    exact (congrArg (fun q : E.ChildCarrier c => (Sum.inl q.1 : Q.Carrier ⊕ D.Carrier))
      (E.childCap_boundary_eq c b y).symm).trans (E.childCapFun_eq c b _).symm
  have hcomp : _root_.Manifold.IsSmoothEmbedding (𝓡 2) ThreeModel ∞
      (inclusion ∘ E.childSeamSphere c b) := by
    rw [heq]
    exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp
      (𝓡 2) ThreeModel _ (E.capBoundary_isSmoothEmbedding b.1) E.presentation
  have hsm : ContMDiff (𝓡 2) ThreeModel ∞ (E.childSeamSphere c b) := by
    apply (ContMDiff.subtypeVal_comp_iff (Q.componentOpen c) _).mp
    exact contMDiff_of_contMDiff_inl hcomp.contMDiff
  have hi : ContMDiff ThreeModel ThreeModel ∞ inclusion :=
    ContMDiff.inl.comp (contMDiff_subtype_val (U := Q.componentOpen c))
  exact hcomp.of_comp (by simp) hsm hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSeamSphere_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSeamSphere_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSeamSphere_isSmoothEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSeamSphere_isSmoothEmbedding

theorem nonempty_smoothTwoSidedCollar_of_seamSphereSmoothlyEmbedded
    (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c)
    (h : E.seamSphereSmoothlyEmbedded c b) :
    letI : ChartedSpace ThreeSpace (E.ChildCarrier c) := (Q.component c).charts
    letI : IsManifold ThreeModel ∞ (E.ChildCarrier c) := (Q.component c).smooth
    Nonempty (DifferentialGeometry.Topology.SmoothTwoSidedCollar
      (𝓡 2) ThreeModel fun y : Sphere 2 => E.childSeamSphere c b y) := by
  let thisChart : ChartedSpace ThreeSpace (E.ChildCarrier c) := (Q.component c).charts
  let thisSmooth : IsManifold ThreeModel ∞ (E.ChildCarrier c) := (Q.component c).smooth
  exact DifferentialGeometry.Topology.exists_smoothTwoSidedCollar_of_smoothSphereEmbedding
    (fun y : Sphere 2 => E.childSeamSphere c b y) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_smoothTwoSidedCollar_of_seamSphereSmoothlyEmbedded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_smoothTwoSidedCollar_of_seamSphereSmoothlyEmbedded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_smoothTwoSidedCollar_of_seamSphereSmoothlyEmbedded ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_smoothTwoSidedCollar_of_seamSphereSmoothlyEmbedded

theorem nonempty_twoSidedCollar_of_seamSphereSmoothlyEmbedded
    (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c)
    (h : E.seamSphereSmoothlyEmbedded c b) :
    letI : ChartedSpace ThreeSpace (E.ChildCarrier c) := (Q.component c).charts
    letI : IsManifold ThreeModel ∞ (E.ChildCarrier c) := (Q.component c).smooth
    Nonempty (DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
      fun y : Sphere 2 => E.childSeamSphere c b y) := by
  let thisChart : ChartedSpace ThreeSpace (E.ChildCarrier c) := (Q.component c).charts
  let thisSmooth : IsManifold ThreeModel ∞ (E.ChildCarrier c) := (Q.component c).smooth
  obtain ⟨h⟩ := E.nonempty_smoothTwoSidedCollar_of_seamSphereSmoothlyEmbedded c b h
  exact ⟨DifferentialGeometry.Topology.SmoothTwoSidedCollar.toTwoSidedCollar h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_twoSidedCollar_of_seamSphereSmoothlyEmbedded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_twoSidedCollar_of_seamSphereSmoothlyEmbedded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_twoSidedCollar_of_seamSphereSmoothlyEmbedded ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_twoSidedCollar_of_seamSphereSmoothlyEmbedded

theorem nonempty_smoothTwoSidedCollar_childSeamSphere
    (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    letI : ChartedSpace ThreeSpace (E.ChildCarrier c) := (Q.component c).charts
    letI : IsManifold ThreeModel ∞ (E.ChildCarrier c) := (Q.component c).smooth
    Nonempty (DifferentialGeometry.Topology.SmoothTwoSidedCollar
      (𝓡 2) ThreeModel fun y : Sphere 2 => E.childSeamSphere c b y) :=
  E.nonempty_smoothTwoSidedCollar_of_seamSphereSmoothlyEmbedded c b
    (E.childSeamSphere_isSmoothEmbedding c b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_smoothTwoSidedCollar_childSeamSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_smoothTwoSidedCollar_childSeamSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_smoothTwoSidedCollar_childSeamSphere ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_smoothTwoSidedCollar_childSeamSphere

theorem nonempty_twoSidedCollar_childSeamSphere
    (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    Nonempty (DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
      fun y : Sphere 2 => E.childSeamSphere c b y) :=
  E.nonempty_twoSidedCollar_of_seamSphereSmoothlyEmbedded c b
    (E.childSeamSphere_isSmoothEmbedding c b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_twoSidedCollar_childSeamSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_twoSidedCollar_childSeamSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_twoSidedCollar_childSeamSphere ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_twoSidedCollar_childSeamSphere

theorem seamSphereSmoothlyEmbedded_of_isEmpty_childCapBoundary
    (c : ConnectedComponents Q.Carrier) [IsEmpty (E.ChildCapBoundary c)] :
    ∀ b : E.ChildCapBoundary c, E.seamSphereSmoothlyEmbedded c b :=
  fun b => (IsEmpty.false b).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.seamSphereSmoothlyEmbedded_of_isEmpty_childCapBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.seamSphereSmoothlyEmbedded_of_isEmpty_childCapBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.seamSphereSmoothlyEmbedded_of_isEmpty_childCapBoundary ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.seamSphereSmoothlyEmbedded_of_isEmpty_childCapBoundary

theorem simplyConnectedSpace_childCarrier_of_univ_V_producer
    (h : ∀ c : ConnectedComponents Q.Carrier,
      SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
        ∃ d : E.ChildCarrierCoreCapCover c, d.V = _root_.Set.univ)
    (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).Carrier] :
    SimplyConnectedSpace (E.ChildCarrier c) := by
  obtain ⟨d, hd⟩ := h c inferInstance
  exact E.simplyConnectedSpace_childCarrier_of_cover_univ_V c d hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.simplyConnectedSpace_childCarrier_of_univ_V_producer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.simplyConnectedSpace_childCarrier_of_univ_V_producer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.simplyConnectedSpace_childCarrier_of_univ_V_producer ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.simplyConnectedSpace_childCarrier_of_univ_V_producer

def childCoreCapCoverAssembly : Prop :=
  ∀ c : ConnectedComponents Q.Carrier,
    SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
      (∀ b : E.ChildCapBoundary c,
        Nonempty (DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
          fun y : Sphere 2 => E.childSeamSphere c b y)) →
        Nonempty (E.ChildCarrierCoreCapCover c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreCapCoverAssembly then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreCapCoverAssembly"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreCapCoverAssembly ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreCapCoverAssembly

theorem childCoreCapCoverProducer_of_seamCollarFrontier
    (hfrontier : ∀ (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c),
      E.seamSphereSmoothlyEmbedded c b)
    (hassembly : E.childCoreCapCoverAssembly) :
    E.childCoreCapCoverProducer := by
  intro c hpar
  exact hassembly c hpar fun b =>
    E.nonempty_twoSidedCollar_of_seamSphereSmoothlyEmbedded c b (hfrontier c b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreCapCoverProducer_of_seamCollarFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreCapCoverProducer_of_seamCollarFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreCapCoverProducer_of_seamCollarFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreCapCoverProducer_of_seamCollarFrontier


theorem childCoreCapCoverProducer_of_childCoreCapCoverAssembly
    (hassembly : E.childCoreCapCoverAssembly) : E.childCoreCapCoverProducer := by
  intro c hpar
  exact hassembly c hpar (E.nonempty_twoSidedCollar_childSeamSphere c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreCapCoverProducer_of_childCoreCapCoverAssembly then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreCapCoverProducer_of_childCoreCapCoverAssembly"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreCapCoverProducer_of_childCoreCapCoverAssembly ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreCapCoverProducer_of_childCoreCapCoverAssembly

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.Topology

theorem nonempty_smoothTwoSidedCollar_roundSphere :
    Nonempty (SmoothTwoSidedCollar (𝓡 2) (𝓡 3)
      (Subtype.val : SphereTwo → EuclideanSpace ℝ (Fin 3))) :=
  exists_smoothTwoSidedCollar_of_smoothSphereEmbedding
    (Subtype.val : SphereTwo → EuclideanSpace ℝ (Fin 3))
    (isSmoothEmbedding_coe_sphere (E := EuclideanSpace ℝ (Fin 3)) (n := 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_smoothTwoSidedCollar_roundSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_smoothTwoSidedCollar_roundSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_smoothTwoSidedCollar_roundSphere ``Submission.DifferentialGeometry.Topology.nonempty_smoothTwoSidedCollar_roundSphere

end DifferentialGeometry.Topology
