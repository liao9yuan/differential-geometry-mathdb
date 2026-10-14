import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationLocal
import Submission.DifferentialGeometry.Topology.Manifold.OrientationTransportVariation
import Submission.DifferentialGeometry.Topology.Manifold.SmoothMapDifferentialCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Filter _root_.Manifold _root_.TopologicalSpace
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E H M F K N : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable [TopologicalSpace K] (J : ModelWithCorners ℝ F K)
variable [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

theorem coordinateDifferentialEquiv_orientation_pullback (f : M → N)
    (hbij : ∀ x : M, _root_.Function.Bijective (mfderiv I J f x)) (p : M)
    (x : ↥((chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source))
    (o : Orientation ℝ F (Fin (Module.finrank ℝ F))) :
    tangentOrientationEquiv (coordinateDifferentialEquiv I J f hbij p x).symm.toLinearEquiv
        (Orientation.map _ (preferredChartTangentEquiv J (f p) (f x.val) x.property.2).toLinearEquiv o) =
      Orientation.map _ (preferredChartTangentEquiv I p x.val x.property.1).toLinearEquiv
        (tangentOrientationEquiv (differentialEquivOfBijective I J f hbij x.val).symm.toLinearEquiv o) := by
  rw [← tangentOrientationEquiv_self]
  rw [← tangentOrientationEquiv_trans]
  have he : (preferredChartTangentEquiv J (f p) (f x.val) x.property.2).toLinearEquiv.trans
      (coordinateDifferentialEquiv I J f hbij p x).symm.toLinearEquiv =
      (differentialEquivOfBijective I J f hbij x.val).symm.toLinearEquiv.trans
        (preferredChartTangentEquiv I p x.val x.property.1).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change preferredChartTangentEquiv I p x.val x.property.1
      ((differentialEquivOfBijective I J f hbij x.val).symm
        ((preferredChartTangentEquiv J (f p) (f x.val) x.property.2).symm
          (preferredChartTangentEquiv J (f p) (f x.val) x.property.2 v))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
    rfl
  rw [he, tangentOrientationEquiv_trans, tangentOrientationEquiv_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.coordinateDifferentialEquiv_orientation_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.coordinateDifferentialEquiv_orientation_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.coordinateDifferentialEquiv_orientation_pullback ``Submission.DifferentialGeometry.Topology.Manifold.coordinateDifferentialEquiv_orientation_pullback

def pullbackTangentOrientation (f : M → N)
    (hbij : ∀ x : M, _root_.Function.Bijective (mfderiv I J f x))
    (o : N → Orientation ℝ F (Fin (Module.finrank ℝ F))) (x : M) :
    Orientation ℝ E (Fin (Module.finrank ℝ E)) :=
  tangentOrientationEquiv (differentialEquivOfBijective I J f hbij x).symm.toLinearEquiv (o (f x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.pullbackTangentOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.pullbackTangentOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.pullbackTangentOrientation ``Submission.DifferentialGeometry.Topology.Manifold.pullbackTangentOrientation

theorem locallyConstant_neighborhood_of_eventually_eq {X Y : Type*} [TopologicalSpace X]
    (S : _root_.TopologicalSpace.Opens X) (x : S) (g : S → Y) (h : ∀ᶠ y in 𝓝 x, g y = g x) :
    ∃ U : _root_.TopologicalSpace.Opens X, ∃ hU : (U : Set X) ⊆ S,
      x.val ∈ U ∧ IsLocallyConstant (fun y : U => g ⟨y.val, hU y.property⟩) := by
  obtain ⟨W, hW, hWopen, hxW⟩ := mem_nhds_iff.mp h
  let U : _root_.TopologicalSpace.Opens X := ⟨Subtype.val '' W, S.isOpen.isOpenMap_subtype_val W hWopen⟩
  have hU : (U : Set X) ⊆ S := by
    rintro _ ⟨y, _, rfl⟩
    exact y.property
  refine ⟨U, hU, ⟨x, hxW, rfl⟩, ?_⟩
  have he : (fun y : U => g ⟨y.val, hU y.property⟩) = Function.const U (g x) := by
    funext y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨z, hz, rfl⟩
    exact hW hz
  rw [he]
  exact IsLocallyConstant.const _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.locallyConstant_neighborhood_of_eventually_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.locallyConstant_neighborhood_of_eventually_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.locallyConstant_neighborhood_of_eventually_eq ``Submission.DifferentialGeometry.Topology.Manifold.locallyConstant_neighborhood_of_eventually_eq

def orientationPullbackChartDomain (f : M → N) (hf : ContMDiff I J ∞ f) (p : M) : _root_.TopologicalSpace.Opens M :=
  ⟨(chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source,
    (chartAt H p).open_source.inter ((chartAt K (f p)).open_source.preimage hf.continuous)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.orientationPullbackChartDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.orientationPullbackChartDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.orientationPullbackChartDomain ``Submission.DifferentialGeometry.Topology.Manifold.orientationPullbackChartDomain

def orientationPullbackChartPoint (f : M → N) (hf : ContMDiff I J ∞ f) (p : M) :
    orientationPullbackChartDomain I J f hf p :=
  ⟨p, mem_chart_source H p, mem_chart_source K (f p)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.orientationPullbackChartPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.orientationPullbackChartPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.orientationPullbackChartPoint ``Submission.DifferentialGeometry.Topology.Manifold.orientationPullbackChartPoint

def orientationPullbackTargetRepresentation (f : M → N) (hf : ContMDiff I J ∞ f)
    (o : SmoothOrientation J N) (p : M)
    (x : orientationPullbackChartDomain I J f hf p) :
    Orientation ℝ F (Fin (Module.finrank ℝ F)) :=
  Orientation.map _ (preferredChartTangentEquiv J (f p) (f x.val) x.property.2).toLinearEquiv
    (o.val (f x.val))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.orientationPullbackTargetRepresentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.orientationPullbackTargetRepresentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.orientationPullbackTargetRepresentation ``Submission.DifferentialGeometry.Topology.Manifold.orientationPullbackTargetRepresentation

private def orientationPullbackTargetPoint (f : M → N) (hf : ContMDiff I J ∞ f) (p : M) :
    orientationPullbackChartDomain I J f hf p → (chartAt K (f p)).source :=
  fun x => ⟨f x.val, x.property.2⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.orientationPullbackTargetPoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.orientationPullbackTargetPoint target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ F] [IsManifold J ∞ N] in
private theorem orientationPullbackTargetPoint_continuous (f : M → N)
    (hf : ContMDiff I J ∞ f) (p : M) :
    Continuous (orientationPullbackTargetPoint I J f hf p) :=
  (hf.continuous.comp continuous_subtype_val).subtype_mk _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.orientationPullbackTargetPoint_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.orientationPullbackTargetPoint_continuous target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem orientationPullbackTargetRepresentation_eq (f : M → N)
    (hf : ContMDiff I J ∞ f) (o : SmoothOrientation J N) (p : M) :
    orientationPullbackTargetRepresentation I J f hf o p =
      (fun y : (chartAt K (f p)).source =>
        Orientation.map _ (preferredChartTangentEquiv J (f p) y.val y.property).toLinearEquiv
          (o.val y.val)) ∘ orientationPullbackTargetPoint I J f hf p := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.orientationPullbackTargetRepresentation_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.orientationPullbackTargetRepresentation_eq target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem orientationPullbackTargetRepresentation_locallyConstant (f : M → N)
    (hf : ContMDiff I J ∞ f) (o : SmoothOrientation J N) (p : M) :
    IsLocallyConstant (orientationPullbackTargetRepresentation I J f hf o p) := by
  rw [orientationPullbackTargetRepresentation_eq]
  exact (o.property (f p)).comp_continuous (orientationPullbackTargetPoint_continuous I J f hf p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.orientationPullbackTargetRepresentation_locallyConstant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.orientationPullbackTargetRepresentation_locallyConstant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.orientationPullbackTargetRepresentation_locallyConstant ``Submission.DifferentialGeometry.Topology.Manifold.orientationPullbackTargetRepresentation_locallyConstant

omit [FiniteDimensional ℝ F] in
theorem inverseOrientationField_eventually_eq {X : Type*} [TopologicalSpace X]
    (e : X → E ≃L[ℝ] F) (x : X)
    (he : ContinuousAt (fun y => (e y : E →L[ℝ] F)) x)
    (o : X → Orientation ℝ F (Fin (Module.finrank ℝ F))) (ho : IsLocallyConstant o) :
    ∀ᶠ y in 𝓝 x, tangentOrientationEquiv (e y).symm.toLinearEquiv (o y) =
      tangentOrientationEquiv (e x).symm.toLinearEquiv (o x) := by
  filter_upwards [ho.eventually_eq x,
    tangentOrientationEquiv_symm_eventually_eq e x he (o x)] with y hy heq
  rw [hy]
  exact heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.inverseOrientationField_eventually_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.inverseOrientationField_eventually_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.inverseOrientationField_eventually_eq ``Submission.DifferentialGeometry.Topology.Manifold.inverseOrientationField_eventually_eq

theorem pullbackTangentOrientation_eventually_eq (f : M → N)
    (hf : ContMDiff I J ∞ f) (hbij : ∀ x : M, _root_.Function.Bijective (mfderiv I J f x))
    (o : SmoothOrientation J N) (p : M) :
    let S := orientationPullbackChartDomain I J f hf p
    let pS := orientationPullbackChartPoint I J f hf p
    let g : S → Orientation ℝ E (Fin (Module.finrank ℝ E)) := fun x =>
      Orientation.map _ (preferredChartTangentEquiv I p x.val x.property.1).toLinearEquiv
        (pullbackTangentOrientation I J f hbij o.val x.val)
    ∀ᶠ x in 𝓝 pS, g x = g pS := by
  intro S pS g
  let C : S → E ≃L[ℝ] F := coordinateDifferentialEquiv I J f hbij p
  have hc : ContinuousAt (fun x : S => (C x : E →L[ℝ] F)) pS :=
    continuousAt_coordinateDifferentialEquiv I J f hf hbij p
  have hevent := inverseOrientationField_eventually_eq C pS hc
    (orientationPullbackTargetRepresentation I J f hf o p)
    (orientationPullbackTargetRepresentation_locallyConstant I J f hf o p)
  filter_upwards [hevent] with x hx
  exact (coordinateDifferentialEquiv_orientation_pullback I J f hbij p x (o.val (f x.val))).symm.trans
    (hx.trans (coordinateDifferentialEquiv_orientation_pullback I J f hbij p pS (o.val (f p))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.pullbackTangentOrientation_eventually_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.pullbackTangentOrientation_eventually_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.pullbackTangentOrientation_eventually_eq ``Submission.DifferentialGeometry.Topology.Manifold.pullbackTangentOrientation_eventually_eq

theorem pullbackTangentOrientation_localRepresentations (f : M → N)
    (hf : ContMDiff I J ∞ f) (hbij : ∀ x : M, _root_.Function.Bijective (mfderiv I J f x))
    (o : SmoothOrientation J N) (p : M) :
    ∃ U : _root_.TopologicalSpace.Opens M, ∃ hU : (U : Set M) ⊆ (chartAt H p).source,
      p ∈ U ∧ IsLocallyConstant (fun y : U =>
        Orientation.map _ (preferredChartTangentEquiv I p y.val (hU y.property)).toLinearEquiv
          (pullbackTangentOrientation I J f hbij o.val y.val)) := by
  let S : _root_.TopologicalSpace.Opens M := ⟨(chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source,
    (chartAt H p).open_source.inter ((chartAt K (f p)).open_source.preimage hf.continuous)⟩
  let pS : S := ⟨p, mem_chart_source H p, mem_chart_source K (f p)⟩
  let g : S → Orientation ℝ E (Fin (Module.finrank ℝ E)) := fun x =>
    Orientation.map _ (preferredChartTangentEquiv I p x.val x.property.1).toLinearEquiv
      (pullbackTangentOrientation I J f hbij o.val x.val)
  have h : ∀ᶠ x in 𝓝 pS, g x = g pS := pullbackTangentOrientation_eventually_eq I J f hf hbij o p
  obtain ⟨U, hU, hpU, hg⟩ := locallyConstant_neighborhood_of_eventually_eq S pS g h
  exact ⟨U, fun y hy => (hU hy).1, hpU, hg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.pullbackTangentOrientation_localRepresentations then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.pullbackTangentOrientation_localRepresentations"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.pullbackTangentOrientation_localRepresentations ``Submission.DifferentialGeometry.Topology.Manifold.pullbackTangentOrientation_localRepresentations

def pullbackSmoothOrientation (f : M → N) (hf : ContMDiff I J ∞ f)
    (hbij : ∀ x : M, _root_.Function.Bijective (mfderiv I J f x)) (o : SmoothOrientation J N) :
    SmoothOrientation I M :=
  smoothOrientationOfLocalRepresentations I (pullbackTangentOrientation I J f hbij o.val)
    (pullbackTangentOrientation_localRepresentations I J f hf hbij o)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation ``Submission.DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation

theorem pullbackSmoothOrientation_apply (f : M → N) (hf : ContMDiff I J ∞ f)
    (hbij : ∀ x : M, _root_.Function.Bijective (mfderiv I J f x)) (o : SmoothOrientation J N) (x : M) :
    (pullbackSmoothOrientation I J f hf hbij o).val x =
      tangentOrientationEquiv (differentialEquivOfBijective I J f hbij x).symm.toLinearEquiv
        (o.val (f x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_apply ``Submission.DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_apply
end DifferentialGeometry.Topology.Manifold
