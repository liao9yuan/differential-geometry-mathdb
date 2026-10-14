import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareStandardGeometricFrontier
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCoverClassification
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ProjectivePresentation
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormCovering
import Submission.DifferentialGeometry.Geometry.Curvature.ProjectiveSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open private diffeomorphOfPartialDiffeomorphUniv from
  Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareStandardGeometricFrontier
open private isConstantPositiveSectionalCurvature_of_metric from
  Submission.DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormCovering

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff
open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry target :: scope.openDecls } }

theorem isPositiveSpaceFormModel_of_positiveComponent
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (R : PositiveComponent (M := M.Carrier) Set.univ) :
    IsPositiveSpaceFormModel M := by
  cases R with
  | sphere F hs ht => exact isPositiveSpaceFormModel_of_positiveComponent_sphere M hs ht
  | projective Z presentation F hs ht =>
    obtain ⟨e, he⟩ := presentation.exists_realProjectiveThree_diffeomorph
    let d := e.trans (diffeomorphOfPartialDiffeomorphUniv F hs ht)
    exact ⟨Diffeomorph.pullbackMetric roundProjectiveMetric d.symm,
      isConstantPositiveSectionalCurvature_of_pullbackMetric roundProjectiveMetric
        (isConstantPositiveSectionalCurvature_of_metric _
          constantPositiveSectionalCurvatureMetric_roundProjectiveMetric) d.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPositiveSpaceFormModel_of_positiveComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPositiveSpaceFormModel_of_positiveComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPositiveSpaceFormModel_of_positiveComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPositiveSpaceFormModel_of_positiveComponent

theorem MetricCutCapEvent.poincareStandardDiscarded_of_componentwisePositiveOrRoundComponent
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (h : ∀ C : ConnectedComponents E.discarded.Carrier,
      Nonempty (PositiveComponent
        (M := (E.discarded.toClosedOrientedManifold.component C).Carrier) Set.univ) ∨
      ∃ (D' : RealTimeInterval)
        (S : SolutionOn (I := ThreeModel)
          (M := (E.discarded.toClosedOrientedManifold.component C).Carrier) D')
        (ε : ℝ) (x : (E.discarded.toClosedOrientedManifold.component C).Carrier) (t : ℝ),
        Nonempty (RoundComponent S ε x t Set.univ)) : E.poincareStandardDiscarded := by
  apply MetricCutCapEvent.poincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct
    sphericalSpaceFormCovering_holds E
  intro C
  refine ⟨[E.discarded.toClosedOrientedManifold.component C], ?_,
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩
  intro F hF
  rw [List.mem_singleton] at hF
  subst F
  apply Or.inl
  rcases h C with hpositive | hround
  · obtain ⟨R⟩ := hpositive
    exact isPositiveSpaceFormModel_of_positiveComponent _ R
  · obtain ⟨D', S, ε, x, t, ⟨R⟩⟩ := hround
    exact isPositiveSpaceFormModel_of_roundComponent _ R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_componentwisePositiveOrRoundComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_componentwisePositiveOrRoundComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_componentwisePositiveOrRoundComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_componentwisePositiveOrRoundComponent

open _root_.Set _root_.Submission.Set in
theorem isPoincareStandard_of_ball_cap_cover
    (M : ConnectedClosedOrientedManifold.{u} 3)
    {K : Set M.Carrier} (B : PartialDiffeomorph I3 I3 ThreeSpace M.Carrier ∞)
    (hB : Metric.closedBall (0 : ThreeSpace) 1 ⊆ B.source)
    (cap : CapCore K)
    (hcover : B '' Metric.closedBall (0 : ThreeSpace) 1 ∪ K = _root_.Set.univ) :
    isPoincareStandard M.Carrier := by
  obtain ⟨W⟩ := nonempty_positiveComponent_of_ball_cap_cover B hB cap hcover
  exact isPoincareStandard_of_standard_factor M
    (isStandardFactor_of_isPositiveSpaceFormModel sphericalSpaceFormCovering_holds
      (isPositiveSpaceFormModel_of_positiveComponent M W))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPoincareStandard_of_ball_cap_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPoincareStandard_of_ball_cap_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPoincareStandard_of_ball_cap_cover ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPoincareStandard_of_ball_cap_cover


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
