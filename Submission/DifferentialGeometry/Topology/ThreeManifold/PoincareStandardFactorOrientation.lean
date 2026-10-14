import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardOrientationRefinement
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLaws
import Submission.DifferentialGeometry.Topology.ThreeManifold.StandardFactors

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u

def sphericalSpaceFormOrientationClosure : Prop :=
  ∀ G : SphericalSpaceFormGroup, ∃ G' : SphericalSpaceFormGroup,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      G.manifold.opposite.toClosedOrientedManifold G'.manifold.toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphericalSpaceFormOrientationClosure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphericalSpaceFormOrientationClosure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphericalSpaceFormOrientationClosure ``Submission.DifferentialGeometry.Topology.sphericalSpaceFormOrientationClosure

def sphereTwoTimesCircleOrientationClosure : Prop :=
  ∃ ρ : Diffeomorph ((𝓡 2).prod (𝓡 1)) ((𝓡 2).prod (𝓡 1))
      SphereTwoTimesCircle SphereTwoTimesCircle ∞,
    ρ.preservesOrientation sphereTwoTimesCircleOrientation.opposite
      sphereTwoTimesCircleOrientation

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereTwoTimesCircleOrientationClosure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereTwoTimesCircleOrientationClosure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereTwoTimesCircleOrientationClosure ``Submission.DifferentialGeometry.Topology.sphereTwoTimesCircleOrientationClosure

def factorOrientationClosure : Prop :=
  ∀ X : ConnectedClosedOrientedManifold.{u} 3, isStandardFactor X → isStandardFactor X.opposite

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.factorOrientationClosure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.factorOrientationClosure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.factorOrientationClosure ``Submission.DifferentialGeometry.Topology.factorOrientationClosure

theorem factorOrientationClosure_of_sphereTwoTimesCircle_and_sphericalSpaceForm
    (hcirc : sphereTwoTimesCircleOrientationClosure)
    (hform : sphericalSpaceFormOrientationClosure) :
    factorOrientationClosure.{u} := by
  intro X hX
  rcases hX with ⟨G, he⟩ | ⟨f, hf⟩
  · obtain ⟨e⟩ := he
    have heo : ClosedOrientedManifold.OrientedDiffeomorph X.opposite.toClosedOrientedManifold
        G.manifold.opposite.toClosedOrientedManifold :=
      ⟨e.1, Diffeomorph.preservesOrientation_opposite e.2⟩
    obtain ⟨G', he'⟩ := hform G
    obtain ⟨e'⟩ := he'
    exact Or.inl ⟨G', ⟨heo.trans e'⟩⟩
  · obtain ⟨ρ, hρ⟩ := hcirc
    refine Or.inr ⟨f.trans ρ, ?_⟩
    exact Diffeomorph.preservesOrientation_trans
      (Diffeomorph.preservesOrientation_opposite hf) hρ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.factorOrientationClosure_of_sphereTwoTimesCircle_and_sphericalSpaceForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.factorOrientationClosure_of_sphereTwoTimesCircle_and_sphericalSpaceForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.factorOrientationClosure_of_sphereTwoTimesCircle_and_sphericalSpaceForm ``Submission.DifferentialGeometry.Topology.factorOrientationClosure_of_sphereTwoTimesCircle_and_sphericalSpaceForm

theorem poincareStandardOrientationRefinement_of_connectedSumOpposite_and_factorOrientationClosure
    (hopp : connectedSumOpposite.{u}) (hstd : factorOrientationClosure.{u}) :
    poincareStandardOrientationRefinement.{u} := by
  intro F hF
  classical
  obtain ⟨P⟩ := hF
  have hlaws : connectedSumLaws.{u} :=
    connectedSumLaws_of_unit_commutative_associative sphereUnitLaws_holds
      connectedSumCommutative_holds connectedSumAssociative_holds
  have hlist : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum P.factors).toClosedOrientedManifold.opposite
      (finiteConnectedSum
        (P.factors.map ConnectedClosedOrientedManifold.opposite)).toClosedOrientedManifold) :=
    finiteConnectedSum_opposite_of_connectedSumLaws hlaws hopp
      standardThreeSphereLift_orientationReversing_diffeomorph P.factors
  rcases Diffeomorph.preservesOrientation_or_preservesOrientation_opposite P.diffeomorph
    F.orientation (finiteConnectedSum P.factors).orientation with hφ | hφ
  · exact ⟨⟨P.factors, P.standard, ⟨P.diffeomorph, hφ⟩⟩⟩
  · obtain ⟨e⟩ := hlist
    have g : ClosedOrientedManifold.OrientedDiffeomorph F.toClosedOrientedManifold
        (finiteConnectedSum P.factors).toClosedOrientedManifold.opposite :=
      ⟨P.diffeomorph, hφ⟩
    refine ⟨⟨P.factors.map ConnectedClosedOrientedManifold.opposite, ?_, g.trans e⟩⟩
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
    exact hstd Y (P.standard Y hY)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.poincareStandardOrientationRefinement_of_connectedSumOpposite_and_factorOrientationClosure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.poincareStandardOrientationRefinement_of_connectedSumOpposite_and_factorOrientationClosure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.poincareStandardOrientationRefinement_of_connectedSumOpposite_and_factorOrientationClosure ``Submission.DifferentialGeometry.Topology.poincareStandardOrientationRefinement_of_connectedSumOpposite_and_factorOrientationClosure

theorem poincareStandardSumClosed_of_connectedSumOpposite_and_factorOrientationClosure
    (hopp : connectedSumOpposite.{u}) (hstd : factorOrientationClosure.{u}) :
    poincareStandardSumClosed.{u} :=
  poincareStandardSumClosed_of_orientationRefinement
    (poincareStandardOrientationRefinement_of_connectedSumOpposite_and_factorOrientationClosure
      hopp hstd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.poincareStandardSumClosed_of_connectedSumOpposite_and_factorOrientationClosure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.poincareStandardSumClosed_of_connectedSumOpposite_and_factorOrientationClosure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.poincareStandardSumClosed_of_connectedSumOpposite_and_factorOrientationClosure ``Submission.DifferentialGeometry.Topology.poincareStandardSumClosed_of_connectedSumOpposite_and_factorOrientationClosure

end DifferentialGeometry.Topology
