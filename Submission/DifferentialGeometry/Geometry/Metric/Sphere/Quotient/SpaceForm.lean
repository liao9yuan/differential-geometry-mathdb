import Submission.DifferentialGeometry.Topology.ThreeManifold.Closed
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Conditions
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Quotient.PositiveSpaceForm
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

private instance _root_.Submission.DifferentialGeometry.Geometry.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry target :: scope.openDecls } }

structure SphericalSpaceFormQuotientModel
    (I : ModelWithCorners ℝ E H) (N : Type u)
    [TopologicalSpace N] [ChartedSpace H N] : Type _ where
  quotient : RoundSphereQuotient.{0, u} (EuclideanSpace ℝ (Fin 4)) 3
  equiv : N ≃ₘ⟮I, 𝓡 3⟯ quotient.Q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SphericalSpaceFormQuotientModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SphericalSpaceFormQuotientModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SphericalSpaceFormQuotientModel ``Submission.DifferentialGeometry.Geometry.SphericalSpaceFormQuotientModel

def isSphericalSpaceFormQuotient
    (I : ModelWithCorners ℝ E H) (N : Type u)
    [TopologicalSpace N] [ChartedSpace H N] : Prop :=
  Nonempty (SphericalSpaceFormQuotientModel I N)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isSphericalSpaceFormQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isSphericalSpaceFormQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isSphericalSpaceFormQuotient ``Submission.DifferentialGeometry.Geometry.isSphericalSpaceFormQuotient

def isSphericalSpaceForm : Prop :=
  isSphericalSpaceFormQuotient I M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isSphericalSpaceForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isSphericalSpaceForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isSphericalSpaceForm ``Submission.DifferentialGeometry.Geometry.isSphericalSpaceForm

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem constant_positive_sectional_curvature_implies_spherical_space_form
    (hM : isClosedThreeManifold (I := I) (M := M))
    (hconst : admitsConstantPositiveSectionalCurvature (I := I) (M := M)) :
    isSphericalSpaceForm (I := I) (M := M) := by
  obtain ⟨hcompact, hconn, hbdry, hdim⟩ := hM
  obtain ⟨g, c, hc, hsec⟩ := hconst
  let model :=
    constPosQuotient
      (I := I) (M := M) hcompact hconn hbdry hdim g c hc hsec
  exact ⟨⟨model.1, model.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.constant_positive_sectional_curvature_implies_spherical_space_form then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.constant_positive_sectional_curvature_implies_spherical_space_form"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.constant_positive_sectional_curvature_implies_spherical_space_form ``Submission.DifferentialGeometry.Geometry.constant_positive_sectional_curvature_implies_spherical_space_form

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem spherical_space_form_admits_constant_positive_sectional_curvature
    (model : isSphericalSpaceFormQuotient I M) :
    admitsConstantPositiveSectionalCurvature (I := I) (M := M) := by
  obtain ⟨S⟩ := model
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := by
    rw [finrank_euclideanSpace_fin]; infer_instance
  obtain ⟨c, hc, hsec⟩ := S.quotient.gQuot_constPosSec
  refine ⟨Diffeomorph.pullbackMetricCross S.quotient.gQuot S.equiv, c, hc, fun x X Y => ?_⟩
  rw [metricRm04Standard_pullbackCross S.quotient.gQuot S.equiv x X Y Y X, hsec,
    ← Diffeomorph.pullbackMetricCross_inner S.quotient.gQuot S.equiv x X X,
    ← Diffeomorph.pullbackMetricCross_inner S.quotient.gQuot S.equiv x Y Y,
    ← Diffeomorph.pullbackMetricCross_inner S.quotient.gQuot S.equiv x X Y]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.spherical_space_form_admits_constant_positive_sectional_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.spherical_space_form_admits_constant_positive_sectional_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.spherical_space_form_admits_constant_positive_sectional_curvature ``Submission.DifferentialGeometry.Geometry.spherical_space_form_admits_constant_positive_sectional_curvature

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem spherical_space_form_implies_constant_positive_sectional_curvature
    (hsph : isSphericalSpaceForm (I := I) (M := M)) :
    admitsConstantPositiveSectionalCurvature (I := I) (M := M) :=
  spherical_space_form_admits_constant_positive_sectional_curvature
    (I := I) (M := M) hsph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.spherical_space_form_implies_constant_positive_sectional_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.spherical_space_form_implies_constant_positive_sectional_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.spherical_space_form_implies_constant_positive_sectional_curvature ``Submission.DifferentialGeometry.Geometry.spherical_space_form_implies_constant_positive_sectional_curvature

omit [NeZero (Module.finrank ℝ E)] in
theorem constant_positive_sectional_curvature_iff_spherical_space_form
    (hM : isClosedThreeManifold (I := I) (M := M)) :
    admitsConstantPositiveSectionalCurvature (I := I) (M := M) ↔
      isSphericalSpaceForm (I := I) (M := M) := by
  let : I.Boundaryless := hM.2.2.1
  constructor
  · exact constant_positive_sectional_curvature_implies_spherical_space_form
      (I := I) (M := M) hM
  · exact spherical_space_form_implies_constant_positive_sectional_curvature
      (I := I) (M := M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.constant_positive_sectional_curvature_iff_spherical_space_form then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.constant_positive_sectional_curvature_iff_spherical_space_form"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.constant_positive_sectional_curvature_iff_spherical_space_form ``Submission.DifferentialGeometry.Geometry.constant_positive_sectional_curvature_iff_spherical_space_form

end DifferentialGeometry.Geometry
