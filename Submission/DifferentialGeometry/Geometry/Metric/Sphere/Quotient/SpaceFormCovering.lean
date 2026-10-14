import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import Submission.DifferentialGeometry.Geometry.Curvature.PositiveSectional
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormGroup
import Submission.DifferentialGeometry.Topology.Manifold.DiffeomorphOrientationDichotomy
import Submission.DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormOrientationClosure
import Submission.DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormProjective

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Metric _root_.Submission.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

noncomputable def roundSphereQuotientOfSphericalSpaceFormGroup
    (G : DifferentialGeometry.Topology.SphericalSpaceFormGroup) :
    RoundSphereQuotient (EuclideanSpace ℝ (Fin 4)) 3 := by
  classical
  letI : Fintype G.group := Fintype.ofFinite G.group
  exact {
    Q := G.Orbit
    Γ := G.group
    ρ := G.group.subtype
    action_free := by
      intro γ q hq
      exact G.free γ q hq
    proj := G.projection
    proj_smooth := G.projection_isLocalDiffeomorph.contMDiff
    proj_smul := by
      intro γ q
      exact G.projection_invariant γ q
    proj_eq_imp := by
      intro q1 q2 h
      exact (G.projection_eq_iff q1 q2).mp h
    sectionAt := fun x =>
      LocalSmoothSection.ofLocal (proj := G.projection) G.projection_surjective
        G.projection_isLocalDiffeomorph x }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundSphereQuotientOfSphericalSpaceFormGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundSphereQuotientOfSphericalSpaceFormGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundSphereQuotientOfSphericalSpaceFormGroup ``Submission.DifferentialGeometry.Geometry.roundSphereQuotientOfSphericalSpaceFormGroup

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Topology

universe u

private theorem metricRm04StandardAt_eq_zero_of_not_linearIndependent
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (x : M)
    (W T : TangentSpace ThreeModel x) (hdep : ¬ LinearIndependent ℝ ![W, T]) :
    DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt
      (I := ThreeModel) (M := M) g x W T T W = 0 := by
  let B : TangentSpace ThreeModel x → TangentSpace ThreeModel x →
      TangentSpace ThreeModel x → TangentSpace ThreeModel x → ℝ :=
    fun X Y Z U => DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt
      (I := ThreeModel) (M := M) g x X Y Z U
  have hB : DifferentialGeometry.Geometry.Curvature.IsAlgCurvForm B := by
    change DifferentialGeometry.Geometry.Curvature.IsAlgCurvForm
      (DifferentialGeometry.Geometry.Curvature.tensor04StandardAt
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := ThreeModel) (M := M) g x))
    exact DifferentialGeometry.Geometry.Curvature.mem_algebraicCurvatureTensorSubmodule.mp
      (DifferentialGeometry.Geometry.Curvature.metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := ThreeModel) (M := M) g x)
  by_cases hW : W = 0
  · subst hW
    have hzero := hB.smul_left 0 (0 : TangentSpace ThreeModel x) T T 0
    simpa [B] using hzero
  · rw [LinearIndependent.pair_iff' hW] at hdep
    push Not at hdep
    obtain ⟨a, rfl⟩ := hdep
    have hdiag : B W W (a • W) W = 0 := by
      have hskew := hB.anti_first W W (a • W) W
      linarith
    have hskew := hB.anti_first W (a • W) (a • W) W
    have hsmul := hB.smul_left a W W (a • W) W
    change B W (a • W) (a • W) W = 0
    rw [hskew, hsmul, hdiag]
    ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.metricRm04StandardAt_eq_zero_of_not_linearIndependent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.metricRm04StandardAt_eq_zero_of_not_linearIndependent target :: scope.openDecls } }

private theorem sectionalCurvatureDenominator_eq_zero_of_not_linearIndependent
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (x : M)
    (v w : TangentSpace ThreeModel x) (hdep : ¬ LinearIndependent ℝ ![v, w]) :
    g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 = 0 := by
  have hnonneg : 0 ≤ g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 := by
    simpa only [DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_def]
      using DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_nonneg
        (I := ThreeModel) (M := M) g x v w
  have hnotpos : ¬ 0 < g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 := by
    intro hpos
    exact hdep (DifferentialGeometry.Geometry.Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos
      (I := ThreeModel) (M := M) g x v w (by
        simpa only [DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_def]
          using hpos))
  exact le_antisymm (le_of_not_gt hnotpos) hnonneg

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sectionalCurvatureDenominator_eq_zero_of_not_linearIndependent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sectionalCurvatureDenominator_eq_zero_of_not_linearIndependent target :: scope.openDecls } }

theorem sectionalCurvatureMetricBridge_holds :
    sectionalCurvatureMetricBridge.{u} := by
  intro M g hg
  obtain ⟨κ, hκpos, hκ⟩ := hg
  refine ⟨κ, hκpos, fun x X Y => ?_⟩
  by_cases hLI : LinearIndependent ℝ ![X, Y]
  · have hden : 0 < g.inner x X X * g.inner x Y Y - (g.inner x X Y) ^ 2 := by
      simpa only [DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_def]
        using DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent
          (I := ThreeModel) (M := M.Carrier) g x X Y hLI
    have hsec := hκ x X Y hLI
    rw [DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div]
      at hsec
    field_simp [ne_of_gt hden] at hsec
    linarith
  · have hnum := metricRm04StandardAt_eq_zero_of_not_linearIndependent
      (M := M.Carrier) g x X Y hLI
    have hden := sectionalCurvatureDenominator_eq_zero_of_not_linearIndependent
      (M := M.Carrier) g x X Y hLI
    rw [hnum]
    have hden' : g.inner x X X * g.inner x Y Y -
        g.inner x X Y * g.inner x X Y = 0 := by
      simpa only [pow_two] using hden
    rw [hden', _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sectionalCurvatureMetricBridge_holds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sectionalCurvatureMetricBridge_holds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sectionalCurvatureMetricBridge_holds ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sectionalCurvatureMetricBridge_holds

theorem roundSphereQuotientOrientedCovering_holds :
    roundSphereQuotientOrientedCovering.{u} := by
  intro M D he
  obtain ⟨e⟩ := he
  let G := sphericalSpaceFormGroupOfRoundSphereQuotient D
  let F : Diffeomorph (𝓡 3) (𝓡 3) M.Carrier G.Orbit ∞ :=
    e.trans (sphericalSpaceFormOrbitDiffeomorph D).symm
  rcases Diffeomorph.preservesOrientation_or_preservesOrientation_opposite F
      M.orientation G.manifold.orientation with hF | hF
  · exact ⟨G, ⟨⟨F, hF⟩⟩⟩
  · obtain ⟨G', ⟨f⟩⟩ := sphericalSpaceFormOrientationClosure_holds G
    let Fop : ClosedOrientedManifold.OrientedDiffeomorph
        M.toClosedOrientedManifold G.manifold.opposite.toClosedOrientedManifold := ⟨F, hF⟩
    exact ⟨G', ⟨Fop.trans f⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.roundSphereQuotientOrientedCovering_holds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.roundSphereQuotientOrientedCovering_holds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.roundSphereQuotientOrientedCovering_holds ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.roundSphereQuotientOrientedCovering_holds

theorem sphericalSpaceFormCovering_holds : sphericalSpaceFormCovering.{u} :=
  sphericalSpaceFormCovering_of_inputs sectionalCurvatureMetricBridge_holds
    roundSphereQuotientOrientedCovering_holds

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalSpaceFormCovering_holds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalSpaceFormCovering_holds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalSpaceFormCovering_holds ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalSpaceFormCovering_holds

noncomputable def sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup
    (G : SphericalSpaceFormGroup) :
    SphericalSpaceFormQuotientModel ThreeModel G.manifold.Carrier where
  quotient := roundSphereQuotientOfSphericalSpaceFormGroup G
  equiv := Diffeomorph.refl ThreeModel G.manifold.Carrier ∞

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup

private theorem isConstantPositiveSectionalCurvature_of_metric
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M)
    (hg : DifferentialGeometry.Geometry.Curvature.constantPositiveSectionalCurvatureMetric
      (I := ThreeModel) (M := M) g) :
    IsConstantPositiveSectionalCurvature g := by
  obtain ⟨c, hc, hsec⟩ := hg
  refine ⟨c, hc, fun x v w hLI => ?_⟩
  have hden : 0 < g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 := by
    simpa only [DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_def]
      using DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent
        (I := ThreeModel) (M := M) g x v w hLI
  rw [DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div,
    hsec x v w]
  field_simp [ne_of_gt hden]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isConstantPositiveSectionalCurvature_of_metric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isConstantPositiveSectionalCurvature_of_metric target :: scope.openDecls } }

theorem isPositiveSpaceFormModel_antipodal :
    IsPositiveSpaceFormModel SphericalSpaceFormGroup.antipodal.manifold := by
  obtain ⟨g, hg⟩ :=
    spherical_space_form_admits_constant_positive_sectional_curvature
      (I := ThreeModel) (M := SphericalSpaceFormGroup.antipodal.manifold.Carrier)
      ⟨sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup
        SphericalSpaceFormGroup.antipodal⟩
  exact ⟨g, isConstantPositiveSectionalCurvature_of_metric g hg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPositiveSpaceFormModel_antipodal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPositiveSpaceFormModel_antipodal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPositiveSpaceFormModel_antipodal ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPositiveSpaceFormModel_antipodal

theorem exists_isPositiveSpaceFormModel_nonsimplyConnected :
    ∃ M : ConnectedClosedOrientedManifold.{0} 3,
      IsPositiveSpaceFormModel M ∧
        ∀ p : M.Carrier, ¬ Subsingleton (FundamentalGroup M.Carrier p) :=
  ⟨SphericalSpaceFormGroup.antipodal.manifold,
    isPositiveSpaceFormModel_antipodal,
    SphericalSpaceFormGroup.not_subsingleton_fundamentalGroup_antipodal⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_isPositiveSpaceFormModel_nonsimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_isPositiveSpaceFormModel_nonsimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_isPositiveSpaceFormModel_nonsimplyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_isPositiveSpaceFormModel_nonsimplyConnected

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
