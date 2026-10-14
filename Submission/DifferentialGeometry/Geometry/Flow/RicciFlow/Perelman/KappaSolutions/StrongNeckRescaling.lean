import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StrongNeck
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvatureNormalization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

private local instance strongRescalingSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.strongRescalingSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.strongRescalingSphereDimension target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval}

private local instance strongRescalingC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.strongRescalingC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.strongRescalingC1 target :: scope.openDecls } }

omit [T2Space M] in
theorem strongNeckNormalizedMetric_curvatureNormalizedSolution
    (S : SolutionOn (I := I) (M := M) D) (p : M) (t : ℝ)
    (ht : t ∈ D.carrier) (hQ : 0 < S.scalar t p)
    {epsilon : ℝ} {f : C(spatialNeckBuffer epsilon, M)}
    (hf : _root_.Manifold.IsSmoothEmbedding SpatialNeckCylinderModel I ∞ f)
    (hR : 0 < (curvatureNormalizedSolution S t (S.scalar t p) hQ ht).scalar 0 p)
    (s : ℝ) :
    strongNeckNormalizedMetric (curvatureNormalizedSolution S t (S.scalar t p) hQ ht)
        p 0 hR hf s = strongNeckNormalizedMetric S p t hQ hf s := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [strongNeckNormalizedMetric_inner, strongNeckNormalizedMetric_inner,
    curvatureNormalizedSolution_scalar_base S t (S.scalar t p) hQ ht p rfl,
    zero_add, div_one, one_mul]
  change (scaleMetric (S.scalar t p) hQ (S.base.metric (parabolicTime t (S.scalar t p) s))).inner
      (f x) (mfderiv SpatialNeckCylinderModel I f x v) (mfderiv SpatialNeckCylinderModel I f x w) = _
  rw [scaleMetric_inner]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.strongNeckNormalizedMetric_curvatureNormalizedSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.strongNeckNormalizedMetric_curvatureNormalizedSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.strongNeckNormalizedMetric_curvatureNormalizedSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.strongNeckNormalizedMetric_curvatureNormalizedSolution


def StrongNeckWitness.ofCurvatureNormalization
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hcarrier : D.carrier = _root_.Set.Iic (0 : ℝ))
    (yStar : SpatialNeckSphere) (p : M) (t : ℝ)
    (ht : t ∈ D.carrier) (hQ : 0 < S.scalar t p) {epsilon : ℝ}
    (W : StrongNeckWitness (curvatureNormalizedSolution S t (S.scalar t p) hQ ht)
      yStar p 0 epsilon) : StrongNeckWitness S yStar p t epsilon where
  dimension_three := W.dimension_three
  isSolution := hS
  epsilon_pos := W.epsilon_pos
  epsilon_lt_one := W.epsilon_lt_one
  scalar_pos := hQ
  time_window := by
    rw [hcarrier] at ht ⊢
    exact fun _ hs => hs.2.trans ht
  embedding := W.embedding
  smooth_embedding := W.smooth_embedding
  marked := W.marked
  jet := W.jet
  jet_zero := by
    intro s hs x v
    rw [W.jet_zero s hs x v,
      strongNeckNormalizedMetric_curvatureNormalizedSolution S p t ht hQ
        W.smooth_embedding W.scalar_pos s]
  jet_succ := W.jet_succ
  closeness := W.closeness

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StrongNeckWitness.ofCurvatureNormalization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StrongNeckWitness.ofCurvatureNormalization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StrongNeckWitness.ofCurvatureNormalization ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StrongNeckWitness.ofCurvatureNormalization


theorem isStrongNeckCenter_of_curvatureNormalizedSolution
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hcarrier : D.carrier = _root_.Set.Iic (0 : ℝ))
    (yStar : SpatialNeckSphere) (p : M) (t : ℝ)
    (ht : t ∈ D.carrier) (hQ : 0 < S.scalar t p) {epsilon : ℝ}
    (hneck : IsStrongNeckCenter (curvatureNormalizedSolution S t (S.scalar t p) hQ ht)
      yStar p 0 epsilon) : IsStrongNeckCenter S yStar p t epsilon := by
  obtain ⟨W⟩ := hneck
  exact ⟨W.ofCurvatureNormalization S hS hcarrier yStar p t ht hQ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.isStrongNeckCenter_of_curvatureNormalizedSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.isStrongNeckCenter_of_curvatureNormalizedSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.isStrongNeckCenter_of_curvatureNormalizedSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.isStrongNeckCenter_of_curvatureNormalizedSolution

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
