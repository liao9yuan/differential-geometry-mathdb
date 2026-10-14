import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointMixedBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

private theorem original_regular_dense (S : PartialStandardSolution) :
    S.domain ⊆ closure (lifetimeInterval S.lifetime S.lifetime_pos).regular := by
  change (lifetimeInterval S.lifetime S.lifetime_pos).carrier ⊆
    closure (lifetimeInterval S.lifetime S.lifetime_pos).regular
  by_cases htop : S.lifetime = ⊤
  · simpa only [lifetimeInterval, htop, dite_true, RealTimeInterval.closedInfinite, closure_Ioi] using
      (subset_rfl : _root_.Set.Ici (0 : ℝ) ⊆ _root_.Set.Ici 0)
  · have hp : 0 < S.lifetime.toReal := ENNReal.toReal_pos S.lifetime_pos.ne' htop
    simpa only [lifetimeInterval, htop, dite_false, RealTimeInterval.closedOpen, closure_Ioo hp.ne] using
      (_root_.Set.Ico_subset_Icc_self : _root_.Set.Ico (0 : ℝ) S.lifetime.toReal ⊆ _root_.Set.Icc 0 S.lifetime.toReal)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.original_regular_dense
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.original_regular_dense target :: scope.openDecls } }

private theorem mixed_bound_of_curvature (S : PartialStandardSolution)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθT : ENNReal.ofReal θ < S.lifetime)
    (N : ℕ) (K : ℝ) (A : ℕ → ℝ)
    (hcurv : ∀ t ∈ _root_.Set.Icc 0 θ, ∀ x : E3,
      Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤ K)
    (hinit : ∀ k : ℕ, ∀ x : E3,
      Real.sqrt (nablaKRm04NormSqIntrinsic S.toSolutionOn k 0 x) ≤ A k) :
    ∀ a b : ℕ, a + 2 * b ≤ N → ∀ t ∈ _root_.Set.Icc 0 θ, ∀ x : E3,
      Real.sqrt (normSq0S (S.metric t) x (4 + a)
        (iteratedCovariantTimeDerivWithin S.metric
          (fun r => nablaKRm04Field S.toSolutionOn r a x) S.domain b t)) ≤
        endpointMixedCurvatureBound 3 N θ K A := by
  have hslab := (Icc_subset_lifetimeInterval_iff S.lifetime S.lifetime_pos θ hθ).mpr hθT
  have hreg : _root_.Set.Ioo 0 θ ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular := by
    intro t ht
    exact (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos t).mpr
      ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2.le).trans_lt hθT⟩
  have hg := chartGram_contMDiffOn_of_cartesian S.metric S.domain S.smooth
  have hh := curvature_endpoint_mixed_bound θ hθ N K A _ S.toSolutionOn S.isSolutionOn
    (uniqueDiffOn_lifetimeInterval S.lifetime S.lifetime_pos) hg (original_regular_dense S)
    (Or.inl (S.complete 0 (hslab ⟨le_rfl, hθ⟩))) hslab hreg hcurv
    (fun k _ x => hinit k x)
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hh
  convert hh using 1
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.mixed_bound_of_curvature
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.mixed_bound_of_curvature target :: scope.openDecls } }

theorem PartialStandardSolution.curvature_mixed_bounds_closed (S : PartialStandardSolution)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθT : ENNReal.ofReal θ < S.lifetime) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℕ, a + 2 * b ≤ N → ∀ t ∈ _root_.Set.Icc 0 θ, ∀ x : E3,
      Real.sqrt (normSq0S (S.metric t) x (4 + a)
        (iteratedCovariantTimeDerivWithin S.metric
          (fun r => nablaKRm04Field S.toSolutionOn r a x) S.domain b t)) ≤ C := by
  obtain ⟨A, _, hi⟩ := standard_initial_curvature_derivative_bounds
  obtain ⟨K, _, hK⟩ := S.curvature_bound θ hθ hθT
  exact ⟨endpointMixedCurvatureBound 3 N θ K A,
    endpointMixedCurvatureBound_nonneg _ _ _ _ _,
    mixed_bound_of_curvature S θ hθ hθT N K A hK (hi S)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.curvature_mixed_bounds_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.curvature_mixed_bounds_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.curvature_mixed_bounds_closed ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.curvature_mixed_bounds_closed

theorem uniformStandardLifetime_mixed_bounds_closed
    (θ : ℝ) (hθ : 0 ≤ θ) (hθT : ENNReal.ofReal θ < uniformStandardLifetime) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : StandardSolution,
      ∀ a b : ℕ, a + 2 * b ≤ N → ∀ t ∈ _root_.Set.Icc 0 θ, ∀ x : E3,
        Real.sqrt (normSq0S (S.val.metric t) x (4 + a)
          (iteratedCovariantTimeDerivWithin S.val.metric
            (fun r => nablaKRm04Field S.val.toSolutionOn r a x) S.val.domain b t)) ≤ C := by
  obtain ⟨A, _, hi⟩ := standard_initial_curvature_derivative_bounds
  obtain ⟨hlife, K, _, hK⟩ := uniformStandardLifetime_slab θ hθ hθT
  exact ⟨endpointMixedCurvatureBound 3 N θ K A,
    endpointMixedCurvatureBound_nonneg _ _ _ _ _,
    fun S => mixed_bound_of_curvature S.val θ hθ (hlife S) N K A (hK S) (hi S.val)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_mixed_bounds_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_mixed_bounds_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_mixed_bounds_closed ``Submission.DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_mixed_bounds_closed
end DifferentialGeometry.PDE.RicciFlow
