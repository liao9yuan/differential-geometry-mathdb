import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolutionRealization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformLifetime
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.DerivativeBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Shi.Local

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

def PartialStandardSolution.pointedFlow (S : PartialStandardSolution) :
    PointedFlowData (I := 𝓡 3) (lifetimeInterval S.lifetime S.lifetime_pos) where
  M := E3
  basepoint := 0
  S := S.toSolutionOn
  isSolution := S.isSolutionOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.pointedFlow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.pointedFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.pointedFlow ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.pointedFlow

@[simp] theorem PartialStandardSolution.pointedFlow_metric (S : PartialStandardSolution) (t : ℝ) :
    (S.pointedFlow.atTime t).metric = S.metric t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.pointedFlow_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.pointedFlow_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.pointedFlow_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.pointedFlow_metric

theorem PartialStandardSolution.pointedFlow_complete (S : PartialStandardSolution)
    (t : ℝ) (ht : t ∈ S.domain) : MetricComplete (S.pointedFlow.atTime t) := by
  exact (S.complete t ht).complete

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.pointedFlow_complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.pointedFlow_complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.pointedFlow_complete ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.pointedFlow_complete

theorem PartialStandardSolution.initial_curvature_derivative_norm (S : PartialStandardSolution)
    (k : ℕ) (x : E3) :
    nablaKRm04NormSqIntrinsic S.toSolutionOn k 0 x =
      normSq0S DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x (4 + k)
        (iterCov DifferentialGeometry.PDE.RicciFlow.StandardCap.metric 4
          (metricRm04 DifferentialGeometry.PDE.RicciFlow.StandardCap.metric) k x) := by
  unfold nablaKRm04NormSqIntrinsic
  rw [nablaKRm_eq_iterCov]
  change normSq0S (S.metric 0) x (4 + k) (iterCov (S.metric 0) 4
    (metricRm04 (S.metric 0)) k x) = _
  rw [S.initial]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.initial_curvature_derivative_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.initial_curvature_derivative_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.initial_curvature_derivative_norm ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.initial_curvature_derivative_norm

theorem standard_initial_curvature_derivative_bounds :
    ∃ A : ℕ → ℝ, (∀ k, 0 < A k) ∧ ∀ S : PartialStandardSolution, ∀ k : ℕ, ∀ x : E3,
      Real.sqrt (nablaKRm04NormSqIntrinsic S.toSolutionOn k 0 x) ≤ A k := by
  choose A hA hbound using DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_bound_iterCov_metricRm04
  refine ⟨A, hA, ?_⟩
  intro S k x
  rw [S.initial_curvature_derivative_norm]
  exact hbound k x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_initial_curvature_derivative_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_initial_curvature_derivative_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_initial_curvature_derivative_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_initial_curvature_derivative_bounds

theorem PartialStandardSolution.curvature_derivative_bound_positive (S : PartialStandardSolution)
    {δ θ K : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ)
    (hθT : ENNReal.ofReal θ < S.lifetime)
    (hRm : ∀ t ∈ _root_.Set.Icc 0 θ, ∀ x : E3,
      Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤ K)
    (N k : ℕ) (hk : k ≤ N) (t : ℝ) (ht : t ∈ _root_.Set.Icc δ θ) (x : E3) :
    Real.sqrt (nablaKRm04NormSqIntrinsic S.toSolutionOn k t x) ≤
      Real.sqrt (rmOpenBound 3 (K ^ 2) 0 δ θ N k) := by
  have hslab : _root_.Set.Icc 0 θ ⊆ S.domain := fun s hs =>
    (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos s).mpr
      ⟨hs.1, (ENNReal.ofReal_le_ofReal hs.2).trans_lt hθT⟩
  have hreg : _root_.Set.Ioc 0 θ ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular := fun s hs =>
    (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos s).mpr
      ⟨hs.1, (ENNReal.ofReal_le_ofReal hs.2).trans_lt hθT⟩
  have hcurv : ∀ s ∈ _root_.Set.Icc 0 θ, ∀ y : S.pointedFlow.M, S.pointedFlow.rmNormSq s y ≤ K ^ 2 := by
    intro s hs y
    exact (Real.sqrt_le_iff.mp (hRm s hs y)).2
  have hcomplete := S.pointedFlow_complete 0 (hslab ⟨le_rfl, hδ.le.trans hδθ⟩)
  have h := movingRm_of_bound S.pointedFlow hδ hδθ hslab hreg hcomplete (sq_nonneg K)
    hcurv N k hk t ht x
  have hbound : nablaKRm04NormSqIntrinsic S.toSolutionOn k t x ≤
      rmOpenBound 3 (K ^ 2) 0 δ θ N k := by
    simpa only [PartialStandardSolution.pointedFlow, finrank_euclideanSpace, Fintype.card_fin] using h
  exact Real.sqrt_le_sqrt hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.curvature_derivative_bound_positive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.curvature_derivative_bound_positive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.curvature_derivative_bound_positive ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.curvature_derivative_bound_positive

theorem uniformStandardLifetime_curvature_derivative_bounds (δ θ : ℝ)
    (hδ : 0 < δ) (hδθ : δ ≤ θ) (hlt : ENNReal.ofReal θ < uniformStandardLifetime) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : StandardSolution, ∀ k : ℕ, k ≤ N →
      ∀ t ∈ _root_.Set.Icc δ θ, ∀ x : E3, Real.sqrt (nablaKRm04NormSqIntrinsic S.val.toSolutionOn k t x) ≤ C := by
  obtain ⟨hT, K, _, hRm⟩ := uniformStandardLifetime_slab θ (hδ.le.trans hδθ) hlt
  let B : ℕ → ℝ := fun k => Real.sqrt (rmOpenBound 3 (K ^ 2) 0 δ θ N k)
  refine ⟨∑ k ∈ Finset.range (N + 1), B k,
    Finset.sum_nonneg (fun k _ => Real.sqrt_nonneg _), ?_⟩
  intro S k hk t ht x
  have hb := S.val.curvature_derivative_bound_positive hδ hδθ (hT S) (hRm S) N k hk t ht x
  apply hb.trans
  exact Finset.single_le_sum (fun j _ => Real.sqrt_nonneg _)
    (show k ∈ Finset.range (N + 1) from Finset.mem_range.mpr (by omega))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_curvature_derivative_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_curvature_derivative_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_curvature_derivative_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_curvature_derivative_bounds
end DifferentialGeometry.PDE.RicciFlow
