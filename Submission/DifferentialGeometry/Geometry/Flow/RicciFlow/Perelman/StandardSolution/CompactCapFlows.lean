import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CompactDoubleCurvature
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactUniformExistence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointMixedBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

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
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E4 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.S3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE4HAddOfNat : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE4HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE4HAddOfNat target :: scope.openDecls } }

theorem exists_uniform_compact_cap_flows :
    ∃ τ : ℝ, ∃ hτ : 0 < τ, ∃ B : ℕ → ℝ, (∀ N, 0 ≤ B N) ∧
      ∀ (north : S3) (R : ℝ) (hR : _root_.Max.max transitionEnd 2 + 2 ≤ R),
      ∃ S : SolutionOn (I := 𝓡 3) (M := S3) (RealTimeInterval.closed 0 τ hτ.le),
        IsSolutionOn S ∧ S.base.metric 0 = compactDoubleMetric north R hR ∧
        (∀ t ∈ _root_.Set.Icc 0 τ, RiemannianMetricComplete (S.base.metric t)) ∧
        (∀ (x₀ : S3) (i j : Fin (Module.finrank ℝ E3)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
            (fun p : ℝ × S3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
            (_root_.Set.Icc 0 τ ×ˢ (_root_.FiberBundle.trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
        (∀ t ∈ _root_.Set.Icc 0 τ, ∀ (x : S3) (v w : TangentSpace (𝓡 3) x),
          HasDerivWithinAt (fun r => (S.base.metric r).inner x v w)
            (-2 * ricciTensor (S.base.metric t) x v w) (_root_.Set.Ici 0) t) ∧
        ∀ N a b : ℕ, a + 2 * b ≤ N → ∀ t ∈ _root_.Set.Icc 0 τ, ∀ x : S3,
          Real.sqrt (normSq0S (S.base.metric t) x (4 + a)
            (iteratedCovariantTimeDerivWithin S.base.metric
              (fun r => nablaKRm04Field S r a x) (_root_.Set.Icc 0 τ) b t)) ≤ B N := by
  obtain ⟨A, _, hA⟩ := exists_pos_bounds_iterCov_compactDoubleMetric
  let τ := compactCurvatureControlTime 3 (A 0)
  have hτ : 0 < τ := compactCurvatureControlTime_pos _ _
  let K := Real.sqrt (2 * A 0 ^ 2 + 1)
  let B := fun N => endpointMixedCurvatureBound 3 N τ K A
  refine ⟨τ, hτ, B, (fun N => endpointMixedCurvatureBound_nonneg _ N _ _ _), ?_⟩
  intro north R hR
  let g₀ := compactDoubleMetric north R hR
  have hi (x : S3) : Real.sqrt (normSq0S g₀ x 4 (metricRm04 g₀ x)) ≤ A 0 := hA north R hR 0 x
  obtain ⟨T, hT, ⟨P⟩⟩ := exists_compact_flow_beyond_control_time g₀ (by simp) (A 0) hi
  have hτT : τ < T := by simpa only [finrank_euclideanSpace, Fintype.card_fin] using hT
  let D := RealTimeInterval.closed 0 τ hτ.le
  let S := P.S.timeRestrict D
  have hsub : _root_.Set.Icc 0 τ ⊆ _root_.Set.Ico 0 T := fun t ht => ⟨ht.1, ht.2.trans_lt hτT⟩
  have hS : IsSolutionOn S := isSolutionOn_timeRestrict P.isSolution hsub
    (fun t ht => ⟨ht.1, ht.2.trans hτT⟩)
  have hstart : S.base.metric 0 = g₀ := P.start
  have hg (x₀ : S3) (i j : Fin (Module.finrank ℝ E3)) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × S3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
        (_root_.Set.Icc 0 τ ×ˢ (_root_.FiberBundle.trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet) :=
    (P.joint x₀ i j).mono (_root_.Set.prod_mono hsub subset_rfl)
  have hcurv : ∀ t ∈ _root_.Set.Icc 0 τ, ∀ x : S3,
      Real.sqrt (normSq0S (S.base.metric t) x 4 (metricRm04 (S.base.metric t) x)) ≤ K := by
    have hinitial (x : S3) : Real.sqrt (normSq0S (P.S.base.metric 0) x 4
        (metricRm04 (P.S.base.metric 0) x)) ≤ A 0 := by
      have he : P.S.base.metric 0 = g₀ := P.start
      rw [he]
      exact hi x
    exact curvature_bound_from_initial_compact τ hτ.le (A 0) (by simp only [τ, finrank_euclideanSpace,
      Fintype.card_fin, le_refl]) _ P.S P.isSolution hsub
      (fun t ht => ⟨ht.1, ht.2.trans hτT⟩)
      (fun x₀ i j => (P.joint x₀ i j).mono (_root_.Set.prod_mono hsub subset_rfl)) hinitial
  refine ⟨S, hS, hstart, (fun _ _ => ⟨by infer_instance⟩), hg, ?_, ?_⟩
  · intro t ht x v w
    exact P.pde t (hsub ht) x v w
  · intro N a b hab t ht x
    have hinit (j : ℕ) (_hj : j ≤ 3 * N) (y : S3) :
        Real.sqrt (nablaKRm04NormSqIntrinsic S j 0 y) ≤ A j := by
      unfold nablaKRm04NormSqIntrinsic
      rw [nablaKRm_eq_iterCov]
      change Real.sqrt (normSq0S (S.base.metric 0) y (4 + j)
        (iterCov (S.base.metric 0) 4 (metricRm04 (S.base.metric 0)) j y)) ≤ A j
      rw [hstart]
      exact hA north R hR j y
    have hdense : D.carrier ⊆ closure D.regular := by
      change _root_.Set.Icc 0 τ ⊆ closure (_root_.Set.Ioo 0 τ)
      rw [closure_Ioo hτ.ne]
    have hh := curvature_endpoint_mixed_bound τ hτ.le N K A D S hS (uniqueDiffOn_Icc hτ)
      hg hdense (Or.inr (inferInstance : CompactSpace S3)) subset_rfl subset_rfl hcurv hinit
      a b hab t ht x
    simp only [finrank_euclideanSpace, Fintype.card_fin] at hh
    convert hh using 1
    all_goals rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_uniform_compact_cap_flows then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_uniform_compact_cap_flows"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_uniform_compact_cap_flows ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_uniform_compact_cap_flows
end DifferentialGeometry.PDE.RicciFlow
