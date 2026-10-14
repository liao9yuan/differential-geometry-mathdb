import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.TerminalSpatialBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ExpressionBounds
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
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators
namespace DifferentialGeometry.PDE.RicciFlow

private def spatialBound (n N : ℕ) (T K : ℝ) (A : ℕ → ℝ) : ℝ :=
  completeCurvatureEndpointBound n N T (_root_.Max.max 0 K) A +
    compactCurvatureEndpointBound n N T (_root_.Max.max 0 K) A

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.spatialBound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.spatialBound target :: scope.openDecls } }

private theorem spatialBound_nonneg (n N : ℕ) (T K : ℝ) (A : ℕ → ℝ) :
    0 ≤ spatialBound n N T K A :=
  add_nonneg (completeCurvatureEndpointBound_nonneg _ _ _ _ _)
    (compactCurvatureEndpointBound_nonneg _ _ _ _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.spatialBound_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.spatialBound_nonneg target :: scope.openDecls } }

def endpointMixedCurvatureBound (n N : ℕ) (T K : ℝ) (A : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
    ((CurvatureExpression.curvature a).timeIter b).normBound n (spatialBound n N T K A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.endpointMixedCurvatureBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.endpointMixedCurvatureBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.endpointMixedCurvatureBound ``Submission.DifferentialGeometry.PDE.RicciFlow.endpointMixedCurvatureBound

theorem endpointMixedCurvatureBound_nonneg (n N : ℕ) (T K : ℝ) (A : ℕ → ℝ) :
    0 ≤ endpointMixedCurvatureBound n N T K A :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
    CurvatureExpression.normBound_nonneg n _ (spatialBound_nonneg n N T K A)
      ((CurvatureExpression.curvature a).timeIter b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.endpointMixedCurvatureBound_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.endpointMixedCurvatureBound_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.endpointMixedCurvatureBound_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.endpointMixedCurvatureBound_nonneg

theorem endpointMixedCurvatureBound_congr_initial (n N : ℕ) (T K : ℝ) (A B : ℕ → ℝ)
    (hAB : ∀ j ≤ 3 * N, A j = B j) :
    endpointMixedCurvatureBound n N T K A = endpointMixedCurvatureBound n N T K B := by
  have hab (j : ℕ) (hj : j ≤ N) : A j = B j := hAB j (by omega)
  unfold endpointMixedCurvatureBound spatialBound
  rw [completeCurvatureEndpointBound_congr_initial n N T (_root_.Max.max 0 K) A B hab,
    compactCurvatureEndpointBound_congr_initial n N T (_root_.Max.max 0 K) A B hab]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.endpointMixedCurvatureBound_congr_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.endpointMixedCurvatureBound_congr_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.endpointMixedCurvatureBound_congr_initial ``Submission.DifferentialGeometry.PDE.RicciFlow.endpointMixedCurvatureBound_congr_initial

private theorem program_bound_le (n N : ℕ) (T K : ℝ) (A : ℕ → ℝ)
    (a b : ℕ) (hab : a + 2 * b ≤ N) :
    ((CurvatureExpression.curvature a).timeIter b).normBound n (spatialBound n N T K A) ≤
      endpointMixedCurvatureBound n N T K A := by
  let F := fun i j => ((CurvatureExpression.curvature i).timeIter j).normBound n
    (spatialBound n N T K A)
  have hF (i j : ℕ) : 0 ≤ F i j :=
    CurvatureExpression.normBound_nonneg n _ (spatialBound_nonneg n N T K A) _
  have hi : F a b ≤ ∑ j ∈ Finset.range (N + 1), F a j :=
    Finset.single_le_sum (fun j _ => hF a j) (Finset.mem_range.mpr (by omega))
  exact hi.trans (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hF i j))
    (Finset.mem_range.mpr (by omega)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.program_bound_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.program_bound_le target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [T2Space M] in
private theorem tensor_zero_dim {s : ℕ} (hs : 0 < s) {x : M}
    (h0 : Module.finrank ℝ E = 0) (T : Tensor0SSpace s I x) : T = 0 := by
  let : Subsingleton E := (Module.finrank_zero_iff (R := ℝ) (M := E)).mp h0
  apply Tensor0SSpace.toModel_injective
  change Tensor0SSpace.toModel T = Tensor0SSpace.toModel (0 : Tensor0SSpace s I x)
  rw [Tensor0SSpace.toModel_zero]
  ext v
  exact (Tensor0SSpace.toModel T).map_coord_zero (⟨0, hs⟩ : Fin s) (Subsingleton.elim _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.tensor_zero_dim
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.tensor_zero_dim target :: scope.openDecls } }

variable [CompleteSpace E] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M]

theorem curvature_endpoint_mixed_bound (T : ℝ) (hT : 0 ≤ T) (N : ℕ) (K : ℝ) (A : ℕ → ℝ)
    (D : RealTimeInterval) (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hJ : UniqueDiffOn ℝ D.carrier)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
        (D.carrier ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdense : D.carrier ⊆ closure D.regular)
    (hkind : RiemannianMetricComplete (I := I) (S.base.metric 0) ∨ CompactSpace M)
    (hslab : _root_.Set.Icc 0 T ⊆ D.carrier) (hregular : _root_.Set.Ioo 0 T ⊆ D.regular)
    (hcurv : ∀ t ∈ _root_.Set.Icc 0 T, ∀ x : M,
      Real.sqrt (normSq0S (S.base.metric t) x 4 (metricRm04 (S.base.metric t) x)) ≤ K)
    (hinit : ∀ j ≤ 3 * N, ∀ x : M, Real.sqrt (nablaKRm04NormSqIntrinsic S j 0 x) ≤ A j) :
    ∀ a b : ℕ, a + 2 * b ≤ N → ∀ t ∈ _root_.Set.Icc 0 T, ∀ x : M,
      Real.sqrt (normSq0S (S.base.metric t) x (4 + a)
        (iteratedCovariantTimeDerivWithin S.base.metric
          (fun r => nablaKRm04Field S r a x) D.carrier b t)) ≤
        endpointMixedCurvatureBound (Module.finrank ℝ E) N T K A := by
  by_cases h0 : Module.finrank ℝ E = 0
  · intro a b _ t _ x
    have hu := tensor_zero_dim (by omega : 0 < 4 + a) h0
      (iteratedCovariantTimeDerivWithin S.base.metric
        (fun r => nablaKRm04Field S r a x) D.carrier b t)
    rw [hu]
    have hz : normSq0S (S.base.metric t) x (4 + a) (0 : Tensor0SSpace (4 + a) I x) = 0 := by
      simpa only [zero_smul, zero_pow (by decide : 2 ≠ 0), _root_.MulZeroClass.zero_mul] using
        normSq0S_smul (S.base.metric t) (0 : ℝ) (0 : Tensor0SSpace (4 + a) I x)
    rw [hz, Real.sqrt_zero]
    exact endpointMixedCurvatureBound_nonneg _ _ _ _ _
  · let : NeZero (Module.finrank ℝ E) := ⟨h0⟩
    have hK : 0 ≤ _root_.Max.max 0 K := le_max_left _ _
    have hcurv' (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 T) (x : M) :=
      (hcurv t ht x).trans (le_max_right 0 K)
    have hi (j : ℕ) (hj : j ≤ N) (x : M) := hinit j (by omega) x
    have hg (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :=
      (hgram x₀ i j).mono (_root_.Set.prod_mono hslab subset_rfl)
    have hb : ∀ j ≤ N, ∀ t ∈ _root_.Set.Icc 0 T, ∀ x : M,
        Real.sqrt (nablaKRm04NormSqIntrinsic S j t x) ≤
          spatialBound (Module.finrank ℝ E) N T K A := by
      rcases hkind with hc | hc
      · have hh := curvature_endpoint_bound_complete_terminal T hT N (_root_.Max.max 0 K) hK A D S hS hc
          hslab hregular hg hcurv' hi
        intro j hj t ht x
        exact (hh j hj t ht x).trans
          (le_add_of_nonneg_right (compactCurvatureEndpointBound_nonneg _ _ _ _ _))
      · let : CompactSpace M := hc
        have hh := curvature_endpoint_bound_compact_terminal T hT N (_root_.Max.max 0 K) hK A D S hS
          hslab hregular hg hcurv' hi
        intro j hj t ht x
        apply (hh j hj t ht x).trans
        unfold spatialBound completeCurvatureEndpointBound
        linarith [Real.sqrt_nonneg (DifferentialGeometry.Analysis.completeEndpointTowerBound
          (∑ k ∈ Finset.range (N + 1), rmTowerCost (Module.finrank ℝ E) k) (_root_.Max.max 0 K) T A N)]
    intro a b hab t ht x
    have ho := CurvatureExpression.maxOrder_timeIter_le (.curvature a) b
    have he := CurvatureExpression.eval_timeIter_on S hS hJ hgram hdense (.curvature a) b x t
      (hslab ht)
    have hn := CurvatureExpression.eval_norm_le S t x _ (spatialBound_nonneg _ _ _ _ _)
      ((CurvatureExpression.curvature a).timeIter b)
      (fun j hj => hb j (hj.trans (ho.trans hab)) t ht x)
    exact ((congrArg (fun U : Tensor0SSpace (4 + a) I x =>
      Real.sqrt (normSq0S (S.base.metric t) x (4 + a) U)) he).trans_le hn).trans
        (program_bound_le _ N T K A a b hab)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvature_endpoint_mixed_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvature_endpoint_mixed_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvature_endpoint_mixed_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.curvature_endpoint_mixed_bound
end DifferentialGeometry.PDE.RicciFlow
