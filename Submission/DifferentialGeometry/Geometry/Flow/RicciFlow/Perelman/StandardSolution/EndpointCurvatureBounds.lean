import Submission.DifferentialGeometry.Analysis.Calculus.TimeJet.EndpointTower
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointRiemannNorm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.SolutionHeatEquation
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [BoundarylessManifold I M]

def compactCurvatureEndpointBound (n N : ℕ) (T K : ℝ) (A : ℕ → ℝ) : ℝ :=
  Real.sqrt (DifferentialGeometry.Analysis.endpointTowerBound
    (∑ k ∈ Finset.range (N + 1), rmTowerCost n k) K T A N)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.compactCurvatureEndpointBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.compactCurvatureEndpointBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.compactCurvatureEndpointBound ``Submission.DifferentialGeometry.PDE.RicciFlow.compactCurvatureEndpointBound

theorem compactCurvatureEndpointBound_nonneg (n N : ℕ) (T K : ℝ) (A : ℕ → ℝ) :
    0 ≤ compactCurvatureEndpointBound n N T K A := Real.sqrt_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.compactCurvatureEndpointBound_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.compactCurvatureEndpointBound_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.compactCurvatureEndpointBound_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.compactCurvatureEndpointBound_nonneg

theorem compactCurvatureEndpointBound_congr_initial (n N : ℕ) (T K : ℝ) (A B : ℕ → ℝ)
    (hAB : ∀ k ≤ N, A k = B k) :
    compactCurvatureEndpointBound n N T K A = compactCurvatureEndpointBound n N T K B := by
  have hh (c : ℝ) : ∀ m : ℕ, m ≤ N →
      DifferentialGeometry.Analysis.endpointTowerBound c K T A m =
        DifferentialGeometry.Analysis.endpointTowerBound c K T B m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      simp only [DifferentialGeometry.Analysis.endpointTowerBound, ih (by omega), hAB (m + 1) hm]
  unfold compactCurvatureEndpointBound
  rw [hh _ N le_rfl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.compactCurvatureEndpointBound_congr_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.compactCurvatureEndpointBound_congr_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.compactCurvatureEndpointBound_congr_initial ``Submission.DifferentialGeometry.PDE.RicciFlow.compactCurvatureEndpointBound_congr_initial

theorem curvature_endpoint_bound_compact (T : ℝ) (hT : 0 < T)
    (N : ℕ) (K : ℝ) (hK : 0 ≤ K) (A : ℕ → ℝ)
    (D : RealTimeInterval) (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (hslab : _root_.Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t ∈ _root_.Set.Icc 0 T, 0 < t → t ∈ D.regular)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
        (_root_.Set.Icc 0 T ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcurv : ∀ t ∈ _root_.Set.Icc 0 T, ∀ x : M,
      Real.sqrt (normSq0S (S.base.metric t) x 4 (metricRm04 (S.base.metric t) x)) ≤ K)
    (hinit : ∀ k ≤ N, ∀ x : M, Real.sqrt (nablaKRm04NormSqIntrinsic S k 0 x) ≤ A k) :
    ∀ k ≤ N, ∀ t ∈ _root_.Set.Icc 0 T, ∀ x : M,
      Real.sqrt (nablaKRm04NormSqIntrinsic S k t x) ≤
        compactCurvatureEndpointBound (Module.finrank ℝ E) N T K A := by
  let c := ∑ k ∈ Finset.range (N + 1), rmTowerCost (Module.finrank ℝ E) k
  have hc : 0 ≤ c := Finset.sum_nonneg (fun k _ => rmTowerCost_nonneg _ k)
  have hcost (k : ℕ) (hk : k ≤ N) : rmTowerCost (Module.finrank ℝ E) k ≤ c :=
    Finset.single_le_sum (fun j _ => rmTowerCost_nonneg _ j) (Finset.mem_range.mpr (by omega))
  have hcont (k : ℕ) (_ : k ≤ N) :
      ContinuousOn (fun p : ℝ × M => nablaKRm04NormSqIntrinsic S k p.1 p.2) (_root_.Set.Icc 0 T ×ˢ _root_.Set.univ) := by
    have hh := (covariantRiemannNormSq_contMDiffOn S.base.metric (_root_.Set.Icc 0 T)
      (uniqueDiffOn_Icc hT) hgram k).continuousOn
    apply hh.congr
    intro p _
    dsimp only
    unfold nablaKRm04NormSqIntrinsic
    rw [nablaKRm_eq_iterCov]
    rfl
  have htime (k : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 T) (hp : 0 < t) (x : M) :
      DifferentiableWithinAt ℝ (fun s => nablaKRm04NormSqIntrinsic S k s x) (_root_.Set.Icc 0 T) t := by
    obtain ⟨d, hd, _⟩ := towerHeatBoundOn_of_solution S hS k ⟨t, hregular t ht hp⟩ x
    exact (hd.mono hslab).differentiableWithinAt
  have hheat (k : ℕ) (hk : k ≤ N) (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 T)
      (hp : 0 < t) (x : M) :
      parabolicOperatorWithDrift (flowG S) T (fun _ _ => 0) (nablaKRm04NormSqIntrinsic S k) t x ≤
        -2 * nablaKRm04NormSqIntrinsic S (k + 1) t x +
          towerReactionSum (nablaKRm04NormSqIntrinsic S) c k t x := by
    obtain ⟨d, hd, hle⟩ := (towerHeatBoundOn_of_solution S hS k).mono_cost (hcost k hk)
      ⟨t, hregular t ht hp⟩ x
    have hderiv := (hd.mono hslab).derivWithin ((uniqueDiffOn_Icc hT) t ht)
    rw [parabolicOperatorWithDrift_eq, hderiv, heatOperatorWithDrift_zero_drift]
    change d - nablaKNormLap S k t x ≤ _
    exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using hle)
  have hb := DifferentialGeometry.Analysis.endpoint_tower_bound_compact (flowG S) T hT
    (nablaKRm04NormSqIntrinsic S) N c K A hc hK
    (fun k _ t _ x => nablaKRm04NormSqIntrinsic_nonneg S k t x) ?_ hcont
    (fun k _ t ht hp x => htime k t ht hp x)
    (fun k _ t _ _ => nablaKNorm_smooth S t k)
    (fun k hk x => (Real.sqrt_le_iff.mp (hinit k hk x)).2) hheat
  · intro k hk t ht x
    exact Real.sqrt_le_sqrt (hb k hk t ht x)
  · intro t ht x
    have hb := (Real.sqrt_le_iff.mp (hcurv t ht x)).2
    exact hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvature_endpoint_bound_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvature_endpoint_bound_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvature_endpoint_bound_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.curvature_endpoint_bound_compact
end DifferentialGeometry.PDE.RicciFlow
