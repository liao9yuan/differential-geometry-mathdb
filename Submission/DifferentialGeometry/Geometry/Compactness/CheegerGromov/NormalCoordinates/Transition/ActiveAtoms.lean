import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.IntrinsicOverlap
import Submission.DifferentialGeometry.Geometry.Exponential.NormalBall.Recenter
import Submission.DifferentialGeometry.Analysis.Calculus.MapConvergence.Configuration

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.ENNReal
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [∀ k, PseudoEMetricSpace (M k)]
  [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

theorem IntrinsicBallChart.eventually_mapsTo_target_of_near
    {ι : Type*} [Finite ι]
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : ι → ∀ k, M k) {ρ s : ℝ} (hρ : 0 < ρ) (hs : s ≤ 3 * ρ / 4)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : ι → ι → Bool) (j : ι)
    (hnear : ∀ i, ∀ᶠ k in _root_.Filter.atTop,
      near j i = _root_.Bool.true → _root_.EDist.edist (x j k) (x i k) < ENNReal.ofReal (ρ / 4)) :
    ∀ᶠ k in _root_.Filter.atTop, ∀ i, near j i = _root_.Bool.true →
      MapsTo (c i k).hom (Metric.ball (0 : E) s) (c j k).hom.target := by
  filter_upwards [(Filter.eventually_all).2 hnear] with k hk i hi
  have hdist : _root_.EDist.edist (x i k) (x j k) + ENNReal.ofReal s ≤ ENNReal.ofReal ρ := by
    by_cases hs0 : 0 ≤ s
    · rw [_root_.PseudoEMetricSpace.edist_comm]
      calc
        _root_.EDist.edist (x j k) (x i k) + ENNReal.ofReal s ≤
            ENNReal.ofReal (ρ / 4) + ENNReal.ofReal s := add_le_add (hk i hi).le le_rfl
        _ = ENNReal.ofReal (ρ / 4 + s) :=
          (ENNReal.ofReal_add (by positivity) hs0).symm
        _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal (by linarith)
    · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hs0), add_zero, _root_.PseudoEMetricSpace.edist_comm]
      exact (hk i hi).le.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hov := (c i k).overlap_on_ball_of_edist_add_le
    (g k) (hEnorm k) (x i k) (x j k) (c j k) hρ hρ (by linarith) hdist
  intro z hz
  obtain ⟨w, hw, heq⟩ := (hov z hz).2
  change (c j k).hom w = (c i k).hom z at heq
  change w ∈ Metric.ball (0 : E) ρ at hw
  rw [← heq]
  exact (c j k).hom.map_source (by rw [(c j k).source_eq]; exact hw)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.eventually_mapsTo_target_of_near then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.eventually_mapsTo_target_of_near"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.eventually_mapsTo_target_of_near ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.eventually_mapsTo_target_of_near

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
end

noncomputable section
open _root_.Set _root_.Filter
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness

variable {E P H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]

theorem eventually_recenter_apply_eq_of_configuration_convergence
    {p : ∀ k, M k} (c : ∀ k, NormalBallChart (I := I) (p k))
    (a : E) {r : ℝ} (hr : 0 < r)
    (hball : ∀ k, Metric.ball a r ⊆ Metric.ball (0 : E) (c k).radius)
    {ι : Type*} [Fintype ι] {S K : Set P}
    {configuration : ℕ → P → (ι → ℝ) × (ι → E)}
    {mu : P → ι → ℝ} {center : P → E}
    (hcfg : MapCInfConvergenceOnCompacts S configuration
      (fun q => (mu q, fun _ => center q)))
    (hK : IsCompact K) (hKS : K ⊆ S) (hcenter : ContinuousOn center K)
    (hcenterBall : _root_.Set.MapsTo center K (Metric.ball (0 : E) r))
    (atoms : ∀ k, P → ι → M k)
    (htarget : ∀ᶠ k in _root_.Filter.atTop, ∀ q ∈ K, ∀ i, mu q i ≠ 0 →
      atoms k q i ∈ (c k).hom.target)
    (hcoords : ∀ᶠ k in _root_.Filter.atTop, ∀ q ∈ K, ∀ i, mu q i ≠ 0 →
      (configuration k q).2 i = -a + (c k).inv (atoms k q i)) :
    ∀ᶠ k in _root_.Filter.atTop, ∀ q ∈ K, ∀ i, mu q i ≠ 0 →
      ((c k).recenter a hr (hball k)).hom ((configuration k q).2 i) = atoms k q i ∧
      ((c k).recenter a hr (hball k)).inv (atoms k q i) = (configuration k q).2 i ∧
      atoms k q i ∈ ((c k).recenter a hr (hball k)).restrictBall.target := by
  let L : Set (P × E) := (fun q : P => (q, (0 : E))) '' K
  have hL : IsCompact L := hK.image_of_continuousOn
    (continuous_id.prodMk continuous_const).continuousOn
  have hLK : Prod.fst '' L = K := by
    ext q
    constructor
    · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
      exact hz
    · intro hq
      exact ⟨(q, 0), ⟨q, hq, rfl⟩, rfl⟩
  have hfst : _root_.Set.MapsTo Prod.fst L S := by
    rintro _ ⟨q, hq, rfl⟩
    exact hKS hq
  have hpair := hcfg.eventually_configuration_pairs_mem hL hfst
    (hLK ▸ hcenter) (isOpen_univ.prod Metric.isOpen_ball)
    (show _root_.Set.MapsTo (fun q : P × E => (q.2, center q.1)) L
      (Set.univ ×ˢ Metric.ball (0 : E) r) from by
        rintro _ ⟨q, hq, rfl⟩
        exact ⟨Set.mem_univ _, hcenterBall hq⟩)
  filter_upwards [hpair, htarget, hcoords] with k hk ht hc q hq i hi
  exact (c k).recenter_apply_inv_of_mem_target a hr (hball k) (ht q hq i hi)
    (hk (q, 0) ⟨q, hq, rfl⟩ i).2 (hc q hq i hi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.eventually_recenter_apply_eq_of_configuration_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.eventually_recenter_apply_eq_of_configuration_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.eventually_recenter_apply_eq_of_configuration_convergence ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.eventually_recenter_apply_eq_of_configuration_convergence

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart
end
