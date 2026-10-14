import Submission.DifferentialGeometry.Geometry.Metric.Distance.Topology
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball
import Submission.DifferentialGeometry.Geometry.Metric.SmoothMapLipschitz
import Submission.DifferentialGeometry.Topology.MetricSpace.Lipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RegularSpace M] [PreconnectedSpace M]

private theorem locallyLipschitz_of_riemannian_ball_bounds
    (g : SmoothRiemannianMetric I M) (p : M)
    {a b : ℝ} (ell : M × _root_.Set.Icc a b → ℝ)
    (hell : ∀ R : ℝ, 0 ≤ R → ∃ K : ℝ≥0,
      ∀ x ∈ riemannianClosedBallOf g p R,
      ∀ y ∈ riemannianClosedBallOf g p R,
      ∀ s t : _root_.Set.Icc a b, |ell (x, s) - ell (y, t)| ≤
        (K : ℝ) * ((riemannianEDistOf g x y).toReal + |(s : ℝ) - t|)) :
    let : PseudoMetricSpace M := g.toPseudoMetricSpace
    LocallyLipschitz ell := by
  let : PseudoMetricSpace M := g.toPseudoMetricSpace
  change LocallyLipschitz ell
  by_cases hab : a ≤ b
  · apply locallyLipschitz_of_lipschitzOn_closedBall (p, ⟨a, le_rfl, hab⟩)
    intro R hR
    obtain ⟨K, hK⟩ := hell R hR
    refine ⟨2 * K, LipschitzOnWith.of_dist_le_mul ?_⟩
    intro x hx y hy
    have hxB : x.1 ∈ riemannianClosedBallOf g p R := by
      change _root_.EDist.edist p x.1 ≤ ENNReal.ofReal R
      rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hR, dist_comm]
      exact (le_max_left _ _).trans (Metric.mem_closedBall.mp hx)
    have hyB : y.1 ∈ riemannianClosedBallOf g p R := by
      change _root_.EDist.edist p y.1 ≤ ENNReal.ofReal R
      rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hR, dist_comm]
      exact (le_max_left _ _).trans (Metric.mem_closedBall.mp hy)
    have h := hK x.1 hxB y.1 hyB x.2 y.2
    change |ell x - ell y| ≤ (K : ℝ) * (_root_.Dist.dist x.1 y.1 + _root_.Dist.dist x.2 y.2) at h
    change |ell x - ell y| ≤ ((2 * K : ℝ≥0) : ℝ) * _root_.Dist.dist x y
    rw [NNReal.coe_mul, NNReal.coe_ofNat, Prod.dist_eq]
    have hd : _root_.Dist.dist x.1 y.1 + _root_.Dist.dist x.2 y.2 ≤ 2 * _root_.Max.max (_root_.Dist.dist x.1 y.1) (_root_.Dist.dist x.2 y.2) := by
      linarith only [le_max_left (_root_.Dist.dist x.1 y.1) (_root_.Dist.dist x.2 y.2),
        le_max_right (_root_.Dist.dist x.1 y.1) (_root_.Dist.dist x.2 y.2)]
    nlinarith only [h, mul_le_mul_of_nonneg_left hd K.coe_nonneg]
  · rintro ⟨x, t⟩
    exact (hab (t.2.1.trans t.2.2)).elim

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.locallyLipschitz_of_riemannian_ball_bounds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.locallyLipschitz_of_riemannian_ball_bounds target :: scope.openDecls } }

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem locallyLipschitzOn_comp_extChartAt_symm_of_spacetime_bounds
    (g : SmoothRiemannianMetric I M) (p : M)
    {a b : ℝ} (hab : a ≤ b) (ell : M × _root_.Set.Icc a b → ℝ)
    (hell : ∀ R : ℝ, 0 ≤ R → ∃ K : ℝ≥0,
      ∀ x ∈ riemannianClosedBallOf g p R,
      ∀ y ∈ riemannianClosedBallOf g p R,
      ∀ s t : _root_.Set.Icc a b, |ell (x, s) - ell (y, t)| ≤
        (K : ℝ) * ((riemannianEDistOf g x y).toReal + |(s : ℝ) - t|)) (α : M) :
    LocallyLipschitzOn (_root_.Set.univ ×ˢ (extChartAt I α).target)
      (fun p : ℝ × E => ell ((extChartAt I α).symm p.2, _root_.Set.projIcc a b hab p.1)) := by
  let : PseudoMetricSpace M := g.toPseudoMetricSpace
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩
  have he := locallyLipschitz_of_riemannian_ball_bounds g p ell hell
  have hs : LocallyLipschitzOn (_root_.Set.univ ×ˢ (extChartAt I α).target)
      (fun p : ℝ × E => (extChartAt I α).symm p.2) :=
    (locallyLipschitzOn_extChartAt_symm α).comp
      LipschitzWith.prod_snd.locallyLipschitz.locallyLipschitzOn (fun _ hp => hp.2)
  have ht : LocallyLipschitzOn (_root_.Set.univ ×ˢ (extChartAt I α).target)
      (fun p : ℝ × E => _root_.Set.projIcc a b hab p.1) :=
    ((LipschitzWith.projIcc hab).comp LipschitzWith.prod_fst).locallyLipschitz.locallyLipschitzOn
  exact he.locallyLipschitzOn.comp (hs.prodMk ht) (_root_.Set.mapsTo_univ _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_comp_extChartAt_symm_of_spacetime_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_comp_extChartAt_symm_of_spacetime_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_comp_extChartAt_symm_of_spacetime_bounds ``Submission.DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_comp_extChartAt_symm_of_spacetime_bounds

end DifferentialGeometry.Geometry.Riemannian
