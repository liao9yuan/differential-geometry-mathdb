import Submission.DifferentialGeometry.Geometry.Exponential.Inverse.Radius
import Submission.DifferentialGeometry.Geometry.Comparison.Distance.Calabi
import Mathlib.Topology.Sequences

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem riemannian_toReal_eq_dist (p q : M) :
    (_root_.Manifold.riemannianEDist I p q).toReal = _root_.Dist.dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.riemannian_toReal_eq_dist
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.riemannian_toReal_eq_dist target :: scope.openDecls } }

theorem tendsto_minimizing_vectors_of_unique
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p q : M) (u : TangentSpace I p) (v : M → TangentSpace I p)
    (hexp : ∀ y, expMapIntrinsic (I := I) g hEnorm p (v y) = y)
    (hlen : ∀ y, Real.sqrt (g.inner p (v y) (v y)) = _root_.Dist.dist p y)
    (huniq : ∀ w : TangentSpace I p,
      expMapIntrinsic (I := I) g hEnorm p w = q →
      Real.sqrt (g.inner p w w) = _root_.Dist.dist p q → w = u) :
    Tendsto v (𝓝 q) (𝓝 u) := by
  rw [Filter.tendsto_iff_seq_tendsto]
  intro seq hseq
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hz : _root_.Filter.Tendsto (fun n => seq (ns n)) _root_.Filter.atTop (𝓝 q) := hseq.comp hns
  have hdseq : _root_.Filter.Tendsto (fun n => _root_.Dist.dist p (seq (ns n))) _root_.Filter.atTop (𝓝 (_root_.Dist.dist p q)) :=
    tendsto_const_nhds.dist hz
  have hdbdd := Metric.isBounded_range_of_tendsto _ hdseq
  rw [isBounded_iff_forall_norm_le] at hdbdd
  obtain ⟨C, hC⟩ := hdbdd
  let K : Set (TangentSpace I p) := {w | Real.sqrt (g.inner p w w) ≤ _root_.Max.max 0 C}
  have hK : IsCompact K := gLenBall_isCompact (I := I) g p (_root_.Max.max 0 C)
  have hvK (n : ℕ) : v (seq (ns n)) ∈ K := by
    change Real.sqrt (g.inner p (v (seq (ns n))) (v (seq (ns n)))) ≤ _root_.Max.max 0 C
    rw [hlen]
    have hbound := hC _ ⟨n, rfl⟩
    rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] at hbound
    exact hbound.trans (le_max_right _ _)
  obtain ⟨w, _, phi, hphi, hw⟩ := hK.tendsto_subseq hvK
  have hzphi : _root_.Filter.Tendsto (fun n => seq (ns (phi n))) _root_.Filter.atTop (𝓝 q) :=
    hz.comp hphi.tendsto_atTop
  have hmap : _root_.Filter.Tendsto (fun n => expMapIntrinsic (I := I) g hEnorm p
      (v (seq (ns (phi n))))) _root_.Filter.atTop (𝓝 (expMapIntrinsic (I := I) g hEnorm p w)) := by
    simpa only [Function.comp_def] using
      ((expMapIntrinsic_continuous (I := I) g hEnorm p).tendsto w).comp hw
  have hmapq : _root_.Filter.Tendsto (fun n => expMapIntrinsic (I := I) g hEnorm p
      (v (seq (ns (phi n))))) _root_.Filter.atTop (𝓝 q) := by
    simpa only [hexp] using hzphi
  have hwend : expMapIntrinsic (I := I) g hEnorm p w = q :=
    tendsto_nhds_unique hmap hmapq
  have hnorm : _root_.Filter.Tendsto (fun n => Real.sqrt
      (g.inner p (v (seq (ns (phi n)))) (v (seq (ns (phi n))))))
      atTop (𝓝 (Real.sqrt (g.inner p w w))) := by
    simpa only [Function.comp_def] using
      ((continuous_sqrt_gInner_self (I := I) g p).tendsto w).comp hw
  have hnormq : _root_.Filter.Tendsto (fun n => Real.sqrt
      (g.inner p (v (seq (ns (phi n)))) (v (seq (ns (phi n))))))
      atTop (𝓝 (_root_.Dist.dist p q)) := by
    simpa only [hlen] using
      (tendsto_const_nhds : _root_.Filter.Tendsto (fun _ : ℕ => p) _root_.Filter.atTop (𝓝 p)).dist hzphi
  have hwlen : Real.sqrt (g.inner p w w) = _root_.Dist.dist p q :=
    tendsto_nhds_unique hnorm hnormq
  refine ⟨phi, ?_⟩
  rw [huniq w hwend hwlen] at hw
  exact hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.tendsto_minimizing_vectors_of_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.tendsto_minimizing_vectors_of_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.tendsto_minimizing_vectors_of_unique ``Submission.DifferentialGeometry.Geometry.Topology.tendsto_minimizing_vectors_of_unique

theorem contMDiffAt_dist_of_unique_minimizing_exp
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p q : M) (u : TangentSpace I p)
    (hexp : expMapIntrinsic (I := I) g hEnorm p u = q)
    (hupos : 0 < g.inner p u u)
    (hnot : ¬ IsConjVec (I := I) g hEnorm p
      (tangentSpaceModelContinuousLinearEquiv (I := I) p u))
    (huniq : ∀ w : TangentSpace I p,
      expMapIntrinsic (I := I) g hEnorm p w = q →
      Real.sqrt (g.inner p w w) = _root_.Dist.dist p q → w = u) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y : M => _root_.Dist.dist p y) q := by
  classical
  have hmin (y : M) : ∃ w : TangentSpace I p,
      expMapIntrinsic (I := I) g hEnorm p w = y ∧
        Real.sqrt (g.inner p w w) = _root_.Dist.dist p y := by
    have hfin : _root_.Manifold.riemannianEDist I p y ≠ ⊤ := by
      rw [← IsRiemannianManifold.out (I := I)]
      exact edist_ne_top p y
    simpa only [riemannian_toReal_eq_dist (I := I)] using
      minExp_of_ne_top (I := I) g hEnorm p y hfin
  choose v hv hlen using hmin
  have hvlim := tendsto_minimizing_vectors_of_unique (I := I) g hEnorm p q u v hv hlen huniq
  obtain ⟨B, huB⟩ := branch_of_not_conj (I := I) g hEnorm hnot
  have hmem : ∀ᶠ y in 𝓝 q,
      tangentSpaceModelContinuousLinearEquiv (I := I) p (v y) ∈ B.hom.source :=
    ((tangentSpaceModelContinuousLinearEquiv (I := I) p).continuous.tendsto u).comp hvlim
      (B.hom.open_source.mem_nhds huB)
  have hagree : branchRadius (I := I) g B =ᶠ[𝓝 q] fun y => _root_.Dist.dist p y := by
    filter_upwards [hmem] with y hy
    calc
      _ = branchRadius (I := I) g B (expMapIntrinsic (I := I) g hEnorm p (v y)) := by rw [hv]
      _ = Real.sqrt (g.inner p (v y) (v y)) := branchRadius_exp (I := I) B hy
      _ = _root_.Dist.dist p y := hlen y
  have hsmooth := branchRadius_infAt (I := I) B huB hupos
  rw [hexp] at hsmooth
  exact hsmooth.congr_of_eventuallyEq hagree.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.contMDiffAt_dist_of_unique_minimizing_exp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.contMDiffAt_dist_of_unique_minimizing_exp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.contMDiffAt_dist_of_unique_minimizing_exp ``Submission.DifferentialGeometry.Geometry.Topology.contMDiffAt_dist_of_unique_minimizing_exp

end DifferentialGeometry.Geometry.Topology

end
