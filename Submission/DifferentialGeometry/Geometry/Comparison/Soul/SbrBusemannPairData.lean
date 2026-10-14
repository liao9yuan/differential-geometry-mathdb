import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SbrBusemannData

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.NNReal
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow

namespace DifferentialGeometry.Geometry.Topology

section Metric

variable {X : Type*} [MetricSpace X]

theorem lipschitzWith_busemann_complement
    {c : ℝ≥0 → X} (hc : Isometry c) (k : ℝ) :
    LipschitzWith 1 (fun x => k - busemann c x) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have h := (lipschitzWith_busemann hc).dist_le_mul q p
  change |(k - busemann c p) - (k - busemann c q)| ≤ 1 * _root_.Dist.dist p q
  rw [show (k - busemann c p) - (k - busemann c q) =
      busemann c q - busemann c p by ring]
  simpa only [Real.dist_eq, NNReal.coe_one, dist_comm q p] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.lipschitzWith_busemann_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.lipschitzWith_busemann_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.lipschitzWith_busemann_complement ``Submission.DifferentialGeometry.Geometry.Topology.lipschitzWith_busemann_complement

theorem exists_busemann_complement_global_maximum
    {c : ℝ≥0 → X} (hc : Isometry c) {c₁ c₂ : ℝ} (hlevels : c₁ < c₂)
    (hne : ({x : X | busemann c x = c₁}).Nonempty)
    (hC : IsCompact {x : X | busemann c x ≤ c₂}) :
    ∃ m : ℝ, 0 < m ∧ c₂ - c₁ ≤ m ∧
      ∃ q : X, c₂ - busemann c q = m ∧ ∀ z : X, c₂ - busemann c z ≤ m := by
  obtain ⟨p, hp⟩ := hne
  have hp' : busemann c p = c₁ := hp
  have hpC : p ∈ {x : X | busemann c x ≤ c₂} := hp'.le.trans hlevels.le
  obtain ⟨q, _hqC, hqMax⟩ := hC.exists_isMaxOn ⟨p, hpC⟩
    (lipschitzWith_busemann_complement hc c₂).continuous.continuousOn
  let m := c₂ - busemann c q
  have hTm : c₂ - c₁ ≤ m := by
    have hpMax : c₂ - busemann c p ≤ c₂ - busemann c q := hqMax hpC
    simpa only [hp', m] using hpMax
  have hm : 0 < m := (sub_pos.mpr hlevels).trans_le hTm
  refine ⟨m, hm, hTm, q, rfl, ?_⟩
  intro z
  by_cases hz : busemann c z ≤ c₂
  · exact hqMax hz
  · exact (sub_neg.mpr (lt_of_not_ge hz)).le.trans hm.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_busemann_complement_global_maximum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_busemann_complement_global_maximum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_busemann_complement_global_maximum ``Submission.DifferentialGeometry.Geometry.Topology.exists_busemann_complement_global_maximum

end Metric

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem concaveOn_busemann_complement_intrinsicGeodesic
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {c : ℝ≥0 → M} (hc : Isometry c) (k : ℝ)
    (p : M) (v : TangentSpace I p) :
    ConcaveOn ℝ _root_.Set.univ (fun t => k - busemann c (intrinsicGeodesic g hEnorm p v t)) := by
  have hconv := convexOn_busemann_intrinsicGeodesic g hEnorm hsec hc p v convex_univ
  have hneg := (neg_concaveOn_iff.mpr hconv).add_const k
  convert! hneg using 1
  funext t
  exact (sub_eq_add_neg k (busemann c (intrinsicGeodesic g hEnorm p v t))).trans (add_comm _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.concaveOn_busemann_complement_intrinsicGeodesic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.concaveOn_busemann_complement_intrinsicGeodesic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.concaveOn_busemann_complement_intrinsicGeodesic ``Submission.DifferentialGeometry.Geometry.Topology.concaveOn_busemann_complement_intrinsicGeodesic

theorem exists_busemann_pairwise_flow_data
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {c : ℝ≥0 → M} (hc : Isometry c) {c₁ c₂ : ℝ} (hlevels : c₁ < c₂)
    (hne : ({x : M | busemann c x = c₁}).Nonempty)
    (hC : IsCompact {x : M | busemann c x ≤ c₂}) :
    ∃ m : ℝ, 0 < m ∧ c₂ - c₁ ≤ m ∧
      IsCompact {x : M | 0 ≤ c₂ - busemann c x} ∧
      LipschitzWith 1 (fun x => c₂ - busemann c x) ∧
      (∀ (p : M) (v : TangentSpace I p),
        ConcaveOn ℝ _root_.Set.univ (fun t => c₂ - busemann c (intrinsicGeodesic g hEnorm p v t))) ∧
      ∃ q : M, c₂ - busemann c q = m ∧ ∀ z : M, c₂ - busemann c z ≤ m := by
  obtain ⟨m, hm, hTm, hmax⟩ :=
    exists_busemann_complement_global_maximum hc hlevels hne hC
  refine ⟨m, hm, hTm, ?_, lipschitzWith_busemann_complement hc c₂,
    concaveOn_busemann_complement_intrinsicGeodesic g hEnorm hsec hc c₂, hmax⟩
  simpa only [sub_nonneg] using hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_busemann_pairwise_flow_data then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_busemann_pairwise_flow_data"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_busemann_pairwise_flow_data ``Submission.DifferentialGeometry.Geometry.Topology.exists_busemann_pairwise_flow_data

end DifferentialGeometry.Geometry.Topology
