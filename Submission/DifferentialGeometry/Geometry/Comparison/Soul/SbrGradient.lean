import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SbrDirectionalConcavity
import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SbrGradientAlgebra
import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.NNReal _root_.ENNReal
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem existsUnique_intrinsicGeneralizedGradient
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (p : M) :
    ∃! G : TangentSpace I p,
      (∀ v : TangentSpace I p, intrinsicRightDerivative g hEnorm F p v ≤ g.inner p G v) ∧
      intrinsicRightDerivative g hEnorm F p G = g.inner p G G := by
  let D : TangentSpace I p → ℝ := intrinsicRightDerivative g hEnorm F p
  have hzero : D 0 = 0 := intrinsicRightDerivative_zero g hEnorm F p
  have hsmul : ∀ (a : ℝ), 0 ≤ a → ∀ v : TangentSpace I p, D (a • v) = a * D v := by
    intro a ha v
    exact intrinsicRightDerivative_smul g hEnorm F p v (hconc p v) ha
  have hadd : ∀ v w : TangentSpace I p, D v + D w ≤ D (v + w) :=
    intrinsicRightDerivative_superadditive g hEnorm hF hconc p
  have hbound : ∀ v w : TangentSpace I p,
      |D v - D w| ≤ L * Real.sqrt (g.inner p (v - w) (v - w)) :=
    abs_intrinsicRightDerivative_sub_le g hEnorm hF hconc p
  let K : InnerProductSpace.Core ℝ (TangentSpace I p) := g.toRiemannianMetric.toCore p
  have hKcont : ContinuousAt (fun v : TangentSpace I p => K.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt p
  have hKbounded : Bornology.IsVonNBounded ℝ
      {v : TangentSpace I p | RCLike.re (K.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded p
  let : NormedAddCommGroup (TangentSpace I p) :=
    K.toNormedAddCommGroupOfTopology hKcont hKbounded
  let : InnerProductSpace ℝ (TangentSpace I p) :=
    InnerProductSpace.ofCoreOfTopology K hKcont hKbounded
  have hinner (v w : TangentSpace I p) : _root_.Inner.inner ℝ v w = g.inner p v w := rfl
  have hnorm (v : TangentSpace I p) : ‖v‖ = Real.sqrt (g.inner p v v) := by
    rw [norm_eq_sqrt_real_inner, hinner]
  have hsq (v : TangentSpace I p) : ‖v‖ ^ 2 = g.inner p v v :=
    (real_inner_self_eq_norm_sq v).symm
  have hD : LipschitzWith L D := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, hnorm] using hbound v w
  obtain ⟨G, hG, huniq⟩ := existsUnique_superadditive_gradient hD hzero hsmul hadd
  refine ⟨G, ⟨?_, ?_⟩, ?_⟩
  · intro v
    simpa only [hinner] using hG.1 v
  · simpa only [hsq] using hG.2
  · intro G' hG'
    apply huniq G'
    constructor
    · intro v
      simpa only [hinner] using hG'.1 v
    · simpa only [hsq] using hG'.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.existsUnique_intrinsicGeneralizedGradient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.existsUnique_intrinsicGeneralizedGradient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.existsUnique_intrinsicGeneralizedGradient ``Submission.DifferentialGeometry.Geometry.Topology.existsUnique_intrinsicGeneralizedGradient

def intrinsicGeneralizedGradient
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (p : M) : TangentSpace I p :=
  Classical.choose (existsUnique_intrinsicGeneralizedGradient g hEnorm hF hconc p).exists

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient ``Submission.DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient

theorem intrinsicGeneralizedGradient_spec
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (p : M) :
    let G := intrinsicGeneralizedGradient g hEnorm hF hconc p
    (∀ v : TangentSpace I p, intrinsicRightDerivative g hEnorm F p v ≤ g.inner p G v) ∧
      intrinsicRightDerivative g hEnorm F p G = g.inner p G G :=
  Classical.choose_spec (existsUnique_intrinsicGeneralizedGradient g hEnorm hF hconc p).exists

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_spec ``Submission.DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_spec

theorem intrinsicGeneralizedGradient_eq_iff
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (p : M) (G : TangentSpace I p) :
    G = intrinsicGeneralizedGradient g hEnorm hF hconc p ↔
      (∀ v : TangentSpace I p, intrinsicRightDerivative g hEnorm F p v ≤ g.inner p G v) ∧
      intrinsicRightDerivative g hEnorm F p G = g.inner p G G := by
  constructor
  · intro hG
    rw [hG]
    exact intrinsicGeneralizedGradient_spec g hEnorm hF hconc p
  · intro hG
    exact (existsUnique_intrinsicGeneralizedGradient g hEnorm hF hconc p).unique hG
      (intrinsicGeneralizedGradient_spec g hEnorm hF hconc p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_eq_iff ``Submission.DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_eq_iff

theorem intrinsicRightDerivative_le_gradient_norm_mul
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (p : M) (v : TangentSpace I p) :
    let G := intrinsicGeneralizedGradient g hEnorm hF hconc p
    intrinsicRightDerivative g hEnorm F p v ≤
      Real.sqrt (g.inner p G G) * Real.sqrt (g.inner p v v) := by
  let D : TangentSpace I p → ℝ := intrinsicRightDerivative g hEnorm F p
  let G := intrinsicGeneralizedGradient g hEnorm hF hconc p
  have hs : ∀ w : TangentSpace I p, D w ≤ g.inner p G w :=
    (intrinsicGeneralizedGradient_spec g hEnorm hF hconc p).1
  let K : InnerProductSpace.Core ℝ (TangentSpace I p) := g.toRiemannianMetric.toCore p
  have hKcont : ContinuousAt (fun v : TangentSpace I p => K.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt p
  have hKbounded : Bornology.IsVonNBounded ℝ
      {v : TangentSpace I p | RCLike.re (K.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded p
  let : NormedAddCommGroup (TangentSpace I p) :=
    K.toNormedAddCommGroupOfTopology hKcont hKbounded
  let : InnerProductSpace ℝ (TangentSpace I p) :=
    InnerProductSpace.ofCoreOfTopology K hKcont hKbounded
  have hnorm (w : TangentSpace I p) : ‖w‖ = Real.sqrt (g.inner p w w) :=
    norm_eq_sqrt_real_inner w
  have hs' : ∀ w : TangentSpace I p, D w ≤ _root_.Inner.inner ℝ G w := hs
  simpa only [hnorm] using superadditive_gradient_le_norm_mul hs' v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.intrinsicRightDerivative_le_gradient_norm_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.intrinsicRightDerivative_le_gradient_norm_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.intrinsicRightDerivative_le_gradient_norm_mul ``Submission.DifferentialGeometry.Geometry.Topology.intrinsicRightDerivative_le_gradient_norm_mul

theorem intrinsicGeneralizedGradient_norm_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (p : M) :
    let G := intrinsicGeneralizedGradient g hEnorm hF hconc p
    Real.sqrt (g.inner p G G) ≤ L := by
  let G := intrinsicGeneralizedGradient g hEnorm hF hconc p
  change Real.sqrt (g.inner p G G) ≤ L
  by_cases hG : G = 0
  · simpa only [hG, map_zero, zero_apply, Real.sqrt_zero] using L.coe_nonneg
  · have hpos := g.pos p G hG
    have hnpos := Real.sqrt_pos.mpr hpos
    have hsq := Real.sq_sqrt hpos.le
    have hc := (intrinsicGeneralizedGradient_spec g hEnorm hF hconc p).2
    have hb := (le_abs_self (intrinsicRightDerivative g hEnorm F p G)).trans
      (abs_intrinsicRightDerivative_le g hEnorm hF p G (hconc p G))
    rw [hc] at hb
    nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_norm_le ``Submission.DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_norm_le

theorem intrinsicGeneralizedGradient_eq_zero_iff
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (p : M) :
    intrinsicGeneralizedGradient g hEnorm hF hconc p = 0 ↔
      ∀ v : TangentSpace I p, intrinsicRightDerivative g hEnorm F p v ≤ 0 := by
  let G := intrinsicGeneralizedGradient g hEnorm hF hconc p
  have hG := intrinsicGeneralizedGradient_spec g hEnorm hF hconc p
  constructor
  · intro hzero v
    simpa only [hzero, map_zero, zero_apply] using hG.1 v
  · intro hnonpos
    by_contra hne
    have hvalue := hnonpos G
    rw [hG.2] at hvalue
    exact (not_le_of_gt (g.pos p G hne)) hvalue

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_eq_zero_iff ``Submission.DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_eq_zero_iff

theorem intrinsicGeneralizedGradient_unit_maximizer
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (p : M) (hG : intrinsicGeneralizedGradient g hEnorm hF hconc p ≠ 0) :
    let G := intrinsicGeneralizedGradient g hEnorm hF hconc p
    let U := (Real.sqrt (g.inner p G G))⁻¹ • G
    Real.sqrt (g.inner p U U) = 1 ∧
      intrinsicRightDerivative g hEnorm F p U = Real.sqrt (g.inner p G G) ∧
      (∀ v : TangentSpace I p, Real.sqrt (g.inner p v v) ≤ 1 →
        intrinsicRightDerivative g hEnorm F p v ≤ Real.sqrt (g.inner p G G)) ∧
      (∀ v : TangentSpace I p, Real.sqrt (g.inner p v v) ≤ 1 →
        intrinsicRightDerivative g hEnorm F p v = Real.sqrt (g.inner p G G) → v = U) := by
  let D : TangentSpace I p → ℝ := intrinsicRightDerivative g hEnorm F p
  let G := intrinsicGeneralizedGradient g hEnorm hF hconc p
  have hsmul : ∀ (a : ℝ), 0 ≤ a → ∀ v : TangentSpace I p, D (a • v) = a * D v := by
    intro a ha v
    exact intrinsicRightDerivative_smul g hEnorm F p v (hconc p v) ha
  have hs : ∀ v : TangentSpace I p, D v ≤ g.inner p G v :=
    (intrinsicGeneralizedGradient_spec g hEnorm hF hconc p).1
  have hc : D G = g.inner p G G :=
    (intrinsicGeneralizedGradient_spec g hEnorm hF hconc p).2
  let K : InnerProductSpace.Core ℝ (TangentSpace I p) := g.toRiemannianMetric.toCore p
  have hKcont : ContinuousAt (fun v : TangentSpace I p => K.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt p
  have hKbounded : Bornology.IsVonNBounded ℝ
      {v : TangentSpace I p | RCLike.re (K.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded p
  let : NormedAddCommGroup (TangentSpace I p) :=
    K.toNormedAddCommGroupOfTopology hKcont hKbounded
  let : InnerProductSpace ℝ (TangentSpace I p) :=
    InnerProductSpace.ofCoreOfTopology K hKcont hKbounded
  have hnorm (v : TangentSpace I p) : ‖v‖ = Real.sqrt (g.inner p v v) :=
    norm_eq_sqrt_real_inner v
  have hs' : ∀ v : TangentSpace I p, D v ≤ _root_.Inner.inner ℝ G v := hs
  have hc' : D G = ‖G‖ ^ 2 := hc.trans (real_inner_self_eq_norm_sq G)
  simpa only [hnorm] using superadditive_gradient_unit_maximizer hsmul hs' hc' hG

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_unit_maximizer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_unit_maximizer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_unit_maximizer ``Submission.DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_unit_maximizer

theorem exists_minimizing_intrinsic_directional_secant
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (F : M → ℝ)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (p q : M) :
    ∃ v : TangentSpace I p, expMapIntrinsic g hEnorm p v = q ∧
      Real.sqrt (g.inner p v v) = _root_.Dist.dist p q ∧
      F q - F p ≤ intrinsicRightDerivative g hEnorm F p v := by
  obtain ⟨v, hv, hlen⟩ := minExp_of_ne_top g hEnorm p q (by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top p q)
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg] at hlen
  refine ⟨v, hv, hlen, ?_⟩
  have hsec := slope_le_intrinsicRightDerivative g hEnorm F p v (hconc p v)
    (t := 1) zero_lt_one
  simpa only [← expMapIntrinsic_def, hv, div_one] using hsec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_minimizing_intrinsic_directional_secant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_minimizing_intrinsic_directional_secant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_minimizing_intrinsic_directional_secant ``Submission.DifferentialGeometry.Geometry.Topology.exists_minimizing_intrinsic_directional_secant

theorem intrinsicGeneralizedGradient_secant_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (p q : M) :
    let G := intrinsicGeneralizedGradient g hEnorm hF hconc p
    F q - F p ≤ Real.sqrt (g.inner p G G) * _root_.Dist.dist p q := by
  obtain ⟨v, _, hlen, hsec⟩ :=
    exists_minimizing_intrinsic_directional_secant g hEnorm F hconc p q
  have hbound := intrinsicRightDerivative_le_gradient_norm_mul g hEnorm hF hconc p v
  rw [hlen] at hbound
  exact hsec.trans hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_secant_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_secant_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_secant_le ``Submission.DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_secant_le

theorem secant_div_dist_le_intrinsicGeneralizedGradient_norm
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    {p q : M} (hpq : p ≠ q) :
    let G := intrinsicGeneralizedGradient g hEnorm hF hconc p
    (F q - F p) / _root_.Dist.dist p q ≤ Real.sqrt (g.inner p G G) :=
  (div_le_iff₀ (dist_pos.mpr hpq)).mpr
    (intrinsicGeneralizedGradient_secant_le g hEnorm hF hconc p q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.secant_div_dist_le_intrinsicGeneralizedGradient_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.secant_div_dist_le_intrinsicGeneralizedGradient_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.secant_div_dist_le_intrinsicGeneralizedGradient_norm ``Submission.DifferentialGeometry.Geometry.Topology.secant_div_dist_le_intrinsicGeneralizedGradient_norm

theorem intrinsicGeneralizedGradient_ne_zero_of_lt
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    {p q : M} (hpq : F p < F q) :
    intrinsicGeneralizedGradient g hEnorm hF hconc p ≠ 0 := by
  intro hzero
  obtain ⟨v, _, _, hsec⟩ :=
    exists_minimizing_intrinsic_directional_secant g hEnorm F hconc p q
  have hnonpos := (intrinsicGeneralizedGradient_eq_zero_iff g hEnorm hF hconc p).mp hzero v
  exact (not_le_of_gt (sub_pos.mpr hpq)) (hsec.trans hnonpos)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_ne_zero_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_ne_zero_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_ne_zero_of_lt ``Submission.DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_ne_zero_of_lt

theorem intrinsicGeneralizedGradient_norm_pos_le_of_lt
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    {p q : M} (hpq : F p < F q) :
    let G := intrinsicGeneralizedGradient g hEnorm hF hconc p
    0 < Real.sqrt (g.inner p G G) ∧ Real.sqrt (g.inner p G G) ≤ L := by
  refine ⟨Real.sqrt_pos.mpr (g.pos p _ ?_),
    intrinsicGeneralizedGradient_norm_le g hEnorm hF hconc p⟩
  exact intrinsicGeneralizedGradient_ne_zero_of_lt g hEnorm hF hconc hpq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_norm_pos_le_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_norm_pos_le_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_norm_pos_le_of_lt ``Submission.DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_norm_pos_le_of_lt

end DifferentialGeometry.Geometry.Topology
