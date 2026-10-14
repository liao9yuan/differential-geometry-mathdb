import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckCoreCurves
import Mathlib.Order.Filter.AtTopBot.Basic

import Submission.DifferentialGeometry.Geometry.Metric.Distance.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions


def spatialNeckCoreRadiusConstant (epsilon : ℝ) : ℝ :=
  13 / 12 * Real.sqrt 2 * Real.sqrt (Real.pi ^ 2 + (epsilon⁻¹) ^ 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCoreRadiusConstant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCoreRadiusConstant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCoreRadiusConstant ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCoreRadiusConstant

theorem spatialNeckCoreRadiusConstant_pos (epsilon : ℝ) :
    0 < spatialNeckCoreRadiusConstant epsilon := by
  unfold spatialNeckCoreRadiusConstant
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCoreRadiusConstant_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCoreRadiusConstant_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCoreRadiusConstant_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCoreRadiusConstant_pos

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [IsRiemannianManifold I N]

private local instance coreSizeC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coreSizeC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coreSizeC1 target :: scope.openDecls } }

theorem SpatialNeckWitness.core_dist_le
    {h : SmoothRiemannianMetric I N} {mark : SpatialNeckSphere} {p : N} {epsilon : ℝ}
    (W : SpatialNeckWitness h mark p epsilon) (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon) {q : N} (hq : q ∈ W.core) :
    _root_.Dist.dist p q ≤ spatialNeckCoreRadiusConstant epsilon /
      Real.sqrt (metricScalarAt (I := I) h p) := by
  obtain ⟨z, hz, rfl⟩ := hq
  have hscale := spatialNeckScale_pos h p W.scalar_pos
  have hbound := W.core_edist_upper hsmall
    (spatialNeckCentralPoint epsilon W.epsilon_pos mark) z
    (spatialNeckCentralDomain_subset_core epsilon W.epsilon_pos rfl) hz
  rw [W.marked, riemannianEDistOf_eq_riemannianEDist h hEnorm,
    ← IsRiemannianManifold.out (I := I)] at hbound
  change _root_.EDist.edist p (W.embedding z) ≤ ENNReal.ofReal
    ((13 / 12 * spatialNeckScale h p) * Real.sqrt (Real.pi ^ 2 + (z.val.2 - 0) ^ 2)) at hbound
  rw [sub_zero] at hbound
  have hreal := (edist_le_ofReal (by positivity : 0 ≤
    (13 / 12 * spatialNeckScale h p) * Real.sqrt (Real.pi ^ 2 + z.val.2 ^ 2))).mp hbound
  have habs : |z.val.2| ≤ epsilon⁻¹ := abs_le.mpr hz
  have hsq : z.val.2 ^ 2 ≤ (epsilon⁻¹) ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg z.val.2) (inv_nonneg.mpr W.epsilon_pos.le)).mpr habs
    simpa only [sq_abs] using hh
  calc
    _root_.Dist.dist p (W.embedding z) ≤
        (13 / 12 * spatialNeckScale h p) * Real.sqrt (Real.pi ^ 2 + (epsilon⁻¹) ^ 2) :=
      hreal.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by positivity))
    _ = spatialNeckCoreRadiusConstant epsilon / Real.sqrt (metricScalarAt (I := I) h p) := by
      dsimp only [spatialNeckCoreRadiusConstant, spatialNeckScale]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.core_dist_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.core_dist_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.core_dist_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.core_dist_le

theorem eventually_spatialNeck_core_subset_ball
    {h : SmoothRiemannianMetric I N} {marks : ℕ → SpatialNeckSphere}
    {centers : ℕ → N} {epsilon : ℝ}
    (W : ∀ i : ℕ, SpatialNeckWitness h (marks i) (centers i) epsilon)
    (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hscalar : _root_.Filter.Tendsto (fun i => metricScalarAt (I := I) h (centers i)) _root_.Filter.atTop _root_.Filter.atTop)
    (r : ℝ) (hr : 0 < r) :
    ∀ᶠ i in _root_.Filter.atTop, (W i).core ⊆ Metric.ball (centers i) r := by
  let C := spatialNeckCoreRadiusConstant epsilon
  have hC : 0 < C := spatialNeckCoreRadiusConstant_pos epsilon
  filter_upwards [hscalar.eventually_gt_atTop ((C / r) ^ 2)] with i hi
  have hsqrt : 0 < Real.sqrt (metricScalarAt (I := I) h (centers i)) :=
    Real.sqrt_pos.mpr (W i).scalar_pos
  have hlarge : C / r < Real.sqrt (metricScalarAt (I := I) h (centers i)) := by
    by_contra! hn
    have hsq := (sq_le_sq₀ hsqrt.le (by positivity : 0 ≤ C / r)).mpr hn
    rw [Real.sq_sqrt (W i).scalar_pos.le] at hsq
    exact (not_le_of_gt hi) hsq
  have hsmallRadius : C / Real.sqrt (metricScalarAt (I := I) h (centers i)) < r := by
    apply (div_lt_iff₀ hsqrt).mpr
    have hm := (div_lt_iff₀ hr).mp hlarge
    nlinarith
  intro q hq
  rw [Metric.mem_ball, dist_comm q (centers i)]
  exact ((W i).core_dist_le hEnorm hsmall hq).trans_lt hsmallRadius

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_spatialNeck_core_subset_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_spatialNeck_core_subset_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_spatialNeck_core_subset_ball ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_spatialNeck_core_subset_ball

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem SpatialNeckWitness.core_edist_le
    {h : SmoothRiemannianMetric I M} {mark : SpatialNeckSphere} {p : M} {epsilon : ℝ}
    (W : SpatialNeckWitness h mark p epsilon) (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    {q : M} (hq : q ∈ W.core) :
    riemannianEDistOf h q p ≤ ENNReal.ofReal (spatialNeckCoreRadiusConstant epsilon /
      Real.sqrt (metricScalarAt h p)) := by
  obtain ⟨z, hz, rfl⟩ := hq
  have hscale := spatialNeckScale_pos h p W.scalar_pos
  have hbound := W.core_edist_upper hsmall
    (spatialNeckCentralPoint epsilon W.epsilon_pos mark) z
    (spatialNeckCentralDomain_subset_core epsilon W.epsilon_pos rfl) hz
  rw [W.marked] at hbound
  change riemannianEDistOf h p (W.embedding z) ≤ ENNReal.ofReal
    ((13 / 12 * spatialNeckScale h p) * Real.sqrt (Real.pi ^ 2 + (z.val.2 - 0) ^ 2)) at hbound
  rw [sub_zero] at hbound
  have habs : |z.val.2| ≤ epsilon⁻¹ := abs_le.mpr hz
  have hsq : z.val.2 ^ 2 ≤ (epsilon⁻¹) ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg z.val.2) (inv_nonneg.mpr W.epsilon_pos.le)).mpr habs
    simpa only [sq_abs] using hh
  rw [riemannianEDistOf_comm h]
  apply hbound.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    (13 / 12 * spatialNeckScale h p) * Real.sqrt (Real.pi ^ 2 + z.val.2 ^ 2)
      ≤ (13 / 12 * spatialNeckScale h p) * Real.sqrt (Real.pi ^ 2 + (epsilon⁻¹) ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by positivity)
    _ = spatialNeckCoreRadiusConstant epsilon / Real.sqrt (metricScalarAt h p) := by
      dsimp only [spatialNeckCoreRadiusConstant, spatialNeckScale]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.core_edist_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.core_edist_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.core_edist_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.core_edist_le

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
