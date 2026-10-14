import Submission.DifferentialGeometry.Geometry.Metric.Distance.Finiteness
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.LipschitzBound
import Submission.DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import Mathlib.Topology.MetricSpace.Lipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian

open _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.NNReal _root_.ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def radialDistanceCutoff (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) (x : M) : ℝ :=
  _root_.Max.max 0 (1 - (riemannianEDistOf g p x).toReal / R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.radialDistanceCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.radialDistanceCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.radialDistanceCutoff ``Submission.DifferentialGeometry.Geometry.Riemannian.radialDistanceCutoff

theorem radialDistanceCutoff_mem_Icc
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ} (hR : 0 < R) (x : M) :
    radialDistanceCutoff g p R x ∈ _root_.Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le zero_le_one (sub_le_self 1 (div_nonneg ENNReal.toReal_nonneg hR.le))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.radialDistanceCutoff_mem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.radialDistanceCutoff_mem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.radialDistanceCutoff_mem_Icc ``Submission.DifferentialGeometry.Geometry.Riemannian.radialDistanceCutoff_mem_Icc

theorem radialDistanceCutoff_eq_zero_of_not_mem_closedBall
    [PreconnectedSpace M] (g : SmoothRiemannianMetric I M) (p : M)
    {R : ℝ} (hR : 0 < R) {x : M} (hx : x ∉ riemannianClosedBallOf g p R) :
    radialDistanceCutoff g p R x = 0 := by
  have hfin := riemannianEDistOf_ne_top g p x
  have hlt : ENNReal.ofReal R < riemannianEDistOf g p x := lt_of_not_ge hx
  have hreal : R < (riemannianEDistOf g p x).toReal := by
    exact (ENNReal.ofReal_lt_iff_lt_toReal hR.le hfin).mp hlt
  apply max_eq_left
  exact sub_nonpos.mpr ((le_div_iff₀ hR).mpr (by simpa using hreal.le))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.radialDistanceCutoff_eq_zero_of_not_mem_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.radialDistanceCutoff_eq_zero_of_not_mem_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.radialDistanceCutoff_eq_zero_of_not_mem_closedBall ``Submission.DifferentialGeometry.Geometry.Riemannian.radialDistanceCutoff_eq_zero_of_not_mem_closedBall

theorem hasCompactSupport_radialDistanceCutoff
    [T2Space M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (riemannianClosedBallOf g p R)) :
    HasCompactSupport (radialDistanceCutoff g p R) := by
  apply hcompact.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hcompact.isClosed
  intro x hx
  by_contra hn
  exact hx (radialDistanceCutoff_eq_zero_of_not_mem_closedBall g p hR hn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.hasCompactSupport_radialDistanceCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.hasCompactSupport_radialDistanceCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.hasCompactSupport_radialDistanceCutoff ``Submission.DifferentialGeometry.Geometry.Riemannian.hasCompactSupport_radialDistanceCutoff

theorem edist_radialDistanceCutoff_le
    [PreconnectedSpace M] (g : SmoothRiemannianMetric I M) (p : M)
    {R : ℝ} (hR : 0 < R) (x y : M) :
    _root_.EDist.edist (radialDistanceCutoff g p R x) (radialDistanceCutoff g p R y) ≤
      ENNReal.ofReal (1 / R) * riemannianEDistOf g x y := by
  have htri₁ := riemannianEDistOf_toReal_triangle g p x y
    (riemannianEDistOf_ne_top g p x) (riemannianEDistOf_ne_top g x y)
  have htri₂ := riemannianEDistOf_toReal_triangle g p y x
    (riemannianEDistOf_ne_top g p y) (riemannianEDistOf_ne_top g y x)
  rw [riemannianEDistOf_comm g y x] at htri₂
  have hdiff : |(riemannianEDistOf g p x).toReal -
      (riemannianEDistOf g p y).toReal| ≤ (riemannianEDistOf g x y).toReal :=
    abs_le.mpr ⟨by linarith only [htri₁], by linarith only [htri₂]⟩
  have hmax := abs_max_sub_max_le_max (0 : ℝ)
    (1 - (riemannianEDistOf g p x).toReal / R) 0
    (1 - (riemannianEDistOf g p y).toReal / R)
  have hcut : |radialDistanceCutoff g p R x - radialDistanceCutoff g p R y| ≤
      (1 / R) * (riemannianEDistOf g x y).toReal := by
    change |_root_.Max.max 0 (1 - (riemannianEDistOf g p x).toReal / R) -
      _root_.Max.max 0 (1 - (riemannianEDistOf g p y).toReal / R)| ≤ _
    have hsub : (1 - (riemannianEDistOf g p x).toReal / R) -
        (1 - (riemannianEDistOf g p y).toReal / R) =
        -((riemannianEDistOf g p x).toReal -
          (riemannianEDistOf g p y).toReal) / R := by ring
    rw [sub_self, abs_zero, max_eq_right (abs_nonneg
      ((1 - (riemannianEDistOf g p x).toReal / R) -
        (1 - (riemannianEDistOf g p y).toReal / R))), hsub,
      abs_div, abs_neg, abs_of_pos hR] at hmax
    exact hmax.trans (by simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using
      div_le_div_of_nonneg_right hdiff hR.le)
  rw [edist_dist, Real.dist_eq]
  have he := ENNReal.ofReal_le_ofReal hcut
  rwa [ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_toReal (riemannianEDistOf_ne_top g x y)] at he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.edist_radialDistanceCutoff_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.edist_radialDistanceCutoff_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.edist_radialDistanceCutoff_le ``Submission.DifferentialGeometry.Geometry.Riemannian.edist_radialDistanceCutoff_le

theorem gradient_radialDistanceCutoff_norm_le_of_metric_le
    [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [PreconnectedSpace M]
    (g h : SmoothRiemannianMetric I M)
    (hgh : ∀ x v, g.inner x v v ≤ h.inner x v v)
    (p : M) {R : ℝ} (hR : 0 < R) (x : M) :
    Real.sqrt (h.inner x (gradientFun h (radialDistanceCutoff g p R) x)
      (gradientFun h (radialDistanceCutoff g p R) x)) ≤ 1 / R := by
  let L : ℝ≥0 := ⟨1 / R, by positivity⟩
  apply grad_norm_le_lip_all (L := L) h
  intro y z
  have hb := (edist_radialDistanceCutoff_le g p hR y z).trans
    (mul_le_mul_right (edistOf_mono g h hgh y z) (ENNReal.ofReal (1 / R)))
  have hL : ENNReal.ofReal (1 / R) = (L : ℝ≥0∞) := by
    change ENNReal.ofReal (L : ℝ) = (L : ℝ≥0∞)
    exact ENNReal.ofReal_coe_nnreal
  rwa [hL] at hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.gradient_radialDistanceCutoff_norm_le_of_metric_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.gradient_radialDistanceCutoff_norm_le_of_metric_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.gradient_radialDistanceCutoff_norm_le_of_metric_le ``Submission.DifferentialGeometry.Geometry.Riemannian.gradient_radialDistanceCutoff_norm_le_of_metric_le

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lipschitzWith_radialDistanceCutoff
    [RegularSpace M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ} (hR : 0 < R) :
    let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    LipschitzWith ⟨1 / R, by positivity⟩ (radialDistanceCutoff g p R) := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  let L : ℝ≥0 := ⟨1 / R, by positivity⟩
  change LipschitzWith L (radialDistanceCutoff g p R)
  intro x y
  have hL : ENNReal.ofReal (1 / R) = (L : ℝ≥0∞) := by
    change ENNReal.ofReal (L : ℝ) = (L : ℝ≥0∞)
    exact ENNReal.ofReal_coe_nnreal
  have hb := edist_radialDistanceCutoff_le g p hR x y
  rw [hL] at hb
  exact hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.lipschitzWith_radialDistanceCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.lipschitzWith_radialDistanceCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.lipschitzWith_radialDistanceCutoff ``Submission.DifferentialGeometry.Geometry.Riemannian.lipschitzWith_radialDistanceCutoff

theorem tendsto_radialDistanceCutoff
    (g : SmoothRiemannianMetric I M) (p : M) {ι : Type*} {l : Filter ι}
    {R : ι → ℝ} (hR : _root_.Filter.Tendsto R l _root_.Filter.atTop) (x : M) :
    Tendsto (fun i => radialDistanceCutoff g p (R i) x) l (𝓝 1) := by
  have hbase : _root_.Filter.Tendsto (fun i => 1 - (riemannianEDistOf g p x).toReal / R i)
      l (𝓝 1) := by
    simpa only [sub_zero] using
      tendsto_const_nhds.sub (hR.const_div_atTop (riemannianEDistOf g p x).toReal)
  simpa only [radialDistanceCutoff, max_eq_right zero_le_one] using
    (tendsto_const_nhds.max hbase : _root_.Filter.Tendsto
      (fun i => _root_.Max.max (0 : ℝ) (1 - (riemannianEDistOf g p x).toReal / R i)) l (𝓝 (_root_.Max.max 0 1)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.tendsto_radialDistanceCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.tendsto_radialDistanceCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.tendsto_radialDistanceCutoff ``Submission.DifferentialGeometry.Geometry.Riemannian.tendsto_radialDistanceCutoff

end DifferentialGeometry.Geometry.Riemannian

end

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RegularSpace M] [PreconnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem continuous_radialDistanceCutoff
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ} (hr : 0 < r) :
    Continuous (radialDistanceCutoff g p r) := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  exact (lipschitzWith_radialDistanceCutoff g p hr).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.continuous_radialDistanceCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.continuous_radialDistanceCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.continuous_radialDistanceCutoff ``Submission.DifferentialGeometry.Geometry.Riemannian.continuous_radialDistanceCutoff

end DifferentialGeometry.Geometry.Riemannian
