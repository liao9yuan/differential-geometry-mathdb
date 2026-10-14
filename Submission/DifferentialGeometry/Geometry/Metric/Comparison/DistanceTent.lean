import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.MetricSpace.ThickenedIndicator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [RegularSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
noncomputable def riemDistTent
    (g : SmoothRiemannianMetric I M) (a : M) {r : ℝ} (hr : 0 < r) (x : M) : ℝ :=
  letI : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  ((thickenedIndicator (show 0 < r / 4 by positivity)
    (Metric.closedEBall a (ENNReal.ofReal (r / 2))) x : ℝ≥0) : ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemDistTent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemDistTent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemDistTent ``Submission.DifferentialGeometry.riemDistTent

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemTent_mem_Icc
    (g : SmoothRiemannianMetric I M) (a : M) {r : ℝ} (hr : 0 < r) (x : M) :
    riemDistTent g a hr x ∈ Set.Icc (0 : ℝ) 1 := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  constructor
  · change 0 ≤ ((thickenedIndicator (show 0 < r / 4 by positivity)
      (Metric.closedEBall a (ENNReal.ofReal (r / 2))) x : ℝ≥0) : ℝ)
    exact NNReal.coe_nonneg _
  · exact_mod_cast thickenedIndicator_le_one (show 0 < r / 4 by positivity)
      (Metric.closedEBall a (ENNReal.ofReal (r / 2))) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemTent_mem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemTent_mem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemTent_mem_Icc ``Submission.DifferentialGeometry.riemTent_mem_Icc

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemTent_eq_one
    (g : SmoothRiemannianMetric I M) (a : M) {r : ℝ} (hr : 0 < r) {x : M}
    (hx : riemannianEDistOf (I := I) g a x ≤ ENNReal.ofReal (r / 2)) :
    riemDistTent g a hr x = 1 := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  have hx' : x ∈ Metric.closedEBall a (ENNReal.ofReal (r / 2)) := by
    rw [Metric.mem_closedEBall', IsRiemannianManifold.out (I := I) a x]
    simpa only [riemannianEDistOf] using hx
  change ((thickenedIndicator (show 0 < r / 4 by positivity)
    (Metric.closedEBall a (ENNReal.ofReal (r / 2))) x : ℝ≥0) : ℝ) = 1
  rw [thickenedIndicator_one (show 0 < r / 4 by positivity)
    (Metric.closedEBall a (ENNReal.ofReal (r / 2))) hx']
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemTent_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemTent_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemTent_eq_one ``Submission.DifferentialGeometry.riemTent_eq_one

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemTent_eq_zero
    (g : SmoothRiemannianMetric I M) (a : M) {r : ℝ} (hr : 0 < r) {x : M}
    (hx : ENNReal.ofReal (3 * r / 4) ≤ riemannianEDistOf (I := I) g a x) :
    riemDistTent g a hr x = 0 := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  let S : Set M := Metric.closedEBall a (ENNReal.ofReal (r / 2))
  have hx' : ENNReal.ofReal (3 * r / 4) ≤ _root_.EDist.edist a x := by
    rw [IsRiemannianManifold.out (I := I) a x]
    simpa only [riemannianEDistOf] using hx
  have hout : x ∉ Metric.thickening (r / 4) S := by
    intro hxin
    obtain ⟨z, hzS, hxz⟩ :=
      (Metric.mem_thickening_iff_exists_edist_lt S x).1 hxin
    have haz : _root_.EDist.edist a z ≤ ENNReal.ofReal (r / 2) :=
      Metric.mem_closedEBall'.1 hzS
    have hzx : _root_.EDist.edist z x < ENNReal.ofReal (r / 4) := by
      simpa only [_root_.PseudoEMetricSpace.edist_comm] using hxz
    have hax : _root_.EDist.edist a x < ENNReal.ofReal (3 * r / 4) := by
      calc
        edist a x ≤ _root_.EDist.edist a z + _root_.EDist.edist z x := _root_.PseudoEMetricSpace.edist_triangle _ _ _
        _ < ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 4) :=
          ENNReal.add_lt_add_of_le_of_lt
            (ne_top_of_le_ne_top ENNReal.ofReal_ne_top haz) haz hzx
        _ = ENNReal.ofReal (3 * r / 4) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 2
          ring
    exact (not_lt_of_ge hx') hax
  change ((thickenedIndicator (show 0 < r / 4 by positivity) S x : ℝ≥0) : ℝ) = 0
  rw [thickenedIndicator_zero (show 0 < r / 4 by positivity) S hout]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemTent_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemTent_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemTent_eq_zero ``Submission.DifferentialGeometry.riemTent_eq_zero

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemTent_support
    (g : SmoothRiemannianMetric I M) (a : M) {r : ℝ} (hr : 0 < r) :
    Function.support (riemDistTent g a hr) ⊆
      {x | riemannianEDistOf (I := I) g a x < ENNReal.ofReal (3 * r / 4)} := by
  intro x hx
  simp only [Set.mem_ofPred_eq]
  by_contra hdist
  exact hx (riemTent_eq_zero g a hr (not_lt.1 hdist))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemTent_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemTent_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemTent_support ``Submission.DifferentialGeometry.riemTent_support

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemTent_tsupport
    (g : SmoothRiemannianMetric I M) (a : M) {r : ℝ} (hr : 0 < r) :
    tsupport (riemDistTent g a hr) ⊆
      {x | riemannianEDistOf (I := I) g a x < ENNReal.ofReal r} := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  have hsupp : Function.support (riemDistTent g a hr) ⊆
      Metric.closedEBall a (ENNReal.ofReal (3 * r / 4)) := by
    intro x hx
    rw [Metric.mem_closedEBall', IsRiemannianManifold.out (I := I) a x]
    exact (riemTent_support g a hr hx).le
  have hclose : tsupport (riemDistTent g a hr) ⊆
      Metric.closedEBall a (ENNReal.ofReal (3 * r / 4)) :=
    closure_minimal hsupp Metric.isClosed_closedEBall
  intro x hx
  have hxle : _root_.EDist.edist a x ≤ ENNReal.ofReal (3 * r / 4) :=
    Metric.mem_closedEBall'.1 (hclose hx)
  have hrad : ENNReal.ofReal (3 * r / 4) < ENNReal.ofReal r :=
    ENNReal.ofReal_lt_ofReal_iff hr |>.2 (by linarith)
  rw [IsRiemannianManifold.out (I := I) a x] at hxle
  exact hxle.trans_lt hrad

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemTent_tsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemTent_tsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemTent_tsupport ``Submission.DifferentialGeometry.riemTent_tsupport

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemTent_lip
    (g : SmoothRiemannianMetric I M) (a : M) {r : ℝ} (hr : 0 < r) (x y : M) :
    _root_.EDist.edist (riemDistTent g a hr x) (riemDistTent g a hr y) ≤
      ENNReal.ofNNReal (⟨4 / r, div_nonneg (by norm_num) hr.le⟩ : ℝ≥0) *
        riemannianEDistOf (I := I) g x y := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  let hδ : 0 < r / 4 := by positivity
  let S : Set M := Metric.closedEBall a (ENNReal.ofReal (r / 2))
  have hreal : LipschitzWith (r / 4).toNNReal⁻¹
      (fun z : M => ((thickenedIndicator hδ S z : ℝ≥0) : ℝ)) :=
    by
      have h := NNReal.isometry_coe.lipschitz.comp
        (lipschitzWith_thickenedIndicator hδ S)
      intro x y
      simpa only [Function.comp_apply, one_mul] using h x y
  have hconst : (r / 4).toNNReal⁻¹ =
      (⟨4 / r, div_nonneg (by norm_num) hr.le⟩ : ℝ≥0) := by
    apply NNReal.eq
    rw [NNReal.coe_inv, Real.coe_toNNReal (r / 4) (by positivity)]
    change (r / 4)⁻¹ = 4 / r
    field_simp [hr.ne']
  have hxy := hreal x y
  rw [hconst] at hxy
  rw [IsRiemannianManifold.out (I := I) x y] at hxy
  change _root_.EDist.edist
      (((thickenedIndicator hδ S x : ℝ≥0) : ℝ))
      (((thickenedIndicator hδ S y : ℝ≥0) : ℝ)) ≤
    ENNReal.ofNNReal (⟨4 / r, div_nonneg (by norm_num) hr.le⟩ : ℝ≥0) *
      riemannianEDistOf (I := I) g x y
  simpa only [riemannianEDistOf] using hxy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemTent_lip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemTent_lip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemTent_lip ``Submission.DifferentialGeometry.riemTent_lip

end DifferentialGeometry
