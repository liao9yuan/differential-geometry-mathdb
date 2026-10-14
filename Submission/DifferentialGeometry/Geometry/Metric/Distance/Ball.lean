import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.Connected.PathConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def riemannianClosedBallOf (g : SmoothRiemannianMetric I M) (x : M) (r : ℝ) : Set M :=
  {y | riemannianEDistOf (I := I) g x y ≤ ENNReal.ofReal r}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianClosedBallOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianClosedBallOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianClosedBallOf ``Submission.DifferentialGeometry.riemannianClosedBallOf

def riemannianBallOf (g : SmoothRiemannianMetric I M) (x : M) (r : ℝ) : Set M :=
  {y | riemannianEDistOf (I := I) g x y < ENNReal.ofReal r}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianBallOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianBallOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianBallOf ``Submission.DifferentialGeometry.riemannianBallOf

theorem riemannianClosedBallOf_mono (g : SmoothRiemannianMetric I M) (x : M) {r r' : ℝ}
    (h : r ≤ r') :
    riemannianClosedBallOf (I := I) g x r ⊆ riemannianClosedBallOf (I := I) g x r' := by
  intro y hy
  exact hy.trans (ENNReal.ofReal_le_ofReal h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianClosedBallOf_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianClosedBallOf_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianClosedBallOf_mono ``Submission.DifferentialGeometry.riemannianClosedBallOf_mono

theorem riemannianBallOf_mono (g : SmoothRiemannianMetric I M) (x : M) {r r' : ℝ}
    (h : r ≤ r') :
    riemannianBallOf (I := I) g x r ⊆ riemannianBallOf (I := I) g x r' := by
  intro y hy
  exact hy.trans_le (ENNReal.ofReal_le_ofReal h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianBallOf_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianBallOf_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianBallOf_mono ``Submission.DifferentialGeometry.riemannianBallOf_mono

theorem riemannianClosedBallOf_scaleMetric
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) (r : ℝ) :
    riemannianClosedBallOf (I := I) (scaleMetric (I := I) c hc g) x (Real.sqrt c * r) =
      riemannianClosedBallOf (I := I) g x r := by
  ext y
  have ha0 : ENNReal.ofReal (Real.sqrt c) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hc))
  have hatop : ENNReal.ofReal (Real.sqrt c) ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
  change riemannianEDistOf (I := I) (scaleMetric (I := I) c hc g) x y ≤
      ENNReal.ofReal (Real.sqrt c * r) ↔
    riemannianEDistOf (I := I) g x y ≤ ENNReal.ofReal r
  rw [edistOf_scale, ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
  constructor
  · intro h
    by_contra hcon
    exact absurd ((ENNReal.mul_lt_mul_iff_right ha0 hatop).2 (not_le.1 hcon)) (not_lt.2 h)
  · intro h
    by_contra hcon
    exact absurd ((ENNReal.mul_lt_mul_iff_right ha0 hatop).1 (not_le.1 hcon)) (not_lt.2 h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianClosedBallOf_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianClosedBallOf_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianClosedBallOf_scaleMetric ``Submission.DifferentialGeometry.riemannianClosedBallOf_scaleMetric

theorem riemannianBallOf_scaleMetric
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) (r : ℝ) :
    riemannianBallOf (I := I) (scaleMetric (I := I) c hc g) x (Real.sqrt c * r) =
      riemannianBallOf (I := I) g x r := by
  ext y
  have ha0 : ENNReal.ofReal (Real.sqrt c) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hc))
  have hatop : ENNReal.ofReal (Real.sqrt c) ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
  change riemannianEDistOf (I := I) (scaleMetric (I := I) c hc g) x y <
      ENNReal.ofReal (Real.sqrt c * r) ↔
    riemannianEDistOf (I := I) g x y < ENNReal.ofReal r
  rw [edistOf_scale, ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
  exact ENNReal.mul_lt_mul_iff_right ha0 hatop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianBallOf_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianBallOf_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianBallOf_scaleMetric ``Submission.DifferentialGeometry.riemannianBallOf_scaleMetric

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem isPathConnected_riemannianBallOf
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ} (hr : 0 < r) :
    IsPathConnected (riemannianBallOf g p r) := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  refine ⟨p, ?_, ?_⟩
  · change _root_.Manifold.riemannianEDist I p p < ENNReal.ofReal r
    rw [_root_.Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr hr
  intro q hq
  change _root_.Manifold.riemannianEDist I p q < ENNReal.ofReal r at hq
  obtain ⟨γ, hzero, hone, hγ, hlength⟩ := _root_.Manifold.exists_lt_of_riemannianEDist_lt hq
  let η : Path p q := ⟨⟨fun t => γ t, hγ.continuousOn.domRestrict⟩, hzero, hone⟩
  refine ⟨η, fun t => ?_⟩
  change _root_.Manifold.riemannianEDist I p (γ t) < ENNReal.ofReal r
  have hprefix := _root_.Manifold.riemannianEDist_le_pathELength
    (hγ.mono (_root_.Set.Icc_subset_Icc le_rfl t.property.2)) hzero rfl t.property.1
  exact (hprefix.trans (_root_.Manifold.pathELength_mono (I := I) le_rfl t.property.2)).trans_lt hlength

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.isPathConnected_riemannianBallOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.isPathConnected_riemannianBallOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.isPathConnected_riemannianBallOf ``Submission.DifferentialGeometry.isPathConnected_riemannianBallOf


namespace Geometry.Metric

open _root_.Set in
theorem subset_ball_of_scaled_tip_distance_bounds
    (g : SmoothRiemannianMetric I M) (tip p : M) (K : Set M)
    {q S C R : ℝ} (hq : 0 < q) (hS : 0 < S) (hR : 0 < R)
    (hscale : S / q < C)
    (hp : riemannianEDistOf (scaleMetric q hq g) tip p ≤ ENNReal.ofReal (2 * R))
    (hK : ∀ x ∈ K, riemannianEDistOf (scaleMetric q hq g) tip x ≤ ENNReal.ofReal (2 * R)) :
    K ⊆ riemannianBallOf (scaleMetric S hS g) p (4 * R * Real.sqrt C) := by
  have hc : 0 < S / q := div_pos hS hq
  have hC : 0 < C := hc.trans hscale
  have heq : scaleMetric S hS g = scaleMetric (S / q) hc (scaleMetric q hq g) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [scaleMetric_inner]
    field_simp
  intro x hx
  have htip := riemannianEDistOf_triangle (scaleMetric q hq g) p tip x
  rw [riemannianEDistOf_comm (scaleMetric q hq g) p tip] at htip
  have hb : riemannianEDistOf (scaleMetric q hq g) p x ≤ ENNReal.ofReal (4 * R) := by
    have hh := htip.trans (add_le_add hp (hK x hx))
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * R) (by positivity)] at hh
    simpa only [show 2 * R + 2 * R = 4 * R by ring] using hh
  change riemannianEDistOf (scaleMetric S hS g) p x < ENNReal.ofReal (4 * R * Real.sqrt C)
  rw [heq, edistOf_scale]
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt (S / q)) * ENNReal.ofReal (4 * R) :=
      mul_le_mul' le_rfl hb
    _ = ENNReal.ofReal (Real.sqrt (S / q) * (4 * R)) :=
      (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
    _ < _ := by
      apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos (by positivity) (Real.sqrt_pos.mpr hC))).mpr
      have hsqrt : Real.sqrt (S / q) < Real.sqrt C := Real.sqrt_lt_sqrt hc.le hscale
      nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.subset_ball_of_scaled_tip_distance_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.subset_ball_of_scaled_tip_distance_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.subset_ball_of_scaled_tip_distance_bounds ``Submission.DifferentialGeometry.Geometry.Metric.subset_ball_of_scaled_tip_distance_bounds

end Geometry.Metric

end DifferentialGeometry
