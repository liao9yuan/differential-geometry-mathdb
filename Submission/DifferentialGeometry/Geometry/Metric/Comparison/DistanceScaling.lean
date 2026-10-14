import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.NormDiamond
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Scaling
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_eq_riemannianEDist
    [_root_.Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [hContinuous : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm (I := I) (M := M) g)
    (x y : M) :
    riemannianEDistOf (I := I) g x y = _root_.Manifold.riemannianEDist I x y := by
  let _ := hContinuous
  rw [edistOf_iInf (I := I) g x y]
  rw [Manifold.riemannianEDist]
  refine iInf_congr fun γ => ?_
  refine iInf_congr fun hγ => ?_
  refine _root_.MeasureTheory.lintegral_congr fun t => ?_
  rw [hEnorm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianEDistOf_eq_riemannianEDist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianEDistOf_eq_riemannianEDist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianEDistOf_eq_riemannianEDist ``Submission.DifferentialGeometry.riemannianEDistOf_eq_riemannianEDist

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem edistOf_mono
    (g h : SmoothRiemannianMetric I M)
    (hgh : ∀ x v, g.inner x v v ≤ h.inner x v v)
    (x y : M) :
    riemannianEDistOf (I := I) g x y ≤
      riemannianEDistOf (I := I) h x y := by
  rw [edistOf_iInf, edistOf_iInf]
  refine iInf_mono fun γ => ?_
  refine iInf_mono fun hγ => ?_
  refine _root_.MeasureTheory.lintegral_mono fun t => ?_
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hgh (γ t) _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.edistOf_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.edistOf_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.edistOf_mono ``Submission.DifferentialGeometry.edistOf_mono

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem edistOf_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (x y : M) :
    riemannianEDistOf (I := I) (scaleMetric (I := I) c hc g) x y =
      ENNReal.ofReal (Real.sqrt c) * riemannianEDistOf (I := I) g x y := by
  rw [edistOf_iInf, edistOf_iInf]
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt c)
  have ha0 : a ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hc))
  have hatop : a ≠ (∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  change
    (⨅ (γ : Path x y) (_ : CMDiff 1 γ),
      ∫⁻ t, ENNReal.ofReal (Real.sqrt
        ((scaleMetric (I := I) c hc g).inner
          (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))) =
      a * ⨅ (γ : Path x y) (_ : CMDiff 1 γ),
        ∫⁻ t, ENNReal.ofReal (Real.sqrt
          (g.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))))
  rw [ENNReal.mul_iInf_of_ne ha0 hatop]
  refine iInf_congr fun γ => ?_
  rw [ENNReal.mul_iInf_of_ne ha0 hatop]
  refine iInf_congr fun hγ => ?_
  rw [← _root_.MeasureTheory.lintegral_const_mul' a _ hatop]
  refine _root_.MeasureTheory.lintegral_congr fun t => ?_
  simp only [scaleMetric_inner]
  rw [Real.sqrt_mul hc.le]
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg c)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.edistOf_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.edistOf_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.edistOf_scale ``Submission.DifferentialGeometry.edistOf_scale

theorem edistOf_le_of_quad
    (g h : SmoothRiemannianMetric I M) {c : Real} (hc : 0 < c)
    (hu : ∀ x v, h.inner x v v ≤ c * g.inner x v v)
    (x y : M) :
    riemannianEDistOf (I := I) h x y ≤
      ENNReal.ofReal (Real.sqrt c) * riemannianEDistOf (I := I) g x y := by
  calc
    riemannianEDistOf (I := I) h x y ≤
        riemannianEDistOf (I := I) (scaleMetric (I := I) c hc g) x y :=
      edistOf_mono h (scaleMetric (I := I) c hc g)
        (by
          intro z v
          simpa only [scaleMetric_inner] using hu z v)
        x y
    _ = ENNReal.ofReal (Real.sqrt c) *
        riemannianEDistOf (I := I) g x y :=
      edistOf_scale c hc g x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.edistOf_le_of_quad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.edistOf_le_of_quad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.edistOf_le_of_quad ``Submission.DifferentialGeometry.edistOf_le_of_quad

theorem le_edistOf_of_quad
    (g h : SmoothRiemannianMetric I M) {c : Real} (hc : 0 < c)
    (hl : ∀ x v, c * g.inner x v v ≤ h.inner x v v)
    (x y : M) :
    ENNReal.ofReal (Real.sqrt c) * riemannianEDistOf (I := I) g x y ≤
      riemannianEDistOf (I := I) h x y := by
  calc
    ENNReal.ofReal (Real.sqrt c) * riemannianEDistOf (I := I) g x y =
        riemannianEDistOf (I := I) (scaleMetric (I := I) c hc g) x y :=
      (edistOf_scale c hc g x y).symm
    _ ≤ riemannianEDistOf (I := I) h x y :=
      edistOf_mono (scaleMetric (I := I) c hc g) h
        (by
          intro z v
          simpa only [scaleMetric_inner] using hl z v)
        x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.le_edistOf_of_quad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.le_edistOf_of_quad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.le_edistOf_of_quad ``Submission.DifferentialGeometry.le_edistOf_of_quad

theorem edistBall_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (x : M) (r : Real) :
    {y : M | riemannianEDistOf (I := I)
        (scaleMetric (I := I) c hc g) x y <
          ENNReal.ofReal (Real.sqrt c * r)} =
      {y : M | riemannianEDistOf (I := I) g x y < ENNReal.ofReal r} := by
  ext y
  simp only [Set.mem_ofPred_eq]
  rw [edistOf_scale]
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt c)
  have ha0 : a ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hc))
  have hatop : a ≠ (∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  exact ENNReal.mul_lt_mul_iff_right ha0 hatop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.edistBall_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.edistBall_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.edistBall_scale ``Submission.DifferentialGeometry.edistBall_scale

end DifferentialGeometry

end
