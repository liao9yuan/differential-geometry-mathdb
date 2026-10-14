import Submission.DifferentialGeometry.Geometry.Metric.CurveVariation.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianCurveVariation_le_of_quad (g h : SmoothRiemannianMetric I M) {c : ℝ}
    (hc : 0 < c) (hgh : ∀ x v, h.inner x v v ≤ c * g.inner x v v)
    (γ : ℝ → M) (a b : ℝ) :
    riemannianCurveVariation h γ a b ≤
      ENNReal.ofReal (Real.sqrt c) * riemannianCurveVariation g γ a b := by
  unfold riemannianCurveVariation
  rw [ENNReal.mul_iSup]
  refine iSup_le fun p => ?_
  calc ∑ i ∈ Finset.range p.1,
        riemannianEDistOf h (γ (p.2.1 (i + 1))) (γ (p.2.1 i))
      ≤ ∑ i ∈ Finset.range p.1, ENNReal.ofReal (Real.sqrt c) *
          riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) :=
        Finset.sum_le_sum fun i _ => edistOf_le_of_quad g h hc hgh _ _
    _ = ENNReal.ofReal (Real.sqrt c) * ∑ i ∈ Finset.range p.1,
          riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) :=
        (Finset.mul_sum ..).symm
    _ ≤ ⨆ q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ _root_.Set.Icc a b},
          ENNReal.ofReal (Real.sqrt c) * ∑ i ∈ Finset.range q.1,
            riemannianEDistOf g (γ (q.2.1 (i + 1))) (γ (q.2.1 i)) := le_iSup (f := fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ _root_.Set.Icc a b} => ENNReal.ofReal (Real.sqrt c) * ∑ i ∈ Finset.range q.1, riemannianEDistOf g (γ (q.2.1 (i + 1))) (γ (q.2.1 i))) p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveVariation_le_of_quad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveVariation_le_of_quad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveVariation_le_of_quad ``Submission.DifferentialGeometry.Geometry.riemannianCurveVariation_le_of_quad

theorem le_riemannianCurveVariation_of_quad (g h : SmoothRiemannianMetric I M) {c : ℝ}
    (hc : 0 < c) (hl : ∀ x v, c * g.inner x v v ≤ h.inner x v v)
    (γ : ℝ → M) (a b : ℝ) :
    ENNReal.ofReal (Real.sqrt c) * riemannianCurveVariation g γ a b ≤
      riemannianCurveVariation h γ a b := by
  unfold riemannianCurveVariation
  rw [ENNReal.mul_iSup]
  refine iSup_le fun p => ?_
  calc ENNReal.ofReal (Real.sqrt c) * ∑ i ∈ Finset.range p.1,
        riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i))
      = ∑ i ∈ Finset.range p.1, ENNReal.ofReal (Real.sqrt c) *
          riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) := Finset.mul_sum ..
    _ ≤ ∑ i ∈ Finset.range p.1,
          riemannianEDistOf h (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) :=
        Finset.sum_le_sum fun i _ => le_edistOf_of_quad g h hc hl _ _
    _ ≤ ⨆ q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ _root_.Set.Icc a b},
          ∑ i ∈ Finset.range q.1,
            riemannianEDistOf h (γ (q.2.1 (i + 1))) (γ (q.2.1 i)) := le_iSup (f := fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ _root_.Set.Icc a b} => ∑ i ∈ Finset.range q.1, riemannianEDistOf h (γ (q.2.1 (i + 1))) (γ (q.2.1 i))) p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.le_riemannianCurveVariation_of_quad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.le_riemannianCurveVariation_of_quad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.le_riemannianCurveVariation_of_quad ``Submission.DifferentialGeometry.Geometry.le_riemannianCurveVariation_of_quad

theorem riemannianCurveVariation_scaleMetric (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) :
    riemannianCurveVariation (scaleMetric (I := I) c hc g) γ a b =
      ENNReal.ofReal (Real.sqrt c) * riemannianCurveVariation g γ a b := by
  refine le_antisymm ?_ ?_
  · refine riemannianCurveVariation_le_of_quad g (scaleMetric (I := I) c hc g) hc ?_ γ a b
    intro x v
    simp
  · exact le_riemannianCurveVariation_of_quad g (scaleMetric (I := I) c hc g) hc
      (fun x v => by simp) γ a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveVariation_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveVariation_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveVariation_scaleMetric ``Submission.DifferentialGeometry.Geometry.riemannianCurveVariation_scaleMetric


end DifferentialGeometry.Geometry
