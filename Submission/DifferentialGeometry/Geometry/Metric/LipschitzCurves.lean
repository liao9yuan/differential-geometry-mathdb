import Submission.DifferentialGeometry.Geometry.Measure.Area.ManifoldRademacherSource
import Submission.DifferentialGeometry.Geometry.Metric.CurveSpeedCalculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Submission.DifferentialGeometry
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]



theorem ae_mdifferentiableAt_riemannian_curve
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y) :
    ∀ᵐ t ∂volume, MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t :=
  ae_mdifferentiableAt_of_metric_lipschitz g hγ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.ae_mdifferentiableAt_riemannian_curve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.ae_mdifferentiableAt_riemannian_curve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.ae_mdifferentiableAt_riemannian_curve ``Submission.DifferentialGeometry.Geometry.ae_mdifferentiableAt_riemannian_curve

set_option backward.isDefEq.respectTransparency false in
theorem riemannianCurveSpeed_le_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y) (t : ℝ) :
    riemannianCurveSpeed g γ t ≤ C := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    let : Subsingleton (TangentSpace 𝓘(ℝ, E) (γ t)) := ‹Subsingleton E›
    unfold riemannianCurveSpeed
    have hz : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 = (0 : E) := Subsingleton.elim _ _
    rw [hz, map_zero, Real.sqrt_zero]
    exact C.coe_nonneg
  let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  by_cases hd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t
  · let : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩
    have h := metric_differential_le_of_edist_le (standardEuclideanMetric ℝ) g
      (u := id) (v := γ) mdifferentiableAt_id hd (fun y => by
        simpa only [id_eq, riemannianEDistOf_standardEuclideanMetric] using hγ t y) (1 : ℝ)
    have hs : Real.sqrt ((standardEuclideanMetric ℝ).inner t
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (id : ℝ → ℝ) t 1)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (id : ℝ → ℝ) t 1)) = 1 := by
      rw [mfderiv_id]
      change Real.sqrt (_root_.Inner.inner ℝ (1 : ℝ) 1) = 1
      norm_num
    exact h.trans_eq ((congrArg (fun s : ℝ => (C : ℝ) * s) hs).trans (mul_one _))
  · unfold riemannianCurveSpeed
    rw [mfderiv_zero_of_not_mdifferentiableAt hd]
    simp only [zero_apply, map_zero, Real.sqrt_zero]
    exact C.coe_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveSpeed_le_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveSpeed_le_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveSpeed_le_of_lipschitz ``Submission.DifferentialGeometry.Geometry.riemannianCurveSpeed_le_of_lipschitz

theorem riemannianCurveELength_le_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y) (a b : ℝ) :
    riemannianCurveELength g γ a b ≤ (C : ℝ≥0∞) * ENNReal.ofReal (b - a) :=
  riemannianCurveELength_le g (fun t _ => riemannianCurveSpeed_le_of_lipschitz g hγ t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveELength_le_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveELength_le_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveELength_le_of_lipschitz ``Submission.DifferentialGeometry.Geometry.riemannianCurveELength_le_of_lipschitz

theorem riemannianCurveELength_ne_top_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y) (a b : ℝ) :
    riemannianCurveELength g γ a b ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
    (riemannianCurveELength_le_of_lipschitz g hγ a b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveELength_ne_top_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveELength_ne_top_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveELength_ne_top_of_lipschitz ``Submission.DifferentialGeometry.Geometry.riemannianCurveELength_ne_top_of_lipschitz

end DifferentialGeometry.Geometry
