import Submission.DifferentialGeometry.Geometry.Metric.CurveEnergy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.Geometry.Riemannian

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

theorem ofReal_mul_curveEnergy_le_lintegral_of_inner_le
    (g : SmoothRiemannianMetric I M) {gamma : ℝ → M} {a b mu : ℝ} (hab : a ≤ b)
    (hmu : 0 ≤ mu) (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (_root_.Set.Icc a b))
    (f : ℝ → ℝ) (hf : ∀ t ∈ _root_.Set.Ioc a b,
      mu * g.inner (gamma t) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t 1) ≤ f t) :
    ENNReal.ofReal (mu * curveEnergy g gamma a b) ≤ ∫⁻ t in _root_.Set.Ioc a b, ENNReal.ofReal (f t) := by
  let e : ℝ → ℝ := fun t => g.inner (gamma t) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)
    (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)
  have hint : _root_.MeasureTheory.IntegrableOn e (_root_.Set.Ioc a b) :=
    (integrableOn_inner_mfderiv_self_of_contMDiffOn g hgamma).mono_set _root_.Set.Ioc_subset_Icc_self
  have heq : ENNReal.ofReal (mu * curveEnergy g gamma a b) =
      ∫⁻ t in _root_.Set.Ioc a b, ENNReal.ofReal (mu * e t) := by
    rw [← _root_.MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint.const_mul mu)
      (Filter.Eventually.of_forall (fun t => mul_nonneg hmu
        (DifferentialGeometry.metric_inner_self_nonneg _ _ _)))]
    congr 1
    rw [_root_.MeasureTheory.integral_const_mul, curveEnergy, intervalIntegral.integral_of_le hab]
    rfl
  rw [heq]
  exact _root_.MeasureTheory.setLIntegral_mono' measurableSet_Ioc (fun t ht => ENNReal.ofReal_le_ofReal (hf t ht))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.ofReal_mul_curveEnergy_le_lintegral_of_inner_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.ofReal_mul_curveEnergy_le_lintegral_of_inner_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.ofReal_mul_curveEnergy_le_lintegral_of_inner_le ``Submission.DifferentialGeometry.Geometry.Riemannian.ofReal_mul_curveEnergy_le_lintegral_of_inner_le

theorem ofReal_mul_sq_div_le_lintegral_of_inner_le_of_endpoint_separation
    (g : SmoothRiemannianMetric I M) {gamma : ℝ → M} {a b mu r : ℝ} (hab : a < b)
    (hmu : 0 ≤ mu) (hr : 0 ≤ r)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (_root_.Set.Icc a b))
    (f : ℝ → ℝ) (hf : ∀ t ∈ _root_.Set.Ioc a b,
      mu * g.inner (gamma t) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t 1) ≤ f t)
    (hsep : ENNReal.ofReal r ≤ riemannianEDistOf g (gamma a) (gamma b)) :
    ENNReal.ofReal (mu * r ^ 2 / (b - a)) ≤ ∫⁻ t in _root_.Set.Ioc a b, ENNReal.ofReal (f t) := by
  have hint := integrableOn_inner_mfderiv_self_of_contMDiffOn g hgamma
  have hd := edistOf_le_energy g hab.le hgamma hint
  have hfinite : riemannianEDistOf g (gamma a) (gamma b) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd
  have hdist : r ≤ (riemannianEDistOf g (gamma a) (gamma b)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hsep
  have henergy := riemannianEDistOf_toReal_sq_le_curveEnergy g hab.le hgamma hint
  have hsq := (pow_le_pow_left₀ hr hdist 2).trans henergy
  have hmul := mul_le_mul_of_nonneg_left hsq hmu
  have hbound : mu * r ^ 2 / (b - a) ≤ mu * curveEnergy g gamma a b := by
    apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
    nlinarith
  exact (ENNReal.ofReal_le_ofReal hbound).trans
    (ofReal_mul_curveEnergy_le_lintegral_of_inner_le g hab.le hmu hgamma f hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.ofReal_mul_sq_div_le_lintegral_of_inner_le_of_endpoint_separation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.ofReal_mul_sq_div_le_lintegral_of_inner_le_of_endpoint_separation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.ofReal_mul_sq_div_le_lintegral_of_inner_le_of_endpoint_separation ``Submission.DifferentialGeometry.Geometry.Riemannian.ofReal_mul_sq_div_le_lintegral_of_inner_le_of_endpoint_separation

end DifferentialGeometry.Geometry.Riemannian

end
