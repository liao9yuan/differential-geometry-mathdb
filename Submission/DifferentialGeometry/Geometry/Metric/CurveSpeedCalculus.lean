import Submission.DifferentialGeometry.Geometry.Metric.CompactSourceCurves

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry _root_.MeasureTheory
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Bundle _root_.Submission.Bundle _root_.ENNReal _root_.NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]


def riemannianCurveSpeed (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : ℝ → M) (t : ℝ) : ℝ :=
  Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ))
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveSpeed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveSpeed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveSpeed ``Submission.DifferentialGeometry.Geometry.riemannianCurveSpeed

theorem riemannianCurveSpeed_nonneg (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : ℝ → M) (t : ℝ) : 0 ≤ riemannianCurveSpeed g γ t := Real.sqrt_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveSpeed_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveSpeed_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveSpeed_nonneg ``Submission.DifferentialGeometry.Geometry.riemannianCurveSpeed_nonneg

set_option backward.isDefEq.respectTransparency false in


theorem riemannianCurveSpeed_comp (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {r : V → M} {v : ℝ → V} {t : ℝ}
    (hr : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) r (v t)) (hv : DifferentiableAt ℝ v t) :
    riemannianCurveSpeed g (r ∘ v) t = Real.sqrt (g.inner (r (v t))
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) r (v t) (deriv v t))
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) r (v t) (deriv v t))) := by
  have hD := mfderiv_comp t hr hv.mdifferentiableAt
  have hDv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) v t (1 : ℝ) = deriv v t := by
    rw [mfderiv_eq_fderiv]
    exact fderiv_apply_one_eq_deriv (𝕜 := ℝ) (f := v) (x := t)
  unfold riemannianCurveSpeed
  rw [hD]
  change Real.sqrt (g.inner (r (v t))
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) r (v t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) v t (1 : ℝ)))
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) r (v t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) v t (1 : ℝ)))) = _
  rw [hDv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveSpeed_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveSpeed_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveSpeed_comp ``Submission.DifferentialGeometry.Geometry.riemannianCurveSpeed_comp



def riemannianCurveELength (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : ℝ → M) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in _root_.Set.Icc a b, ENNReal.ofReal (riemannianCurveSpeed g γ t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveELength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveELength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveELength ``Submission.DifferentialGeometry.Geometry.riemannianCurveELength


theorem riemannianCurveELength_le (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} {C : ℝ≥0} {a b : ℝ}
    (h : ∀ t ∈ _root_.Set.Icc a b, riemannianCurveSpeed g γ t ≤ C) :
    riemannianCurveELength g γ a b ≤ (C : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
  unfold riemannianCurveELength
  calc
    (∫⁻ t in _root_.Set.Icc a b, ENNReal.ofReal (riemannianCurveSpeed g γ t)) ≤
        ∫⁻ _t in _root_.Set.Icc a b, (C : ℝ≥0∞) := by
      apply _root_.MeasureTheory.lintegral_mono_ae
      filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
      simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (h t ht)
    _ = (C : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
      rw [_root_.MeasureTheory.lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveELength_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveELength_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveELength_le ``Submission.DifferentialGeometry.Geometry.riemannianCurveELength_le

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem riemannianCurveELength_eq_pathELength (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : ℝ → M) (a b : ℝ) :
    riemannianCurveELength g γ a b =
      (letI : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩;
        Manifold.pathELength 𝓘(ℝ, E) γ a b) := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [_root_.Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  apply _root_.MeasureTheory.lintegral_congr_ae
  filter_upwards [] with t
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveELength_eq_pathELength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveELength_eq_pathELength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveELength_eq_pathELength ``Submission.DifferentialGeometry.Geometry.riemannianCurveELength_eq_pathELength

end DifferentialGeometry.Geometry
