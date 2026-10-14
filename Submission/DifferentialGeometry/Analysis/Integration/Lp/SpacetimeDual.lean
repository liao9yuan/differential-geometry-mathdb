import Submission.DifferentialGeometry.Analysis.Integration.Lp.ProductL2

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ENNReal _root_.InnerProductSpace
namespace MeasureTheory
open _root_.MeasureTheory
variable {A B E V : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {μ : Measure A} {ν : Measure B} [SFinite ν]

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem Lp.exists_lp_dual_integral_prod
    (J : V →L[ℝ] _root_.MeasureTheory.Lp E 2 ν) (F : _root_.MeasureTheory.Lp E 2 (μ.prod ν)) :
    ∃ ℓ : _root_.MeasureTheory.Lp (V →L[ℝ] ℝ) 2 μ, ∀ η : _root_.MeasureTheory.Lp ℝ 2 μ, ∀ v : V,
      (∫ t, η t * ℓ t v ∂μ) =
        ∫ p, η p.1 * _root_.Inner.inner ℝ (F p) (J v p.2) ∂μ.prod ν := by
  let Q := (Lp.uncurry (μ := μ) (ν := ν) (E := E) ℝ
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).toContinuousLinearMap.adjoint F
  let K : _root_.MeasureTheory.Lp E 2 ν →L[ℝ] V →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ (_root_.MeasureTheory.Lp E 2 ν)) J
  refine ⟨K.compLpL 2 μ Q, ?_⟩
  intro η v
  calc
    (∫ t, η t * (K.compLpL 2 μ Q) t v ∂μ) =
        ∫ t, η t * _root_.Inner.inner ℝ (Q t) (J v) ∂μ := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [K.coeFn_compLpL Q] with t ht
      rw [ht]
      rfl
    _ = _ := Lp.integral_inner_uncurryAdjoint_eq_integral_mul F η (J v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.exists_lp_dual_integral_prod then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.exists_lp_dual_integral_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.exists_lp_dual_integral_prod ``Submission.MeasureTheory.Lp.exists_lp_dual_integral_prod
open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem Lp.exists_lp_dual_integral_uncurry
    (J : V →L[ℝ] _root_.MeasureTheory.Lp E 2 ν) (F : _root_.MeasureTheory.Lp E 2 (μ.prod ν)) :
    ∃ ℓ : _root_.MeasureTheory.Lp (V →L[ℝ] ℝ) 2 μ,
      (∀ η : _root_.MeasureTheory.Lp ℝ 2 μ, ∀ v : V,
        (∫ t, η t * ℓ t v ∂μ) =
          ∫ p, η p.1 * _root_.Inner.inner ℝ (F p) (J v p.2) ∂μ.prod ν) ∧
      (∀ z : _root_.MeasureTheory.Lp V 2 μ, (∫ t, ℓ t (z t) ∂μ) =
        ∫ p, _root_.Inner.inner ℝ (F p) ((Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
          (J.compLpL 2 μ z)) p) ∂μ.prod ν) := by
  let Q := (Lp.uncurry (μ := μ) (ν := ν) (E := E) ℝ
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).toContinuousLinearMap.adjoint F
  let K : _root_.MeasureTheory.Lp E 2 ν →L[ℝ] V →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ (_root_.MeasureTheory.Lp E 2 ν)) J
  let ℓ := K.compLpL 2 μ Q
  have hvariable (z : _root_.MeasureTheory.Lp V 2 μ) : (∫ t, ℓ t (z t) ∂μ) =
      ∫ p, _root_.Inner.inner ℝ (F p) ((Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
        (J.compLpL 2 μ z)) p) ∂μ.prod ν := by
    calc
      (∫ t, ℓ t (z t) ∂μ) = _root_.Inner.inner ℝ Q (J.compLpL 2 μ z) := by
        rw [L2.inner_def]
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards [K.coeFn_compLpL Q, J.coeFn_compLpL z] with t hKt hJt
        change ℓ t = K (Q t) at hKt
        rw [hKt, hJt]
        rfl
      _ = _root_.Inner.inner ℝ F (Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
          (J.compLpL 2 μ z)) :=
        ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = _ := L2.inner_def _ _
  refine ⟨ℓ, ?_, hvariable⟩
  intro η v
  calc
    (∫ t, η t * ℓ t v ∂μ) = ∫ t, η t * _root_.Inner.inner ℝ (Q t) (J v) ∂μ := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [K.coeFn_compLpL Q] with t ht
      change ℓ t = K (Q t) at ht
      rw [ht]
      rfl
    _ = _ := Lp.integral_inner_uncurryAdjoint_eq_integral_mul F η (J v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.exists_lp_dual_integral_uncurry then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.exists_lp_dual_integral_uncurry"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.exists_lp_dual_integral_uncurry ``Submission.MeasureTheory.Lp.exists_lp_dual_integral_uncurry

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem Lp.integral_inner_uncurry_compLpL_eq_integral_integral [_root_.MeasureTheory.SFinite μ]
    (J : V →L[ℝ] _root_.MeasureTheory.Lp E 2 ν) (F : _root_.MeasureTheory.Lp E 2 (μ.prod ν)) (z : _root_.MeasureTheory.Lp V 2 μ) :
    (∫ p, _root_.Inner.inner ℝ (F p) ((Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (J.compLpL 2 μ z)) p) ∂μ.prod ν) =
        ∫ t, ∫ x, _root_.Inner.inner ℝ (F (t, x)) (J (z t) x) ∂ν ∂μ := by
  let Z := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (J.compLpL 2 μ z)
  have hprod := _root_.MeasureTheory.integral_prod (fun p => _root_.Inner.inner ℝ (F p) (Z p)) (L2.integrable_inner F Z)
  apply hprod.trans
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [Lp.uncurry_compLpL_coeFn (𝕜 := ℝ)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) J z] with t ht
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [ht] with x hx
  exact congrArg (fun y : E => _root_.Inner.inner ℝ (F (t, x)) y) hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.integral_inner_uncurry_compLpL_eq_integral_integral then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.integral_inner_uncurry_compLpL_eq_integral_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.integral_inner_uncurry_compLpL_eq_integral_integral ``Submission.MeasureTheory.Lp.integral_inner_uncurry_compLpL_eq_integral_integral

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem Lp.exists_lp_scalar_dual_integral_uncurry
    (J : V →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 ν) (F : _root_.MeasureTheory.Lp ℝ 2 (μ.prod ν)) :
    ∃ ℓ : _root_.MeasureTheory.Lp (V →L[ℝ] ℝ) 2 μ,
      (∀ τ : _root_.MeasureTheory.Lp ℝ 2 μ, ∀ v : V, (∫ t, τ t * ℓ t v ∂μ) =
        ∫ p, τ p.1 * F p * J v p.2 ∂μ.prod ν) ∧
      ∀ z : _root_.MeasureTheory.Lp V 2 μ, (∫ t, ℓ t (z t) ∂μ) =
        ∫ p, F p * (Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
          (J.compLpL 2 μ z)) p ∂μ.prod ν := by
  obtain ⟨ℓ, hℓ, hv⟩ := Lp.exists_lp_dual_integral_uncurry J F
  refine ⟨ℓ, ?_, ?_⟩
  · intro τ v
    exact (hℓ τ v).trans (_root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by
      simp only [Real.inner_apply]
      ring))
  · intro z
    exact (hv z).trans (_root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by
      exact mul_comm _ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.exists_lp_scalar_dual_integral_uncurry then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.exists_lp_scalar_dual_integral_uncurry"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.exists_lp_scalar_dual_integral_uncurry ``Submission.MeasureTheory.Lp.exists_lp_scalar_dual_integral_uncurry

end MeasureTheory
