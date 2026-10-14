import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace.WeakDerivatives

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Filter _root_.Set

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem HasWeakPartialDeriv.congr_ae
    {j : Fin d} {g f g' f' : E → ℝ} {Ω : Set E}
    (h : HasWeakPartialDeriv (d := d) j g f Ω)
    (hf : f =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Ω] f')
    (hg : g =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Ω] g') :
    HasWeakPartialDeriv (d := d) j g' f' Ω := by
  intro φ hφ hφ_support hφ_sub
  have h_lhs :
      ∫ x in Ω, f' x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) =
        ∫ x in Ω, f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) := by
    refine _root_.MeasureTheory.integral_congr_ae ?_
    filter_upwards [hf] with x hx
    rw [hx]
  have h_rhs :
      ∫ x in Ω, g' x * φ x = ∫ x in Ω, g x * φ x := by
    refine _root_.MeasureTheory.integral_congr_ae ?_
    filter_upwards [hg] with x hx
    rw [hx]
  rw [h_lhs, h_rhs]
  exact h φ hφ hφ_support hφ_sub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.HasWeakPartialDeriv.congr_ae then
    throwError "Refusing to shadow existing declaration DeGiorgi.HasWeakPartialDeriv.congr_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.HasWeakPartialDeriv.congr_ae ``Submission.DeGiorgi.HasWeakPartialDeriv.congr_ae

omit [NeZero d] in
theorem HasWeakPartialDeriv.const_smul
    {j : Fin d} {g f : E → ℝ} {Ω : Set E}
    (h : HasWeakPartialDeriv (d := d) j g f Ω) (c : ℝ) :
    HasWeakPartialDeriv (d := d) j
      (fun x => c • g x) (fun x => c • f x) Ω := by
  intro φ hφ hφ_support hφ_sub
  have h_base := h φ hφ hφ_support hφ_sub
  have h_lhs :
      ∫ x in Ω, (c • f x) * (fderiv ℝ φ x) (EuclideanSpace.single j 1) =
        c * ∫ x in Ω, f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) := by
    rw [← _root_.MeasureTheory.integral_const_mul]
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [smul_eq_mul]
    ring
  have h_rhs :
      ∫ x in Ω, (c • g x) * φ x = c * ∫ x in Ω, g x * φ x := by
    rw [← _root_.MeasureTheory.integral_const_mul]
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [smul_eq_mul]
    ring
  rw [h_lhs, h_rhs, h_base, mul_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.HasWeakPartialDeriv.const_smul then
    throwError "Refusing to shadow existing declaration DeGiorgi.HasWeakPartialDeriv.const_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.HasWeakPartialDeriv.const_smul ``Submission.DeGiorgi.HasWeakPartialDeriv.const_smul

omit [NeZero d] in
theorem HasWeakPartialDeriv.add
    {j : Fin d} {f₁ f₂ g₁ g₂ : E → ℝ} {Ω : Set E}
    (h₁ : HasWeakPartialDeriv (d := d) j g₁ f₁ Ω)
    (h₂ : HasWeakPartialDeriv (d := d) j g₂ f₂ Ω)
    (hf₁ : _root_.MeasureTheory.LocallyIntegrable f₁ ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Ω))
    (hf₂ : _root_.MeasureTheory.LocallyIntegrable f₂ ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Ω))
    (hg₁ : _root_.MeasureTheory.LocallyIntegrable g₁ ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Ω))
    (hg₂ : _root_.MeasureTheory.LocallyIntegrable g₂ ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Ω)) :
    HasWeakPartialDeriv (d := d) j (g₁ + g₂) (f₁ + f₂) Ω := by
  intro φ hφ_smooth hφ_support hφ_sub
  have heq₁ := h₁ φ hφ_smooth hφ_support hφ_sub
  have heq₂ := h₂ φ hφ_smooth hφ_support hφ_sub
  have hint_f₁ : _root_.MeasureTheory.Integrable
      (fun x => f₁ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1))
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Ω) := by
    have h := hf₁.integrable_smul_right_of_hasCompactSupport
      (hg := (hφ_smooth.continuous_fderiv (by simp)).clm_apply
        continuous_const)
      (h'g := hφ_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1))
    simpa [smul_eq_mul] using h
  have hint_f₂ : _root_.MeasureTheory.Integrable
      (fun x => f₂ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1))
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Ω) := by
    have h := hf₂.integrable_smul_right_of_hasCompactSupport
      (hg := (hφ_smooth.continuous_fderiv (by simp)).clm_apply
        continuous_const)
      (h'g := hφ_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1))
    simpa [smul_eq_mul] using h
  have hint_g₁ : _root_.MeasureTheory.Integrable (fun x => g₁ x * φ x)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Ω) := by
    have h := hg₁.integrable_smul_right_of_hasCompactSupport
      (hg := hφ_smooth.continuous) (h'g := hφ_support)
    simpa [smul_eq_mul] using h
  have hint_g₂ : _root_.MeasureTheory.Integrable (fun x => g₂ x * φ x)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Ω) := by
    have h := hg₂.integrable_smul_right_of_hasCompactSupport
      (hg := hφ_smooth.continuous) (h'g := hφ_support)
    simpa [smul_eq_mul] using h
  have h_lhs :
      ∫ x in Ω, (f₁ + f₂) x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) =
        (∫ x in Ω, f₁ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1)) +
          ∫ x in Ω, f₂ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) := by
    have h_eq : (fun x => (f₁ + f₂) x *
        (fderiv ℝ φ x) (EuclideanSpace.single j 1)) =
      fun x => f₁ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) +
        f₂ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) := by
      ext x
      change (f₁ x + f₂ x) * (fderiv ℝ φ x) (EuclideanSpace.single j 1) =
        f₁ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) +
          f₂ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1)
      ring
    rw [h_eq, _root_.MeasureTheory.integral_add hint_f₁ hint_f₂]
  rw [h_lhs]
  have h_rhs :
      ∫ x in Ω, (g₁ + g₂) x * φ x =
        (∫ x in Ω, g₁ x * φ x) + ∫ x in Ω, g₂ x * φ x := by
    have h_eq : (fun x => (g₁ + g₂) x * φ x) =
      fun x => g₁ x * φ x + g₂ x * φ x := by
      ext x
      change (g₁ x + g₂ x) * φ x = g₁ x * φ x + g₂ x * φ x
      ring
    rw [h_eq, _root_.MeasureTheory.integral_add hint_g₁ hint_g₂]
  rw [h_rhs, neg_add]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.HasWeakPartialDeriv.add then
    throwError "Refusing to shadow existing declaration DeGiorgi.HasWeakPartialDeriv.add"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.HasWeakPartialDeriv.add ``Submission.DeGiorgi.HasWeakPartialDeriv.add

end DeGiorgi
