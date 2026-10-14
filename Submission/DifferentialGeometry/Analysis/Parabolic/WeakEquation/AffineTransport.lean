import Submission.DifferentialGeometry.Analysis.Integration.Measure.Affine
import Submission.DifferentialGeometry.Analysis.Calculus.AffineComposition
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Analysis.Parabolic

open _root_.Submission.DifferentialGeometry.Analysis.Calculus

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem weighted_weak_equation_comp_add_smul
    (μ : _root_.MeasureTheory.Measure ℝ) [_root_.MeasureTheory.SFinite μ] (J : Set ℝ) (Ω : Set V)
    (ρ U F : ℝ × V → ℝ) (A : Fin n → Fin n → ℝ × V → ℝ)
    (K : Fin n → ℝ × V → ℝ)
    (hweak : ∀ φ : ℝ × V → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ J ×ˢ Ω →
      (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂μ.prod (volume.restrict Ω)) =
        (∑ j, ∫ p, (∑ i, A i j p * K i p) *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω)) -
        ∫ p, F p * φ p ∂μ.prod (volume.restrict Ω))
    (b : V) {r : ℝ} (hr : r ≠ 0) :
    let S : ℝ × V → ℝ × V := fun p => (p.1, b + r • p.2)
    let δ := |r ^ n|
    ∀ φ : ℝ × V → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ J ×ˢ ((fun x => b + r • x) ⁻¹' Ω) →
      (∫ p, (δ * ρ (S p)) * U (S p) * fderiv ℝ φ p (1, 0)
        ∂μ.prod (volume.restrict ((fun x => b + r • x) ⁻¹' Ω))) =
        (∑ j, ∫ p, (∑ i, (δ / r ^ 2 * A i j (S p)) * (r * K i (S p))) *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1)
            ∂μ.prod (volume.restrict ((fun x => b + r • x) ⁻¹' Ω))) -
        ∫ p, (δ * F (S p)) * φ p
          ∂μ.prod (volume.restrict ((fun x => b + r • x) ⁻¹' Ω)) := by
  intro S δ φ hφ hφc hφs
  let ψ : ℝ × V → ℝ := fun p => φ (p.1, r⁻¹ • (p.2 - b))
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    contDiff_comp_spatial_affine_inverse b r hφ
  have hψc : HasCompactSupport ψ :=
    hasCompactSupport_comp_spatial_affine_inverse b hr hφc
  have hψs : tsupport ψ ⊆ J ×ˢ Ω :=
    tsupport_comp_spatial_affine_inverse_subset_of_preimage b hr hφs
  have hvalue (p : ℝ × V) : ψ (S p) = φ p := by
    simp only [ψ, S]
    congr 1
    simp [smul_smul, hr, sub_eq_add_neg, add_assoc]
  have htime (p : ℝ × V) :
      fderiv ℝ ψ (S p) (1, 0) = fderiv ℝ φ p (1, 0) :=
    fderiv_comp_spatial_affine_inverse_time_at_image b hr
      ((hφ.differentiable (by simp)) p)
  have hspace (j : Fin n) (p : ℝ × V) :
      fderiv ℝ ψ (S p) (0, EuclideanSpace.single j 1) =
        r⁻¹ * fderiv ℝ φ p (0, EuclideanSpace.single j 1) :=
    fderiv_comp_spatial_affine_inverse_spatial_at_image b hr
      ((hφ.differentiable (by simp)) p) (EuclideanSpace.single j 1)
  have hchange (f : ℝ × V → ℝ) :
      (∫ p, δ * f (S p)
        ∂μ.prod (volume.restrict ((fun x => b + r • x) ⁻¹' Ω))) =
        ∫ p, f p ∂μ.prod (volume.restrict Ω) := by
    simpa only [S, δ, finrank_euclideanSpace_fin, smul_eq_mul] using
      integral_prod_abs_pow_smul_comp_add_smul μ _root_.MeasureTheory.MeasureSpace.volume f b hr Ω
  have hleft :
      (∫ p, (δ * ρ (S p)) * U (S p) * fderiv ℝ φ p (1, 0)
        ∂μ.prod (volume.restrict ((fun x => b + r • x) ⁻¹' Ω))) =
        ∫ p, ρ p * U p * fderiv ℝ ψ p (1, 0) ∂μ.prod (volume.restrict Ω) := by
    rw [← hchange (fun p => ρ p * U p * fderiv ℝ ψ p (1, 0))]
    apply _root_.MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun p => by dsimp only; rw [htime]; ring
  have hright (j : Fin n) :
      (∫ p, (∑ i, (δ / r ^ 2 * A i j (S p)) * (r * K i (S p))) *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1)
          ∂μ.prod (volume.restrict ((fun x => b + r • x) ⁻¹' Ω))) =
        ∫ p, (∑ i, A i j p * K i p) *
          fderiv ℝ ψ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω) := by
    rw [← hchange (fun p => (∑ i, A i j p * K i p) *
      fderiv ℝ ψ p (0, EuclideanSpace.single j 1))]
    apply _root_.MeasureTheory.integral_congr_ae
    refine Filter.Eventually.of_forall fun p => ?_
    dsimp only
    rw [hspace]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hr]
  have hforcing :
      (∫ p, (δ * F (S p)) * φ p
        ∂μ.prod (volume.restrict ((fun x => b + r • x) ⁻¹' Ω))) =
        ∫ p, F p * ψ p ∂μ.prod (volume.restrict Ω) := by
    rw [← hchange (fun p => F p * ψ p)]
    apply _root_.MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun p => by dsimp only; rw [hvalue]; ring
  rw [hleft, hforcing]
  simp only [hright]
  exact hweak ψ hψ hψc hψs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.weighted_weak_equation_comp_add_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.weighted_weak_equation_comp_add_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.weighted_weak_equation_comp_add_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.weighted_weak_equation_comp_add_smul

end DifferentialGeometry.Analysis.Parabolic
