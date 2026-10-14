-- Modified 2026-04-28: updated internal import paths for project namespace
import Submission.DifferentialGeometry.External.DeGiorgi.Foundations

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Chapter 03: Coefficients

This chapter defines the elliptic coefficient structures used throughout the
development.

It uses a unified coefficient structure with measurable coefficients, lower
ellipticity on `a` and `a⁻¹`, and derived mixed and upper bounds recorded as
theorems rather than primitive fields.
-/

noncomputable section

open _root_.MeasureTheory
open scoped _root_.InnerProductSpace

namespace DeGiorgi

/-- The ambient Euclidean space used by the elliptic regularity development. -/
abbrev AmbientSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.AmbientSpace then
    throwError "Refusing to shadow existing declaration DeGiorgi.AmbientSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.AmbientSpace ``Submission.DeGiorgi.AmbientSpace

/-- Matrix action on the ambient Euclidean space. -/
def matMulE {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (ξ : AmbientSpace d) : AmbientSpace d :=
  WithLp.toLp 2 (Matrix.mulVec M ξ.ofLp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.matMulE then
    throwError "Refusing to shadow existing declaration DeGiorgi.matMulE"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.matMulE ``Submission.DeGiorgi.matMulE

@[simp] theorem matMulE_ofLp {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (ξ : AmbientSpace d) :
    (matMulE M ξ).ofLp = Matrix.mulVec M ξ.ofLp :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.matMulE_ofLp then
    throwError "Refusing to shadow existing declaration DeGiorgi.matMulE_ofLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.matMulE_ofLp ``Submission.DeGiorgi.matMulE_ofLp

@[simp] theorem matMulE_apply {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (ξ : AmbientSpace d) (i : Fin d) :
    matMulE M ξ i = Matrix.mulVec M ξ.ofLp i :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.matMulE_apply then
    throwError "Refusing to shadow existing declaration DeGiorgi.matMulE_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.matMulE_apply ``Submission.DeGiorgi.matMulE_apply

/-- Unified nonsymmetric elliptic coefficient field for the elliptic regularity
development.

It is designed to serve both:

- the variational / weak-solution branch, which needs measurability;
- the De Giorgi / Moser branch, which uses coercivity of `a⁻¹` to derive mixed
  and upper bounds.

The upper bounds are intentionally not primitive fields in this structure. -/
structure EllipticCoeff (d : ℕ) [NeZero d] (Ω : Set (AmbientSpace d)) where
  /-- Matrix-valued coefficient field. -/
  a : AmbientSpace d → Matrix (Fin d) (Fin d) ℝ
  /-- Lower ellipticity constant. -/
  lam : ℝ
  /-- Upper ellipticity constant. -/
  Λ : ℝ
  /-- Componentwise measurability of the coefficient field. -/
  measurable_comp : ∀ i j, Measurable (fun x => a x i j)
  /-- Positivity of the lower ellipticity constant. -/
  hlam : 0 < lam
  /-- Comparison of lower and upper ellipticity scales. -/
  hΛ : lam ≤ Λ
  /-- Coercivity on `a`, stated almost everywhere on `Ω`. -/
  coercive : ∀ᵐ x ∂(MeasureTheory.volume.restrict Ω), ∀ ξ : AmbientSpace d,
    lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE (a x) ξ⟫_ℝ
  /-- Coercivity on `a⁻¹`, stated almost everywhere on `Ω`. -/
  coercive_inv : ∀ᵐ x ∂(MeasureTheory.volume.restrict Ω), ∀ ξ : AmbientSpace d,
    Λ⁻¹ * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE ((a x)⁻¹) ξ⟫_ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff ``Submission.DeGiorgi.EllipticCoeff

/-- The ellipticity ratio governing scale-invariant estimates. -/
def ellipticityRatio {d : ℕ} [NeZero d] {Ω : Set (AmbientSpace d)}
    (A : EllipticCoeff d Ω) : ℝ :=
  A.Λ / A.lam

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.ellipticityRatio then
    throwError "Refusing to shadow existing declaration DeGiorgi.ellipticityRatio"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.ellipticityRatio ``Submission.DeGiorgi.ellipticityRatio

/-- Optional normalized view of the unified coefficient structure. -/
abbrev NormalizedEllipticCoeff (d : ℕ) [NeZero d] (Ω : Set (AmbientSpace d)) :=
  {A : EllipticCoeff d Ω // A.lam = 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.NormalizedEllipticCoeff then
    throwError "Refusing to shadow existing declaration DeGiorgi.NormalizedEllipticCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.NormalizedEllipticCoeff ``Submission.DeGiorgi.NormalizedEllipticCoeff

namespace EllipticCoeff

variable {d : ℕ} [NeZero d] {Ω : Set (AmbientSpace d)} (A : EllipticCoeff d Ω)

@[simp] theorem ellipticityRatio_def :
    ellipticityRatio A = A.Λ / A.lam := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.ellipticityRatio_def then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.ellipticityRatio_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.ellipticityRatio_def ``Submission.DeGiorgi.EllipticCoeff.ellipticityRatio_def

theorem lam_nonneg : 0 ≤ A.lam :=
  le_of_lt A.hlam

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.lam_nonneg then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.lam_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.lam_nonneg ``Submission.DeGiorgi.EllipticCoeff.lam_nonneg

theorem Λ_pos : 0 < A.Λ :=
  lt_of_lt_of_le A.hlam A.hΛ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.Λ_pos then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.Λ_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.Λ_pos ``Submission.DeGiorgi.EllipticCoeff.Λ_pos

theorem Λ_nonneg : 0 ≤ A.Λ :=
  A.Λ_pos.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.Λ_nonneg then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.Λ_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.Λ_nonneg ``Submission.DeGiorgi.EllipticCoeff.Λ_nonneg

theorem ellipticityRatio_pos : 0 < ellipticityRatio A := by
  dsimp [ellipticityRatio]
  exact div_pos A.Λ_pos A.hlam

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.ellipticityRatio_pos then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.ellipticityRatio_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.ellipticityRatio_pos ``Submission.DeGiorgi.EllipticCoeff.ellipticityRatio_pos

theorem ellipticityRatio_nonneg : 0 ≤ ellipticityRatio A :=
  (A.ellipticityRatio_pos).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.ellipticityRatio_nonneg then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.ellipticityRatio_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.ellipticityRatio_nonneg ``Submission.DeGiorgi.EllipticCoeff.ellipticityRatio_nonneg

theorem one_le_ellipticityRatio : 1 ≤ ellipticityRatio A := by
  simpa [ellipticityRatio] using (one_le_div A.hlam).2 A.hΛ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.one_le_ellipticityRatio then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.one_le_ellipticityRatio"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.one_le_ellipticityRatio ``Submission.DeGiorgi.EllipticCoeff.one_le_ellipticityRatio

theorem ae_coercive_nonneg :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict Ω), ∀ ξ : AmbientSpace d,
      0 ≤ ⟪ξ, matMulE (A.a x) ξ⟫_ℝ := by
  filter_upwards [A.coercive] with x hx
  intro ξ
  have hnonneg : 0 ≤ A.lam * ‖ξ‖ ^ 2 := by
    exact mul_nonneg A.lam_nonneg (sq_nonneg ‖ξ‖)
  exact le_trans hnonneg (hx ξ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.ae_coercive_nonneg then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.ae_coercive_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.ae_coercive_nonneg ``Submission.DeGiorgi.EllipticCoeff.ae_coercive_nonneg

theorem ae_coercive_inv_nonneg :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict Ω), ∀ ξ : AmbientSpace d,
      0 ≤ ⟪ξ, matMulE ((A.a x)⁻¹) ξ⟫_ℝ := by
  filter_upwards [A.coercive_inv] with x hx
  intro ξ
  have hnonneg : 0 ≤ A.Λ⁻¹ * ‖ξ‖ ^ 2 := by
    exact mul_nonneg (inv_nonneg.mpr A.Λ_nonneg) (sq_nonneg ‖ξ‖)
  exact le_trans hnonneg (hx ξ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.ae_coercive_inv_nonneg then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.ae_coercive_inv_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.ae_coercive_inv_nonneg ``Submission.DeGiorgi.EllipticCoeff.ae_coercive_inv_nonneg

theorem measurable_apply (i j : Fin d) :
    Measurable (fun x => A.a x i j) :=
  A.measurable_comp i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.measurable_apply then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.measurable_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.measurable_apply ``Submission.DeGiorgi.EllipticCoeff.measurable_apply

theorem det_ne_zero_of_coercive {x : AmbientSpace d}
    (hx : ∀ ξ : AmbientSpace d,
      A.lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE (A.a x) ξ⟫_ℝ) :
    (A.a x).det ≠ 0 := by
  classical
  rw [ne_eq, ← Matrix.exists_mulVec_eq_zero_iff]
  intro hsing
  rcases hsing with ⟨v, hv_ne, hv_zero⟩
  let ξ : AmbientSpace d := WithLp.toLp 2 v
  have hξ_zero_action : matMulE (A.a x) ξ = 0 := by
    apply PiLp.ext
    intro i
    simp [matMulE, ξ, hv_zero]
  have hcoer : A.lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE (A.a x) ξ⟫_ℝ := hx ξ
  have hmul_nonneg : 0 ≤ A.lam * ‖ξ‖ ^ 2 := by
    exact mul_nonneg A.lam_nonneg (sq_nonneg ‖ξ‖)
  have hmul_eq_zero : A.lam * ‖ξ‖ ^ 2 = 0 := by
    refine le_antisymm ?_ hmul_nonneg
    simpa [hξ_zero_action] using hcoer
  have hnorm_sq_eq_zero : ‖ξ‖ ^ 2 = 0 := by
    exact (mul_eq_zero.mp hmul_eq_zero).resolve_left (ne_of_gt A.hlam)
  have hnorm_eq_zero : ‖ξ‖ = 0 := by
    nlinarith [sq_nonneg ‖ξ‖, hnorm_sq_eq_zero]
  have hξ_zero' : ξ = 0 := norm_eq_zero.mp hnorm_eq_zero
  have hv_zero' : v = 0 := by
    have hcoords : ξ.ofLp = 0 := by
      simpa [ξ] using congrArg (fun η : AmbientSpace d => η.ofLp) hξ_zero'
    simpa [ξ] using hcoords
  exact hv_ne hv_zero'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.det_ne_zero_of_coercive then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.det_ne_zero_of_coercive"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.det_ne_zero_of_coercive ``Submission.DeGiorgi.EllipticCoeff.det_ne_zero_of_coercive

theorem inv_matMulE_matMulE {x : AmbientSpace d}
    (hx : ∀ ξ : AmbientSpace d,
      A.lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE (A.a x) ξ⟫_ℝ)
    (ξ : AmbientSpace d) :
    matMulE ((A.a x)⁻¹) (matMulE (A.a x) ξ) = ξ := by
  apply PiLp.ext
  intro i
  have hdet_unit : IsUnit (A.a x).det :=
    (isUnit_iff_ne_zero.2 <| A.det_ne_zero_of_coercive hx)
  simp [matMulE, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet_unit, Matrix.one_mulVec]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.inv_matMulE_matMulE then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.inv_matMulE_matMulE"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.inv_matMulE_matMulE ``Submission.DeGiorgi.EllipticCoeff.inv_matMulE_matMulE

/-- Mixed quadratic bound derived from inverse coercivity. -/
theorem mulVec_sq_le :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict Ω), ∀ ξ : AmbientSpace d,
      ‖matMulE (A.a x) ξ‖ ^ 2 ≤ A.Λ * ⟪ξ, matMulE (A.a x) ξ⟫_ℝ := by
  filter_upwards [A.coercive, A.coercive_inv] with x hx_coercive hx_inv
  intro ξ
  let η : AmbientSpace d := matMulE (A.a x) ξ
  have hscaled :
      ‖η‖ ^ 2 ≤ A.Λ * ⟪η, matMulE ((A.a x)⁻¹) η⟫_ℝ := by
    have h := mul_le_mul_of_nonneg_left (hx_inv η) A.Λ_nonneg
    have hΛ_ne : A.Λ ≠ 0 := ne_of_gt A.Λ_pos
    simpa [η, mul_assoc, hΛ_ne] using h
  calc
    ‖matMulE (A.a x) ξ‖ ^ 2 = ‖η‖ ^ 2 := by
      rfl
    _ ≤ A.Λ * ⟪η, matMulE ((A.a x)⁻¹) η⟫_ℝ := hscaled
    _ = A.Λ * ⟪η, ξ⟫_ℝ := by
      rw [A.inv_matMulE_matMulE hx_coercive ξ]
    _ = A.Λ * ⟪ξ, η⟫_ℝ := by
      rw [real_inner_comm]
    _ = A.Λ * ⟪ξ, matMulE (A.a x) ξ⟫_ℝ := by
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.mulVec_sq_le then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.mulVec_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.mulVec_sq_le ``Submission.DeGiorgi.EllipticCoeff.mulVec_sq_le

/-- Pointwise quadratic upper bound derived from the mixed bound. -/
theorem quadratic_upper :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict Ω), ∀ ξ : AmbientSpace d,
      ⟪ξ, matMulE (A.a x) ξ⟫_ℝ ≤ A.Λ * ‖ξ‖ ^ 2 := by
  filter_upwards [A.coercive, A.mulVec_sq_le] with x hx_coercive hx_mul ξ
  let q : ℝ := ⟪ξ, matMulE (A.a x) ξ⟫_ℝ
  let m : ℝ := ‖matMulE (A.a x) ξ‖
  let n : ℝ := ‖ξ‖
  have hq_nonneg : 0 ≤ q := by
    exact le_trans (mul_nonneg A.lam_nonneg (sq_nonneg ‖ξ‖)) (by simpa [q] using hx_coercive ξ)
  have hq_le : q ≤ n * m := by
    simpa [q, m, n, abs_of_nonneg hq_nonneg, mul_comm] using
      (abs_real_inner_le_norm ξ (matMulE (A.a x) ξ))
  have hm_sq : m ^ 2 ≤ A.Λ * q := by
    simpa [m, q] using hx_mul ξ
  have hn_nonneg : 0 ≤ n := norm_nonneg ξ
  have hm_nonneg : 0 ≤ m := norm_nonneg (matMulE (A.a x) ξ)
  have hq_mul : q * q ≤ (A.Λ * n ^ 2) * q := by
    nlinarith [hq_le, hm_sq, hn_nonneg, hm_nonneg, A.Λ_nonneg]
  have hupper : q ≤ A.Λ * n ^ 2 := by
    by_cases hq_zero : q = 0
    · have hnonneg : 0 ≤ A.Λ * n ^ 2 := mul_nonneg A.Λ_nonneg (sq_nonneg n)
      simpa [hq_zero] using hnonneg
    · have hq_pos : 0 < q := lt_of_le_of_ne hq_nonneg (by simpa [eq_comm] using hq_zero)
      exact le_of_mul_le_mul_right
        (by simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hq_mul)
        hq_pos
  simpa [q, n] using hupper

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.quadratic_upper then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.quadratic_upper"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.quadratic_upper ``Submission.DeGiorgi.EllipticCoeff.quadratic_upper

/-- Mixed bilinear bound needed by the variational branch. -/
theorem mixed_bound :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict Ω), ∀ ξ ζ : AmbientSpace d,
      |⟪ζ, matMulE (A.a x) ξ⟫_ℝ| ≤ A.Λ * ‖ζ‖ * ‖ξ‖ := by
  filter_upwards [A.mulVec_sq_le, A.quadratic_upper] with x hx_mul hx_quad
  intro ξ ζ
  let m : ℝ := ‖matMulE (A.a x) ξ‖
  let nξ : ℝ := ‖ξ‖
  let nζ : ℝ := ‖ζ‖
  have habs : |⟪ζ, matMulE (A.a x) ξ⟫_ℝ| ≤ nζ * m := by
    simpa [m, nζ, mul_comm] using abs_real_inner_le_norm ζ (matMulE (A.a x) ξ)
  have hm_sq : m ^ 2 ≤ A.Λ * ⟪ξ, matMulE (A.a x) ξ⟫_ℝ := by
    simpa [m] using hx_mul ξ
  have hq_upper :
      ⟪ξ, matMulE (A.a x) ξ⟫_ℝ ≤ A.Λ * nξ ^ 2 := by
    simpa [nξ] using hx_quad ξ
  have hm_le : m ≤ A.Λ * nξ := by
    have hm_nonneg : 0 ≤ m := norm_nonneg (matMulE (A.a x) ξ)
    have hnξ_nonneg : 0 ≤ nξ := norm_nonneg ξ
    have hrhs_nonneg : 0 ≤ A.Λ * nξ := mul_nonneg A.Λ_nonneg hnξ_nonneg
    have hm_sq_upper : m ^ 2 ≤ (A.Λ * nξ) ^ 2 := by
      nlinarith [hm_sq, hq_upper, A.Λ_nonneg]
    exact (sq_le_sq₀ hm_nonneg hrhs_nonneg).1 hm_sq_upper
  have hnζ_nonneg : 0 ≤ nζ := norm_nonneg ζ
  calc
    |⟪ζ, matMulE (A.a x) ξ⟫_ℝ| ≤ nζ * m := habs
    _ ≤ nζ * (A.Λ * nξ) := by
      exact mul_le_mul_of_nonneg_left hm_le hnζ_nonneg
    _ = A.Λ * ‖ζ‖ * ‖ξ‖ := by
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.mixed_bound then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.mixed_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.mixed_bound ``Submission.DeGiorgi.EllipticCoeff.mixed_bound

end EllipticCoeff

namespace NormalizedEllipticCoeff

variable {d : ℕ} [NeZero d] {Ω : Set (AmbientSpace d)}
  (A : NormalizedEllipticCoeff d Ω)

@[simp] theorem lam_eq_one : A.1.lam = 1 :=
  A.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.NormalizedEllipticCoeff.lam_eq_one then
    throwError "Refusing to shadow existing declaration DeGiorgi.NormalizedEllipticCoeff.lam_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.NormalizedEllipticCoeff.lam_eq_one ``Submission.DeGiorgi.NormalizedEllipticCoeff.lam_eq_one

theorem ellipticityRatio_eq_Λ :
    ellipticityRatio A.1 = A.1.Λ := by
  simp [ellipticityRatio]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.NormalizedEllipticCoeff.ellipticityRatio_eq_Λ then
    throwError "Refusing to shadow existing declaration DeGiorgi.NormalizedEllipticCoeff.ellipticityRatio_eq_Λ"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.NormalizedEllipticCoeff.ellipticityRatio_eq_Λ ``Submission.DeGiorgi.NormalizedEllipticCoeff.ellipticityRatio_eq_Λ

end NormalizedEllipticCoeff

end DeGiorgi
