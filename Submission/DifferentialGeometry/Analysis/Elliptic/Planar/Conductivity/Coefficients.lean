import Submission.DifferentialGeometry.Analysis.Complex.Beltrami.Coefficient
import Submission.DifferentialGeometry.Analysis.Elliptic.Coefficients
import Mathlib.LinearAlgebra.Matrix.Adjugate

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Matrix
open scoped _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis

def planarConductivity (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt (a * b - c ^ 2))⁻¹ • !![b, -c; -c, a]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.planarConductivity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.planarConductivity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.planarConductivity ``Submission.DifferentialGeometry.Analysis.planarConductivity

theorem planarConductivity_posDef {a b c : ℝ} (ha : 0 < a) (hd : 0 < a * b - c ^ 2) :
    (planarConductivity a b c).PosDef := by
  have hs : 0 < Real.sqrt (a * b - c ^ 2) := Real.sqrt_pos.mpr hd
  have hab : 0 < b := by nlinarith [sq_nonneg c]
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [planarConductivity, Matrix.transpose_apply]
  · intro v hv
    have hquad : 0 < b * v 0 ^ 2 - 2 * c * v 0 * v 1 + a * v 1 ^ 2 := by
      have hsum : a * (b * v 0 ^ 2 - 2 * c * v 0 * v 1 + a * v 1 ^ 2) =
          (a * b - c ^ 2) * v 0 ^ 2 + (a * v 1 - c * v 0) ^ 2 := by ring
      by_cases h0 : v 0 = 0
      · have h1 : v 1 ≠ 0 := by
          intro h1
          apply hv
          ext i
          fin_cases i <;> simp [h0, h1]
        simp only [h0, zero_pow (by decide : 2 ≠ 0), _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.zero_mul, sub_zero, zero_add]
        exact mul_pos ha (sq_pos_of_ne_zero h1)
      · have hp := mul_pos hd (sq_pos_of_ne_zero h0)
        nlinarith [sq_nonneg (a * v 1 - c * v 0)]
    have hp := mul_pos (inv_pos.mpr hs) hquad
    convert hp using 1
    simp [planarConductivity, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.planarConductivity_posDef then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.planarConductivity_posDef"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.planarConductivity_posDef ``Submission.DifferentialGeometry.Analysis.planarConductivity_posDef

theorem planarConductivity_eq_sqrt_det_smul_inv {a b c : ℝ}
    (hd : 0 < a * b - c ^ 2) :
    planarConductivity a b c = Real.sqrt (!![a, c; c, b] : Matrix (Fin 2) (Fin 2) ℝ).det •
      (!![a, c; c, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ := by
  have hs : Real.sqrt (a * b - c ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have hs2 := Real.sq_sqrt hd.le
  have hmat : (!![a, c; c, b] : Matrix (Fin 2) (Fin 2) ℝ).det = a * b - c ^ 2 := by
    simp [Matrix.det_fin_two, pow_two]
  rw [Matrix.inv_def, hmat, Matrix.adjugate_fin_two]
  simp only [Ring.inverse_eq_inv', smul_smul]
  have hcoef : Real.sqrt (a * b - c ^ 2) * (a * b - c ^ 2)⁻¹ =
      (Real.sqrt (a * b - c ^ 2))⁻¹ := by
    apply (mul_right_cancel₀ hs)
    rw [inv_mul_cancel₀ hs]
    have hh : Real.sqrt (a * b - c ^ 2) * (a * b - c ^ 2)⁻¹ *
        Real.sqrt (a * b - c ^ 2) = (Real.sqrt (a * b - c ^ 2)) ^ 2 * (a * b - c ^ 2)⁻¹ := by ring
    rw [hh, hs2, mul_inv_cancel₀ hd.ne']
  rw [hcoef]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planarConductivity]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.planarConductivity_eq_sqrt_det_smul_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.planarConductivity_eq_sqrt_det_smul_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.planarConductivity_eq_sqrt_det_smul_inv ``Submission.DifferentialGeometry.Analysis.planarConductivity_eq_sqrt_det_smul_inv

theorem contDiffOn_planarConductivity
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : Set X} {a b c : X → ℝ}
    {n : ℕ∞ω} (ha : ContDiffOn ℝ n a s) (hb : ContDiffOn ℝ n b s)
    (hc : ContDiffOn ℝ n c s) (hd : ∀ x ∈ s, 0 < a x * b x - c x ^ 2) (i j : Fin 2) :
    ContDiffOn ℝ n (fun x => planarConductivity (a x) (b x) (c x) i j) s := by
  have hh := ((ha.mul hb).sub (hc.pow 2)).sqrt (fun x hx => (hd x hx).ne')
  have hi := hh.inv (fun x hx => (Real.sqrt_pos.mpr (hd x hx)).ne')
  fin_cases i <;> fin_cases j
  · change ContDiffOn ℝ n (fun x => (Real.sqrt (a x * b x - c x ^ 2))⁻¹ * b x) s
    exact hi.mul hb
  · change ContDiffOn ℝ n (fun x => (Real.sqrt (a x * b x - c x ^ 2))⁻¹ * (-c x)) s
    exact hi.mul hc.neg
  · change ContDiffOn ℝ n (fun x => (Real.sqrt (a x * b x - c x ^ 2))⁻¹ * (-c x)) s
    exact hi.mul hc.neg
  · change ContDiffOn ℝ n (fun x => (Real.sqrt (a x * b x - c x ^ 2))⁻¹ * a x) s
    exact hi.mul ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiffOn_planarConductivity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiffOn_planarConductivity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiffOn_planarConductivity ``Submission.DifferentialGeometry.Analysis.contDiffOn_planarConductivity

end DifferentialGeometry.Analysis

end

end

section

noncomputable section

namespace DifferentialGeometry.Analysis

theorem det_planarConductivity {a b c : ℝ} (hdet : 0 < a * b - c ^ 2) :
    (planarConductivity a b c).det = 1 := by
  have hs : Real.sqrt (a * b - c ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hdet).ne'
  have hs2 := Real.sq_sqrt hdet.le
  simp only [planarConductivity, Matrix.det_fin_two]
  change (Real.sqrt (a * b - c ^ 2))⁻¹ * b * ((Real.sqrt (a * b - c ^ 2))⁻¹ * a) -
    (Real.sqrt (a * b - c ^ 2))⁻¹ * (-c) * ((Real.sqrt (a * b - c ^ 2))⁻¹ * (-c)) = 1
  field_simp [hs]
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.det_planarConductivity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.det_planarConductivity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.det_planarConductivity ``Submission.DifferentialGeometry.Analysis.det_planarConductivity

end DifferentialGeometry.Analysis

end

end
