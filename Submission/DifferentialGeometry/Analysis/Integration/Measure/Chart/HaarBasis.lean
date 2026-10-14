import Submission.DifferentialGeometry.Tensor.BilinearForm
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory
open scoped _root_.ENNReal

namespace Module.Basis
open _root_.Module _root_.Module.Basis

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

open _root_.Module _root_.Module.Basis in
theorem det_smul_addHaar (b b' : _root_.Module.Basis ι ℝ E) :
    ENNReal.ofReal |b.det b'| • b'.addHaar = b.addHaar := by
  change Real.toNNReal |b.det b'| • b'.addHaar = b.addHaar
  rw [eq_comm, b.addHaar_eq_iff]
  simp only [Measure.smul_apply, Basis.coe_parallelepiped,
    Measure.addHaar_parallelepiped,
    ENNReal.smul_def, smul_eq_mul, ENNReal.ofNNReal_toNNReal]
  rw [← ENNReal.ofReal_mul (abs_nonneg (b.det b')), ← abs_mul,
    b.det_mul_det b' b, b.det_self, abs_one, ENNReal.ofReal_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Module.Basis.det_smul_addHaar then
    throwError "Refusing to shadow existing declaration Module.Basis.det_smul_addHaar"
  Lean.modifyEnv fun env => Lean.addAlias env `Module.Basis.det_smul_addHaar ``Submission.Module.Basis.det_smul_addHaar

open _root_.Module _root_.Module.Basis in
theorem lintegral_basis_det (b b' : _root_.Module.Basis ι ℝ E) (f : E → ENNReal) :
    (∫⁻ x, f x ∂b.addHaar) =
      ∫⁻ x, ENNReal.ofReal |b.det b'| * f x ∂b'.addHaar := by
  rw [← det_smul_addHaar b b', _root_.MeasureTheory.lintegral_smul_measure]
  exact (_root_.MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Module.Basis.lintegral_basis_det then
    throwError "Refusing to shadow existing declaration Module.Basis.lintegral_basis_det"
  Lean.modifyEnv fun env => Lean.addAlias env `Module.Basis.lintegral_basis_det ``Submission.Module.Basis.lintegral_basis_det

end Module.Basis

namespace LinearMap.BilinForm
open _root_.LinearMap _root_.LinearMap.BilinForm

open _root_.LinearMap _root_.LinearMap.BilinForm in
theorem sqrt_det_gram_eq_abs_det_mul_sqrt_det_toMatrix
    {V i : Type*} [AddCommGroup V] [Module Real V]
    [Fintype i] [DecidableEq i] (B : LinearMap.BilinForm Real V) (b : Module.Basis i Real V)
    (v : i → V) :
    Real.sqrt (Matrix.of fun i j => B (v i) (v j)).det =
      |b.det v| * Real.sqrt (_root_.LinearMap.BilinForm.toMatrix b B).det := by
  rw [B.det_gram_eq_sq_mul_det_toMatrix b v, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LinearMap.BilinForm.sqrt_det_gram_eq_abs_det_mul_sqrt_det_toMatrix then
    throwError "Refusing to shadow existing declaration LinearMap.BilinForm.sqrt_det_gram_eq_abs_det_mul_sqrt_det_toMatrix"
  Lean.modifyEnv fun env => Lean.addAlias env `LinearMap.BilinForm.sqrt_det_gram_eq_abs_det_mul_sqrt_det_toMatrix ``Submission.LinearMap.BilinForm.sqrt_det_gram_eq_abs_det_mul_sqrt_det_toMatrix

open _root_.LinearMap _root_.LinearMap.BilinForm in
theorem sqrt_det_toMatrix_basis_change
    {E i : Type*} [AddCommGroup E] [Module Real E]
    [Fintype i] [DecidableEq i] (B : LinearMap.BilinForm Real E) (b c : Module.Basis i Real E) :
    Real.sqrt (_root_.LinearMap.BilinForm.toMatrix c B).det = |b.det c| * Real.sqrt (_root_.LinearMap.BilinForm.toMatrix b B).det := by
  rw [B.det_toMatrix_basis_change b c, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LinearMap.BilinForm.sqrt_det_toMatrix_basis_change then
    throwError "Refusing to shadow existing declaration LinearMap.BilinForm.sqrt_det_toMatrix_basis_change"
  Lean.modifyEnv fun env => Lean.addAlias env `LinearMap.BilinForm.sqrt_det_toMatrix_basis_change ``Submission.LinearMap.BilinForm.sqrt_det_toMatrix_basis_change

open _root_.LinearMap _root_.LinearMap.BilinForm in
theorem sqrt_det_smul_addHaar_eq
    {E i : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
    [MeasurableSpace E] [BorelSpace E] [Fintype i] [DecidableEq i]
    (B : LinearMap.BilinForm Real E) (b c : Module.Basis i Real E) :
    ENNReal.ofReal (Real.sqrt (_root_.LinearMap.BilinForm.toMatrix b B).det) • b.addHaar =
      ENNReal.ofReal (Real.sqrt (_root_.LinearMap.BilinForm.toMatrix c B).det) • c.addHaar := by
  rw [B.sqrt_det_toMatrix_basis_change b c, ENNReal.ofReal_mul (abs_nonneg _),
    mul_comm, _root_.SemigroupAction.mul_smul, Module.Basis.det_smul_addHaar]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LinearMap.BilinForm.sqrt_det_smul_addHaar_eq then
    throwError "Refusing to shadow existing declaration LinearMap.BilinForm.sqrt_det_smul_addHaar_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `LinearMap.BilinForm.sqrt_det_smul_addHaar_eq ``Submission.LinearMap.BilinForm.sqrt_det_smul_addHaar_eq

end LinearMap.BilinForm
