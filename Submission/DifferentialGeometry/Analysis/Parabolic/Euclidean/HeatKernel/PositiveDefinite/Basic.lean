import Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.Convolution.LinearChangeOfVariables
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Matrix _root_.Real
open scoped _root_.MatrixOrder _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section PositiveDefinite

variable {n : Type*} [Fintype n] [DecidableEq n]
private abbrev matrixCLM (A : Matrix n n ℝ) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
  Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.matrixCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Euclidean.matrixCLM target :: scope.openDecls } }
def spdSqrtEquiv (A : Matrix n n ℝ) (hA : A.PosDef) :
    EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n :=
  let S := CFC.sqrt A
  let hS : S.PosDef := hA.isStrictlyPositive.sqrt.posDef
  let L := matrixCLM S
  have hunit : IsUnit S :=
    (Matrix.isUnit_iff_isUnit_det S).mpr
      (isUnit_iff_ne_zero.mpr hS.det_pos.ne')
  have hinj : Function.Injective L := by
    intro x y hxy
    apply WithLp.ofLp_injective
    apply Matrix.mulVec_injective_of_isUnit hunit
    simpa only [L, matrixCLM, Matrix.ofLp_toEuclideanCLM] using
      congrArg WithLp.ofLp hxy
  ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr
      (L.toLinearMap.surjective_of_injective hinj))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrtEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrtEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrtEquiv ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrtEquiv

@[simp]
theorem spdSqrtEquiv_apply (A : Matrix n n ℝ) (hA : A.PosDef)
    (x : EuclideanSpace ℝ n) :
    spdSqrtEquiv A hA x =
      matrixCLM (CFC.sqrt A) x := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrtEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrtEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrtEquiv_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrtEquiv_apply

theorem spdSqrt_comp (A : Matrix n n ℝ) (hA : A.PosDef)
    (x : EuclideanSpace ℝ n) :
    spdSqrtEquiv A hA (spdSqrtEquiv A hA x) =
      matrixCLM A x := by
  simp only [spdSqrtEquiv_apply]
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
    CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_comp ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_comp

theorem spdSqrt_selfAdj (A : Matrix n n ℝ) (hA : A.PosDef) :
    IsSelfAdjoint
      (spdSqrtEquiv A hA : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) := by
  have heq :
      (spdSqrtEquiv A hA : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) =
        matrixCLM (CFC.sqrt A) := by
    apply ContinuousLinearMap.ext
    intro x
    exact spdSqrtEquiv_apply A hA x
  rw [heq]
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  rw [show
    (matrixCLM (CFC.sqrt A) :
      EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n) =
        Matrix.toEuclideanLin (CFC.sqrt A) from
      Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (CFC.sqrt A)]
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (CFC.sqrt_nonneg A).isSelfAdjoint.isHermitian

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_selfAdj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_selfAdj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_selfAdj ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_selfAdj
theorem spdSqrt_norm_sq (A : Matrix n n ℝ) (hA : A.PosDef)
    (x : EuclideanSpace ℝ n) :
    ‖spdSqrtEquiv A hA x‖ ^ 2 =
      inner ℝ x (matrixCLM A x) := by
  calc
    ‖spdSqrtEquiv A hA x‖ ^ 2 =
        inner ℝ (spdSqrtEquiv A hA x) (spdSqrtEquiv A hA x) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = _root_.Inner.inner ℝ x (spdSqrtEquiv A hA (spdSqrtEquiv A hA x)) :=
      (spdSqrt_selfAdj A hA).isSymmetric x (spdSqrtEquiv A hA x)
    _ = _root_.Inner.inner ℝ x (matrixCLM A x) := by
      rw [spdSqrt_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_norm_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_norm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_norm_sq ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_norm_sq

theorem spdSqrt_det (A : Matrix n n ℝ) (hA : A.PosDef) :
    LinearMap.det
        ((spdSqrtEquiv A hA : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :
          EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n) =
      Real.sqrt A.det := by
  let b := (EuclideanSpace.basisFun n ℝ).toBasis
  have hlin :
      ((spdSqrtEquiv A hA : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :
        EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n) =
        Matrix.toLin b b (CFC.sqrt A) := by
    apply LinearMap.ext
    intro x
    change spdSqrtEquiv A hA x = Matrix.toLin b b (CFC.sqrt A) x
    rw [spdSqrtEquiv_apply]
    rfl
  calc
    LinearMap.det
        ((spdSqrtEquiv A hA : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :
          EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n) =
        (LinearMap.toMatrix b b
          ((spdSqrtEquiv A hA : EuclideanSpace ℝ n →L[ℝ]
            EuclideanSpace ℝ n) : EuclideanSpace ℝ n →ₗ[ℝ]
              EuclideanSpace ℝ n)).det :=
      (LinearMap.det_toMatrix b _).symm
    _ = (CFC.sqrt A).det := by rw [hlin, LinearMap.toMatrix_toLin]
    _ = Real.sqrt A.det := by simpa using hA.posSemidef.det_sqrt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_det then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_det"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_det ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_det

theorem gaussSPD_int (A : Matrix n n ℝ) (hA : A.PosDef) :
    ∫ x : EuclideanSpace ℝ n,
        Real.exp (-_root_.Inner.inner ℝ x (matrixCLM A x)) =
      (Real.sqrt A.det)⁻¹ *
        (Real.pi : ℝ) ^ (Fintype.card n / 2 : ℝ) := by
  let L := spdSqrtEquiv A hA
  let f : EuclideanSpace ℝ n → ℝ := fun y => Real.exp (-‖y‖ ^ 2)
  have hdet : LinearMap.det (L : EuclideanSpace ℝ n →ₗ[ℝ]
      EuclideanSpace ℝ n) = Real.sqrt A.det := spdSqrt_det A hA
  have hdet_pos : 0 < LinearMap.det (L : EuclideanSpace ℝ n →ₗ[ℝ]
      EuclideanSpace ℝ n) := hdet ▸ Real.sqrt_pos.2 hA.det_pos
  have hmap : MeasureTheory.Measure.map
      (L : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ n)) =
        ENNReal.ofReal ((LinearMap.det (L : EuclideanSpace ℝ n →ₗ[ℝ]
          EuclideanSpace ℝ n))⁻¹) • MeasureTheory.volume := by
    simpa [abs_of_pos hdet_pos] using
      MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ n)) hdet_pos.ne'
  calc
    ∫ x : EuclideanSpace ℝ n, Real.exp (-_root_.Inner.inner ℝ x (matrixCLM A x)) =
        ∫ x : EuclideanSpace ℝ n, f (L x) := by
          congr 1
          funext x
          simp only [f, L, spdSqrt_norm_sq]
    _ = ∫ y : EuclideanSpace ℝ n, f y ∂MeasureTheory.Measure.map
          (L : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n)
          MeasureTheory.volume := by
            rw [MeasureTheory.integral_map]
            · rfl
            · exact (L : EuclideanSpace ℝ n →L[ℝ]
                EuclideanSpace ℝ n).continuous.aemeasurable
            · exact Real.continuous_exp.comp
                (continuous_neg.comp (continuous_norm.pow 2)) |>.aestronglyMeasurable
    _ = (LinearMap.det (L : EuclideanSpace ℝ n →ₗ[ℝ]
          EuclideanSpace ℝ n))⁻¹ * ∫ y : EuclideanSpace ℝ n, f y := by
            rw [hmap, MeasureTheory.integral_smul_measure]
            simp [ENNReal.toReal_ofReal, hdet_pos.le, smul_eq_mul]
    _ = (Real.sqrt A.det)⁻¹ *
        (Real.pi : ℝ) ^ (Fintype.card n / 2 : ℝ) := by
          rw [hdet]
          simp only [f]
          have hg := GaussianFourier.integral_rexp_neg_mul_sq_norm
            (V := EuclideanSpace ℝ n) (b := 1) zero_lt_one
          simpa only [neg_one_mul, div_one, finrank_euclideanSpace] using
            congrArg (fun z => (Real.sqrt A.det)⁻¹ * z) hg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.gaussSPD_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.gaussSPD_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.gaussSPD_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.gaussSPD_int

theorem spdSqrt_apply_le (A : Matrix n n ℝ) (hA : A.PosDef)
    {ellMax : ℝ} (hMax : 0 ≤ ellMax)
    (hupper : ∀ x : EuclideanSpace ℝ n,
      _root_.Inner.inner ℝ x (matrixCLM A x) ≤ ellMax * ‖x‖ ^ 2)
    (x : EuclideanSpace ℝ n) :
    ‖spdSqrtEquiv A hA x‖ ≤ √ellMax * ‖x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (_root_.Real.sqrt_nonneg _) (norm_nonneg _)),
    spdSqrt_norm_sq, mul_pow, Real.sq_sqrt hMax]
  exact hupper x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_apply_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_apply_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_apply_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_apply_le

theorem spdSqrt_norm_le (A : Matrix n n ℝ) (hA : A.PosDef)
    {ellMax : ℝ} (hMax : 0 ≤ ellMax)
    (hupper : ∀ x : EuclideanSpace ℝ n,
      _root_.Inner.inner ℝ x (matrixCLM A x) ≤ ellMax * ‖x‖ ^ 2) :
    ‖(spdSqrtEquiv A hA : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)‖ ≤
      √ellMax := by
  exact ContinuousLinearMap.opNorm_le_bound _ (_root_.Real.sqrt_nonneg ellMax)
    (spdSqrt_apply_le A hA hMax hupper)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_norm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_norm_le

theorem spdSqrt_symm_le (A : Matrix n n ℝ) (hA : A.PosDef)
    {ellMin : ℝ} (hMin : 0 < ellMin)
    (hlower : ∀ x : EuclideanSpace ℝ n,
      ellMin * ‖x‖ ^ 2 ≤ _root_.Inner.inner ℝ x (matrixCLM A x))
    (y : EuclideanSpace ℝ n) :
    ‖(spdSqrtEquiv A hA).symm y‖ ≤ (√ellMin)⁻¹ * ‖y‖ := by
  have hsq := hlower ((spdSqrtEquiv A hA).symm y)
  rw [← spdSqrt_norm_sq A hA,
    ContinuousLinearEquiv.apply_symm_apply] at hsq
  rw [inv_mul_eq_div, le_div_iff₀ (Real.sqrt_pos.2 hMin)]
  have hsqrt :
      √ellMin * ‖(spdSqrtEquiv A hA).symm y‖ ≤ ‖y‖ := by
    rw [← sq_le_sq₀
      (mul_nonneg (_root_.Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _),
      mul_pow, Real.sq_sqrt hMin.le]
    exact hsq
  simpa [mul_comm] using hsqrt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_symm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_symm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_symm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_symm_le

theorem spdSqrt_inv_le (A : Matrix n n ℝ) (hA : A.PosDef)
    {ellMin : ℝ} (hMin : 0 < ellMin)
    (hlower : ∀ x : EuclideanSpace ℝ n,
      ellMin * ‖x‖ ^ 2 ≤ _root_.Inner.inner ℝ x (matrixCLM A x)) :
    ‖((spdSqrtEquiv A hA).symm :
      EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)‖ ≤ (√ellMin)⁻¹ := by
  exact ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (_root_.Real.sqrt_nonneg ellMin))
    (spdSqrt_symm_le A hA hMin hlower)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_inv_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_inv_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_inv_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.spdSqrt_inv_le

end PositiveDefinite

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry
