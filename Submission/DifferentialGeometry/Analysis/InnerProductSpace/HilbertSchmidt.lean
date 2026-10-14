import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace OrthonormalBasis
open _root_.OrthonormalBasis

variable {𝕜 U V : Type*} [RCLike 𝕜] [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {ι : Type*} [Fintype ι]

open _root_.OrthonormalBasis in
def continuousLinearMapEquiv (b : OrthonormalBasis ι 𝕜 U) :
    (U →L[𝕜] V) ≃L[𝕜] PiLp 2 (fun _ : ι => V) := by
  classical
  exact ((b.toBasis.equivFunL.arrowCongr (ContinuousLinearEquiv.refl 𝕜 V)).trans
    (ContinuousLinearEquiv.piRing ι)).trans
    (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => V)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrthonormalBasis.continuousLinearMapEquiv then
    throwError "Refusing to shadow existing declaration OrthonormalBasis.continuousLinearMapEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `OrthonormalBasis.continuousLinearMapEquiv ``Submission.OrthonormalBasis.continuousLinearMapEquiv

open _root_.OrthonormalBasis in
@[simp] theorem continuousLinearMapEquiv_apply (b : OrthonormalBasis ι 𝕜 U)
    (A : U →L[𝕜] V) (i : ι) : b.continuousLinearMapEquiv A i = A (b i) := by
  classical
  change A (b.toBasis.equivFunL.symm (Pi.single i 1)) = A (b i)
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrthonormalBasis.continuousLinearMapEquiv_apply then
    throwError "Refusing to shadow existing declaration OrthonormalBasis.continuousLinearMapEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `OrthonormalBasis.continuousLinearMapEquiv_apply ``Submission.OrthonormalBasis.continuousLinearMapEquiv_apply

end OrthonormalBasis

namespace ContinuousLinearMap
open _root_.ContinuousLinearMap

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

open _root_.ContinuousLinearMap in
def hilbertSchmidtInner (A C : U →L[ℝ] V) : ℝ :=
  ∑ i, _root_.Inner.inner ℝ (A (stdOrthonormalBasis ℝ U i)) (C (stdOrthonormalBasis ℝ U i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.hilbertSchmidtInner then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.hilbertSchmidtInner"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.hilbertSchmidtInner ``Submission.ContinuousLinearMap.hilbertSchmidtInner

open _root_.ContinuousLinearMap in
theorem hilbertSchmidtInner_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ U) (A C : U →L[ℝ] V) :
    hilbertSchmidtInner A C = ∑ i, _root_.Inner.inner ℝ (A (b i)) (C (b i)) := by
  let L : U →ₗ[ℝ] U →ₗ[ℝ] ℝ :=
    LinearMap.compl₂ ((innerₗ V).comp A.toLinearMap) C.toLinearMap
  have h := congrArg (TensorProduct.lift L)
    (InnerProductSpace.canonicalCovariantTensor_eq_sum U b)
  simpa [InnerProductSpace.canonicalCovariantTensor, hilbertSchmidtInner, L] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.hilbertSchmidtInner_eq_sum then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.hilbertSchmidtInner_eq_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.hilbertSchmidtInner_eq_sum ``Submission.ContinuousLinearMap.hilbertSchmidtInner_eq_sum

open _root_.ContinuousLinearMap in
theorem hilbertSchmidtInner_eq_inner {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ U)
    (A C : U →L[ℝ] V) :
    hilbertSchmidtInner A C =
      inner ℝ (b.continuousLinearMapEquiv A) (b.continuousLinearMapEquiv C) := by
  rw [hilbertSchmidtInner_eq_sum b, PiLp.inner_apply]
  simp only [OrthonormalBasis.continuousLinearMapEquiv_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.hilbertSchmidtInner_eq_inner then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.hilbertSchmidtInner_eq_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.hilbertSchmidtInner_eq_inner ``Submission.ContinuousLinearMap.hilbertSchmidtInner_eq_inner

open _root_.ContinuousLinearMap in
theorem hilbertSchmidtInner_comm (A C : U →L[ℝ] V) :
    hilbertSchmidtInner A C = hilbertSchmidtInner C A := by
  simp only [hilbertSchmidtInner, real_inner_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.hilbertSchmidtInner_comm then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.hilbertSchmidtInner_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.hilbertSchmidtInner_comm ``Submission.ContinuousLinearMap.hilbertSchmidtInner_comm

open _root_.ContinuousLinearMap in
theorem hilbertSchmidtInner_self_pos {A : U →L[ℝ] V} (hA : A ≠ 0) :
    0 < hilbertSchmidtInner A A := by
  rw [hilbertSchmidtInner_eq_inner (stdOrthonormalBasis ℝ U)]
  apply real_inner_self_pos.mpr
  exact (stdOrthonormalBasis ℝ U).continuousLinearMapEquiv.injective.ne
    (by simpa using hA)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.hilbertSchmidtInner_self_pos then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.hilbertSchmidtInner_self_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.hilbertSchmidtInner_self_pos ``Submission.ContinuousLinearMap.hilbertSchmidtInner_self_pos

open _root_.ContinuousLinearMap in
theorem hilbertSchmidtInner_self_le_finrank_mul_norm_sq (A : U →L[ℝ] V) :
    A.hilbertSchmidtInner A ≤ Module.finrank ℝ U * ‖A‖ ^ 2 := by
  rw [hilbertSchmidtInner]
  calc
    _ ≤ ∑ _i : Fin (Module.finrank ℝ U), ‖A‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [real_inner_self_eq_norm_sq]
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
      simpa only [(stdOrthonormalBasis ℝ U).orthonormal.norm_eq_one i, mul_one] using
        A.le_opNorm ((stdOrthonormalBasis ℝ U) i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.hilbertSchmidtInner_self_le_finrank_mul_norm_sq then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.hilbertSchmidtInner_self_le_finrank_mul_norm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.hilbertSchmidtInner_self_le_finrank_mul_norm_sq ``Submission.ContinuousLinearMap.hilbertSchmidtInner_self_le_finrank_mul_norm_sq

open _root_.ContinuousLinearMap in
def hilbertSchmidtInnerSL : (U →L[ℝ] V) →L[ℝ] (U →L[ℝ] V) →L[ℝ] ℝ :=
  ∑ i, (innerSL ℝ (E := V)).bilinearComp
    (_root_.ContinuousLinearMap.apply ℝ V (stdOrthonormalBasis ℝ U i))
    (_root_.ContinuousLinearMap.apply ℝ V (stdOrthonormalBasis ℝ U i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.hilbertSchmidtInnerSL then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.hilbertSchmidtInnerSL"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.hilbertSchmidtInnerSL ``Submission.ContinuousLinearMap.hilbertSchmidtInnerSL

open _root_.ContinuousLinearMap in
@[simp] theorem hilbertSchmidtInnerSL_apply (A C : U →L[ℝ] V) :
    hilbertSchmidtInnerSL A C = hilbertSchmidtInner A C := by
  simp [hilbertSchmidtInnerSL, hilbertSchmidtInner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.hilbertSchmidtInnerSL_apply then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.hilbertSchmidtInnerSL_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.hilbertSchmidtInnerSL_apply ``Submission.ContinuousLinearMap.hilbertSchmidtInnerSL_apply

open _root_.ContinuousLinearMap in
theorem continuous_hilbertSchmidtInner :
    Continuous (fun p : (U →L[ℝ] V) × (U →L[ℝ] V) => hilbertSchmidtInner p.1 p.2) := by
  exact (hilbertSchmidtInnerSL (U := U) (V := V)).continuous₂.congr
    (fun p => hilbertSchmidtInnerSL_apply p.1 p.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.continuous_hilbertSchmidtInner then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.continuous_hilbertSchmidtInner"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.continuous_hilbertSchmidtInner ``Submission.ContinuousLinearMap.continuous_hilbertSchmidtInner

variable {U' V' : Type*} [NormedAddCommGroup U'] [InnerProductSpace ℝ U']
  [FiniteDimensional ℝ U'] [NormedAddCommGroup V'] [InnerProductSpace ℝ V']

open _root_.ContinuousLinearMap in
theorem hilbertSchmidtInner_congr (eU : U ≃ₗᵢ[ℝ] U') (eV : V →ₗᵢ[ℝ] V')
    (A C : U →L[ℝ] V) :
    hilbertSchmidtInner
        (eV.toContinuousLinearMap.comp (A.comp eU.symm.toContinuousLinearEquiv.toContinuousLinearMap))
        (eV.toContinuousLinearMap.comp (C.comp eU.symm.toContinuousLinearEquiv.toContinuousLinearMap)) =
      hilbertSchmidtInner A C := by
  rw [hilbertSchmidtInner_eq_sum ((stdOrthonormalBasis ℝ U).map eU)]
  simp only [OrthonormalBasis.map_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometry.inner_map_map, hilbertSchmidtInner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.hilbertSchmidtInner_congr then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.hilbertSchmidtInner_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.hilbertSchmidtInner_congr ``Submission.ContinuousLinearMap.hilbertSchmidtInner_congr

end ContinuousLinearMap


namespace ContinuousLinearMap
open _root_.ContinuousLinearMap

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

open _root_.ContinuousLinearMap in
theorem hilbertSchmidtInner_comp_right (A C : U →L[ℝ] V) (K : U →L[ℝ] U) :
    hilbertSchmidtInner (A.comp K) C = hilbertSchmidtInner A (C.comp K.adjoint) := by
  classical
  let b := stdOrthonormalBasis ℝ U
  rw [hilbertSchmidtInner_eq_sum b, hilbertSchmidtInner_eq_sum b]
  simp only [_root_.ContinuousLinearMap.comp_apply]
  have hleft (i) : _root_.Inner.inner ℝ (A (K (b i))) (C (b i)) =
      ∑ j, _root_.Inner.inner ℝ (b j) (K (b i)) * _root_.Inner.inner ℝ (A (b j)) (C (b i)) := by
    nth_rw 1 [← b.sum_repr' (K (b i))]
    rw [map_sum, sum_inner]
    simp only [map_smul, inner_smul_left, conj_trivial]
  have hright (i) : _root_.Inner.inner ℝ (A (b i)) (C (K.adjoint (b i))) =
      ∑ j, _root_.Inner.inner ℝ (b j) (K.adjoint (b i)) * _root_.Inner.inner ℝ (A (b i)) (C (b j)) := by
    nth_rw 1 [← b.sum_repr' (K.adjoint (b i))]
    rw [map_sum, inner_sum]
    simp only [map_smul, inner_smul_right]
  simp_rw [hleft, hright]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [K.adjoint_inner_right]
  rw [real_inner_comm (K (b j)) (b i)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.hilbertSchmidtInner_comp_right then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.hilbertSchmidtInner_comp_right"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.hilbertSchmidtInner_comp_right ``Submission.ContinuousLinearMap.hilbertSchmidtInner_comp_right


open _root_.ContinuousLinearMap in
theorem hilbertSchmidtInner_comp_add_eq_zero (A C : U →L[ℝ] V) (K : U →L[ℝ] U)
    (hK : K.adjoint = -K) :
    hilbertSchmidtInner (A.comp K) C + hilbertSchmidtInner A (C.comp K) = 0 := by
  rw [hilbertSchmidtInner_comp_right, hK, _root_.ContinuousLinearMap.comp_neg]
  rw [← hilbertSchmidtInnerSL_apply, ← hilbertSchmidtInnerSL_apply, map_neg]
  exact neg_add_cancel _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.hilbertSchmidtInner_comp_add_eq_zero then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.hilbertSchmidtInner_comp_add_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.hilbertSchmidtInner_comp_add_eq_zero ``Submission.ContinuousLinearMap.hilbertSchmidtInner_comp_add_eq_zero

end ContinuousLinearMap

open scoped _root_.RealInnerProductSpace

namespace ContinuousLinearMap
open _root_.ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

open _root_.ContinuousLinearMap in
theorem hilbertSchmidtInner_conjugate_of_inner_eq_mul (e : E ≃L[ℝ] F)
    (c : ℝ) (hc : 0 < c) (hinner : ∀ u v, ⟪e u, e v⟫ = c * ⟪u, v⟫)
    (A C : E →L[ℝ] E) :
    hilbertSchmidtInner
        (e.toContinuousLinearMap.comp (A.comp e.symm.toContinuousLinearMap))
        (e.toContinuousLinearMap.comp (C.comp e.symm.toContinuousLinearMap)) =
      hilbertSchmidtInner A C := by
  let s := Real.sqrt c
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hsq : s ^ 2 = c := Real.sq_sqrt hc.le
  have hcoeff : s⁻¹ * s⁻¹ * c = 1 := by
    rw [← hsq]
    field_simp
  let e₀ : E ≃ₗᵢ[ℝ] F :=
    (Units.mk0 s⁻¹ (inv_ne_zero hs) • e.toLinearEquiv).isometryOfInner (by
      intro u v
      simp only [LinearEquiv.smul_apply, Units.val_mk0, ContinuousLinearEquiv.coe_toLinearEquiv,
        real_inner_smul_left, real_inner_smul_right, hinner]
      calc
        s⁻¹ * (s⁻¹ * (c * ⟪u, v⟫)) = (s⁻¹ * s⁻¹ * c) * ⟪u, v⟫ := by ring
        _ = ⟪u, v⟫ := by rw [hcoeff, one_mul])
  have he₀ (u : E) : e₀ u = s⁻¹ • e u := rfl
  have he₀inv (v : F) : e₀.symm v = s • e.symm v := by
    apply e₀.injective
    rw [e₀.apply_symm_apply, he₀, map_smul, e.apply_symm_apply, smul_smul,
      inv_mul_cancel₀ hs, one_smul]
  have hconj (L : E →L[ℝ] E) :
      e₀.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (L.comp e₀.symm.toContinuousLinearEquiv.toContinuousLinearMap) =
        e.toContinuousLinearMap.comp (L.comp e.symm.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro v
    change e₀ (L (e₀.symm v)) = e (L (e.symm v))
    rw [he₀inv, he₀, map_smul, map_smul, smul_smul, inv_mul_cancel₀ hs, one_smul]
  have h := hilbertSchmidtInner_congr e₀ e₀.toLinearIsometry A C
  change hilbertSchmidtInner
      (e₀.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (A.comp e₀.symm.toContinuousLinearEquiv.toContinuousLinearMap))
      (e₀.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (C.comp e₀.symm.toContinuousLinearEquiv.toContinuousLinearMap)) = _ at h
  simpa only [hconj] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.hilbertSchmidtInner_conjugate_of_inner_eq_mul then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.hilbertSchmidtInner_conjugate_of_inner_eq_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.hilbertSchmidtInner_conjugate_of_inner_eq_mul ``Submission.ContinuousLinearMap.hilbertSchmidtInner_conjugate_of_inner_eq_mul

end ContinuousLinearMap
