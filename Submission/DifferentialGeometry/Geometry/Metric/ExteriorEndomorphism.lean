import Submission.DifferentialGeometry.Geometry.Metric.ExteriorPowerSmooth
import Submission.DifferentialGeometry.Tensor.Alternating.Block

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace exteriorPower
open _root_.exteriorPower

open scoped _root_.RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

open _root_.exteriorPower in
def ιMultiContinuous (k : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) (⋀[ℝ]^k E) :=
  { (_root_.exteriorPower.ιMulti ℝ k).toMultilinearMap with cont := (contDiff_ιMulti k 0).continuous }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.ιMultiContinuous then
    throwError "Refusing to shadow existing declaration exteriorPower.ιMultiContinuous"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.ιMultiContinuous ``Submission.exteriorPower.ιMultiContinuous

open _root_.exteriorPower in
@[simp] theorem ιMultiContinuous_apply (k : ℕ) (v : Fin k → E) :
    ιMultiContinuous k v = _root_.exteriorPower.ιMulti ℝ k v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.ιMultiContinuous_apply then
    throwError "Refusing to shadow existing declaration exteriorPower.ιMultiContinuous_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.ιMultiContinuous_apply ``Submission.exteriorPower.ιMultiContinuous_apply

open _root_.exteriorPower in
def endomorphismTensor (k : ℕ) (R : (⋀[ℝ]^k E) →L[ℝ] ⋀[ℝ]^k E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => E) ℝ :=
  (((ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ).comp
      ((musicalEquiv k).toContinuousLinearMap.comp R)).compContinuousMultilinearMap
        (ιMultiContinuous k)).uncurrySum.domDomCongr finSumFinEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.endomorphismTensor then
    throwError "Refusing to shadow existing declaration exteriorPower.endomorphismTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.endomorphismTensor ``Submission.exteriorPower.endomorphismTensor

open _root_.exteriorPower in
theorem endomorphismTensor_apply (k : ℕ)
    (R : (⋀[ℝ]^k E) →L[ℝ] ⋀[ℝ]^k E) (v : Fin (k + k) → E) :
    endomorphismTensor k R v =
      ⟪R (_root_.exteriorPower.ιMulti ℝ k (v ∘ Fin.castAdd k)), _root_.exteriorPower.ιMulti ℝ k (v ∘ Fin.natAdd k)⟫ := by
  simp only [endomorphismTensor, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply]
  exact musicalEquiv_apply k _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.endomorphismTensor_apply then
    throwError "Refusing to shadow existing declaration exteriorPower.endomorphismTensor_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.endomorphismTensor_apply ``Submission.exteriorPower.endomorphismTensor_apply

open _root_.exteriorPower in
theorem endomorphismTensor_apply_append (k : ℕ)
    (R : (⋀[ℝ]^k E) →L[ℝ] ⋀[ℝ]^k E) (v w : Fin k → E) :
    endomorphismTensor k R (Fin.append v w) = ⟪R (_root_.exteriorPower.ιMulti ℝ k v), _root_.exteriorPower.ιMulti ℝ k w⟫ := by
  rw [endomorphismTensor_apply]
  simp only [Function.comp_def, Fin.append_left, Fin.append_right]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.endomorphismTensor_apply_append then
    throwError "Refusing to shadow existing declaration exteriorPower.endomorphismTensor_apply_append"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.endomorphismTensor_apply_append ``Submission.exteriorPower.endomorphismTensor_apply_append

open _root_.exteriorPower in
def endomorphismTensorLinear (k : ℕ) :
    ((⋀[ℝ]^k E) →L[ℝ] ⋀[ℝ]^k E) →ₗ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => E) ℝ where
  toFun := endomorphismTensor k
  map_add' R S := by
    ext v
    simp only [endomorphismTensor_apply, add_apply, inner_add_left]
  map_smul' c R := by
    ext v
    simp only [endomorphismTensor_apply, smul_apply,
      real_inner_smul_left, smul_eq_mul,
      RingHom.id_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.endomorphismTensorLinear then
    throwError "Refusing to shadow existing declaration exteriorPower.endomorphismTensorLinear"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.endomorphismTensorLinear ``Submission.exteriorPower.endomorphismTensorLinear

open _root_.exteriorPower in
theorem endomorphismTensor_injective (k : ℕ) :
    Function.Injective (endomorphismTensor (E := E) k) := by
  intro R S h
  apply ContinuousLinearMap.coe_injective
  apply _root_.exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  have hPair : innerₗ (⋀[ℝ]^k E) (R (_root_.exteriorPower.ιMulti ℝ k v)) =
      innerₗ (⋀[ℝ]^k E) (S (_root_.exteriorPower.ιMulti ℝ k v)) := by
    apply _root_.exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro z
    have hh := congrArg (fun T => T (Fin.append v z)) h
    simpa only [endomorphismTensor_apply_append, LinearMap.compAlternatingMap_apply,
      innerₗ_apply_apply] using hh
  exact LinearMap.congr_fun hPair w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.endomorphismTensor_injective then
    throwError "Refusing to shadow existing declaration exteriorPower.endomorphismTensor_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.endomorphismTensor_injective ``Submission.exteriorPower.endomorphismTensor_injective

open _root_.exteriorPower in
theorem isSymmetric_iff_endomorphismTensor (k : ℕ)
    (R : (⋀[ℝ]^k E) →L[ℝ] ⋀[ℝ]^k E) :
    R.toLinearMap.IsSymmetric ↔ ∀ (v w : Fin k → E),
      endomorphismTensor k R (Fin.append v w) =
        endomorphismTensor k R (Fin.append w v) := by
  constructor
  · intro h v w
    simpa only [endomorphismTensor_apply_append, ContinuousLinearMap.coe_coe,
      real_inner_comm] using h (_root_.exteriorPower.ιMulti ℝ k v) (_root_.exteriorPower.ιMulti ℝ k w)
  · intro h u z
    have heq : (innerₗ (⋀[ℝ]^k E)).comp R.toLinearMap =
        (innerₗ (⋀[ℝ]^k E)).flip.compl₂ R.toLinearMap := by
      apply _root_.exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro v
      apply _root_.exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro w
      simpa only [endomorphismTensor_apply_append, LinearMap.compAlternatingMap_apply,
        LinearMap.coe_comp, Function.comp_apply, innerₗ_apply_apply,
        LinearMap.flip_apply, LinearMap.compl₂_apply, ContinuousLinearMap.coe_coe,
        real_inner_comm] using h v w
    simpa only [LinearMap.coe_comp, Function.comp_apply, innerₗ_apply_apply,
      LinearMap.flip_apply, LinearMap.compl₂_apply, real_inner_comm] using
      LinearMap.congr_fun (LinearMap.congr_fun heq u) z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.isSymmetric_iff_endomorphismTensor then
    throwError "Refusing to shadow existing declaration exteriorPower.isSymmetric_iff_endomorphismTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.isSymmetric_iff_endomorphismTensor ``Submission.exteriorPower.isSymmetric_iff_endomorphismTensor

end exteriorPower

namespace exteriorPower
open _root_.exteriorPower

open scoped _root_.RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

open _root_.exteriorPower in
def alternatingEndomorphism (k : ℕ)
    (A : E [⋀^Fin k]→L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ) :
    (⋀[ℝ]^k E) →L[ℝ] ⋀[ℝ]^k E :=
  (_root_.exteriorPower.alternatingMapLinearEquiv
    (((musicalEquiv k).symm.toContinuousLinearMap).compContinuousAlternatingMap A).toAlternatingMap
    ).toContinuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.alternatingEndomorphism then
    throwError "Refusing to shadow existing declaration exteriorPower.alternatingEndomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.alternatingEndomorphism ``Submission.exteriorPower.alternatingEndomorphism

open _root_.exteriorPower in
theorem alternatingEndomorphism_apply_ιMulti (k : ℕ)
    (A : E [⋀^Fin k]→L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) :
    alternatingEndomorphism k A (_root_.exteriorPower.ιMulti ℝ k v) = (musicalEquiv k).symm (A v) :=
  _root_.exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.alternatingEndomorphism_apply_ιMulti then
    throwError "Refusing to shadow existing declaration exteriorPower.alternatingEndomorphism_apply_ιMulti"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.alternatingEndomorphism_apply_ιMulti ``Submission.exteriorPower.alternatingEndomorphism_apply_ιMulti

open _root_.exteriorPower in
theorem endomorphismTensor_alternatingEndomorphism_apply_append (k : ℕ)
    (A : E [⋀^Fin k]→L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ) (v w : Fin k → E) :
    endomorphismTensor k (alternatingEndomorphism k A) (Fin.append v w) = A v w := by
  rw [endomorphismTensor_apply_append, alternatingEndomorphism_apply_ιMulti,
    inner_musicalEquiv_symm_ιMulti]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.endomorphismTensor_alternatingEndomorphism_apply_append then
    throwError "Refusing to shadow existing declaration exteriorPower.endomorphismTensor_alternatingEndomorphism_apply_append"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.endomorphismTensor_alternatingEndomorphism_apply_append ``Submission.exteriorPower.endomorphismTensor_alternatingEndomorphism_apply_append

open _root_.exteriorPower in
def multilinearEndomorphism (k : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => E) ℝ)
    (hleft : ∀ (v w : Fin k → E) (i j : Fin k), i ≠ j → v i = v j →
      T (Fin.append v w) = 0) : (⋀[ℝ]^k E) →L[ℝ] ⋀[ℝ]^k E :=
  alternatingEndomorphism k (ContinuousMultilinearMap.toBlockAlternating k k T hleft)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.multilinearEndomorphism then
    throwError "Refusing to shadow existing declaration exteriorPower.multilinearEndomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.multilinearEndomorphism ``Submission.exteriorPower.multilinearEndomorphism

open _root_.exteriorPower in
theorem endomorphismTensor_multilinearEndomorphism (k : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => E) ℝ)
    (hleft : ∀ (v w : Fin k → E) (i j : Fin k), i ≠ j → v i = v j →
      T (Fin.append v w) = 0)
    (hright : ∀ (v w : Fin k → E) (i j : Fin k), i ≠ j → w i = w j →
      T (Fin.append v w) = 0) :
    endomorphismTensor k (multilinearEndomorphism k T hleft) = T := by
  ext z
  have hz : Fin.append (z ∘ Fin.castAdd k) (z ∘ Fin.natAdd k) = z := by
    funext i
    exact Fin.addCases (fun j => Fin.append_left _ _ j) (fun j => Fin.append_right _ _ j) i
  rw [← hz]
  exact (endomorphismTensor_alternatingEndomorphism_apply_append k
    (ContinuousMultilinearMap.toBlockAlternating k k T hleft) _ _).trans
      (ContinuousMultilinearMap.toBlockAlternating_apply k k T hleft hright _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.endomorphismTensor_multilinearEndomorphism then
    throwError "Refusing to shadow existing declaration exteriorPower.endomorphismTensor_multilinearEndomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.endomorphismTensor_multilinearEndomorphism ``Submission.exteriorPower.endomorphismTensor_multilinearEndomorphism

open _root_.exteriorPower in
theorem multilinearEndomorphism_isSymmetric (k : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => E) ℝ)
    (hleft : ∀ (v w : Fin k → E) (i j : Fin k), i ≠ j → v i = v j →
      T (Fin.append v w) = 0)
    (hright : ∀ (v w : Fin k → E) (i j : Fin k), i ≠ j → w i = w j →
      T (Fin.append v w) = 0)
    (hpair : ∀ v w : Fin k → E, T (Fin.append v w) = T (Fin.append w v)) :
    (multilinearEndomorphism k T hleft).toLinearMap.IsSymmetric := by
  rw [isSymmetric_iff_endomorphismTensor,
    endomorphismTensor_multilinearEndomorphism k T hleft hright]
  exact hpair

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.multilinearEndomorphism_isSymmetric then
    throwError "Refusing to shadow existing declaration exteriorPower.multilinearEndomorphism_isSymmetric"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.multilinearEndomorphism_isSymmetric ``Submission.exteriorPower.multilinearEndomorphism_isSymmetric

end exteriorPower
