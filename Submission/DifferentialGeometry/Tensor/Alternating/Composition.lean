/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
import Submission.DifferentialGeometry.Tensor.Multilinear.Composition
import Submission.DifferentialGeometry.Analysis.Calculus.AnalyticTransfer
import Submission.DifferentialGeometry.Tensor.Multilinear.Smoothness.LinearIsometry
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.ContinuousAlternatingMap

noncomputable section Comp

namespace ContinuousLinearMap
open _root_.ContinuousLinearMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {ι : Type*} [Fintype ι]
  {ι' : Type*} [Fintype ι']

open _root_.ContinuousLinearMap in
def compContinuousAlternatingMap₂ (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') : M [⋀^ι]→L[𝕜] M' [⋀^ι']→L[𝕜] N'' := by
  let F₁ : MultilinearMap 𝕜 (fun _ ↦ M) (M' [⋀^ι']→L[𝕜] N'') := MultilinearMap.mk
    (toFun := fun v => (f (g v)).compContinuousAlternatingMap h)
    (map_update_add' := fun m i x y => by
      simp only [ContinuousAlternatingMap.map_update_add, map_add]
      congr)
    (map_update_smul' := fun m i c x => by
      rw [ContinuousAlternatingMap.map_update_smul, ContinuousLinearMap.map_smul]
      congr)
  let F₂ : ContinuousMultilinearMap 𝕜 (fun _ ↦ M) (M' [⋀^ι']→L[𝕜] N'') :=
    F₁.mkContinuous (‖f‖ * ‖g‖ * ‖h‖) (H := by
      intro m
      unfold F₁
      simp only [MultilinearMap.coe_mk]
      apply ContinuousAlternatingMap.opNorm_le_bound
      · positivity
      intro m'
      simp only [_root_.ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply]
      calc
        ‖(f (g m)) (h m')‖ ≤ ‖f (g m)‖ * ‖h m'‖ := ContinuousLinearMap.le_opNorm (f (g m)) (h m')
        _ ≤ ‖f (g m)‖ * (‖h‖ * ∏ i, ‖m' i‖) := by
          apply mul_le_mul_of_nonneg_left
          · exact ContinuousAlternatingMap.le_opNorm h m'
          positivity
        _ ≤ ‖f‖ * ‖g m‖ * (‖h‖ * ∏ i, ‖m' i‖) := by
          apply mul_le_mul_of_nonneg_right
          · exact ContinuousLinearMap.le_opNorm f (g m)
          positivity
        _ ≤ ‖f‖ * (‖g‖ * ∏ i, ‖m i‖) * (‖h‖ * ∏ i, ‖m' i‖) := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left
            · exact ContinuousAlternatingMap.le_opNorm g m
            positivity
          positivity
        _ = (‖f‖ * ‖g‖ * ‖h‖ * ∏ i, ‖m i‖) * ∏ i, ‖m' i‖ := by ring)
  exact ContinuousAlternatingMap.mk F₂ (map_eq_zero_of_eq' := by
    intro v i j h₁ h₂
    simp only [MultilinearMap.toFun_eq_coe, ContinuousMultilinearMap.coe_coe,
      MultilinearMap.coe_mkContinuous, MultilinearMap.coe_mk, F₂, F₁]
    have : g v = 0 := g.map_eq_zero_of_eq' v i j h₁ h₂
    rw [this, ContinuousLinearMap.map_zero]
    ext v'
    rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.compContinuousAlternatingMap₂ then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.compContinuousAlternatingMap₂"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.compContinuousAlternatingMap₂ ``Submission.ContinuousLinearMap.compContinuousAlternatingMap₂

open _root_.ContinuousLinearMap in
theorem compContinuousAlternatingMap₂_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') (m : ι → M) (m' : ι' → M') :
    f.compContinuousAlternatingMap₂ g h m m' = f (g m) (h m') :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.compContinuousAlternatingMap₂_apply then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.compContinuousAlternatingMap₂_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.compContinuousAlternatingMap₂_apply ``Submission.ContinuousLinearMap.compContinuousAlternatingMap₂_apply

open _root_.ContinuousLinearMap in
theorem compContinuousAlternatingMap₂_mul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] 𝕜) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) * (h m') :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.compContinuousAlternatingMap₂_mul_apply then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.compContinuousAlternatingMap₂_mul_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.compContinuousAlternatingMap₂_mul_apply ``Submission.ContinuousLinearMap.compContinuousAlternatingMap₂_mul_apply

open _root_.ContinuousLinearMap in
theorem compContinuousAlternatingMap₂_lsmul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] N) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.lsmul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) • (h m') :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.compContinuousAlternatingMap₂_lsmul_apply then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.compContinuousAlternatingMap₂_lsmul_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.compContinuousAlternatingMap₂_lsmul_apply ``Submission.ContinuousLinearMap.compContinuousAlternatingMap₂_lsmul_apply

open _root_.LinearIsometry in
noncomputable def _root_.Submission.LinearIsometry.compLeft {𝕜 : Type*} {𝕜₂ : Type*}
    {𝕜₃ : Type*} (E : Type*) {F : Type*} {G : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃] [NormedSpace 𝕜 E]
    [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] (σ₁₂ : 𝕜 →+* 𝕜₂) {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃]
    [RingHomIsometric σ₁₃] (f : F →ₛₗᵢ[σ₂₃] G) :
    (E →SL[σ₁₂] F) →ₛₗᵢ[σ₂₃] (E →SL[σ₁₃] G) :=
  { ContinuousLinearMap.compSL _ _ _ _ _ f.toContinuousLinearMap with
    norm_map' := fun _ ↦ f.norm_toContinuousLinearMap_comp }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LinearIsometry.compLeft then
    throwError "Refusing to shadow existing declaration LinearIsometry.compLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `LinearIsometry.compLeft ``Submission.LinearIsometry.compLeft

omit [Fintype ι] in
open _root_.ContinuousLinearMap in
theorem compContinuousAlternatingMapCLM_cont [Finite ι] :
    Continuous (ContinuousAlternatingMap.compContinuousLinearMapCLM :
    (M →L[𝕜] M') → (M' [⋀^ι]→L[𝕜] N) →L[𝕜] (M [⋀^ι]→L[𝕜] N)) := by
  let := Fintype.ofFinite ι
  let φ : (M [⋀^ι]→L[𝕜] N) →ₗᵢ[𝕜] _ := ContinuousAlternatingMap.toContinuousMultilinearMapLI
  let Φ : ((M' [⋀^ι]→L[𝕜] N) →L[𝕜] (M [⋀^ι]→L[𝕜] N)) →ₗᵢ[𝕜] _ := φ.compLeft _ (RingHom.id _)
  rw [← Φ.comp_continuous_iff]
  change Continuous (fun p : M →L[𝕜] M' ↦
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ ↦ p) :
    ContinuousMultilinearMap 𝕜 (fun _ ↦ M') N →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ ↦ M) N).comp
    (ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜))
  exact Continuous.clm_comp compContinuousMultilinearMapL_diag_continuous continuous_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.compContinuousAlternatingMapCLM_cont then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.compContinuousAlternatingMapCLM_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.compContinuousAlternatingMapCLM_cont ``Submission.ContinuousLinearMap.compContinuousAlternatingMapCLM_cont

end ContinuousLinearMap

namespace ContinuousAlternatingMap
open _root_.ContinuousAlternatingMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {ι ι' : Type*}
variable
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  [Fintype ι] [Fintype ι']

open _root_.ContinuousAlternatingMap in
def compContinuousAlternatingMap₂ (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') : M [⋀^ι]→L[𝕜] M' [⋀^ι']→L[𝕜] N'' :=
  f.compContinuousAlternatingMap₂ g h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.compContinuousAlternatingMap₂ then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.compContinuousAlternatingMap₂"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.compContinuousAlternatingMap₂ ``Submission.ContinuousAlternatingMap.compContinuousAlternatingMap₂

open _root_.ContinuousAlternatingMap in
theorem compContinuousAlternatingMap₂_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') (m : ι → M) (m' : ι' → M') :
    f.compContinuousAlternatingMap₂ g h m m' = f (g m) (h m') :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.compContinuousAlternatingMap₂_apply then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.compContinuousAlternatingMap₂_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.compContinuousAlternatingMap₂_apply ``Submission.ContinuousAlternatingMap.compContinuousAlternatingMap₂_apply

open _root_.ContinuousAlternatingMap in
theorem compContinuousAlternatingMap₂_mul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] 𝕜) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) * (h m') :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.compContinuousAlternatingMap₂_mul_apply then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.compContinuousAlternatingMap₂_mul_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.compContinuousAlternatingMap₂_mul_apply ``Submission.ContinuousAlternatingMap.compContinuousAlternatingMap₂_mul_apply

open _root_.ContinuousAlternatingMap in
theorem compContinuousAlternatingMap₂_lsmul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] N) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.lsmul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) • (h m') :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.compContinuousAlternatingMap₂_lsmul_apply then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.compContinuousAlternatingMap₂_lsmul_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.compContinuousAlternatingMap₂_lsmul_apply ``Submission.ContinuousAlternatingMap.compContinuousAlternatingMap₂_lsmul_apply

omit [Fintype ι] in
open _root_.ContinuousAlternatingMap in
theorem compContinuousLinearMap_compContinuousLinearMap
    {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    (L : E [⋀^ι]→L[𝕜] N) (A : E' →L[𝕜] E) (B : E'' →L[𝕜] E') :
    (L.compContinuousLinearMap A).compContinuousLinearMap B =
      L.compContinuousLinearMap (A ∘L B) := by
  ext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.compContinuousLinearMap_compContinuousLinearMap then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.compContinuousLinearMap_compContinuousLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.compContinuousLinearMap_compContinuousLinearMap ``Submission.ContinuousAlternatingMap.compContinuousLinearMap_compContinuousLinearMap

omit [Fintype ι] in
open _root_.ContinuousAlternatingMap in
theorem compContinuousLinearMap_id {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (L : E [⋀^ι]→L[𝕜] N) :
    L.compContinuousLinearMap (ContinuousLinearMap.id 𝕜 E) = L := by
  ext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.compContinuousLinearMap_id then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.compContinuousLinearMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.compContinuousLinearMap_id ``Submission.ContinuousAlternatingMap.compContinuousLinearMap_id

omit [Fintype ι] in
open _root_.ContinuousAlternatingMap in
theorem compContinuousLinearMap_add {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] (L₁ L₂ : E [⋀^ι]→L[𝕜] N)
    (A : E' →L[𝕜] E) :
    (L₁ + L₂).compContinuousLinearMap A =
      L₁.compContinuousLinearMap A + L₂.compContinuousLinearMap A := by
  ext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.compContinuousLinearMap_add then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.compContinuousLinearMap_add"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.compContinuousLinearMap_add ``Submission.ContinuousAlternatingMap.compContinuousLinearMap_add

omit [Fintype ι] in
open _root_.ContinuousAlternatingMap in
theorem compContinuousLinearMap_smul {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] (c : 𝕜) (L : E [⋀^ι]→L[𝕜] N)
    (A : E' →L[𝕜] E) :
    (c • L).compContinuousLinearMap A = c • L.compContinuousLinearMap A := by
  ext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.compContinuousLinearMap_smul then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.compContinuousLinearMap_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.compContinuousLinearMap_smul ``Submission.ContinuousAlternatingMap.compContinuousLinearMap_smul

omit [Fintype ι] in
open _root_.ContinuousAlternatingMap in
theorem compContinuousLinearMap_zero {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] (A : E' →L[𝕜] E) :
    (0 : E [⋀^ι]→L[𝕜] N).compContinuousLinearMap A = 0 := by
  ext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.compContinuousLinearMap_zero then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.compContinuousLinearMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.compContinuousLinearMap_zero ``Submission.ContinuousAlternatingMap.compContinuousLinearMap_zero

end ContinuousAlternatingMap

section Continuous

variable
  (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (ι : Type*) [Finite ι]
  (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [ContinuousAdd F₁]

open _root_.ContinuousAlternatingMap in
theorem ContinuousAlternatingMap.compContinuousLinearMapL_continuous :
    Continuous (fun p : F₁ →L[𝕜] F₁ ↦
    (ContinuousAlternatingMap.compContinuousLinearMapCLM p :
    (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) := by
  let := Fintype.ofFinite ι
  let φ : (F₁ [⋀^ι]→L[𝕜] F₂) →ₗᵢ[𝕜] _ := ContinuousAlternatingMap.toContinuousMultilinearMapLI
  let Φ : ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)) →ₗᵢ[𝕜] _ := φ.compLeft _ (RingHom.id _)
  rw [← Φ.comp_continuous_iff]
  change Continuous (fun p : F₁ →L[𝕜] F₁ ↦
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ ↦ p) :
    ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂ →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂).comp
    (_root_.ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜))
  exact (ContinuousMultilinearMap.compContinuousLinearMapL_diag_continuous 𝕜 ι F₁ F₂).clm_comp
    continuous_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.compContinuousLinearMapL_continuous then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.compContinuousLinearMapL_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.compContinuousLinearMapL_continuous ``Submission.ContinuousAlternatingMap.compContinuousLinearMapL_continuous

end Continuous

section Smooth
variable {𝕜 ι F₁ F₂} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

open scoped _root_.Bundle _root_.Manifold

omit [CharZero 𝕜] in
private theorem norm_alternatization_le (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) :
    ‖ContinuousMultilinearMap.alternatization f‖ ≤
      (Fintype.card (Equiv.Perm ι) : ℝ) * ‖f‖ := by
  refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_
  change ‖ContinuousMultilinearMap.alternatization f v‖ ≤
    (Fintype.card (Equiv.Perm ι) : ℝ) * ‖f‖ * ∏ i, ‖v i‖
  rw [ContinuousMultilinearMap.alternatization_apply_apply]
  calc
    ‖∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f (v ∘ σ)‖
        ≤ ∑ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • f (v ∘ σ)‖ := norm_sum_le _ _
    _ ≤ ∑ σ : Equiv.Perm ι, ‖f‖ * ∏ i, ‖v i‖ := by
      apply Finset.sum_le_sum
      intro σ _
      have hnorm : ‖Equiv.Perm.sign σ • f (v ∘ σ)‖ = ‖f (v ∘ σ)‖ := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
      rw [hnorm]
      calc
        ‖f (v ∘ σ)‖ ≤ ‖f‖ * ∏ i, ‖(v ∘ σ) i‖ := ContinuousMultilinearMap.le_opNorm _ _
        _ = ‖f‖ * ∏ i, ‖v i‖ := by
          simp only [Function.comp_apply]
          rw [Equiv.prod_comp σ (fun i => ‖v i‖)]
    _ = (Fintype.card (Equiv.Perm ι) : ℝ) * (‖f‖ * ∏ i, ‖v i‖) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card (Equiv.Perm ι) : ℝ) * ‖f‖ * ∏ i, ‖v i‖ := by ring

run_cmd do
  let target := ``Submission.norm_alternatization_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `norm_alternatization_le target :: scope.openDecls } }

open _root_.ContinuousMultilinearMap in
noncomputable def ContinuousMultilinearMap.alternatizationCLM : (ContinuousMultilinearMap 𝕜
    (fun _ : ι => F₁) F₂) →L[𝕜]
    (F₁ [⋀^ι]→L[𝕜] F₂) :=
  LinearMap.mkContinuous
    { toFun := fun f => (↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹ •
        ContinuousMultilinearMap.alternatization f
      map_add' := by
        intro f g
        ext v
        rw [show ContinuousMultilinearMap.alternatization (f + g) =
            ContinuousMultilinearMap.alternatization f +
              ContinuousMultilinearMap.alternatization g from
          (ContinuousMultilinearMap.alternatization.map_add f g)]
        rw [smul_add]
      map_smul' := by
        intro c f
        have hlin : ContinuousMultilinearMap.alternatization (c • f) =
            c • ContinuousMultilinearMap.alternatization f := by
          ext v
          rw [ContinuousMultilinearMap.alternatization_apply_apply]
          simp only [_root_.smul_apply]
          rw [ContinuousAlternatingMap.smul_apply,
            ContinuousMultilinearMap.alternatization_apply_apply,
            Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro σ _
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
        ext v
        simp only [ContinuousAlternatingMap.smul_apply, hlin]
        exact _root_.SMulCommClass.smul_comm ((↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹) c
          (ContinuousMultilinearMap.alternatization f v) }
    (‖(↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹‖ * Fintype.card (Equiv.Perm ι))
    (by
      intro f
      calc
        ‖(↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹ • ContinuousMultilinearMap.alternatization f‖
            ≤ ‖(↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹‖ *
                ‖ContinuousMultilinearMap.alternatization f‖ :=
              norm_smul_le (r := (↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹)
                (x := ContinuousMultilinearMap.alternatization f)
        _ ≤ ‖(↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹‖ *
                ((Fintype.card (Equiv.Perm ι) : ℝ) * ‖f‖) := by
          exact mul_le_mul_of_nonneg_left (norm_alternatization_le f) (norm_nonneg _)
        _ = (‖(↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹‖ * Fintype.card (Equiv.Perm ι)) * ‖f‖ := by
          ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMultilinearMap.alternatizationCLM then
    throwError "Refusing to shadow existing declaration ContinuousMultilinearMap.alternatizationCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMultilinearMap.alternatizationCLM ``Submission.ContinuousMultilinearMap.alternatizationCLM

open _root_.ContinuousMultilinearMap in
theorem ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap
    (L : F₁ [⋀^ι]→L[𝕜] F₂) :
    ContinuousMultilinearMap.alternatizationCLM
      (ContinuousAlternatingMap.toContinuousMultilinearMap L) = L := by
  ext v
  simp only [ContinuousMultilinearMap.alternatizationCLM, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousAlternatingMap.smul_apply]
  rw [ContinuousMultilinearMap.alternatization_apply_apply]
  change ((↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹ •
    (∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • L (v ∘ σ))) = L v
  have hsum : ∑ σ : Equiv.Perm ι,
    Equiv.Perm.sign σ • L (v ∘ σ) = (Fintype.card (Equiv.Perm ι) : 𝕜) • L v := by
    calc
      (∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • L (v ∘ σ)) = ∑ σ : Equiv.Perm ι, L v := by
        apply Finset.sum_congr rfl
        intro σ _
        change Equiv.Perm.sign σ • (L.toAlternatingMap (v ∘ σ)) = L.toAlternatingMap v
        rw [L.toAlternatingMap.map_perm v σ]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
        · rw [hs]
          exact (one_zsmul (a := ((↑(1 : ℤˣ) : ℤ) • L.toAlternatingMap v))).trans
            (one_zsmul (a := L.toAlternatingMap v))
        · rw [hs]
          exact ((neg_one_zsmul (x := ((↑(-1 : ℤˣ) : ℤ) • L.toAlternatingMap v))).trans
            (congrArg Neg.neg (neg_one_zsmul (x := L.toAlternatingMap v)))).trans
            (neg_neg (a := L.toAlternatingMap v))
      _ = (Fintype.card (Equiv.Perm ι) : 𝕜) • L v := by
        rw [Finset.sum_const]
        exact (Nat.cast_smul_eq_nsmul 𝕜 (Fintype.card (Equiv.Perm ι)) (L v)).symm
  rw [hsum]
  simp only [Fintype.card_perm, smul_smul]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_pos (Fintype.card ι)).ne',
    Nat.factorial_ne_zero (Fintype.card ι)]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap then
    throwError "Refusing to shadow existing declaration ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap ``Submission.ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap

omit [CharZero 𝕜] in
open _root_.ContinuousMultilinearMap in
theorem ContinuousMultilinearMap.alternatizationCLM_compContinuousLinearMap
    {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace 𝕜 F₁']
    (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)
    (A : F₁' →L[𝕜] F₁) :
    ContinuousMultilinearMap.alternatizationCLM
        (f.compContinuousLinearMap (fun _ => A)) =
      (ContinuousMultilinearMap.alternatizationCLM f).compContinuousLinearMap A := by
  ext v
  simp only [ContinuousMultilinearMap.alternatizationCLM, LinearMap.mkContinuous_apply,
    LinearMap.coe_mk, AddHom.coe_mk, ContinuousAlternatingMap.smul_apply]
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  simp only [ContinuousAlternatingMap.smul_apply]
  rw [ContinuousMultilinearMap.alternatization_apply_apply,
    ContinuousMultilinearMap.alternatization_apply_apply]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMultilinearMap.alternatizationCLM_compContinuousLinearMap then
    throwError "Refusing to shadow existing declaration ContinuousMultilinearMap.alternatizationCLM_compContinuousLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMultilinearMap.alternatizationCLM_compContinuousLinearMap ``Submission.ContinuousMultilinearMap.alternatizationCLM_compContinuousLinearMap

omit [DecidableEq ι] in
open _root_.ContinuousAlternatingMap in
theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff :
    ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁ =>
      (_root_.ContinuousAlternatingMap.compContinuousLinearMapCLM p : (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜]
        (F₁ [⋀^ι]→L[𝕜] F₂))) := by
  classical
  let ψ : (F₁ [⋀^ι]→L[𝕜] F₂) →ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂ :=
    ContinuousAlternatingMap.toContinuousMultilinearMapLI
  let altCLM : (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂) :=
    ContinuousMultilinearMap.alternatizationCLM
  let B : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) →ₗ[𝕜]
      (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂) :=
    { toFun := fun M => altCLM.comp (M.comp ψ.toContinuousLinearMap)
      map_add' := by intro M₁ M₂; ext L; simp
      map_smul' := by intro c M; ext L; simp }
  have hbound : ∀ (M : (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)),
      ‖B M‖ ≤ ‖altCLM‖ * ‖M‖ := by
    intro M
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg altCLM)
      (norm_nonneg M)) ?_
    intro L
    calc
      ‖altCLM (M (ψ L))‖ ≤ ‖altCLM‖ * ‖M (ψ L)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖altCLM‖ * (‖M‖ * ‖L‖) := by
        have h1 : ‖M (ψ L)‖ ≤ ‖M‖ * ‖L‖ := by
          calc
            ‖M (ψ L)‖ ≤ ‖M‖ * ‖ψ L‖ := ContinuousLinearMap.le_opNorm M (ψ L)
            _ = ‖M‖ * ‖L‖ := by rw [ψ.norm_map]
        exact mul_le_mul_of_nonneg_left h1 (norm_nonneg altCLM)
      _ = ‖altCLM‖ * ‖M‖ * ‖L‖ := by rw [← mul_assoc]
  have hΦlin : IsLinearMap 𝕜 (fun M : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) =>
      (B M : (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) :=
    { map_add := by intro M₁ M₂; ext L; simp
      map_smul := by intro c M; ext L; simp }
  have hΦ : IsBoundedLinearMap 𝕜 (fun M : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) =>
      (B M : (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) :=
    hΦlin.with_bound (‖altCLM‖) hbound
  have hΦcont : ContDiff 𝕜 ⊤ (fun M : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) =>
      (B M : (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) := by
    simpa using (IsBoundedLinearMap.contDiff (𝕜 := 𝕜) (n := ⊤)
      (f := (fun M : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) →L[𝕜]
        (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) =>
        (B M : (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)))) hΦ)
  convert hΦcont.comp ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff using 1
  funext p
  ext L x
  change (_root_.ContinuousAlternatingMap.compContinuousLinearMapCLM p) L x =
    (ContinuousMultilinearMap.alternatizationCLM
      (ContinuousAlternatingMap.toContinuousMultilinearMap
      (L.compContinuousLinearMap p))) x
  rw [ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff ``Submission.ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff

omit [DecidableEq ι] in
open _root_.ContinuousAlternatingMap in
theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff :
    let F : (F₁ →L[𝕜] F₁) → (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)
      := fun p ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM p
    ContMDiff (𝓘(𝕜, (F₁ →L[𝕜] F₁))) (𝓘(𝕜, ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)))) ⊤ F := by
  rw [contMDiff_iff_contDiff]
  exact ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff ``Submission.ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff

omit [DecidableEq ι] in
open _root_.ContinuousAlternatingMap in
theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space
    {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace 𝕜 F₁'] :
    ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁' =>
      (_root_.ContinuousAlternatingMap.compContinuousLinearMapCLM p : (F₁' [⋀^ι]→L[𝕜] F₂) →L[𝕜]
        (F₁ [⋀^ι]→L[𝕜] F₂))) := by
  classical
  let ψ : (F₁' [⋀^ι]→L[𝕜] F₂) →ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁') F₂ :=
    ContinuousAlternatingMap.toContinuousMultilinearMapLI
  let ψ₀ : (F₁ [⋀^ι]→L[𝕜] F₂) →ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂ :=
    ContinuousAlternatingMap.toContinuousMultilinearMapLI
  let altCLM : (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁') F₂) →L[𝕜] (F₁' [⋀^ι]→L[𝕜] F₂) :=
    ContinuousMultilinearMap.alternatizationCLM
  let altCLM₀ : (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂) :=
    ContinuousMultilinearMap.alternatizationCLM
  let B : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁') F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) →ₗ[𝕜]
      (F₁' [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂) :=
    { toFun := fun M => altCLM₀.comp (M.comp ψ.toContinuousLinearMap)
      map_add' := by intro M₁ M₂; ext L; simp
      map_smul' := by intro c M; ext L; simp }
  have hbound : ∀ (M : (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁') F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)),
      ‖B M‖ ≤ ‖altCLM₀‖ * ‖M‖ := by
    intro M
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg altCLM₀)
      (norm_nonneg M)) ?_
    intro L
    calc
      ‖altCLM₀ (M (ψ L))‖ ≤ ‖altCLM₀‖ * ‖M (ψ L)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖altCLM₀‖ * (‖M‖ * ‖L‖) := by
        have h1 : ‖M (ψ L)‖ ≤ ‖M‖ * ‖L‖ := by
          calc
            ‖M (ψ L)‖ ≤ ‖M‖ * ‖ψ L‖ := ContinuousLinearMap.le_opNorm M (ψ L)
            _ = ‖M‖ * ‖L‖ := by rw [ψ.norm_map]
        exact mul_le_mul_of_nonneg_left h1 (norm_nonneg altCLM₀)
      _ = ‖altCLM₀‖ * ‖M‖ * ‖L‖ := by rw [← mul_assoc]
  have hΦlin : IsLinearMap 𝕜 (fun M : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁') F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) =>
      (B M : (F₁' [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) :=
    { map_add := by intro M₁ M₂; ext L; simp
      map_smul := by intro c M; ext L; simp }
  have hΦ : IsBoundedLinearMap 𝕜 (fun M : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁') F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) =>
      (B M : (F₁' [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) :=
    hΦlin.with_bound (‖altCLM₀‖) hbound
  have hΦcont : ContDiff 𝕜 ⊤ (fun M : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁') F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) =>
      (B M : (F₁' [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) := by
    simpa using (IsBoundedLinearMap.contDiff (𝕜 := 𝕜) (n := ⊤)
      (f := (fun M : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁') F₂) →L[𝕜]
        (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) =>
        (B M : (F₁' [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)))) hΦ)
  convert hΦcont.comp ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff_of_space
    using 1
  funext p
  ext L x
  change (_root_.ContinuousAlternatingMap.compContinuousLinearMapCLM p) L x =
    (ContinuousMultilinearMap.alternatizationCLM
      (ContinuousAlternatingMap.toContinuousMultilinearMap
      (L.compContinuousLinearMap p))) x
  rw [ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space ``Submission.ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space

omit [DecidableEq ι] in
open _root_.ContinuousAlternatingMap in
theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_of_space
    {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace 𝕜 F₁'] :
    let F : (F₁ →L[𝕜] F₁') → (F₁' [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)
      := fun p ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM p
    ContMDiff (𝓘(𝕜, (F₁ →L[𝕜] F₁'))) (𝓘(𝕜,
      ((F₁' [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)))) ⊤ F := by
  rw [contMDiff_iff_contDiff]
  exact ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_of_space then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_of_space"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_of_space ``Submission.ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_of_space

end Smooth

section Smooth
variable {ι F₁ F₂} [Fintype ι]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]

open scoped _root_.Bundle _root_.Manifold

open _root_.ContinuousAlternatingMap in
theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_real :
    ContDiff ℝ ⊤ (fun p : F₁ →L[ℝ] F₁ =>
      (_root_.ContinuousAlternatingMap.compContinuousLinearMapCLM p : (F₁ [⋀^ι]→L[ℝ] F₂) →L[ℝ]
        (F₁ [⋀^ι]→L[ℝ] F₂))) := by
  exact ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_real then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_real"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_real ``Submission.ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_real

open _root_.ContinuousAlternatingMap in
theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_real :
    let F : (F₁ →L[ℝ] F₁) → (F₁ [⋀^ι]→L[ℝ] F₂) →L[ℝ] (F₁ [⋀^ι]→L[ℝ] F₂)
      := fun p ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM p
    ContMDiff (𝓘(ℝ, (F₁ →L[ℝ] F₁))) (𝓘(ℝ, ((F₁ [⋀^ι]→L[ℝ] F₂) →L[ℝ] (F₁ [⋀^ι]→L[ℝ] F₂)))) ⊤ F := by
  rw [contMDiff_iff_contDiff]
  exact ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_real

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_real then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_real"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_real ``Submission.ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_real

open _root_.ContinuousAlternatingMap in
theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space_real
    {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace ℝ F₁'] :
    ContDiff ℝ ⊤ (fun p : F₁ →L[ℝ] F₁' =>
      (_root_.ContinuousAlternatingMap.compContinuousLinearMapCLM p : (F₁' [⋀^ι]→L[ℝ] F₂) →L[ℝ]
        (F₁ [⋀^ι]→L[ℝ] F₂))) := by
  exact ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space_real then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space_real"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space_real ``Submission.ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space_real

open _root_.ContinuousAlternatingMap in
theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_of_space_real
    {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace ℝ F₁'] :
    let F : (F₁ →L[ℝ] F₁') → (F₁' [⋀^ι]→L[ℝ] F₂) →L[ℝ] (F₁ [⋀^ι]→L[ℝ] F₂)
      := fun p ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM p
    ContMDiff (𝓘(ℝ, (F₁ →L[ℝ] F₁'))) (𝓘(ℝ,
      ((F₁' [⋀^ι]→L[ℝ] F₂) →L[ℝ] (F₁ [⋀^ι]→L[ℝ] F₂)))) ⊤ F := by
  rw [contMDiff_iff_contDiff]
  exact ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space_real

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_of_space_real then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_of_space_real"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_of_space_real ``Submission.ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_of_space_real

end Smooth

end Comp
