import Mathlib.Analysis.Normed.Module.Multilinear.Curry

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry
namespace Tensor
namespace Multilinear

section NormBridge

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable local instance normBridgeDualNormedAddCommGroup :
    NormedAddCommGroup (F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.normBridgeDualNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.normBridgeDualNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.normBridgeDualNormedAddCommGroup ``Submission.DifferentialGeometry.Tensor.Multilinear.normBridgeDualNormedAddCommGroup

noncomputable local instance normBridgeDualNormedSpace :
    NormedSpace ℝ (F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.normBridgeDualNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.normBridgeDualNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.normBridgeDualNormedSpace ``Submission.DifferentialGeometry.Tensor.Multilinear.normBridgeDualNormedSpace

noncomputable local instance normBridgeBilinearNormedAddCommGroup :
    NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.normBridgeBilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.normBridgeBilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.normBridgeBilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Tensor.Multilinear.normBridgeBilinearNormedAddCommGroup

noncomputable local instance normBridgeBilinearNormedSpace :
    NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.normBridgeBilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.normBridgeBilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.normBridgeBilinearNormedSpace ``Submission.DifferentialGeometry.Tensor.Multilinear.normBridgeBilinearNormedSpace

noncomputable local instance normBridgeTrilinearNormedAddCommGroup :
    NormedAddCommGroup (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.normBridgeTrilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.normBridgeTrilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.normBridgeTrilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Tensor.Multilinear.normBridgeTrilinearNormedAddCommGroup

noncomputable local instance normBridgeTrilinearNormedSpace :
    NormedSpace ℝ (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.normBridgeTrilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.normBridgeTrilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.normBridgeTrilinearNormedSpace ``Submission.DifferentialGeometry.Tensor.Multilinear.normBridgeTrilinearNormedSpace

noncomputable local instance normBridgeQuadrilinearNormedAddCommGroup :
    NormedAddCommGroup (F →L[ℝ] F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.normBridgeQuadrilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.normBridgeQuadrilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.normBridgeQuadrilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Tensor.Multilinear.normBridgeQuadrilinearNormedAddCommGroup

noncomputable local instance normBridgeQuadrilinearNormedSpace :
    NormedSpace ℝ (F →L[ℝ] F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.normBridgeQuadrilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.normBridgeQuadrilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.normBridgeQuadrilinearNormedSpace ``Submission.DifferentialGeometry.Tensor.Multilinear.normBridgeQuadrilinearNormedSpace

def biForm₂ToModel :
    (F →L[ℝ] F →L[ℝ] ℝ) ≃ₗ[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 2 => F) ℝ :=
  ((ContinuousLinearEquiv.refl ℝ F).arrowCongr
      (continuousMultilinearCurryFin1 ℝ F ℝ).symm.toContinuousLinearEquiv).toLinearEquiv.trans
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => F) ℝ).symm.toLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel ``Submission.DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel

theorem biForm₂ToModel_apply (B : F →L[ℝ] F →L[ℝ] ℝ) (v : Fin 2 → F) :
    biForm₂ToModel F B v = B (v 0) (v 1) := by
  classical
  change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => F) ℝ).symm
      (((ContinuousLinearEquiv.refl ℝ F).arrowCongr
          (continuousMultilinearCurryFin1 ℝ F ℝ).symm.toContinuousLinearEquiv) B) v =
    B (v 0) (v 1)
  rw [continuousMultilinearCurryLeftEquiv_symm_apply,
    ContinuousLinearEquiv.arrowCongr_apply]
  simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [continuousMultilinearCurryFin1_symm_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_apply ``Submission.DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_apply

theorem biForm₂ToModel_symm_apply
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => F) ℝ) (v w : F) :
    (biForm₂ToModel F).symm T v w = T ![v, w] := by
  classical
  have h := biForm₂ToModel_apply F ((biForm₂ToModel F).symm T) ![v, w]
  rw [(biForm₂ToModel F).apply_symm_apply T] at h
  simpa using h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_symm_apply ``Submission.DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_symm_apply

theorem biForm₂ToModel_norm_map (B : F →L[ℝ] F →L[ℝ] ℝ) :
    ‖biForm₂ToModel F B‖ = ‖B‖ := by
  classical
  refine le_antisymm ?_ ?_
  · refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg B) (fun m => ?_)
    rw [biForm₂ToModel_apply, Fin.prod_univ_two]
    calc ‖B (m 0) (m 1)‖
        ≤ ‖B‖ * ‖m 0‖ * ‖m 1‖ := B.le_opNorm₂ (m 0) (m 1)
      _ = ‖B‖ * (‖m 0‖ * ‖m 1‖) := by ring
  · refine ContinuousLinearMap.opNorm_le_bound₂ B (norm_nonneg _) (fun v w => ?_)
    have hsymm : B v w = biForm₂ToModel F B ![v, w] := by
      rw [biForm₂ToModel_apply]; simp
    rw [hsymm]
    calc ‖biForm₂ToModel F B ![v, w]‖
        ≤ ‖biForm₂ToModel F B‖ * ∏ i : Fin 2, ‖(![v, w] : Fin 2 → F) i‖ :=
          (biForm₂ToModel F B).le_opNorm _
      _ = ‖biForm₂ToModel F B‖ * ‖v‖ * ‖w‖ := by
          rw [Fin.prod_univ_two]; simp [Matrix.cons_val_zero, Matrix.cons_val_one]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_norm_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_norm_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_norm_map ``Submission.DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_norm_map

def biForm₂ToModelₗᵢ :
    (F →L[ℝ] F →L[ℝ] ℝ) ≃ₗᵢ[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 2 => F) ℝ :=
  { biForm₂ToModel F with norm_map' := biForm₂ToModel_norm_map F }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.biForm₂ToModelₗᵢ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.biForm₂ToModelₗᵢ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.biForm₂ToModelₗᵢ ``Submission.DifferentialGeometry.Tensor.Multilinear.biForm₂ToModelₗᵢ

def triFormToModel :
    (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) ≃ₗ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 3 => F) ℝ :=
  ((ContinuousLinearEquiv.refl ℝ F).arrowCongr
      (biForm₂ToModelₗᵢ F).toContinuousLinearEquiv).toLinearEquiv.trans
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => F) ℝ).symm.toLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.triFormToModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.triFormToModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.triFormToModel ``Submission.DifferentialGeometry.Tensor.Multilinear.triFormToModel

theorem triFormToModel_apply (B : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) (v : Fin 3 → F) :
    triFormToModel F B v = B (v 0) (v 1) (v 2) := by
  classical
  change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => F) ℝ).symm
      (((ContinuousLinearEquiv.refl ℝ F).arrowCongr
          (biForm₂ToModelₗᵢ F).toContinuousLinearEquiv) B) v =
    B (v 0) (v 1) (v 2)
  rw [continuousMultilinearCurryLeftEquiv_symm_apply,
    ContinuousLinearEquiv.arrowCongr_apply]
  simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  change (biForm₂ToModelₗᵢ F) (B (v 0)) (Fin.tail v) = _
  rw [show ⇑(biForm₂ToModelₗᵢ F) = ⇑(biForm₂ToModel F) from rfl, biForm₂ToModel_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.triFormToModel_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.triFormToModel_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.triFormToModel_apply ``Submission.DifferentialGeometry.Tensor.Multilinear.triFormToModel_apply

theorem triFormToModel_norm_map (B : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :
    ‖triFormToModel F B‖ = ‖B‖ := by
  classical
  have h_curry : ‖triFormToModel F B‖ =
      ‖((ContinuousLinearEquiv.refl ℝ F).arrowCongr
          (biForm₂ToModelₗᵢ F).toContinuousLinearEquiv) B‖ := by
    change ‖(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => F) ℝ).symm
      (((ContinuousLinearEquiv.refl ℝ F).arrowCongr
        (biForm₂ToModelₗᵢ F).toContinuousLinearEquiv) B)‖ = _
    rw [(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => F) ℝ).symm.norm_map]
  rw [h_curry]
  have hcomp : ((ContinuousLinearEquiv.refl ℝ F).arrowCongr
        (biForm₂ToModelₗᵢ F).toContinuousLinearEquiv) B =
      (biForm₂ToModelₗᵢ F).toLinearIsometry.toContinuousLinearMap.comp B := by
    ext u
    simp only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.refl_symm,
      ContinuousLinearEquiv.refl_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearMap.coe_comp, Function.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
  rw [hcomp, (biForm₂ToModelₗᵢ F).toLinearIsometry.norm_toContinuousLinearMap_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.triFormToModel_norm_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.triFormToModel_norm_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.triFormToModel_norm_map ``Submission.DifferentialGeometry.Tensor.Multilinear.triFormToModel_norm_map

def triFormToModelₗᵢ :
    (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) ≃ₗᵢ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 3 => F) ℝ :=
  { triFormToModel F with norm_map' := triFormToModel_norm_map F }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.triFormToModelₗᵢ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.triFormToModelₗᵢ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.triFormToModelₗᵢ ``Submission.DifferentialGeometry.Tensor.Multilinear.triFormToModelₗᵢ

def quadFormToModel :
    (F →L[ℝ] F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) ≃ₗ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ :=
  ((ContinuousLinearEquiv.refl ℝ F).arrowCongr
      (triFormToModelₗᵢ F).toContinuousLinearEquiv).toLinearEquiv.trans
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 4 => F) ℝ).symm.toLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.quadFormToModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.quadFormToModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.quadFormToModel ``Submission.DifferentialGeometry.Tensor.Multilinear.quadFormToModel

theorem quadFormToModel_apply (B : F →L[ℝ] F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) (v : Fin 4 → F) :
    quadFormToModel F B v = B (v 0) (v 1) (v 2) (v 3) := by
  classical
  change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 4 => F) ℝ).symm
      (((ContinuousLinearEquiv.refl ℝ F).arrowCongr
          (triFormToModelₗᵢ F).toContinuousLinearEquiv) B) v =
    B (v 0) (v 1) (v 2) (v 3)
  rw [continuousMultilinearCurryLeftEquiv_symm_apply,
    ContinuousLinearEquiv.arrowCongr_apply]
  simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  change (triFormToModelₗᵢ F) (B (v 0)) (Fin.tail v) = _
  rw [show ⇑(triFormToModelₗᵢ F) = ⇑(triFormToModel F) from rfl, triFormToModel_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.quadFormToModel_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.quadFormToModel_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.quadFormToModel_apply ``Submission.DifferentialGeometry.Tensor.Multilinear.quadFormToModel_apply

theorem quadFormToModel_norm_map (B : F →L[ℝ] F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :
    ‖quadFormToModel F B‖ = ‖B‖ := by
  classical
  have h_curry : ‖quadFormToModel F B‖ =
      ‖((ContinuousLinearEquiv.refl ℝ F).arrowCongr
          (triFormToModelₗᵢ F).toContinuousLinearEquiv) B‖ := by
    change ‖(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 4 => F) ℝ).symm
      (((ContinuousLinearEquiv.refl ℝ F).arrowCongr
        (triFormToModelₗᵢ F).toContinuousLinearEquiv) B)‖ = _
    rw [(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 4 => F) ℝ).symm.norm_map]
  rw [h_curry]
  have hcomp : ((ContinuousLinearEquiv.refl ℝ F).arrowCongr
        (triFormToModelₗᵢ F).toContinuousLinearEquiv) B =
      (triFormToModelₗᵢ F).toLinearIsometry.toContinuousLinearMap.comp B := by
    ext u
    simp only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.refl_symm,
      ContinuousLinearEquiv.refl_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearMap.coe_comp, Function.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
  rw [hcomp, (triFormToModelₗᵢ F).toLinearIsometry.norm_toContinuousLinearMap_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.quadFormToModel_norm_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.quadFormToModel_norm_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.quadFormToModel_norm_map ``Submission.DifferentialGeometry.Tensor.Multilinear.quadFormToModel_norm_map

def quadFormToModelₗᵢ :
    (F →L[ℝ] F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) ≃ₗᵢ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ :=
  { quadFormToModel F with norm_map' := quadFormToModel_norm_map F }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.quadFormToModelₗᵢ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.quadFormToModelₗᵢ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.quadFormToModelₗᵢ ``Submission.DifferentialGeometry.Tensor.Multilinear.quadFormToModelₗᵢ

end NormBridge
end Multilinear
end Tensor
end DifferentialGeometry

end
