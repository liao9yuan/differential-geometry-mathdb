/-
Authors: Jack McCarthy
-/
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Defs
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Basis

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Tensor.Multilinear

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set

open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

namespace Bundle.continuousMultilinearMap
open _root_.Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {s : ℕ}

instance instFunLike (s : ℕ) (x : B) :
    FunLike (Bundle.continuousMultilinearMap 𝕜 s F E x) (Fin s → E x) 𝕜 :=
  ContinuousMultilinearMap.funLike

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.instFunLike then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.instFunLike"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.instFunLike ``Submission.Bundle.continuousMultilinearMap.instFunLike

theorem topology_eq (s : ℕ) (x : B) :
    (inferInstance : TopologicalSpace (Bundle.continuousMultilinearMap 𝕜 s F E x)) =
    (inferInstanceAs (TopologicalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜))) := by
  change instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x = _
  simp only [instTopologicalSpaceContinuousMultilinearMap]
  set e := _root_.FiberBundle.trivializationAt F E x
  set g : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜 →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => e.symmL 𝕜 x) with hg_def
  have hfactor : (↑(Pretrivialization.continuousMultilinearMap 𝕜 s e) ∘
      TotalSpace.mk' _ x) = Prod.mk x ∘ g := by funext; rfl
  rw [hfactor, ← induced_compose, (isInducing_prodMkRight x).eq_induced.symm]
  set g' := ContinuousMultilinearMap.compContinuousLinearMapL (F := 𝕜)
    (E₁ := fun _ : Fin s => F) (E := fun _ : Fin s => E x)
    (fun _ => e.continuousLinearMapAt 𝕜 x) with hg'_def
  have hx : x ∈ e.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt F E x
  have hleft : Function.LeftInverse g' g := by
    intro L
    apply ContinuousMultilinearMap.ext
    intro v
    dsimp [g, g']
    apply congrArg L
    funext i
    exact e.symmₗ_linearMapAt hx (v i)
  have hright : Function.RightInverse g' g := by
    intro M
    apply ContinuousMultilinearMap.ext
    intro v
    dsimp [g, g']
    apply congrArg M
    funext i
    exact e.linearMapAt_symmₗ hx (v i)
  exact (Homeomorph.mk ⟨g, g', hleft, hright⟩
    g.continuous g'.continuous).isInducing.eq_induced.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.topology_eq then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.topology_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.topology_eq ``Submission.Bundle.continuousMultilinearMap.topology_eq

instance instNormedAddCommGroup (s : ℕ) (x : B) :
    NormedAddCommGroup (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  delta Bundle.continuousMultilinearMap; infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.instNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.instNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.instNormedAddCommGroup ``Submission.Bundle.continuousMultilinearMap.instNormedAddCommGroup

instance instNormedSpace (s : ℕ) (x : B) :
    NormedSpace 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  delta Bundle.continuousMultilinearMap; exact ContinuousMultilinearMap.normedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.instNormedSpace then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.instNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.instNormedSpace ``Submission.Bundle.continuousMultilinearMap.instNormedSpace

instance instT2Space (s : ℕ) (x : B) :
    @T2Space (Bundle.continuousMultilinearMap 𝕜 s F E x) inferInstance :=
  (topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x).symm ▸
    inferInstanceAs (@T2Space (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.instT2Space then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.instT2Space"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.instT2Space ``Submission.Bundle.continuousMultilinearMap.instT2Space

instance instIsTopologicalAddGroup (s : ℕ) (x : B) :
    @IsTopologicalAddGroup (Bundle.continuousMultilinearMap 𝕜 s F E x) inferInstance _ :=
  (topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x).symm ▸
    inferInstanceAs (@IsTopologicalAddGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.instIsTopologicalAddGroup then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.instIsTopologicalAddGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.instIsTopologicalAddGroup ``Submission.Bundle.continuousMultilinearMap.instIsTopologicalAddGroup

instance instContinuousSMul (s : ℕ) (x : B) :
    @ContinuousSMul 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) _ _ inferInstance :=
  (topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x).symm ▸
    inferInstanceAs (@ContinuousSMul 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) _ _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.instContinuousSMul then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.instContinuousSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.instContinuousSMul ``Submission.Bundle.continuousMultilinearMap.instContinuousSMul

instance instContinuousAdd (s : ℕ) (x : B) :
    @ContinuousAdd (Bundle.continuousMultilinearMap 𝕜 s F E x) inferInstance _ :=
  @IsTopologicalAddGroup.toContinuousAdd _ inferInstance _ (instIsTopologicalAddGroup s x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.instContinuousAdd then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.instContinuousAdd"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.instContinuousAdd ``Submission.Bundle.continuousMultilinearMap.instContinuousAdd

def continuousLinearEquivAt (s : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 s F E x ≃L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 where
  toFun := ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ => (_root_.FiberBundle.trivializationAt F E x).symmL 𝕜 x)
  invFun := ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ => (_root_.FiberBundle.trivializationAt F E x).continuousLinearMapAt 𝕜 x)
  left_inv L := ContinuousMultilinearMap.ext fun v => by
    dsimp [ContinuousMultilinearMap.compContinuousLinearMapL]
    congr 1; funext i
    exact (_root_.FiberBundle.trivializationAt F E x).symmₗ_linearMapAt
      (_root_.FiberBundle.mem_baseSet_trivializationAt F E x) (v i)
  right_inv M := ContinuousMultilinearMap.ext fun v => by
    dsimp [ContinuousMultilinearMap.compContinuousLinearMapL]
    congr 1; funext i
    exact (_root_.FiberBundle.trivializationAt F E x).linearMapAt_symmₗ
      (_root_.FiberBundle.mem_baseSet_trivializationAt F E x) (v i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by
    change @Continuous (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x)
      ContinuousMultilinearMap.instTopologicalSpace _
    rw [show instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x =
      ContinuousMultilinearMap.instTopologicalSpace from topology_eq s x]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => (_root_.FiberBundle.trivializationAt F E x).symmL 𝕜 x)).continuous
  continuous_invFun := by
    change @Continuous (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 s F E x)
      ContinuousMultilinearMap.instTopologicalSpace
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x) _
    rw [show instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x =
      ContinuousMultilinearMap.instTopologicalSpace from topology_eq s x]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => (_root_.FiberBundle.trivializationAt F E x).continuousLinearMapAt 𝕜 x)).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.continuousLinearEquivAt then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.continuousLinearEquivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.continuousLinearEquivAt ``Submission.Bundle.continuousMultilinearMap.continuousLinearEquivAt

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E] in
@[ext]
theorem ext {s : ℕ} {x : B}
    {T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 s F E x}
    (h : ∀ m, T₁ m = T₂ m) : T₁ = T₂ :=
  ContinuousMultilinearMap.ext h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.ext then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.ext"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.ext ``Submission.Bundle.continuousMultilinearMap.ext

theorem triv_zero_apply_eq (x₀ x : B)
    (T : Bundle.continuousMultilinearMap 𝕜 0 F E x)
    (w : Fin 0 → F) :
    (_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 0 F E) x₀ ⟨x, T⟩).2 w = T Fin.elim0 := by
  change T (fun i : Fin 0 => (_root_.FiberBundle.trivializationAt F E x₀).symmL 𝕜 x (w i)) = T Fin.elim0
  exact congrArg T (Subsingleton.elim _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.triv_zero_apply_eq then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.triv_zero_apply_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.triv_zero_apply_eq ``Submission.Bundle.continuousMultilinearMap.triv_zero_apply_eq

theorem triv_zero_symmL_apply_elim0 (x₀ x : B)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt F E x₀).baseSet)
    (ω₀ : ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) :
    ((_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F E) x₀).symmL 𝕜 x ω₀ :
        Bundle.continuousMultilinearMap 𝕜 0 F E x) Fin.elim0 = ω₀ 0 := by
  set e := _root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
    (Bundle.continuousMultilinearMap 𝕜 0 F E) x₀ with he_def
  have hbase : x ∈ e.baseSet := hx
  have hsymmL : (e.symmL 𝕜 x ω₀ : Bundle.continuousMultilinearMap 𝕜 0 F E x) =
      e.symm x ω₀ := by
    exact e.symmL_apply hbase ω₀
  rw [hsymmL]
  have h1 := triv_zero_apply_eq (F := F) (E := E) x₀ x (e.symm x ω₀) 0
  have h2 : (e ⟨x, e.symm x ω₀⟩ : B × _) = (x, ω₀) :=
    e.apply_mk_symm hbase ω₀
  rw [show (e ⟨x, e.symm x ω₀⟩ : B × _).2 = ω₀ from congrArg Prod.snd h2] at h1
  exact h1.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.triv_zero_symmL_apply_elim0 then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.triv_zero_symmL_apply_elim0"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.triv_zero_symmL_apply_elim0 ``Submission.Bundle.continuousMultilinearMap.triv_zero_symmL_apply_elim0

theorem triv_symmL_eq_compContinuousLinearMap {s : ℕ} (x₀ x : B)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt F E x₀).baseSet)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    ((_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 s F E) x₀).symmL 𝕜 x T :
        Bundle.continuousMultilinearMap 𝕜 s F E x) =
      T.compContinuousLinearMap
        (fun _ : Fin s => (_root_.FiberBundle.trivializationAt F E x₀).continuousLinearMapAt 𝕜 x) := by
  set e := _root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (Bundle.continuousMultilinearMap 𝕜 s F E) x₀ with he_def
  have hbase : x ∈ e.baseSet := hx
  have hsymmL : (e.symmL 𝕜 x T : Bundle.continuousMultilinearMap 𝕜 s F E x) =
      e.symm x T := by
    exact e.symmL_apply hbase T
  rw [hsymmL]
  apply Bundle.continuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have h_fwd : ∀ (M : Bundle.continuousMultilinearMap 𝕜 s F E x)
      (w : Fin s → F),
      (e ⟨x, M⟩).2 w = M (fun i => (_root_.FiberBundle.trivializationAt F E x₀).symmL 𝕜 x (w i)) := by
    intro M w; rfl
  have h_rt : (e ⟨x, e.symm x T⟩ : B × _) = (x, T) :=
    e.apply_mk_symm hbase T
  have h_snd : (e ⟨x, e.symm x T⟩ : B × _).2 = T := congrArg Prod.snd h_rt
  have h_apply := h_fwd (e.symm x T)
    (fun i => (_root_.FiberBundle.trivializationAt F E x₀).continuousLinearMapAt 𝕜 x (v i))
  rw [h_snd] at h_apply
  conv_rhs at h_apply =>
    arg 2; ext i
    rw [(_root_.FiberBundle.trivializationAt F E x₀).symmL_continuousLinearMapAt hx (v i)]
  exact h_apply.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap ``Submission.Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap

def toModel {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 :=
  continuousLinearEquivAt (F := F) (E := E) s x T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.toModel then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.toModel"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.toModel ``Submission.Bundle.continuousMultilinearMap.toModel

def toModelL (s : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 s F E x →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 :=
  (continuousLinearEquivAt (F := F) (E := E) s x).toContinuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.toModelL then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.toModelL"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.toModelL ``Submission.Bundle.continuousMultilinearMap.toModelL

def ofModel {s : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    Bundle.continuousMultilinearMap 𝕜 s F E x :=
  (continuousLinearEquivAt (F := F) (E := E) s x).symm f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.ofModel then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.ofModel"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.ofModel ``Submission.Bundle.continuousMultilinearMap.ofModel

@[simp]
theorem toModelL_apply {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModelL (F := F) (E := E) s x T = toModel T := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.toModelL_apply then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.toModelL_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.toModelL_apply ``Submission.Bundle.continuousMultilinearMap.toModelL_apply

@[simp]
theorem toModel_add {s : ℕ} {x : B}
    (T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (T₁ + T₂) =
      toModel T₁ + toModel T₂ :=
  map_add (continuousLinearEquivAt (F := F) (E := E) s x) T₁ T₂

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.toModel_add then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.toModel_add"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.toModel_add ``Submission.Bundle.continuousMultilinearMap.toModel_add

@[simp]
theorem toModel_smul {s : ℕ} {x : B}
    (c : 𝕜) (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (c • T) = c • toModel T :=
  map_smul (continuousLinearEquivAt (F := F) (E := E) s x) c T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.toModel_smul then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.toModel_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.toModel_smul ``Submission.Bundle.continuousMultilinearMap.toModel_smul

@[simp]
theorem toModel_zero {s : ℕ} {x : B} :
    toModel (F := F) (E := E)
      (0 : Bundle.continuousMultilinearMap 𝕜 s F E x) = 0 :=
  map_zero (continuousLinearEquivAt (F := F) (E := E) s x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.toModel_zero then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.toModel_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.toModel_zero ``Submission.Bundle.continuousMultilinearMap.toModel_zero

@[simp]
theorem toModel_neg {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (-T) = -toModel T :=
  map_neg (continuousLinearEquivAt (F := F) (E := E) s x) T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.toModel_neg then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.toModel_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.toModel_neg ``Submission.Bundle.continuousMultilinearMap.toModel_neg

@[simp]
theorem toModel_sub {s : ℕ} {x : B}
    (T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (T₁ - T₂) =
      toModel T₁ - toModel T₂ :=
  map_sub (continuousLinearEquivAt (F := F) (E := E) s x) T₁ T₂

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.toModel_sub then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.toModel_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.toModel_sub ``Submission.Bundle.continuousMultilinearMap.toModel_sub

@[simp]
theorem ofModel_toModel {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    ofModel (F := F) (E := E) (toModel T) = T :=
  (continuousLinearEquivAt (F := F) (E := E) s x).symm_apply_apply T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.ofModel_toModel then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.ofModel_toModel"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.ofModel_toModel ``Submission.Bundle.continuousMultilinearMap.ofModel_toModel

@[simp]
theorem toModel_ofModel {s : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    toModel (F := F) (E := E) (ofModel (x := x) f) = f :=
  (continuousLinearEquivAt (F := F) (E := E) s x).apply_symm_apply f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.toModel_ofModel then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.toModel_ofModel"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.toModel_ofModel ``Submission.Bundle.continuousMultilinearMap.toModel_ofModel

theorem toModel_continuous {s : ℕ} {x : B} :
    Continuous
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T) :=
  (continuousLinearEquivAt (F := F) (E := E) s x).continuous_toFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.toModel_continuous then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.toModel_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.toModel_continuous ``Submission.Bundle.continuousMultilinearMap.toModel_continuous

theorem toModel_injective {s : ℕ} {x : B} :
    Function.Injective
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T) :=
  (continuousLinearEquivAt (F := F) (E := E) s x).injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.toModel_injective then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.toModel_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.toModel_injective ``Submission.Bundle.continuousMultilinearMap.toModel_injective

theorem toModel_surjective {s : ℕ} {x : B} :
    Function.Surjective
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T) :=
  (continuousLinearEquivAt (F := F) (E := E) s x).surjective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.toModel_surjective then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.toModel_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.toModel_surjective ``Submission.Bundle.continuousMultilinearMap.toModel_surjective

theorem toModel_bijective {s : ℕ} {x : B} :
    Function.Bijective
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T) :=
  (continuousLinearEquivAt (F := F) (E := E) s x).bijective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.toModel_bijective then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.toModel_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.toModel_bijective ``Submission.Bundle.continuousMultilinearMap.toModel_bijective

def fiberContinuousLinearEquiv (s : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 s F E x ≃L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜 where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by
    change @Continuous (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜)
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x)
      ContinuousMultilinearMap.instTopologicalSpace id
    rw [show instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x =
      ContinuousMultilinearMap.instTopologicalSpace from
        topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x]
    exact @continuous_id _ ContinuousMultilinearMap.instTopologicalSpace
  continuous_invFun := by
    change @Continuous (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 s F E x)
      ContinuousMultilinearMap.instTopologicalSpace
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x) id
    rw [show instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x =
      ContinuousMultilinearMap.instTopologicalSpace from
        topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x]
    exact @continuous_id _ ContinuousMultilinearMap.instTopologicalSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.fiberContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.fiberContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.fiberContinuousLinearEquiv ``Submission.Bundle.continuousMultilinearMap.fiberContinuousLinearEquiv

def curryFin0Equiv (x : B) :
    Bundle.continuousMultilinearMap 𝕜 0 F E x ≃L[𝕜] 𝕜 :=
  (fiberContinuousLinearEquiv (F := F) 0 x).trans
    (continuousMultilinearCurryFin0 𝕜 (E x) 𝕜)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.curryFin0Equiv then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.curryFin0Equiv"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.curryFin0Equiv ``Submission.Bundle.continuousMultilinearMap.curryFin0Equiv

@[simp] theorem curryFin0Equiv_apply (x : B)
    (T : Bundle.continuousMultilinearMap 𝕜 0 F E x) :
    curryFin0Equiv (𝕜 := 𝕜) (F := F) (E := E) x T = T Fin.elim0 := by
  change T 0 = T Fin.elim0
  exact congrArg T (Subsingleton.elim _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.curryFin0Equiv_apply then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.curryFin0Equiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.curryFin0Equiv_apply ``Submission.Bundle.continuousMultilinearMap.curryFin0Equiv_apply

@[simp] theorem curryFin0Equiv_symm_apply (x : B) (c : 𝕜) (v : Fin 0 → E x) :
    (curryFin0Equiv (𝕜 := 𝕜) (F := F) (E := E) x).symm c v = c := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.curryFin0Equiv_symm_apply then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.curryFin0Equiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.curryFin0Equiv_symm_apply ``Submission.Bundle.continuousMultilinearMap.curryFin0Equiv_symm_apply

def curryLeftEquiv (s : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 (s + 1) F E x ≃L[𝕜]
      (E x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  (fiberContinuousLinearEquiv (F := F) (s + 1) x).trans
    ((continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E x) 𝕜).toContinuousLinearEquiv.trans
      ((ContinuousLinearEquiv.refl 𝕜 (E x)).arrowCongr
        (fiberContinuousLinearEquiv (F := F) s x).symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.curryLeftEquiv then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.curryLeftEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.curryLeftEquiv ``Submission.Bundle.continuousMultilinearMap.curryLeftEquiv

@[simp] theorem curryLeftEquiv_apply (s : ℕ) (x : B)
    (T : Bundle.continuousMultilinearMap 𝕜 (s + 1) F E x)
    (v : E x) (w : Fin s → E x) :
    curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := E) s x T v w = T (Fin.cons v w) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.curryLeftEquiv_apply then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.curryLeftEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.curryLeftEquiv_apply ``Submission.Bundle.continuousMultilinearMap.curryLeftEquiv_apply

@[simp] theorem curryLeftEquiv_symm_apply (s : ℕ) (x : B)
    (A : E x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 s F E x)
    (v : Fin (s + 1) → E x) :
    (curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := E) s x).symm A v = A (v 0) (Fin.tail v) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.curryLeftEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.curryLeftEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.curryLeftEquiv_symm_apply ``Submission.Bundle.continuousMultilinearMap.curryLeftEquiv_symm_apply

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

noncomputable instance instFiniteDimensional (s : ℕ) (x : B) :
    FiniteDimensional 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  have : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  exact (continuousLinearEquivAt (F := F) (E := E) s x).symm.toLinearEquiv.finiteDimensional

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.instFiniteDimensional then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.instFiniteDimensional"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.instFiniteDimensional ``Submission.Bundle.continuousMultilinearMap.instFiniteDimensional

@[simp]
theorem finrank_eq (s : ℕ) (x : B) :
    Module.finrank 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) =
    (Module.finrank 𝕜 F) ^ s := by
  rw [(continuousLinearEquivAt (F := F) (E := E) s x).toLinearEquiv.finrank_eq,
      finrank_continuousMultilinearMap s]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.finrank_eq then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.finrank_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.finrank_eq ``Submission.Bundle.continuousMultilinearMap.finrank_eq

end Bundle.continuousMultilinearMap

end
