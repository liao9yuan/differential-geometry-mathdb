/-
Authors: Jack McCarthy
Modified by: Ziyang Qin
-/
import Submission.DifferentialGeometry.Tensor.Mixed.Bundle
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Section
import Submission.DifferentialGeometry.Bundle.Section

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
namespace DifferentialGeometry


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap

open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

abbrev MixedSection
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB] (IB : ModelWithCorners 𝕜 EB HB)
    {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
    (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (_root_.Bundle.TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E]
    (n : WithTop ℕ∞) (r s : ℕ) :=
  @ContMDiffSection 𝕜 _ EB _ _ HB _ IB B _ _
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    _ _ n
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
              Bundle.continuousMultilinearMap 𝕜 s F E x)
    (Bundle.continuousMultilinearMap.mixedTopology r s)
    (fun _ => inferInstance)
    (Bundle.continuousMultilinearMap.mixedFiberBundle r s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MixedSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MixedSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MixedSection ``Submission.DifferentialGeometry.MixedSection

namespace MixedSection

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

noncomputable def toMultilinearSection {s : ℕ}
    (T : MixedSection 𝕜 F IB E n 0 s) :
    MultilinearSection 𝕜 F IB E n s :=
  ⟨fun x => T x (ContinuousMultilinearMap.constOfIsEmpty 𝕜 (fun _ : Fin 0 => E x) 1), by
    exact T.contMDiff.clm_bundle_apply
      (MultilinearSection.fromScalarField (F := F) (E := E) n
        (fun _ => (1 : 𝕜)) contMDiff_const).contMDiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MixedSection.toMultilinearSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MixedSection.toMultilinearSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MixedSection.toMultilinearSection ``Submission.DifferentialGeometry.MixedSection.toMultilinearSection

noncomputable def eval₀ (x : B) :
    Bundle.continuousMultilinearMap 𝕜 0 F E x →L[𝕜] 𝕜 :=
  (continuousMultilinearCurryFin0 𝕜 F 𝕜).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (Bundle.continuousMultilinearMap.toModelL (𝕜 := 𝕜) (F := F) (E := E) 0 x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MixedSection.eval₀ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MixedSection.eval₀"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MixedSection.eval₀ ``Submission.DifferentialGeometry.MixedSection.eval₀

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem eval₀_apply (x : B) (T : Bundle.continuousMultilinearMap 𝕜 0 F E x) :
    eval₀ (F := F) (E := E) x T = T Fin.elim0 := by
  change (continuousMultilinearCurryFin0 𝕜 F 𝕜)
      (Bundle.continuousMultilinearMap.toModel (F := F) (E := E) T) = T Fin.elim0
  rw [continuousMultilinearCurryFin0_apply]
  exact congrArg T (Subsingleton.elim _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MixedSection.eval₀_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MixedSection.eval₀_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MixedSection.eval₀_apply ``Submission.DifferentialGeometry.MixedSection.eval₀_apply

noncomputable def fromMultilinearSection {s : ℕ}
    (α : MultilinearSection 𝕜 F IB E n s) :
    MixedSection 𝕜 F IB E n 0 s :=
  ⟨fun x => (eval₀ (F := F) (E := E) x).smulRight (α x), by
    intro x₀
    rw [_root_.Bundle.contMDiffAt_section x₀]
    have hα := (_root_.Bundle.contMDiffAt_section x₀).mp α.contMDiff.contMDiffAt
    refine ((contMDiffAt_const
      (c := ContinuousLinearMap.smulRightL 𝕜
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (continuousMultilinearCurryFin0 𝕜 F 𝕜).toContinuousLinearMap)).clm_apply
      hα).congr_of_eventuallyEq ?_
    filter_upwards [(_root_.FiberBundle.trivializationAt F E x₀).open_baseSet.mem_nhds
      (_root_.FiberBundle.mem_baseSet_trivializationAt F E x₀)] with x hx
    have hx_s : x ∈ (_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 s F E) x₀).baseSet := hx
    apply ContinuousLinearMap.ext
    intro ω₀
    apply ContinuousMultilinearMap.ext
    intro m
    rw [hom_trivializationAt_apply]
    simp only [ContinuousLinearMap.inCoordinates,
      ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smulRightL_apply_apply,
      smul_apply,
      map_smul,
      eval₀_apply]
    rw [Bundle.continuousMultilinearMap.triv_zero_symmL_apply_elim0
      (F := F) (E := E) x₀ x hx ω₀]
    congr 2
    rw [(_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 s F E) x₀).continuousLinearMapAt_apply 𝕜]
    exact congrFun ((_root_.FiberBundle.trivializationAt _ (Bundle.continuousMultilinearMap 𝕜 s F E) x₀
      ).coe_linearMapAt_of_mem (R := 𝕜) hx_s) (α x)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MixedSection.fromMultilinearSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MixedSection.fromMultilinearSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MixedSection.fromMultilinearSection ``Submission.DifferentialGeometry.MixedSection.fromMultilinearSection

def smulByFun {r s : ℕ}
    (φ : B → 𝕜) (hφ : ContMDiff IB 𝓘(𝕜) n φ)
    (T : MixedSection 𝕜 F IB E n r s) :
    MixedSection 𝕜 F IB E n r s :=
  ⟨fun x => φ x • T x, hφ.smul_section T.contMDiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MixedSection.smulByFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MixedSection.smulByFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MixedSection.smulByFun ``Submission.DifferentialGeometry.MixedSection.smulByFun

@[simp]
theorem toMultilinearSection_add {s : ℕ}
    (T₁ T₂ : MixedSection 𝕜 F IB E n 0 s) :
    (T₁ + T₂).toMultilinearSection n =
      T₁.toMultilinearSection n + T₂.toMultilinearSection n := by
  apply ContMDiffSection.ext
  intro x
  apply Bundle.continuousMultilinearMap.ext
  intro m
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MixedSection.toMultilinearSection_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MixedSection.toMultilinearSection_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MixedSection.toMultilinearSection_add ``Submission.DifferentialGeometry.MixedSection.toMultilinearSection_add

@[simp]
theorem toMultilinearSection_smulByFun {s : ℕ}
    (φ : B → 𝕜) (hφ : ContMDiff IB 𝓘(𝕜) n φ)
    (T : MixedSection 𝕜 F IB E n 0 s) :
    (smulByFun n φ hφ T).toMultilinearSection n =
      MultilinearSection.smulByFun n φ hφ (T.toMultilinearSection n) := by
  apply ContMDiffSection.ext
  intro x
  apply Bundle.continuousMultilinearMap.ext
  intro m
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MixedSection.toMultilinearSection_smulByFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MixedSection.toMultilinearSection_smulByFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MixedSection.toMultilinearSection_smulByFun ``Submission.DifferentialGeometry.MixedSection.toMultilinearSection_smulByFun

omit [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem zero_fiber_eq_smul_constOfIsEmpty {x : B}
    (ψ : Bundle.continuousMultilinearMap 𝕜 0 F E x) :
    (ψ Fin.elim0) • (ContinuousMultilinearMap.constOfIsEmpty 𝕜 (fun _ : Fin 0 => E x) 1
      : Bundle.continuousMultilinearMap 𝕜 0 F E x) = ψ := by
  apply Bundle.continuousMultilinearMap.ext
  intro m
  rw [smul_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, smul_eq_mul, mul_one]
  exact (congrArg ψ (Subsingleton.elim _ _)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MixedSection.zero_fiber_eq_smul_constOfIsEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MixedSection.zero_fiber_eq_smul_constOfIsEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MixedSection.zero_fiber_eq_smul_constOfIsEmpty ``Submission.DifferentialGeometry.MixedSection.zero_fiber_eq_smul_constOfIsEmpty

@[simp]
theorem toMultilinearSection_fromMultilinearSection {s : ℕ}
    (α : MultilinearSection 𝕜 F IB E n s) :
    (fromMultilinearSection n α).toMultilinearSection n = α := by
  apply ContMDiffSection.ext
  intro x
  change ((eval₀ (F := F) (E := E) x).smulRight (α x))
      (ContinuousMultilinearMap.constOfIsEmpty 𝕜 (fun _ : Fin 0 => E x) 1) = α x
  rw [ContinuousLinearMap.smulRight_apply, eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MixedSection.toMultilinearSection_fromMultilinearSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MixedSection.toMultilinearSection_fromMultilinearSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MixedSection.toMultilinearSection_fromMultilinearSection ``Submission.DifferentialGeometry.MixedSection.toMultilinearSection_fromMultilinearSection

@[simp]
theorem fromMultilinearSection_toMultilinearSection {s : ℕ}
    (T : MixedSection 𝕜 F IB E n 0 s) :
    fromMultilinearSection n (T.toMultilinearSection n) = T := by
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro ψ
  change ((eval₀ (F := F) (E := E) x).smulRight (T x
      (ContinuousMultilinearMap.constOfIsEmpty 𝕜 (fun _ : Fin 0 => E x) 1))) ψ = T x ψ
  rw [ContinuousLinearMap.smulRight_apply, eval₀_apply]
  rw [← map_smul (T x), zero_fiber_eq_smul_constOfIsEmpty ψ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MixedSection.fromMultilinearSection_toMultilinearSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MixedSection.fromMultilinearSection_toMultilinearSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MixedSection.fromMultilinearSection_toMultilinearSection ``Submission.DifferentialGeometry.MixedSection.fromMultilinearSection_toMultilinearSection

theorem fromMultilinearSection_add {s : ℕ}
    (α β : MultilinearSection 𝕜 F IB E n s) (x : B) :
    (fromMultilinearSection n (α + β)).1 x =
    (fromMultilinearSection n α).1 x + (fromMultilinearSection n β).1 x := by
  change (eval₀ (F := F) (E := E) x).smulRight (α.1 x + β.1 x) =
    (eval₀ (F := F) (E := E) x).smulRight (α.1 x) +
      (eval₀ (F := F) (E := E) x).smulRight (β.1 x)
  apply ContinuousLinearMap.ext
  intro ψ
  rw [add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
    smul_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MixedSection.fromMultilinearSection_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MixedSection.fromMultilinearSection_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MixedSection.fromMultilinearSection_add ``Submission.DifferentialGeometry.MixedSection.fromMultilinearSection_add

theorem fromMultilinearSection_smulByFun {s : ℕ}
    (φ : B → 𝕜) (hφ : ContMDiff IB 𝓘(𝕜) n φ)
    (α : MultilinearSection 𝕜 F IB E n s) (x : B) :
    (fromMultilinearSection n (MultilinearSection.smulByFun n φ hφ α)).1 x =
    φ x • (fromMultilinearSection n α).1 x := by
  change (eval₀ (F := F) (E := E) x).smulRight (φ x • α.1 x) =
    φ x • (eval₀ (F := F) (E := E) x).smulRight (α.1 x)
  apply ContinuousLinearMap.ext
  intro ψ
  rw [smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, _root_.SMulCommClass.smul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MixedSection.fromMultilinearSection_smulByFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MixedSection.fromMultilinearSection_smulByFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MixedSection.fromMultilinearSection_smulByFun ``Submission.DifferentialGeometry.MixedSection.fromMultilinearSection_smulByFun

end MixedSection

section BundleEquiv

open _root_.Submission.DifferentialGeometry.MixedSection

variable {s : ℕ}

noncomputable def multilinearBundleMixedBundleEquiv
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM]
    {IM : ModelWithCorners ℝ EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
    {FM : Type*} [NormedAddCommGroup FM] [NormedSpace ℝ FM] [FiniteDimensional ℝ FM]
    [CompleteSpace ℝ]
    {EM' : M → Type*} [∀ x, NormedAddCommGroup (EM' x)] [∀ x, NormedSpace ℝ (EM' x)]
    [TopologicalSpace (_root_.Bundle.TotalSpace FM EM')]
    [FiberBundle FM EM'] [VectorBundle ℝ FM EM']
    {nm : ℕ∞} [Fact (1 ≤ nm)] [ContMDiffVectorBundle nm FM EM' IM]
    [IsManifold IM ∞ M] [T2Space M]
    [FiniteDimensional ℝ EM] :
    ContMDiffVectorBundleEquiv ℝ IM nm
      (ContinuousMultilinearMap ℝ (fun _ : Fin s => FM) ℝ)
      (Bundle.continuousMultilinearMap ℝ s FM EM')
      (ContinuousMultilinearMap ℝ (fun _ : Fin 0 => FM) ℝ →L[ℝ]
       ContinuousMultilinearMap ℝ (fun _ : Fin s => FM) ℝ)
      (fun x => Bundle.continuousMultilinearMap ℝ 0 FM EM' x →L[ℝ]
                Bundle.continuousMultilinearMap ℝ s FM EM' x) := by
  let Fequiv : Cₛ^nm⟮IM; ContinuousMultilinearMap ℝ (fun _ : Fin s => FM) ℝ,
        Bundle.continuousMultilinearMap ℝ s FM EM'⟯
      ≃ₗ[C^nm⟮IM, M; ℝ⟯]
      Cₛ^nm⟮IM; ContinuousMultilinearMap ℝ (fun _ : Fin 0 => FM) ℝ →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin s => FM) ℝ,
        fun x => Bundle.continuousMultilinearMap ℝ 0 FM EM' x →L[ℝ]
                  Bundle.continuousMultilinearMap ℝ s FM EM' x⟯ :=
    { toFun := fun α => fromMultilinearSection nm α
      invFun := fun T => toMultilinearSection nm T
      map_add' := fun α β => by
        apply ContMDiffSection.ext; intro x
        exact fromMultilinearSection_add nm α β x
      map_smul' := fun φ α => by
        apply ContMDiffSection.ext; intro x
        exact fromMultilinearSection_smulByFun nm φ φ.contMDiff α x
      left_inv := fun α => toMultilinearSection_fromMultilinearSection nm α
      right_inv := fun T => fromMultilinearSection_toMultilinearSection nm T }
  exact ContMDiffVectorBundleEquiv.ofLinearEquivSection Fequiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.multilinearBundleMixedBundleEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.multilinearBundleMixedBundleEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.multilinearBundleMixedBundleEquiv ``Submission.DifferentialGeometry.multilinearBundleMixedBundleEquiv

end BundleEquiv

end DifferentialGeometry
end
