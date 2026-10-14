/-
Authors: Jack McCarthy (pattern), extended for slot permutation of smooth sections
-/
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.TensorProduct

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
variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

theorem triv_coord_domDomCongr {s s' d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F)
    (e : Fin s ≃ Fin s')
    (idx : Fin s' → Fin d) (x₀ x : B)
    (α : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    (continuousMultilinearMapBasis b s').repr
      (_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s' => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 s' F E x) x₀
        ⟨x, ContinuousMultilinearMap.domDomCongr e α⟩).2 idx =
    (continuousMultilinearMapBasis b s).repr
      (_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀ ⟨x, α⟩).2
        (idx ∘ e) := by
  simp_rw [continuousMultilinearMap_basis_repr]
  have htriv : ∀ {m : ℕ} (T : Bundle.continuousMultilinearMap 𝕜 m F E x) (w : Fin m → F),
      (_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin m => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 m F E x) x₀ ⟨x, T⟩).2 w =
      T (fun i => (_root_.FiberBundle.trivializationAt F E x₀).symmL 𝕜 x (w i)) := by
    intro m T w; rfl
  simp_rw [htriv, ContinuousMultilinearMap.domDomCongr_apply, Function.comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.triv_coord_domDomCongr then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.triv_coord_domDomCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.triv_coord_domDomCongr ``Submission.Bundle.continuousMultilinearMap.triv_coord_domDomCongr

end Bundle.continuousMultilinearMap

namespace DifferentialGeometry.MultilinearSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

noncomputable def domDomCongr {s s' : ℕ} (e : Fin s ≃ Fin s')
    (α : MultilinearSection 𝕜 F IB E n s) :
    MultilinearSection 𝕜 F IB E n s' :=
  ⟨fun x => ContinuousMultilinearMap.domDomCongr e (α x), by
    let d := Module.finrank 𝕜 F
    let b : Module.Basis (Fin d) 𝕜 F := Module.finBasis 𝕜 F
    rw [contMDiff_multilinearSection_iff_coord E n b]
    intro idx x₀
    have hα := ((contMDiff_multilinearSection_iff_coord E n b
      (fun x => (α x : Bundle.continuousMultilinearMap 𝕜 s F E x))).mp α.contMDiff)
    simp_rw [Bundle.continuousMultilinearMap.triv_coord_domDomCongr b e idx x₀ _ (α _)]
    exact hα (idx ∘ e) x₀⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.domDomCongr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.domDomCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.domDomCongr ``Submission.DifferentialGeometry.MultilinearSection.domDomCongr

@[simp] theorem domDomCongr_apply {s s' : ℕ} (e : Fin s ≃ Fin s')
    (α : MultilinearSection 𝕜 F IB E n s) (x : B) :
    (domDomCongr (IB := IB) n e α) x = ContinuousMultilinearMap.domDomCongr e (α x) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.domDomCongr_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.domDomCongr_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.domDomCongr_apply ``Submission.DifferentialGeometry.MultilinearSection.domDomCongr_apply

@[simp] theorem domDomCongr_refl {s : ℕ} (α : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n (Equiv.refl (Fin s)) α = α := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  simp [domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.domDomCongr_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.domDomCongr_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.domDomCongr_refl ``Submission.DifferentialGeometry.MultilinearSection.domDomCongr_refl

@[simp] theorem domDomCongr_zero {s s' : ℕ} (e : Fin s ≃ Fin s') :
    domDomCongr (IB := IB) n e (0 : MultilinearSection 𝕜 F IB E n s)
      = (0 : MultilinearSection 𝕜 F IB E n s') := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  simp [domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContMDiffSection.coe_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.domDomCongr_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.domDomCongr_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.domDomCongr_zero ``Submission.DifferentialGeometry.MultilinearSection.domDomCongr_zero

theorem domDomCongr_id_of_valPres {s : ℕ} (e : Fin s ≃ Fin s)
    (he : ∀ i, ((e i : Fin s) : ℕ) = (i : ℕ))
    (α : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n e α = α := by
  have hee : e = Equiv.refl (Fin s) := Equiv.ext fun i => Fin.ext (he i)
  rw [hee, domDomCongr_refl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.domDomCongr_id_of_valPres then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.domDomCongr_id_of_valPres"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.domDomCongr_id_of_valPres ``Submission.DifferentialGeometry.MultilinearSection.domDomCongr_id_of_valPres

theorem domDomCongr_trans {s s' s'' : ℕ} (e₁ : Fin s ≃ Fin s') (e₂ : Fin s' ≃ Fin s'')
    (α : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n e₂ (domDomCongr (IB := IB) n e₁ α)
      = domDomCongr (IB := IB) n (e₁.trans e₂) α := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  simp [domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.domDomCongr_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.domDomCongr_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.domDomCongr_trans ``Submission.DifferentialGeometry.MultilinearSection.domDomCongr_trans

theorem domDomCongr_add {s s' : ℕ} (e : Fin s ≃ Fin s')
    (α β : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n e (α + β)
      = domDomCongr (IB := IB) n e α + domDomCongr (IB := IB) n e β := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  simp [domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.domDomCongr_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.domDomCongr_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.domDomCongr_add ``Submission.DifferentialGeometry.MultilinearSection.domDomCongr_add

theorem domDomCongr_smul {s s' : ℕ} (e : Fin s ≃ Fin s') (c : 𝕜)
    (α : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n e (c • α) = c • domDomCongr (IB := IB) n e α := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  simp [domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContMDiffSection.coe_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.domDomCongr_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.domDomCongr_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.domDomCongr_smul ``Submission.DifferentialGeometry.MultilinearSection.domDomCongr_smul

theorem product_domDomCongr_left {s s' q : ℕ} (e : Fin s ≃ Fin s')
    (α : MultilinearSection 𝕜 F IB E n s) (β : MultilinearSection 𝕜 F IB E n q) :
    product (IB := IB) n (domDomCongr (IB := IB) n e α) β
      = domDomCongr (IB := IB) n
          (finSumFinEquiv.symm.trans
            ((Equiv.sumCongr e (Equiv.refl (Fin q))).trans finSumFinEquiv))
          (product (IB := IB) n α β) := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  change Bundle.continuousMultilinearMap.productFun
      ((domDomCongr (IB := IB) n e α) x) (β x) V = _
  rw [domDomCongr_apply, Bundle.continuousMultilinearMap.product_fun_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (domDomCongr (IB := IB) n
      (finSumFinEquiv.symm.trans
        ((Equiv.sumCongr e (Equiv.refl (Fin q))).trans finSumFinEquiv))
      (product (IB := IB) n α β)) x V
    = Bundle.continuousMultilinearMap.productFun (α x) (β x)
        (fun i => V (finSumFinEquiv (Equiv.sumCongr e (Equiv.refl (Fin q))
          (finSumFinEquiv.symm i)))) from rfl]
  rw [Bundle.continuousMultilinearMap.product_fun_apply]
  congr 1
  · congr 1
    funext i
    simp only [Function.comp_apply, Equiv.sumCongr_apply,
      finSumFinEquiv_symm_apply_castAdd, Sum.map_inl, finSumFinEquiv_apply_left]
  · congr 1
    funext j
    simp only [Function.comp_apply, Equiv.sumCongr_apply,
      finSumFinEquiv_symm_apply_natAdd, Sum.map_inr, finSumFinEquiv_apply_right,
      Equiv.refl_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.product_domDomCongr_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.product_domDomCongr_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.product_domDomCongr_left ``Submission.DifferentialGeometry.MultilinearSection.product_domDomCongr_left

end DifferentialGeometry.MultilinearSection
