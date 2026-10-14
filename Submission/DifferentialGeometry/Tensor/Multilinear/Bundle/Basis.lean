/-
Authors: Jack McCarthy
-/
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Tensor.Multilinear


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set

open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

local notation "MLF" s => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

noncomputable instance multilinearMap_finiteDimensional (s : ℕ) :
    FiniteDimensional 𝕜 (MultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) := by
  have : Module.Finite 𝕜 F := inferInstance
  have : Module.Free 𝕜 F := inferInstance
  have : Module.Finite 𝕜 𝕜 := inferInstance
  have : Module.Free 𝕜 𝕜 := inferInstance
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.multilinearMap_finiteDimensional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.multilinearMap_finiteDimensional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.multilinearMap_finiteDimensional ``Submission.DifferentialGeometry.Tensor.Multilinear.multilinearMap_finiteDimensional

noncomputable instance continuousMultilinearMap_finiteDimensional (s : ℕ) :
    FiniteDimensional 𝕜 (MLF s) := by
  have : FiniteDimensional 𝕜 (MultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    multilinearMap_finiteDimensional s
  exact FiniteDimensional.of_injective
    ContinuousMultilinearMap.toMultilinearMapLinear
    ContinuousMultilinearMap.toMultilinearMap_injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_finiteDimensional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_finiteDimensional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_finiteDimensional ``Submission.DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_finiteDimensional

theorem finrank_continuousMultilinearMap (s : ℕ) :
    Module.finrank 𝕜 (MLF s) = (Module.finrank 𝕜 F) ^ s := by
  induction s with
  | zero =>
    have e := continuousMultilinearCurryFin0 𝕜 F 𝕜
    rw [e.toLinearEquiv.finrank_eq]
    simp [pow_zero, Module.finrank_self]
  | succ s ih =>
    have e := continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (s + 1) => F) 𝕜
    rw [e.toLinearEquiv.finrank_eq]
    have : FiniteDimensional 𝕜 (MLF s) := continuousMultilinearMap_finiteDimensional s
    have : Module.Free 𝕜 F := inferInstance
    have : Module.Free 𝕜 (MLF s) := inferInstance
    have e2 : (F →L[𝕜] MLF s) ≃ₗ[𝕜] (F →ₗ[𝕜] MLF s) := LinearMap.toContinuousLinearMap.symm
    rw [e2.finrank_eq, Module.finrank_linearMap 𝕜 𝕜, ih]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.finrank_continuousMultilinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.finrank_continuousMultilinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.finrank_continuousMultilinearMap ``Submission.DifferentialGeometry.Tensor.Multilinear.finrank_continuousMultilinearMap

noncomputable def continuousMultilinearMapBasisElem {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s : ℕ) (σ : Fin s → Fin d) : MLF s :=
  (ContinuousMultilinearMap.mkPiRing 𝕜 (Fin s) (1 : 𝕜)).compContinuousLinearMap
    (fun j => LinearMap.toContinuousLinearMap (b.coord (σ j)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapBasisElem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapBasisElem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapBasisElem ``Submission.DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapBasisElem

theorem continuousMultilinearMap_basisElem_apply {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F) (s : ℕ)
    (σ σ' : Fin s → Fin d) :
    continuousMultilinearMapBasisElem b s σ (fun j => b (σ' j)) =
    if σ = σ' then 1 else 0 := by
  simp_rw [continuousMultilinearMapBasisElem,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiRing_apply, smul_eq_mul, mul_one,
    LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : σ = σ'
  · subst h; simp
  · simp only [h, ite_false]
    have ⟨j, hj⟩ : ∃ j, σ j ≠ σ' j := by contrapose! h; exact funext h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg (Ne.symm hj))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_basisElem_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_basisElem_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_basisElem_apply ``Submission.DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_basisElem_apply

theorem continuousMultilinearMap_basisElem_linearIndependent {d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F) (s : ℕ) :
    LinearIndependent 𝕜 (continuousMultilinearMapBasisElem b s) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc σ'
  have h1 : (∑ σ : Fin s → Fin d, c σ • continuousMultilinearMapBasisElem b s σ)
      (fun j => b (σ' j)) = 0 := by rw [hc]; rfl
  simp only [sum_apply, smul_apply,
    continuousMultilinearMap_basisElem_apply] at h1
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
  rwa [smul_eq_mul, mul_one] at h1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_basisElem_linearIndependent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_basisElem_linearIndependent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_basisElem_linearIndependent ``Submission.DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_basisElem_linearIndependent

noncomputable def continuousMultilinearMapBasis {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s : ℕ) : Module.Basis (Fin s → Fin d) 𝕜 (MLF s) :=
  Module.Basis.mk (continuousMultilinearMap_basisElem_linearIndependent b s)
    ((continuousMultilinearMap_basisElem_linearIndependent b s).span_eq_top_of_card_eq_finrank'
      (by
        have hd : Module.finrank 𝕜 F = d := by
          rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          finrank_continuousMultilinearMap, hd])).ge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapBasis ``Submission.DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapBasis

theorem continuousMultilinearMap_basis_repr {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s : ℕ) (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) (σ : Fin s → Fin d) :
    (continuousMultilinearMapBasis b s).repr f σ = f (fun j => b (σ j)) := by
  have hbasis : ∀ ρ, (continuousMultilinearMapBasis b s) ρ =
      continuousMultilinearMapBasisElem b s ρ :=
    fun ρ => congr_fun (Module.Basis.coe_mk
      (continuousMultilinearMap_basisElem_linearIndependent b s) _) ρ
  conv_rhs => rw [← (continuousMultilinearMapBasis b s).sum_repr f]
  simp only [sum_apply, smul_apply,
    smul_eq_mul, hbasis, continuousMultilinearMap_basisElem_apply,
    mul_ite, mul_one, _root_.MulZeroClass.mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_basis_repr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_basis_repr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_basis_repr ``Submission.DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_basis_repr

section smooth

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  (E : B → Type*) [Π x, AddCommMonoid (E x)] [Π x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [Π x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

omit [ContMDiffVectorBundle n F E IB] in
theorem contMDiff_multilinearSection_iff_coord {d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F) {s : ℕ}
    (f : ∀ x : B, _root_.Submission.Bundle.continuousMultilinearMap 𝕜 s F E x) :
    ContMDiff IB (IB.prod 𝓘(𝕜, MLF s)) n
      (fun x => TotalSpace.mk' (MLF s) x (f x)) ↔
    ∀ σ : Fin s → Fin d, ∀ x₀ : B,
      ContMDiffAt IB 𝓘(𝕜, 𝕜) n
        (fun x => (continuousMultilinearMapBasis b s).repr
          (_root_.FiberBundle.trivializationAt (MLF s)
            (_root_.Submission.Bundle.continuousMultilinearMap 𝕜 s F E) x₀ ⟨x, f x⟩).2 σ) x₀ := by
  set Bb := continuousMultilinearMapBasis b s
  constructor
  · intro hf σ x₀
    have hsec := (_root_.Bundle.contMDiffAt_section x₀).mp hf.contMDiffAt
    exact (LinearMap.toContinuousLinearMap (Bb.coord σ)).contMDiffAt.comp x₀ hsec
  · intro hcoord x₀
    rw [_root_.Bundle.contMDiffAt_section]
    let g := fun x => (_root_.FiberBundle.trivializationAt (MLF s)
        (_root_.Submission.Bundle.continuousMultilinearMap 𝕜 s F E) x₀ ⟨x, f x⟩).2
    change ContMDiffAt IB 𝓘(𝕜, MLF s) n g x₀
    rw [show g = fun x => Bb.equivFun.symm (Bb.equivFun (g x)) from
        funext fun x => (Bb.equivFun.symm_apply_apply (g x)).symm]
    exact (Bb.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt).comp x₀
      (contMDiffAt_pi_space.mpr fun σ => hcoord σ x₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.contMDiff_multilinearSection_iff_coord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.contMDiff_multilinearSection_iff_coord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.contMDiff_multilinearSection_iff_coord ``Submission.DifferentialGeometry.Tensor.Multilinear.contMDiff_multilinearSection_iff_coord

end smooth

end

end DifferentialGeometry.Tensor.Multilinear
