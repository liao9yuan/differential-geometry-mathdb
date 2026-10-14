/-
Authors: Jack McCarthy
-/
import Submission.DifferentialGeometry.Tensor.Multilinear.PredualBasis
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Basis
import Submission.DifferentialGeometry.Tensor.Multilinear.BundleComp
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Fiber
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Section
import Submission.DifferentialGeometry.Bundle.Dual
import Submission.DifferentialGeometry.Bundle.Equiv
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Topology.VectorBundle.FiniteDimensional

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Tensor.Multilinear

noncomputable section

open _root_.Module _root_.Submission.Module

namespace ContinuousMultilinearMap
open _root_.ContinuousMultilinearMap

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

open _root_.ContinuousMultilinearMap in
noncomputable def tensorOfDualLinearForms (r : ℕ) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
  ContinuousMultilinearMap.compContinuousLinearMapLRight (E := fun _ : Fin r => F)
    (ContinuousMultilinearMap.mkPiAlgebra 𝕜 (Fin r) 𝕜)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMultilinearMap.tensorOfDualLinearForms then
    throwError "Refusing to shadow existing declaration ContinuousMultilinearMap.tensorOfDualLinearForms"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMultilinearMap.tensorOfDualLinearForms ``Submission.ContinuousMultilinearMap.tensorOfDualLinearForms

variable {𝕜 F}

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
open _root_.ContinuousMultilinearMap in
@[simp]
theorem tensorOfDualLinearForms_apply (r : ℕ) (α : Fin r → (F →L[𝕜] 𝕜))
    (v : Fin r → F) :
    tensorOfDualLinearForms 𝕜 F r α v = ∏ i, α i (v i) := by
  simp [tensorOfDualLinearForms,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMultilinearMap.tensorOfDualLinearForms_apply then
    throwError "Refusing to shadow existing declaration ContinuousMultilinearMap.tensorOfDualLinearForms_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMultilinearMap.tensorOfDualLinearForms_apply ``Submission.ContinuousMultilinearMap.tensorOfDualLinearForms_apply

variable (𝕜 F)

open _root_.ContinuousMultilinearMap in
noncomputable def dualMultilinearLinearMap (r : ℕ) :
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) →L[𝕜] 𝕜) →ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 where
  toFun φ := φ.compContinuousMultilinearMap (tensorOfDualLinearForms 𝕜 F r)
  map_add' φ ψ := by
    ext α
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
      add_apply, add_apply,
      Function.comp_apply]
  map_smul' c φ := by
    ext α
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
      smul_apply, smul_apply,
      Function.comp_apply, RingHom.id_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMultilinearMap.dualMultilinearLinearMap then
    throwError "Refusing to shadow existing declaration ContinuousMultilinearMap.dualMultilinearLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMultilinearMap.dualMultilinearLinearMap ``Submission.ContinuousMultilinearMap.dualMultilinearLinearMap

variable {𝕜 F}

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
open _root_.ContinuousMultilinearMap in
@[simp]
theorem dualMultilinearLinearMap_apply (r : ℕ)
    (φ : (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) →L[𝕜] 𝕜)
    (α : Fin r → (F →L[𝕜] 𝕜)) :
    dualMultilinearLinearMap 𝕜 F r φ α =
      φ ((tensorOfDualLinearForms 𝕜 F r) α) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMultilinearMap.dualMultilinearLinearMap_apply then
    throwError "Refusing to shadow existing declaration ContinuousMultilinearMap.dualMultilinearLinearMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMultilinearMap.dualMultilinearLinearMap_apply ``Submission.ContinuousMultilinearMap.dualMultilinearLinearMap_apply

variable (𝕜 F)

open _root_.ContinuousMultilinearMap in
theorem basisElem_eq_tensorOfDualLinearForms {d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F) (r : ℕ) (σ : Fin r → Fin d) :
    continuousMultilinearMapBasisElem (𝕜 := 𝕜) (F := F) b r σ
      = tensorOfDualLinearForms 𝕜 F r
        (fun i => LinearMap.toContinuousLinearMap (b.coord (σ i))) := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [tensorOfDualLinearForms_apply]
  simp [continuousMultilinearMapBasisElem,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiRing_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMultilinearMap.basisElem_eq_tensorOfDualLinearForms then
    throwError "Refusing to shadow existing declaration ContinuousMultilinearMap.basisElem_eq_tensorOfDualLinearForms"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMultilinearMap.basisElem_eq_tensorOfDualLinearForms ``Submission.ContinuousMultilinearMap.basisElem_eq_tensorOfDualLinearForms

open _root_.ContinuousMultilinearMap in
private noncomputable def dualMultilinearInverse (r : ℕ)
    (Ψ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :
    haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
      continuousMultilinearMap_finiteDimensional r
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) →L[𝕜] 𝕜 :=
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  LinearMap.toContinuousLinearMap
    ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := F) (Module.finBasis 𝕜 F) r).constr 𝕜
      (fun σ => Ψ (fun i =>
        LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 F).coord (σ i)))))

run_cmd do
  let target := ``Submission.ContinuousMultilinearMap.dualMultilinearInverse
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ContinuousMultilinearMap.dualMultilinearInverse target :: scope.openDecls } }

variable {𝕜 F}

open _root_.ContinuousMultilinearMap in
private theorem dualMultilinearInverse_basisElem (r : ℕ)
    (Ψ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
    (σ : Fin r → Fin (Module.finrank 𝕜 F)) :
    dualMultilinearInverse 𝕜 F r Ψ
        (continuousMultilinearMapBasisElem (𝕜 := 𝕜) (F := F) (Module.finBasis 𝕜 F) r σ) =
      Ψ (fun i =>
        LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 F).coord (σ i))) := by
  have : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  let b := Module.finBasis 𝕜 F
  let bMLF := continuousMultilinearMapBasis (𝕜 := 𝕜) (F := F) b r
  have hb_eq : (bMLF σ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) =
      continuousMultilinearMapBasisElem b r σ :=
    congr_fun (Module.Basis.coe_mk
      (continuousMultilinearMap_basisElem_linearIndependent b r) _) σ
  change LinearMap.toContinuousLinearMap
      (bMLF.constr 𝕜 (fun σ => Ψ (fun i =>
        LinearMap.toContinuousLinearMap (b.coord (σ i)))))
      (continuousMultilinearMapBasisElem b r σ) = _
  rw [LinearMap.coe_toContinuousLinearMap', ← hb_eq, Basis.constr_basis]

run_cmd do
  let target := ``Submission.ContinuousMultilinearMap.dualMultilinearInverse_basisElem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ContinuousMultilinearMap.dualMultilinearInverse_basisElem target :: scope.openDecls } }

variable (𝕜 F)

open _root_.ContinuousMultilinearMap in
noncomputable def dualMultilinearInverseMap (r : ℕ) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 →ₗ[𝕜]
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) →L[𝕜] 𝕜) where
  toFun := dualMultilinearInverse 𝕜 F r
  map_add' Ψ₁ Ψ₂ := by
    have : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
      continuousMultilinearMap_finiteDimensional r
    apply ContinuousLinearMap.ext
    intro x
    let b := Module.finBasis 𝕜 F
    let bMLF := continuousMultilinearMapBasis (𝕜 := 𝕜) (F := F) b r
    have h_basis : ∀ σ,
        dualMultilinearInverse 𝕜 F r (Ψ₁ + Ψ₂) (bMLF σ) =
          (dualMultilinearInverse 𝕜 F r Ψ₁ + dualMultilinearInverse 𝕜 F r Ψ₂)
            (bMLF σ) := by
      intro σ
      have hb_eq : (bMLF σ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) =
          continuousMultilinearMapBasisElem b r σ :=
        congr_fun (Module.Basis.coe_mk
          (continuousMultilinearMap_basisElem_linearIndependent b r) _) σ
      rw [hb_eq, add_apply,
        dualMultilinearInverse_basisElem,
        dualMultilinearInverse_basisElem,
        dualMultilinearInverse_basisElem]
      rfl
    have hLHS : ∀ x, dualMultilinearInverse 𝕜 F r (Ψ₁ + Ψ₂) x =
        (dualMultilinearInverse 𝕜 F r Ψ₁ + dualMultilinearInverse 𝕜 F r Ψ₂) x := by
      have := bMLF.ext (f₁ := (dualMultilinearInverse 𝕜 F r (Ψ₁ + Ψ₂)).toLinearMap)
        (f₂ := ((dualMultilinearInverse 𝕜 F r Ψ₁ +
          dualMultilinearInverse 𝕜 F r Ψ₂).toLinearMap)) h_basis
      intro x
      exact congrFun (congrArg DFunLike.coe this) x
    exact hLHS x
  map_smul' c Ψ := by
    have : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
      continuousMultilinearMap_finiteDimensional r
    apply ContinuousLinearMap.ext
    intro x
    let b := Module.finBasis 𝕜 F
    let bMLF := continuousMultilinearMapBasis (𝕜 := 𝕜) (F := F) b r
    have h_basis : ∀ σ,
        dualMultilinearInverse 𝕜 F r (c • Ψ) (bMLF σ) =
          (c • dualMultilinearInverse 𝕜 F r Ψ) (bMLF σ) := by
      intro σ
      have hb_eq : (bMLF σ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) =
          continuousMultilinearMapBasisElem b r σ :=
        congr_fun (Module.Basis.coe_mk
          (continuousMultilinearMap_basisElem_linearIndependent b r) _) σ
      rw [hb_eq, smul_apply,
        dualMultilinearInverse_basisElem,
        dualMultilinearInverse_basisElem]
      rfl
    have hLHS : ∀ x, dualMultilinearInverse 𝕜 F r (c • Ψ) x =
        (c • dualMultilinearInverse 𝕜 F r Ψ) x := by
      have := bMLF.ext (f₁ := (dualMultilinearInverse 𝕜 F r (c • Ψ)).toLinearMap)
        (f₂ := ((c • dualMultilinearInverse 𝕜 F r Ψ).toLinearMap)) h_basis
      intro x
      exact congrFun (congrArg DFunLike.coe this) x
    exact hLHS x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMultilinearMap.dualMultilinearInverseMap then
    throwError "Refusing to shadow existing declaration ContinuousMultilinearMap.dualMultilinearInverseMap"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMultilinearMap.dualMultilinearInverseMap ``Submission.ContinuousMultilinearMap.dualMultilinearInverseMap

variable {𝕜 F}

open _root_.ContinuousMultilinearMap in
theorem dualMultilinearInverseMap_basisElem (r : ℕ)
    (Ψ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
    (σ : Fin r → Fin (Module.finrank 𝕜 F)) :
    dualMultilinearInverseMap 𝕜 F r Ψ
        (continuousMultilinearMapBasisElem (𝕜 := 𝕜) (F := F) (Module.finBasis 𝕜 F) r σ) =
      Ψ (fun i =>
        LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 F).coord (σ i))) :=
  dualMultilinearInverse_basisElem r Ψ σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMultilinearMap.dualMultilinearInverseMap_basisElem then
    throwError "Refusing to shadow existing declaration ContinuousMultilinearMap.dualMultilinearInverseMap_basisElem"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMultilinearMap.dualMultilinearInverseMap_basisElem ``Submission.ContinuousMultilinearMap.dualMultilinearInverseMap_basisElem

variable (𝕜 F)

open _root_.ContinuousMultilinearMap in
theorem dualMultilinearInverseMap_dualMultilinearLinearMap (r : ℕ) :
    (dualMultilinearInverseMap 𝕜 F r).comp (dualMultilinearLinearMap 𝕜 F r) =
      LinearMap.id := by
  have : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  apply LinearMap.ext
  intro φ
  change ((dualMultilinearInverseMap 𝕜 F r) ((dualMultilinearLinearMap 𝕜 F r) φ) : _ →L[𝕜] _)
    = φ
  apply ContinuousLinearMap.ext
  intro x
  let b := Module.finBasis 𝕜 F
  let bMLF := continuousMultilinearMapBasis (𝕜 := 𝕜) (F := F) b r
  have h_basis : ∀ σ,
      ((dualMultilinearInverseMap 𝕜 F r) ((dualMultilinearLinearMap 𝕜 F r) φ) :
          _ →L[𝕜] _) (bMLF σ) = φ (bMLF σ) := by
    intro σ
    have hb_eq : (bMLF σ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) =
        continuousMultilinearMapBasisElem b r σ :=
      congr_fun (Module.Basis.coe_mk
        (continuousMultilinearMap_basisElem_linearIndependent b r) _) σ
    rw [hb_eq, dualMultilinearInverseMap_basisElem,
      show (dualMultilinearLinearMap 𝕜 F r φ) (fun i =>
          LinearMap.toContinuousLinearMap (b.coord (σ i))) =
        φ ((tensorOfDualLinearForms 𝕜 F r) (fun i =>
            LinearMap.toContinuousLinearMap (b.coord (σ i)))) from rfl,
      ← basisElem_eq_tensorOfDualLinearForms]
  have hAll : ∀ x, ((dualMultilinearInverseMap 𝕜 F r) ((dualMultilinearLinearMap 𝕜 F r) φ) :
        _ →L[𝕜] _) x = φ x := by
    have :=
      bMLF.ext (f₁ := ((dualMultilinearInverseMap 𝕜 F r) ((dualMultilinearLinearMap 𝕜 F r) φ)
          : _ →L[𝕜] _).toLinearMap)
        (f₂ := (φ : _ →L[𝕜] _).toLinearMap) h_basis
    intro y
    exact congrFun (congrArg DFunLike.coe this) y
  exact hAll x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMultilinearMap.dualMultilinearInverseMap_dualMultilinearLinearMap then
    throwError "Refusing to shadow existing declaration ContinuousMultilinearMap.dualMultilinearInverseMap_dualMultilinearLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMultilinearMap.dualMultilinearInverseMap_dualMultilinearLinearMap ``Submission.ContinuousMultilinearMap.dualMultilinearInverseMap_dualMultilinearLinearMap

open _root_.ContinuousMultilinearMap in
theorem dualMultilinearLinearMap_dualMultilinearInverseMap (r : ℕ) :
    (dualMultilinearLinearMap 𝕜 F r).comp (dualMultilinearInverseMap 𝕜 F r) =
      LinearMap.id := by
  have : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  apply LinearMap.ext
  intro Ψ
  apply ContinuousMultilinearMap.ext
  intro α
  let b := Module.finBasis 𝕜 F
  have hα : ∀ i, α i = ∑ k, α i (b k) •
      LinearMap.toContinuousLinearMap (b.coord k) := fun i =>
    (cdual_sum_repr (𝕜 := 𝕜) (E := F) b (α i)).symm
  have hα_funext : α = (fun i => ∑ k, α i (b k) •
      LinearMap.toContinuousLinearMap (b.coord k)) := funext hα
  change ((dualMultilinearLinearMap 𝕜 F r) ((dualMultilinearInverseMap 𝕜 F r) Ψ)) α = Ψ α
  rw [dualMultilinearLinearMap_apply]
  change (dualMultilinearInverse 𝕜 F r Ψ : _ →L[𝕜] _)
      ((tensorOfDualLinearForms 𝕜 F r) α) = Ψ α
  change LinearMap.toContinuousLinearMap
      ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := F) b r).constr 𝕜
        (fun σ => Ψ (fun i => LinearMap.toContinuousLinearMap (b.coord (σ i)))))
      ((tensorOfDualLinearForms 𝕜 F r) α) = Ψ α
  rw [LinearMap.coe_toContinuousLinearMap',
    Basis.constr_apply_fintype]
  set bMLF := continuousMultilinearMapBasis (𝕜 := 𝕜) (F := F) b r
  have hcoord : ∀ σ, bMLF.equivFun ((tensorOfDualLinearForms 𝕜 F r) α) σ
      = ∏ i, α i (b (σ i)) := by
    intro σ
    rw [Basis.equivFun_apply, continuousMultilinearMap_basis_repr,
      tensorOfDualLinearForms_apply]
  simp_rw [hcoord]
  conv_rhs => rw [hα_funext, ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [show (fun i => α i (b (σ i)) •
        LinearMap.toContinuousLinearMap (b.coord (σ i))) =
      (fun i => (α i (b (σ i))) •
        (fun j => LinearMap.toContinuousLinearMap (b.coord (σ j))) i) from rfl,
    ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMultilinearMap.dualMultilinearLinearMap_dualMultilinearInverseMap then
    throwError "Refusing to shadow existing declaration ContinuousMultilinearMap.dualMultilinearLinearMap_dualMultilinearInverseMap"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMultilinearMap.dualMultilinearLinearMap_dualMultilinearInverseMap ``Submission.ContinuousMultilinearMap.dualMultilinearLinearMap_dualMultilinearInverseMap

open _root_.ContinuousMultilinearMap in
noncomputable def dualMultilinearEquivMultilinearOfDual (r : ℕ) :
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) →L[𝕜] 𝕜) ≃ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 :=
  LinearEquiv.ofLinearMap
    (dualMultilinearLinearMap 𝕜 F r)
    (dualMultilinearInverseMap 𝕜 F r)
    (dualMultilinearLinearMap_dualMultilinearInverseMap 𝕜 F r)
    (dualMultilinearInverseMap_dualMultilinearLinearMap 𝕜 F r)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual then
    throwError "Refusing to shadow existing declaration ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual ``Submission.ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual

end ContinuousMultilinearMap

open _root_.Bundle _root_.Submission.Bundle

namespace Bundle.continuousMultilinearMap
open _root_.Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]

noncomputable def dualMultilinearLinearEquivAt (r : ℕ) (x : B) :
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜] 𝕜) ≃ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (E x →L[𝕜] 𝕜)) 𝕜 :=
  haveI : FiniteDimensional 𝕜 (E x) := VectorBundle.finiteDimensional 𝕜 F E x
  ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 (E x) r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualMultilinearLinearEquivAt then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualMultilinearLinearEquivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualMultilinearLinearEquivAt ``Submission.Bundle.continuousMultilinearMap.dualMultilinearLinearEquivAt

theorem dualMultilinearLinearEquivAt_apply (r : ℕ) (x : B)
    (φ : (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜] 𝕜)
    (α : Fin r → (E x →L[𝕜] 𝕜)) :
    dualMultilinearLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x φ α =
      φ ((ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 (E x) r) α) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualMultilinearLinearEquivAt_apply then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualMultilinearLinearEquivAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualMultilinearLinearEquivAt_apply ``Submission.Bundle.continuousMultilinearMap.dualMultilinearLinearEquivAt_apply

end Bundle.continuousMultilinearMap


open _root_.Set _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap

open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

namespace Bundle.continuousMultilinearMap
open _root_.Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {r : ℕ}

noncomputable instance dualBundleTopology (r : ℕ) :
    TopologicalSpace (_root_.Bundle.TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x)
    𝕜
    (fun _ : B => 𝕜)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualBundleTopology then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualBundleTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualBundleTopology ``Submission.Bundle.continuousMultilinearMap.dualBundleTopology

noncomputable instance dualBundleFiberBundle (r : ℕ) :
    @FiberBundle B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
      _ (by infer_instance : TopologicalSpace _)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)
      (dualBundleTopology r) _ :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x)
    𝕜
    (fun _ : B => 𝕜)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualBundleFiberBundle then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualBundleFiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualBundleFiberBundle ``Submission.Bundle.continuousMultilinearMap.dualBundleFiberBundle

noncomputable instance dualBundleVectorBundle (r : ℕ) :
    @VectorBundle 𝕜 B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)
      _
      (fun x => by infer_instance) (fun x => by infer_instance)
      inferInstance inferInstance _
      (dualBundleTopology r) _
      (dualBundleFiberBundle r) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x)
    𝕜
    (fun _ : B => 𝕜)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualBundleVectorBundle then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualBundleVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualBundleVectorBundle ``Submission.Bundle.continuousMultilinearMap.dualBundleVectorBundle

section smooth

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB]
variable (IB : ModelWithCorners 𝕜 EB HB)
variable [ChartedSpace HB B]
variable (n : WithTop ℕ∞)
variable [ContMDiffVectorBundle n F E IB]

noncomputable instance dualBundleSmoothVectorBundle (r : ℕ) :
    @ContMDiffVectorBundle n 𝕜 B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)
      _ EB _ _ HB _ IB _ _ _ _ _ _
      (dualBundleTopology r) _
      (dualBundleFiberBundle r)
      (dualBundleVectorBundle r) :=
  ContMDiffVectorBundle.continuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualBundleSmoothVectorBundle then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualBundleSmoothVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualBundleSmoothVectorBundle ``Submission.Bundle.continuousMultilinearMap.dualBundleSmoothVectorBundle

end smooth

private theorem dualBundleFiber_type_eq (r : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) =
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜 →L[𝕜] 𝕜) := by
  unfold Bundle.continuousMultilinearMap
  congr 1
  exact topology_eq (𝕜 := 𝕜) (F := F) (E := E) _ x

run_cmd do
  let target := ``Submission.Bundle.continuousMultilinearMap.dualBundleFiber_type_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Bundle.continuousMultilinearMap.dualBundleFiber_type_eq target :: scope.openDecls } }

private def dualBundleFiber_normedInstances (r : ℕ) (x : B) :
    Σ' (ng : NormedAddCommGroup
          (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)),
      @NormedSpace 𝕜
        (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)
        _ ng.toSeminormedAddCommGroup :=
  (dualBundleFiber_type_eq (𝕜 := 𝕜) (F := F) (E := E) r x) ▸ ⟨inferInstance, inferInstance⟩

run_cmd do
  let target := ``Submission.Bundle.continuousMultilinearMap.dualBundleFiber_normedInstances
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Bundle.continuousMultilinearMap.dualBundleFiber_normedInstances target :: scope.openDecls } }

instance dualBundleFiberInstNormedAddCommGroup (r : ℕ) (x : B) :
    NormedAddCommGroup (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) :=
  (dualBundleFiber_normedInstances (𝕜 := 𝕜) (F := F) (E := E) r x).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualBundleFiberInstNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualBundleFiberInstNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualBundleFiberInstNormedAddCommGroup ``Submission.Bundle.continuousMultilinearMap.dualBundleFiberInstNormedAddCommGroup

instance dualBundleFiberInstNormedSpace (r : ℕ) (x : B) :
    NormedSpace 𝕜 (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) :=
  (dualBundleFiber_normedInstances (𝕜 := 𝕜) (F := F) (E := E) r x).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualBundleFiberInstNormedSpace then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualBundleFiberInstNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualBundleFiberInstNormedSpace ``Submission.Bundle.continuousMultilinearMap.dualBundleFiberInstNormedSpace

instance dualBundleFiber_instContinuousSMul (r : ℕ) (x : B) :
    ContinuousSMul 𝕜 (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) :=
  inferInstanceAs (ContinuousSMul 𝕜
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualBundleFiber_instContinuousSMul then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualBundleFiber_instContinuousSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualBundleFiber_instContinuousSMul ``Submission.Bundle.continuousMultilinearMap.dualBundleFiber_instContinuousSMul

def dualBundleContinuousLinearEquivAt (r : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) ≃L[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) :=
  (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x).arrowCongr
    (ContinuousLinearEquiv.refl 𝕜 𝕜)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualBundleContinuousLinearEquivAt then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualBundleContinuousLinearEquivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualBundleContinuousLinearEquivAt ``Submission.Bundle.continuousMultilinearMap.dualBundleContinuousLinearEquivAt

theorem dualBundle_triv_symmL_eq_comp (x₀ x : B)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt F E x₀).baseSet)
    (ζ : F →L[𝕜] 𝕜) (v : E x) :
    ((_root_.FiberBundle.trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x₀).symmL 𝕜 x ζ) v =
      ζ ((_root_.FiberBundle.trivializationAt F E x₀).continuousLinearMapAt 𝕜 x v) := by
  set e := _root_.FiberBundle.trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x₀ with he_def
  have hbase : x ∈ e.baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hx, by simp [_root_.FiberBundle.trivializationAt, FiberBundle.trivializationAt']⟩
  have hsymmL : (e.symmL 𝕜 x ζ : Bundle.dual 𝕜 E x) = e.symm x ζ := by
    exact Trivialization.symmL_apply e hbase ζ
  rw [hsymmL]
  have h_rt : (e ⟨x, e.symm x ζ⟩ : B × _) = (x, ζ) := e.apply_mk_symm hbase ζ
  have h_snd : (e ⟨x, e.symm x ζ⟩ : B × _).2 = ζ := congrArg Prod.snd h_rt
  have hxTriv : x ∈ (_root_.FiberBundle.trivializationAt 𝕜 (fun _ : B => 𝕜) x₀).baseSet := by
    change x ∈ Set.univ; trivial
  have h_fwd : (e ⟨x, e.symm x ζ⟩).2
      ((_root_.FiberBundle.trivializationAt F E x₀).continuousLinearMapAt 𝕜 x v) =
    ((Trivialization.continuousLinearEquivAt 𝕜 (_root_.FiberBundle.trivializationAt 𝕜 (_root_.Bundle.Trivial B 𝕜) x₀) x hxTriv)
      ((e.symm x ζ)
        ((Trivialization.continuousLinearEquivAt 𝕜 (_root_.FiberBundle.trivializationAt F E x₀) x hx).symm
          ((_root_.FiberBundle.trivializationAt F E x₀).continuousLinearMapAt 𝕜 x v)))) := by
    rw [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates_eq hx hxTriv]
    rfl
  rw [h_snd] at h_fwd
  have h_triv : ∀ (z : 𝕜),
      ((Trivialization.continuousLinearEquivAt 𝕜 (_root_.FiberBundle.trivializationAt 𝕜 (_root_.Bundle.Trivial B 𝕜) x₀) x hxTriv
        : 𝕜 →L[𝕜] 𝕜) : 𝕜 → 𝕜) z = z := by intro z; rfl
  conv at h_fwd => rhs; rw [show (Trivialization.continuousLinearEquivAt 𝕜
    (_root_.FiberBundle.trivializationAt 𝕜 (_root_.Bundle.Trivial B 𝕜) x₀) x hxTriv) _ = _ from h_triv _]
  conv_lhs => rw [show v = ((_root_.FiberBundle.trivializationAt F E x₀).continuousLinearEquivAt 𝕜 x hx).symm
    ((_root_.FiberBundle.trivializationAt F E x₀).continuousLinearMapAt 𝕜 x v) from
    by
      rw [← (_root_.FiberBundle.trivializationAt F E x₀).coe_continuousLinearEquivAt_eq' hx]
      exact (((_root_.FiberBundle.trivializationAt F E x₀).continuousLinearEquivAt 𝕜 x hx).symm_apply_apply v).symm]
  exact h_fwd.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualBundle_triv_symmL_eq_comp then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualBundle_triv_symmL_eq_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualBundle_triv_symmL_eq_comp ``Submission.Bundle.continuousMultilinearMap.dualBundle_triv_symmL_eq_comp

end Bundle.continuousMultilinearMap




namespace Bundle.continuousMultilinearMap
open _root_.Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

local notation "MLF" => fun r => ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜

local notation "MLF_dual" => fun r =>
  ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem tensorOfDualLinearForms_compContinuousLinearMap_naturality
    {G : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] (r : ℕ) (L : G →L[𝕜] F)
    (β : Fin r → (F →L[𝕜] 𝕜)) :
    (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r β).compContinuousLinearMap
        (fun _ : Fin r => L) =
      ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 G r (fun i => (β i).comp L) := by
  apply ContinuousMultilinearMap.ext
  intro w
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.tensorOfDualLinearForms_apply,
      ContinuousMultilinearMap.tensorOfDualLinearForms_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.tensorOfDualLinearForms_compContinuousLinearMap_naturality then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.tensorOfDualLinearForms_compContinuousLinearMap_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.tensorOfDualLinearForms_compContinuousLinearMap_naturality ``Submission.Bundle.continuousMultilinearMap.tensorOfDualLinearForms_compContinuousLinearMap_naturality

variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

noncomputable def dualLiftFiber (r : ℕ) (x : B)
    (a : Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) :
    Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜 :=
  (dualBundleContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x).symm
    ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm
      (continuousLinearEquivAt (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x a))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualLiftFiber then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualLiftFiber"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualLiftFiber ``Submission.Bundle.continuousMultilinearMap.dualLiftFiber

theorem dualLiftFiber_apply (r : ℕ) (x : B)
    (a : Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x)
    (T : Bundle.continuousMultilinearMap 𝕜 r F E x) :
    dualLiftFiber (F := F) r x a T =
      (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm
        (continuousLinearEquivAt (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x a)
        (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x T) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualLiftFiber_apply then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualLiftFiber_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualLiftFiber_apply ``Submission.Bundle.continuousMultilinearMap.dualLiftFiber_apply

noncomputable def dualUnliftFiber (r : ℕ) (x : B)
    (ψ : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) :
    Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x :=
  (continuousLinearEquivAt (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x).symm
    ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r)
      (dualBundleContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x ψ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualUnliftFiber then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualUnliftFiber"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualUnliftFiber ``Submission.Bundle.continuousMultilinearMap.dualUnliftFiber

end Bundle.continuousMultilinearMap

abbrev DualBundleSection
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB] (IB : ModelWithCorners 𝕜 EB HB)
    {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
    (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (_root_.Bundle.TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E]
    (n : WithTop ℕ∞) (r : ℕ) :=
  @ContMDiffSection 𝕜 _ EB _ _ HB _ IB B _ _
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
    _ _ n
    (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)
    (Bundle.continuousMultilinearMap.dualBundleTopology r)
    (fun _ => inferInstance)
    (Bundle.continuousMultilinearMap.dualBundleFiberBundle r)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DualBundleSection then
    throwError "Refusing to shadow existing declaration DualBundleSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DualBundleSection ``Submission.DualBundleSection

namespace DifferentialGeometry.MultilinearSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]
variable {r : ℕ}

local instance dualMultilinearInstNormedAddCommGroup :
    NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.dualMultilinearInstNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.dualMultilinearInstNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.dualMultilinearInstNormedAddCommGroup ``Submission.DifferentialGeometry.MultilinearSection.dualMultilinearInstNormedAddCommGroup

local instance dualMultilinearInstNormedSpace :
    NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.dualMultilinearInstNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.dualMultilinearInstNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.dualMultilinearInstNormedSpace ``Submission.DifferentialGeometry.MultilinearSection.dualMultilinearInstNormedSpace

local instance dualOfMultilinearInstNormedAddCommGroup :
    NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.dualOfMultilinearInstNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.dualOfMultilinearInstNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.dualOfMultilinearInstNormedAddCommGroup ``Submission.DifferentialGeometry.MultilinearSection.dualOfMultilinearInstNormedAddCommGroup

local instance dualOfMultilinearInstNormedSpace :
    NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.dualOfMultilinearInstNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.dualOfMultilinearInstNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.dualOfMultilinearInstNormedSpace ``Submission.DifferentialGeometry.MultilinearSection.dualOfMultilinearInstNormedSpace

noncomputable def Bundle.continuousMultilinearMap.modelDualLiftCLM (𝕜 : Type*)
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (r : ℕ) :
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) →L[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) :=
  letI : NormedAddCommGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance
  letI : NormedSpace 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance
  letI : NormedAddCommGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance
  letI : NormedSpace 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance
  haveI : FiniteDimensional 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
    continuousMultilinearMap_finiteDimensional (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) r
  LinearMap.toContinuousLinearMap
    (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual
      (𝕜 := 𝕜) (F := F) r).symm.toLinearMap

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.MultilinearSection.Bundle
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.MultilinearSection.Bundle.continuousMultilinearMap
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.Bundle.continuousMultilinearMap.modelDualLiftCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.Bundle.continuousMultilinearMap.modelDualLiftCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.Bundle.continuousMultilinearMap.modelDualLiftCLM ``Submission.DifferentialGeometry.MultilinearSection.Bundle.continuousMultilinearMap.modelDualLiftCLM

theorem dualLiftFiber_triv_eq {r : ℕ} (x₀ x : B)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt F E x₀).baseSet)
    (a : Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) :
    (_root_.FiberBundle.trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) x₀
        ⟨x, Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x a⟩).2 =
    Bundle.continuousMultilinearMap.modelDualLiftCLM 𝕜 F r
      ((_root_.FiberBundle.trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) x₀
        ⟨x, a⟩).2) := by
  have : FiniteDimensional 𝕜 (E x) := VectorBundle.finiteDimensional 𝕜 F E x
  apply (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual
    (𝕜 := 𝕜) (F := F) r).injective
  rw [show (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual (𝕜 := 𝕜) (F := F) r)
        ((Bundle.continuousMultilinearMap.modelDualLiftCLM 𝕜 F r) _) = _ from
      (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual
        (𝕜 := 𝕜) (F := F) r).apply_symm_apply _]
  apply ContinuousMultilinearMap.ext
  intro β
  change (ContinuousMultilinearMap.dualMultilinearLinearMap 𝕜 F r
    (_ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)) β = _
  rw [ContinuousMultilinearMap.dualMultilinearLinearMap_apply]
  rw [hom_trivializationAt_apply]
  have hxTriv : x ∈ (_root_.FiberBundle.trivializationAt 𝕜 (fun _ : B => 𝕜) x₀).baseSet := by
    change x ∈ Set.univ; trivial
  have hxMlb : x ∈ (_root_.FiberBundle.trivializationAt
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x) x₀).baseSet := hx
  rw [ContinuousLinearMap.inCoordinates_eq hxMlb hxTriv]
  change ((Trivialization.continuousLinearEquivAt 𝕜
      (_root_.FiberBundle.trivializationAt 𝕜 (_root_.Bundle.Trivial B 𝕜) x₀) x hxTriv : 𝕜 →L[𝕜] 𝕜).comp
    ((Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x a).comp
      ((Trivialization.continuousLinearEquivAt 𝕜
        (_root_.FiberBundle.trivializationAt
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
          (Bundle.continuousMultilinearMap 𝕜 r F E) x₀) x hxMlb).symm : _ →L[𝕜] _)))
    (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r β) =
    (_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) x₀
      ⟨x, a⟩).2 β
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have h_cle_triv : ∀ (z : 𝕜),
      ((Trivialization.continuousLinearEquivAt 𝕜
        (_root_.FiberBundle.trivializationAt 𝕜 (_root_.Bundle.Trivial B 𝕜) x₀) x hxTriv : 𝕜 →L[𝕜] 𝕜) : 𝕜 → 𝕜) z = z := by
    intro z; rfl
  rw [h_cle_triv]
  rw [Trivialization.symm_continuousLinearEquivAt_eq']
  change (Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x a)
    ((_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 r F E) x₀).symmL 𝕜 x
      (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r β)) = _
  rw [Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap x₀ x hx]
  rw [Bundle.continuousMultilinearMap.dualLiftFiber_apply]
  conv_lhs =>
    rw [show Bundle.continuousMultilinearMap.continuousLinearEquivAt
          (𝕜 := 𝕜) (F := F) (E := E) r x
          (((ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r) β).compContinuousLinearMap
            (fun _ => (_root_.FiberBundle.trivializationAt F E x₀).continuousLinearMapAt 𝕜 x)) =
        ((ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r) β).compContinuousLinearMap
          (fun _ => ((_root_.FiberBundle.trivializationAt F E x₀).continuousLinearMapAt 𝕜 x).comp
            ((_root_.FiberBundle.trivializationAt F E x).symmL 𝕜 x)) from rfl]
  rw [Bundle.continuousMultilinearMap.tensorOfDualLinearForms_compContinuousLinearMap_naturality]
  show (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm
    (Bundle.continuousMultilinearMap.continuousLinearEquivAt
      (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x a)
    (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r
      (fun i => (β i).comp (((_root_.FiberBundle.trivializationAt F E x₀).continuousLinearMapAt 𝕜 x).comp
        ((_root_.FiberBundle.trivializationAt F E x).symmL 𝕜 x)))) = _
  have h_rt : ∀ (m : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
      (γ : Fin r → (F →L[𝕜] 𝕜)),
      (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm m
        (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r γ) = m γ := by
    intro m γ
    have := (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).apply_symm_apply
      m
    have h2 := congr_fun (congr_arg DFunLike.coe this) γ
    exact h2
  rw [h_rt]
  change (Bundle.continuousMultilinearMap.continuousLinearEquivAt
      (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x a)
    (fun i => (β i).comp (((_root_.FiberBundle.trivializationAt F E x₀).continuousLinearMapAt 𝕜 x).comp
      ((_root_.FiberBundle.trivializationAt F E x).symmL 𝕜 x))) = _
  change a (fun i => (_root_.FiberBundle.trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x).symmL 𝕜 x
    ((β i).comp (((_root_.FiberBundle.trivializationAt F E x₀).continuousLinearMapAt 𝕜 x).comp
      ((_root_.FiberBundle.trivializationAt F E x).symmL 𝕜 x)))) = _
  change a (fun i => (_root_.FiberBundle.trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x).symmL 𝕜 x
    ((β i).comp (((_root_.FiberBundle.trivializationAt F E x₀).continuousLinearMapAt 𝕜 x).comp
      ((_root_.FiberBundle.trivializationAt F E x).symmL 𝕜 x)))) =
    a (fun i => (_root_.FiberBundle.trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x₀).symmL 𝕜 x (β i))
  congr 1
  funext i
  apply ContinuousLinearMap.ext
  intro v
  rw [Bundle.continuousMultilinearMap.dualBundle_triv_symmL_eq_comp x₀ x hx,
    Bundle.continuousMultilinearMap.dualBundle_triv_symmL_eq_comp x x
      (_root_.FiberBundle.mem_baseSet_trivializationAt F E x)]
  simp only [ContinuousLinearMap.comp_apply]
  rw [(_root_.FiberBundle.trivializationAt F E x).symmL_continuousLinearMapAt
    (_root_.FiberBundle.mem_baseSet_trivializationAt F E x)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.dualLiftFiber_triv_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.dualLiftFiber_triv_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.dualLiftFiber_triv_eq ``Submission.DifferentialGeometry.MultilinearSection.dualLiftFiber_triv_eq

noncomputable def Bundle.continuousMultilinearMap.modelDualUnliftCLM (𝕜 : Type*)
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (r : ℕ) :
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) →L[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
  letI : NormedAddCommGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance
  letI : NormedSpace 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance
  letI : NormedAddCommGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance
  letI : NormedSpace 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance
  haveI : FiniteDimensional 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := by
    have : FiniteDimensional 𝕜
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
      continuousMultilinearMap_finiteDimensional (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) r
    exact (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual
      (𝕜 := 𝕜) (F := F) r).symm.finiteDimensional
  LinearMap.toContinuousLinearMap
    (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual
      (𝕜 := 𝕜) (F := F) r).toLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.Bundle.continuousMultilinearMap.modelDualUnliftCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.Bundle.continuousMultilinearMap.modelDualUnliftCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.Bundle.continuousMultilinearMap.modelDualUnliftCLM ``Submission.DifferentialGeometry.MultilinearSection.Bundle.continuousMultilinearMap.modelDualUnliftCLM

theorem dualUnliftFiber_triv_eq {r : ℕ} (x₀ x : B)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt F E x₀).baseSet)
    (ψ : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) :
    (_root_.FiberBundle.trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) x₀
        ⟨x, Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x ψ⟩).2 =
    Bundle.continuousMultilinearMap.modelDualUnliftCLM 𝕜 F r
      ((_root_.FiberBundle.trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) x₀
        ⟨x, ψ⟩).2) := by
  have h_rt_fiber : Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x
      (Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x ψ) = ψ := by
    change (Bundle.continuousMultilinearMap.dualBundleContinuousLinearEquivAt
          (𝕜 := 𝕜) (F := F) (E := E) r x).symm
        ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm
          ((Bundle.continuousMultilinearMap.continuousLinearEquivAt
              (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x)
            ((Bundle.continuousMultilinearMap.continuousLinearEquivAt
                (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x).symm
              ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r)
                ((Bundle.continuousMultilinearMap.dualBundleContinuousLinearEquivAt
                    (𝕜 := 𝕜) (F := F) (E := E) r x) ψ))))) = ψ
    simp only [ContinuousLinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  have h_triv := dualLiftFiber_triv_eq x₀ x hx
    (Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x ψ)
  rw [h_rt_fiber] at h_triv
  set triv_mlbdual := (_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) x₀
    ⟨x, Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x ψ⟩).2
  rw [h_triv]
  exact ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual
    (𝕜 := 𝕜) (F := F) r).apply_symm_apply triv_mlbdual).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.dualUnliftFiber_triv_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.dualUnliftFiber_triv_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.dualUnliftFiber_triv_eq ``Submission.DifferentialGeometry.MultilinearSection.dualUnliftFiber_triv_eq

end DifferentialGeometry.MultilinearSection

section BundleEquiv

open _root_.Submission.DifferentialGeometry.MultilinearSection

namespace Bundle.continuousMultilinearMap
open _root_.Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {n : WithTop ℕ∞} [ContMDiffVectorBundle n F E IB]
variable {r : ℕ}

local instance _root_.Submission.Bundle.continuousMultilinearMap.instNormedAddCommGroupContinuousMultilinearMapFinContinuousLinearMapId : NormedAddCommGroup
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.instNormedAddCommGroupContinuousMultilinearMapFinContinuousLinearMapId then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.instNormedAddCommGroupContinuousMultilinearMapFinContinuousLinearMapId"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.instNormedAddCommGroupContinuousMultilinearMapFinContinuousLinearMapId ``Submission.Bundle.continuousMultilinearMap.instNormedAddCommGroupContinuousMultilinearMapFinContinuousLinearMapId
local instance _root_.Submission.Bundle.continuousMultilinearMap.instNormedSpaceContinuousMultilinearMapFinContinuousLinearMapId : NormedSpace 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.instNormedSpaceContinuousMultilinearMapFinContinuousLinearMapId then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.instNormedSpaceContinuousMultilinearMapFinContinuousLinearMapId"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.instNormedSpaceContinuousMultilinearMapFinContinuousLinearMapId ``Submission.Bundle.continuousMultilinearMap.instNormedSpaceContinuousMultilinearMapFinContinuousLinearMapId
local instance _root_.Submission.Bundle.continuousMultilinearMap.instNormedAddCommGroupContinuousLinearMapIdContinuousMultilinearMapFin : NormedAddCommGroup
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.instNormedAddCommGroupContinuousLinearMapIdContinuousMultilinearMapFin then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.instNormedAddCommGroupContinuousLinearMapIdContinuousMultilinearMapFin"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.instNormedAddCommGroupContinuousLinearMapIdContinuousMultilinearMapFin ``Submission.Bundle.continuousMultilinearMap.instNormedAddCommGroupContinuousLinearMapIdContinuousMultilinearMapFin
local instance _root_.Submission.Bundle.continuousMultilinearMap.instNormedSpaceContinuousLinearMapIdContinuousMultilinearMapFin : NormedSpace 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.instNormedSpaceContinuousLinearMapIdContinuousMultilinearMapFin then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.instNormedSpaceContinuousLinearMapIdContinuousMultilinearMapFin"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.instNormedSpaceContinuousLinearMapIdContinuousMultilinearMapFin ``Submission.Bundle.continuousMultilinearMap.instNormedSpaceContinuousLinearMapIdContinuousMultilinearMapFin

noncomputable def dualMultilinearFiberwiseEquiv (r : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) ≃ₗ[𝕜]
    Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x :=
  (dualBundleContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x).toLinearEquiv.trans
    ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).trans
      (continuousLinearEquivAt (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜)
        (E := Bundle.dual 𝕜 E) r x).symm.toLinearEquiv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv ``Submission.Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv

omit [ChartedSpace HB B] [ContMDiffVectorBundle n F E IB] in
theorem dualMultilinearFiberwiseEquiv_apply (k : ℕ) (x : B)
    (φ : Bundle.continuousMultilinearMap 𝕜 k F E x →L[𝕜] 𝕜)
    (α : Fin k → E x →L[𝕜] 𝕜) :
    dualMultilinearFiberwiseEquiv (F := F) (E := E) k x φ α =
      φ (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 (E x) k α) := by
  change φ ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) k x).symm
    (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F k
      (fun i => (_root_.FiberBundle.trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x).continuousLinearMapAt
        𝕜 x (α i)))) = _
  congr 1
  apply ContinuousMultilinearMap.ext
  intro v
  change (∏ i, (_root_.FiberBundle.trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x).continuousLinearMapAt
    𝕜 x (α i) ((_root_.FiberBundle.trivializationAt F E x).continuousLinearMapAt 𝕜 x (v i))) = ∏ i, α i (v i)
  apply Finset.prod_congr rfl
  intro i _
  have h := dualBundle_triv_symmL_eq_comp (𝕜 := 𝕜) (F := F) (E := E) x x
    (_root_.FiberBundle.mem_baseSet_trivializationAt F E x)
    ((_root_.FiberBundle.trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x).continuousLinearMapAt 𝕜 x (α i)) (v i)
  have hcancel := (_root_.FiberBundle.trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x).symmₗ_linearMapAt
    (R := 𝕜) (_root_.FiberBundle.mem_baseSet_trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) (α i)
  exact h.symm.trans (congrArg (fun a : E x →L[𝕜] 𝕜 => a (v i)) hcancel)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_apply then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_apply ``Submission.Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_apply

omit [ChartedSpace HB B] [ContMDiffVectorBundle n F E IB] in
theorem dualMultilinearFiberwiseEquiv_symm_apply_tensorOfDualLinearForms (k : ℕ) (x : B)
    (T : Bundle.continuousMultilinearMap 𝕜 k (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x)
    (α : Fin k → E x →L[𝕜] 𝕜) :
    (dualMultilinearFiberwiseEquiv (F := F) (E := E) k x).symm T
        (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 (E x) k α) = T α := by
  rw [← dualMultilinearFiberwiseEquiv_apply,
    LinearEquiv.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_symm_apply_tensorOfDualLinearForms then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_symm_apply_tensorOfDualLinearForms"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_symm_apply_tensorOfDualLinearForms ``Submission.Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_symm_apply_tensorOfDualLinearForms

omit [ContMDiffVectorBundle n F E IB] in
theorem dualMultilinearFiberwiseEquiv_smooth (r : ℕ)
    [hE : ContMDiffVectorBundle n F E IB] :
    ContMDiff
      (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜))
      (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜))
      n
      (fun p : _root_.Bundle.TotalSpace
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) =>
        (⟨p.1, dualMultilinearFiberwiseEquiv (𝕜 := 𝕜) (F := F) (E := E) r p.1 p.2⟩ :
          _root_.Bundle.TotalSpace
            (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
            (fun x => Bundle.continuousMultilinearMap 𝕜 r
              (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x))) := by
  let _ := hE
  let := dualBundleSmoothVectorBundle (𝕜 := 𝕜) (B := B) (F := F) (E := E) IB n r
  intro p₀
  rw [_root_.Bundle.contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · exact (_root_.Bundle.contMDiff_proj
      (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)).contMDiffAt
  · have h_fiber : ContMDiffAt
        (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜))
        𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) n
        (fun p => (_root_.FiberBundle.trivializationAt
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) p₀.proj p).2)
        p₀ :=
      (_root_.Bundle.contMDiffAt_totalSpace.mp contMDiffAt_id).2
    refine ((contMDiffAt_const
      (c := Bundle.continuousMultilinearMap.modelDualUnliftCLM 𝕜 F r)).clm_apply
        h_fiber).congr_of_eventuallyEq ?_
    filter_upwards [
      ((_root_.FiberBundle.trivializationAt F E p₀.proj).open_baseSet.preimage
        (FiberBundle.continuous_proj _ _)).mem_nhds
        (_root_.FiberBundle.mem_baseSet_trivializationAt F E p₀.proj)
    ] with p hp
    exact dualUnliftFiber_triv_eq p₀.proj p.proj hp p.snd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_smooth then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_smooth ``Submission.Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_smooth

omit [ContMDiffVectorBundle n F E IB] in
theorem dualMultilinearFiberwiseEquiv_symm_smooth (r : ℕ)
    [hE : ContMDiffVectorBundle n F E IB] :
    ContMDiff
      (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜))
      (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜))
      n
      (fun q : _root_.Bundle.TotalSpace
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 r
            (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) =>
        (⟨q.1, (dualMultilinearFiberwiseEquiv (𝕜 := 𝕜) (F := F) (E := E) r q.1).symm q.2⟩ :
          _root_.Bundle.TotalSpace
            (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
            (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜))) := by
  let _ := hE
  have : ContMDiffVectorBundle n (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) IB :=
    ContMDiffVectorBundle.continuousLinearMap
  have : ContMDiffVectorBundle n
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E)) IB :=
    SmoothVectorBundle.continuousMultilinearMap
      (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) (IB := IB) (s := r) n
  intro q₀
  refine _root_.Bundle.contMDiffAt_totalSpace.mpr ⟨?_, ?_⟩
  · exact (_root_.Bundle.contMDiff_proj
      (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜)
        (Bundle.dual 𝕜 E) x)).contMDiffAt
  · have h_fiber : ContMDiffAt
        (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜))
        𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) n
        (fun q => (_root_.FiberBundle.trivializationAt
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜)
            (Bundle.dual 𝕜 E) x) q₀.proj q).2) q₀ :=
      (_root_.Bundle.contMDiffAt_totalSpace.mp contMDiffAt_id).2
    refine ((contMDiffAt_const
      (c := Bundle.continuousMultilinearMap.modelDualLiftCLM 𝕜 F r)).clm_apply
        h_fiber).congr_of_eventuallyEq ?_
    filter_upwards [
      ((_root_.FiberBundle.trivializationAt F E q₀.proj).open_baseSet.preimage
        (FiberBundle.continuous_proj _ _)).mem_nhds
        (_root_.FiberBundle.mem_baseSet_trivializationAt F E q₀.proj)
    ] with q hq
    exact dualLiftFiber_triv_eq q₀.proj q.proj hq q.snd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_symm_smooth then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_symm_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_symm_smooth ``Submission.Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_symm_smooth

end Bundle.continuousMultilinearMap

noncomputable def dualBundleMultilinearOfDualEquiv
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB]
    {IB : ModelWithCorners 𝕜 EB HB}
    {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
    {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (_root_.Bundle.TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E]
    {n : WithTop ℕ∞} [ContMDiffVectorBundle n F E IB]
    (r : ℕ) :
    ContMDiffVectorBundleEquiv 𝕜 IB n
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) :=
  ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv
    (fun x => Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv r x)
    (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_smooth r)
    (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_symm_smooth r)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `dualBundleMultilinearOfDualEquiv then
    throwError "Refusing to shadow existing declaration dualBundleMultilinearOfDualEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `dualBundleMultilinearOfDualEquiv ``Submission.dualBundleMultilinearOfDualEquiv

end BundleEquiv

namespace DifferentialGeometry.MultilinearSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

noncomputable def fromDualBundleSection {r : ℕ}
    (ψ : DualBundleSection 𝕜 F IB E n r) :
    MultilinearSection 𝕜 (F →L[𝕜] 𝕜) IB (Bundle.dual 𝕜 E) n r :=
  ⟨fun x => Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv r x (ψ x),
   (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_smooth r |>.comp
     ψ.contMDiff).congr fun _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.fromDualBundleSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.fromDualBundleSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.fromDualBundleSection ``Submission.DifferentialGeometry.MultilinearSection.fromDualBundleSection

noncomputable def toDualBundleSection {r : ℕ}
    (α : MultilinearSection 𝕜 (F →L[𝕜] 𝕜) IB (Bundle.dual 𝕜 E) n r) :
    DualBundleSection 𝕜 F IB E n r :=
  ⟨fun x => (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv r x).symm (α x),
   (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_symm_smooth r |>.comp
     α.contMDiff).congr fun _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.toDualBundleSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.toDualBundleSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.toDualBundleSection ``Submission.DifferentialGeometry.MultilinearSection.toDualBundleSection

@[simp]
theorem toDualBundleSection_fromDualBundleSection {r : ℕ}
    (ψ : DualBundleSection 𝕜 F IB E n r) :
    toDualBundleSection n (fromDualBundleSection n ψ) = ψ := by
  apply ContMDiffSection.ext; intro x
  exact (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv r x).symm_apply_apply (ψ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.toDualBundleSection_fromDualBundleSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.toDualBundleSection_fromDualBundleSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.toDualBundleSection_fromDualBundleSection ``Submission.DifferentialGeometry.MultilinearSection.toDualBundleSection_fromDualBundleSection

@[simp]
theorem fromDualBundleSection_toDualBundleSection {r : ℕ}
    (α : MultilinearSection 𝕜 (F →L[𝕜] 𝕜) IB (Bundle.dual 𝕜 E) n r) :
    fromDualBundleSection n (toDualBundleSection n α) = α := by
  apply ContMDiffSection.ext; intro x
  exact (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv r x).apply_symm_apply (α x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.fromDualBundleSection_toDualBundleSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.fromDualBundleSection_toDualBundleSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.fromDualBundleSection_toDualBundleSection ``Submission.DifferentialGeometry.MultilinearSection.fromDualBundleSection_toDualBundleSection

theorem fromDualBundleSection_add {r : ℕ}
    (ψ₁ ψ₂ : DualBundleSection 𝕜 F IB E n r) (x : B) :
    (fromDualBundleSection n (ψ₁ + ψ₂)).1 x =
    (fromDualBundleSection n ψ₁).1 x + (fromDualBundleSection n ψ₂).1 x :=
  map_add _ (ψ₁ x) (ψ₂ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.fromDualBundleSection_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.fromDualBundleSection_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.fromDualBundleSection_add ``Submission.DifferentialGeometry.MultilinearSection.fromDualBundleSection_add

theorem fromDualBundleSection_smul {r : ℕ}
    (c : 𝕜) (ψ : DualBundleSection 𝕜 F IB E n r) (x : B) :
    (fromDualBundleSection n (c • ψ)).1 x =
    c • (fromDualBundleSection n ψ).1 x :=
  map_smul _ c (ψ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.fromDualBundleSection_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.fromDualBundleSection_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.fromDualBundleSection_smul ``Submission.DifferentialGeometry.MultilinearSection.fromDualBundleSection_smul

theorem toDualBundleSection_add {r : ℕ}
    (α β : MultilinearSection 𝕜 (F →L[𝕜] 𝕜) IB (Bundle.dual 𝕜 E) n r) (x : B) :
    (toDualBundleSection n (α + β)).1 x =
    (toDualBundleSection n α).1 x + (toDualBundleSection n β).1 x :=
  map_add _ (α x) (β x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.toDualBundleSection_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.toDualBundleSection_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.toDualBundleSection_add ``Submission.DifferentialGeometry.MultilinearSection.toDualBundleSection_add

theorem toDualBundleSection_smulByFun {r : ℕ}
    (φ : B → 𝕜) (hφ : ContMDiff IB 𝓘(𝕜) n φ)
    (α : MultilinearSection 𝕜 (F →L[𝕜] 𝕜) IB (Bundle.dual 𝕜 E) n r) (x : B) :
    (toDualBundleSection n (MultilinearSection.smulByFun n φ hφ α)).1 x =
    φ x • (toDualBundleSection n α).1 x :=
  map_smul _ (φ x) (α x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.toDualBundleSection_smulByFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.toDualBundleSection_smulByFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.toDualBundleSection_smulByFun ``Submission.DifferentialGeometry.MultilinearSection.toDualBundleSection_smulByFun

end DifferentialGeometry.MultilinearSection

end

section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

private theorem contMDiff_mkPiAlgebra_bundle (k : ℕ) (n : WithTop ℕ∞) :
    ContMDiff I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => 𝕜) 𝕜)) n
      (fun y => (⟨y, ContinuousMultilinearMap.mkPiAlgebra 𝕜 (Fin k) 𝕜⟩ :
        _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => 𝕜) 𝕜)
          (Bundle.continuousMultilinearMap 𝕜 k 𝕜 (Bundle.Trivial M 𝕜)))) := by
  intro x
  have hT : ContMDiffAt I
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => 𝕜) 𝕜)) n
      (fun y => (⟨y, ContinuousMultilinearMap.mkPiAlgebra 𝕜 (Fin k) 𝕜⟩ :
        _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => 𝕜) 𝕜)
          (Bundle.continuousMultilinearMap 𝕜 k 𝕜 (Bundle.Trivial M 𝕜)))) x := by
    rw [_root_.Bundle.contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    have heq : (fun y => (_root_.FiberBundle.trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => 𝕜) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k 𝕜 (Bundle.Trivial M 𝕜)) x
          (⟨y, ContinuousMultilinearMap.mkPiAlgebra 𝕜 (Fin k) 𝕜⟩ : _root_.Bundle.TotalSpace
            (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => 𝕜) 𝕜)
            (Bundle.continuousMultilinearMap 𝕜 k 𝕜 (Bundle.Trivial M 𝕜)))).2) =
        (fun _ => ContinuousMultilinearMap.mkPiAlgebra 𝕜 (Fin k) 𝕜) := by
      funext y
      apply ContinuousMultilinearMap.ext
      intro v
      change (ContinuousMultilinearMap.mkPiAlgebra 𝕜 (Fin k) 𝕜)
        (fun i => (_root_.FiberBundle.trivializationAt 𝕜 (Bundle.Trivial M 𝕜) x).symmL 𝕜 y (v i)) = _
      congr 1
      funext i
      rw [Bundle.Trivialization.symmL_apply _ (by simp)]
      simp
    rw [heq]
    exact contMDiffAt_const
  exact hT

run_cmd do
  let target := ``Submission.contMDiff_mkPiAlgebra_bundle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `contMDiff_mkPiAlgebra_bundle target :: scope.openDecls } }


open _root_.ContMDiffWithinAt in
theorem ContMDiffWithinAt.tensorOfDualLinearForms_bundle (k : ℕ)
    (α : Fin k → ∀ x, V x →L[𝕜] 𝕜) {n : WithTop ℕ∞} {s : Set M} {x : M}
    (hα : ∀ i, ContMDiffWithinAt I (I.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) n
      (fun y => (⟨y, α i y⟩ : _root_.Bundle.TotalSpace (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 V))) s x) :
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun y => (⟨y, ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 (V y) k (fun i => α i y)⟩ :
        _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
          (Bundle.continuousMultilinearMap 𝕜 k F V))) s x := by
  exact (contMDiff_mkPiAlgebra_bundle (I := I) k n).contMDiffAt.contMDiffWithinAt
    |>.multilinear_bundle_comp hα

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffWithinAt.tensorOfDualLinearForms_bundle then
    throwError "Refusing to shadow existing declaration ContMDiffWithinAt.tensorOfDualLinearForms_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffWithinAt.tensorOfDualLinearForms_bundle ``Submission.ContMDiffWithinAt.tensorOfDualLinearForms_bundle

open _root_.ContMDiffAt in
theorem ContMDiffAt.tensorOfDualLinearForms_bundle (k : ℕ)
    (α : Fin k → ∀ x, V x →L[𝕜] 𝕜) {n : WithTop ℕ∞} {x : M}
    (hα : ∀ i, ContMDiffAt I (I.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) n
      (fun y => (⟨y, α i y⟩ : _root_.Bundle.TotalSpace (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 V))) x) :
    ContMDiffAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun y => (⟨y, ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 (V y) k (fun i => α i y)⟩ :
        _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
          (Bundle.continuousMultilinearMap 𝕜 k F V))) x := by
  exact (contMDiff_mkPiAlgebra_bundle (I := I) k n).contMDiffAt.multilinear_bundle_comp hα

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffAt.tensorOfDualLinearForms_bundle then
    throwError "Refusing to shadow existing declaration ContMDiffAt.tensorOfDualLinearForms_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffAt.tensorOfDualLinearForms_bundle ``Submission.ContMDiffAt.tensorOfDualLinearForms_bundle

open _root_.ContMDiffOn in
theorem ContMDiffOn.tensorOfDualLinearForms_bundle (k : ℕ)
    (α : Fin k → ∀ x, V x →L[𝕜] 𝕜) {n : WithTop ℕ∞} {s : Set M}
    (hα : ∀ i, ContMDiffOn I (I.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) n
      (fun y => (⟨y, α i y⟩ : _root_.Bundle.TotalSpace (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 V))) s) :
    ContMDiffOn I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun y => (⟨y, ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 (V y) k (fun i => α i y)⟩ :
        _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
          (Bundle.continuousMultilinearMap 𝕜 k F V))) s := by
  exact (contMDiff_mkPiAlgebra_bundle (I := I) k n).contMDiffOn.multilinear_bundle_comp hα

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffOn.tensorOfDualLinearForms_bundle then
    throwError "Refusing to shadow existing declaration ContMDiffOn.tensorOfDualLinearForms_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffOn.tensorOfDualLinearForms_bundle ``Submission.ContMDiffOn.tensorOfDualLinearForms_bundle

open _root_.ContMDiff in
theorem ContMDiff.tensorOfDualLinearForms_bundle (k : ℕ)
    (α : Fin k → ∀ x, V x →L[𝕜] 𝕜) {n : WithTop ℕ∞}
    (hα : ∀ i, ContMDiff I (I.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) n
      (fun y => (⟨y, α i y⟩ : _root_.Bundle.TotalSpace (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 V)))) :
    ContMDiff I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun y => (⟨y, ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 (V y) k (fun i => α i y)⟩ :
        _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
          (Bundle.continuousMultilinearMap 𝕜 k F V))) := by
  exact (contMDiff_mkPiAlgebra_bundle (I := I) k n).multilinear_bundle_comp hα

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiff.tensorOfDualLinearForms_bundle then
    throwError "Refusing to shadow existing declaration ContMDiff.tensorOfDualLinearForms_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiff.tensorOfDualLinearForms_bundle ``Submission.ContMDiff.tensorOfDualLinearForms_bundle

open _root_.MDifferentiableWithinAt in
theorem MDifferentiableWithinAt.tensorOfDualLinearForms_bundle (k : ℕ)
    (α : Fin k → ∀ x, V x →L[𝕜] 𝕜) {s : Set M} {x : M}
    (hα : ∀ i, MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F →L[𝕜] 𝕜))
      (fun y => (⟨y, α i y⟩ : _root_.Bundle.TotalSpace (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 V))) s x) :
    MDifferentiableWithinAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun y => (⟨y, ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 (V y) k (fun i => α i y)⟩ :
        _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
          (Bundle.continuousMultilinearMap 𝕜 k F V))) s x := by
  have h := (contMDiff_mkPiAlgebra_bundle (I := I) (M := M) k 1).mdifferentiable one_ne_zero
  exact h.mdifferentiableAt.mdifferentiableWithinAt.multilinear_bundle_comp hα

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MDifferentiableWithinAt.tensorOfDualLinearForms_bundle then
    throwError "Refusing to shadow existing declaration MDifferentiableWithinAt.tensorOfDualLinearForms_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableWithinAt.tensorOfDualLinearForms_bundle ``Submission.MDifferentiableWithinAt.tensorOfDualLinearForms_bundle

open _root_.MDifferentiableAt in
theorem MDifferentiableAt.tensorOfDualLinearForms_bundle (k : ℕ)
    (α : Fin k → ∀ x, V x →L[𝕜] 𝕜) {x : M}
    (hα : ∀ i, MDifferentiableAt I (I.prod 𝓘(𝕜, F →L[𝕜] 𝕜))
      (fun y => (⟨y, α i y⟩ : _root_.Bundle.TotalSpace (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 V))) x) :
    MDifferentiableAt I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun y => (⟨y, ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 (V y) k (fun i => α i y)⟩ :
        _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
          (Bundle.continuousMultilinearMap 𝕜 k F V))) x := by
  have h := (contMDiff_mkPiAlgebra_bundle (I := I) (M := M) k 1).mdifferentiable one_ne_zero
  exact h.mdifferentiableAt.multilinear_bundle_comp hα

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MDifferentiableAt.tensorOfDualLinearForms_bundle then
    throwError "Refusing to shadow existing declaration MDifferentiableAt.tensorOfDualLinearForms_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableAt.tensorOfDualLinearForms_bundle ``Submission.MDifferentiableAt.tensorOfDualLinearForms_bundle

open _root_.MDifferentiableOn in
theorem MDifferentiableOn.tensorOfDualLinearForms_bundle (k : ℕ)
    (α : Fin k → ∀ x, V x →L[𝕜] 𝕜) {s : Set M}
    (hα : ∀ i, MDifferentiableOn I (I.prod 𝓘(𝕜, F →L[𝕜] 𝕜))
      (fun y => (⟨y, α i y⟩ : _root_.Bundle.TotalSpace (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 V))) s) :
    MDifferentiableOn I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun y => (⟨y, ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 (V y) k (fun i => α i y)⟩ :
        _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
          (Bundle.continuousMultilinearMap 𝕜 k F V))) s := by
  have h := (contMDiff_mkPiAlgebra_bundle (I := I) (M := M) k 1).mdifferentiable one_ne_zero
  exact h.mdifferentiableOn.multilinear_bundle_comp hα

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MDifferentiableOn.tensorOfDualLinearForms_bundle then
    throwError "Refusing to shadow existing declaration MDifferentiableOn.tensorOfDualLinearForms_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableOn.tensorOfDualLinearForms_bundle ``Submission.MDifferentiableOn.tensorOfDualLinearForms_bundle

open _root_.MDifferentiable in
theorem MDifferentiable.tensorOfDualLinearForms_bundle (k : ℕ)
    (α : Fin k → ∀ x, V x →L[𝕜] 𝕜)
    (hα : ∀ i, MDifferentiable I (I.prod 𝓘(𝕜, F →L[𝕜] 𝕜))
      (fun y => (⟨y, α i y⟩ : _root_.Bundle.TotalSpace (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 V)))) :
    MDifferentiable I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun y => (⟨y, ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 (V y) k (fun i => α i y)⟩ :
        _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
          (Bundle.continuousMultilinearMap 𝕜 k F V))) := by
  exact ((contMDiff_mkPiAlgebra_bundle (I := I) k 1).mdifferentiable one_ne_zero).multilinear_bundle_comp hα

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MDifferentiable.tensorOfDualLinearForms_bundle then
    throwError "Refusing to shadow existing declaration MDifferentiable.tensorOfDualLinearForms_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiable.tensorOfDualLinearForms_bundle ``Submission.MDifferentiable.tensorOfDualLinearForms_bundle

end
