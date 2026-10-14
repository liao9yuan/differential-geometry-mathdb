import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Fiber
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Defs
import Submission.DifferentialGeometry.Tensor.Alternating.Composition
import Submission.DifferentialGeometry.Tensor.Multilinear.Composition
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Submission.DifferentialGeometry.Tensor.Multilinear.Smoothness.LinearIsometry
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Submission.DifferentialGeometry.Tensor.Multilinear.Curry.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Tensor.Multilinear

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section



open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

section HomBasis

variable {U W : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [FiniteDimensional 𝕜 U]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

noncomputable def continuousLinearMapHomBasis
    (bU : Module.Basis ι 𝕜 U) (bW : Module.Basis κ 𝕜 W) :
    Module.Basis (κ × ι) 𝕜 (U →L[𝕜] W) :=
  (bU.linearMap bW).map
    (LinearMap.toContinuousLinearMap : (U →ₗ[𝕜] W) ≃ₗ[𝕜] U →L[𝕜] W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.continuousLinearMapHomBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.continuousLinearMapHomBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.continuousLinearMapHomBasis ``Submission.DifferentialGeometry.Tensor0SBundle.continuousLinearMapHomBasis

theorem continuousLinearMap_homBasis_repr
    (bU : Module.Basis ι 𝕜 U) (bW : Module.Basis κ 𝕜 W)
    (A : U →L[𝕜] W) (i : ι) (j : κ) :
    (continuousLinearMapHomBasis (𝕜 := 𝕜) bU bW).repr A (j, i) =
      bW.repr (A (bU i)) j := by
  change (bU.linearMap bW).repr
      ((LinearMap.toContinuousLinearMap : (U →ₗ[𝕜] W) ≃ₗ[𝕜] U →L[𝕜] W).symm A)
      (j, i) =
    bW.repr (A (bU i)) j
  change LinearMap.toMatrix bU bW (A : U →ₗ[𝕜] W) j i =
    bW.repr (A (bU i)) j
  rw [LinearMap.toMatrix_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.continuousLinearMap_homBasis_repr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.continuousLinearMap_homBasis_repr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.continuousLinearMap_homBasis_repr ``Submission.DifferentialGeometry.Tensor0SBundle.continuousLinearMap_homBasis_repr

end HomBasis

noncomputable def tensorRSModelBasis {d : ℕ}
    (bE : Module.Basis (Fin d) 𝕜 E) (r s : ℕ) :
    Module.Basis ((Fin r → Fin d) × (Fin s → Fin d)) 𝕜 (TensorRSModel r s 𝕜 E) :=
  let bR := continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) bE r
  let bS := continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) bE s
  (continuousLinearMapHomBasis (𝕜 := 𝕜) bR bS).reindex
    (Equiv.prodComm (Fin s → Fin d) (Fin r → Fin d))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.tensorRSModelBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.tensorRSModelBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.tensorRSModelBasis ``Submission.DifferentialGeometry.Tensor0SBundle.tensorRSModelBasis

theorem tensorRSModel_basis_repr {d : ℕ}
    (bE : Module.Basis (Fin d) 𝕜 E) (r s : ℕ)
    (A : TensorRSModel r s 𝕜 E)
    (ρ : Fin r → Fin d) (σ : Fin s → Fin d) :
    (tensorRSModelBasis (𝕜 := 𝕜) (E := E) bE r s).repr A (ρ, σ) =
      (A ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) bE r) ρ))
        (fun a : Fin s => bE (σ a)) := by
  unfold tensorRSModelBasis
  rw [Module.Basis.repr_reindex_apply]
  rw [continuousLinearMap_homBasis_repr]
  rw [continuousMultilinearMap_basis_repr]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.tensorRSModel_basis_repr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.tensorRSModel_basis_repr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.tensorRSModel_basis_repr ``Submission.DifferentialGeometry.Tensor0SBundle.tensorRSModel_basis_repr

section SmoothCriterion

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiffAt_tensorRSModel_of_apply_basis_eval_basis
    {d r s : ℕ} (bE : Module.Basis (Fin d) 𝕜 E)
    {G : M → TensorRSModel r s 𝕜 E} {x₀ : M} {n : WithTop ℕ∞}
    (hcoord :
      ∀ ρ : Fin r → Fin d, ∀ σ : Fin s → Fin d,
        ContMDiffAt I 𝓘(𝕜, 𝕜) n
          (fun p : M =>
            (G p ((continuousMultilinearMapBasis
              (𝕜 := 𝕜) (F := E) bE r) ρ))
              (fun a : Fin s => bE (σ a))) x₀) :
    ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E) n G x₀ := by
  classical
  let B := tensorRSModelBasis (𝕜 := 𝕜) (E := E) bE r s
  have hcoords :
      ContMDiffAt I 𝓘(𝕜, ((Fin r → Fin d) × (Fin s → Fin d) → 𝕜)) n
        (fun p : M => B.equivFunL (G p)) x₀ := by
    rw [contMDiffAt_pi_space]
    intro idx
    rcases idx with ⟨ρ, σ⟩
    simpa [B, tensorRSModel_basis_repr] using hcoord ρ σ
  have hsmooth :=
    ((B.equivFunL.symm :
        (((Fin r → Fin d) × (Fin s → Fin d) → 𝕜) →L[𝕜]
          TensorRSModel r s 𝕜 E)).contMDiff.contMDiffAt.comp x₀ hcoords)
  refine hsmooth.congr_of_eventuallyEq ?_
  filter_upwards with p
  simp [B]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.contMDiffAt_tensorRSModel_of_apply_basis_eval_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.contMDiffAt_tensorRSModel_of_apply_basis_eval_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.contMDiffAt_tensorRSModel_of_apply_basis_eval_basis ``Submission.DifferentialGeometry.Tensor0SBundle.contMDiffAt_tensorRSModel_of_apply_basis_eval_basis

end SmoothCriterion

section Trivialization

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable {x₀ x : M}

namespace Tensor0SSpace

noncomputable def constInChart (s : ℕ) (x₀ : M)
    (β : Tensor0SModel s 𝕜 E) (x : M) : Tensor0SSpace s I x := by
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  exact (_root_.FiberBundle.trivializationAt (Tensor0SModel s 𝕜 E)
    (fun x => Tensor0SSpace s I x) x₀).symmL 𝕜 x β

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.constInChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.constInChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.constInChart ``Submission.DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.constInChart

omit [CompleteSpace 𝕜] in
theorem trivializationAt_apply (s : ℕ)
    (T : Tensor0SSpace s I x) (v : Fin s → E) :
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
    ((_root_.FiberBundle.trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀) ⟨x, T⟩).2 v =
      T (fun i => (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i)) := by
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  change (((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousMultilinearMap 𝕜 s)
      ⟨x, T⟩).2 v =
    T (fun i => (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i))
  rw [Bundle.Trivialization.continuousMultilinearMap_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.trivializationAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.trivializationAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.trivializationAt_apply ``Submission.DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.trivializationAt_apply

omit [CompleteSpace 𝕜] in
theorem continuousLinearEquivAt_apply (s : ℕ)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : Tensor0SSpace s I x) (v : Fin s → E) :
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
    ((_root_.FiberBundle.trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).continuousLinearEquivAt 𝕜 x
          (show x ∈ (_root_.FiberBundle.trivializationAt (Tensor0SModel s 𝕜 E)
            (fun x => Tensor0SSpace s I x) x₀).baseSet from hx) T) v =
      T (fun i => (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i)) := by
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  change ((_root_.FiberBundle.trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀) ⟨x, T⟩).2 v =
      T (fun i => (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i))
  exact trivializationAt_apply (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x) s T v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.continuousLinearEquivAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.continuousLinearEquivAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.continuousLinearEquivAt_apply ``Submission.DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.continuousLinearEquivAt_apply

omit [CompleteSpace 𝕜] in
theorem continuousLinearMapAt_apply (s : ℕ)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : Tensor0SSpace s I x) (v : Fin s → E) :
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
    (_root_.FiberBundle.trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).continuousLinearMapAt 𝕜 x T v =
      T (fun i => (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i)) := by
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  rw [Bundle.Trivialization.continuousLinearMapAt_apply,
    show ⇑((_root_.FiberBundle.trivializationAt (Tensor0SModel s 𝕜 E)
      (fun x => Tensor0SSpace s I x) x₀).linearMapAt 𝕜 x) =
      fun y => (_root_.FiberBundle.trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀ ⟨x, y⟩).2 from
      (_root_.FiberBundle.trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.continuousLinearMapAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.continuousLinearMapAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.continuousLinearMapAt_apply ``Submission.DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.continuousLinearMapAt_apply

omit [CompleteSpace 𝕜] in
theorem constInChart_apply (s : ℕ)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet)
    (β : Tensor0SModel s 𝕜 E) (v : Fin s → TangentSpace I x) :
    (constInChart (𝕜 := 𝕜) (I := I) s x₀ β x) v =
      β (fun i => (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (v i)) := by
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  let eT := _root_.FiberBundle.trivializationAt (Tensor0SModel s 𝕜 E)
    (fun x => Tensor0SSpace s I x) x₀
  let e := _root_.FiberBundle.trivializationAt E (TangentSpace I) x₀
  have hxT : x ∈ eT.baseSet := hx
  have hcoord := congrArg
    (fun A : Tensor0SModel s 𝕜 E => A (fun i => e.continuousLinearMapAt 𝕜 x (v i)))
    (eT.continuousLinearMapAt_symmL (R := 𝕜) hxT β)
  unfold constInChart
  dsimp only [eT, e] at hcoord ⊢
  rw [continuousLinearMapAt_apply (𝕜 := 𝕜) (I := I)
    (x₀ := x₀) (x := x) s hx] at hcoord
  have hcancel : (fun i => e.symmL 𝕜 x (e.continuousLinearMapAt 𝕜 x (v i))) = v := by
    funext i
    exact e.symmL_continuousLinearMapAt (R := 𝕜) hx (v i)
  rw [hcancel] at hcoord
  exact hcoord

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.constInChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.constInChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.constInChart_apply ``Submission.DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.constInChart_apply

end Tensor0SSpace

namespace TensorRSSpace

omit [CompleteSpace 𝕜] in
theorem trivializationAt_apply (r s : ℕ)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : TensorRSSpace r s I x) (β : Tensor0SModel r 𝕜 E) (v : Fin s → E) :
    letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
    (((_root_.FiberBundle.trivializationAt (TensorRSModel r s 𝕜 E)
        (fun x => TensorRSSpace r s I x) x₀) ⟨x, T⟩).2 β) v =
      (T ((_root_.FiberBundle.trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x β))
        (fun a => (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v a)) := by
  let := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  let : FiberBundle (Tensor0SModel r 𝕜 E) (fun y : M => Tensor0SSpace r I y) :=
    tensor0SBundleFiber r
  let : FiberBundle (Tensor0SModel s 𝕜 E) (fun y : M => Tensor0SSpace s I y) :=
    tensor0SBundleFiber s
  let : VectorBundle 𝕜 (Tensor0SModel r 𝕜 E) (fun y : M => Tensor0SSpace r I y) :=
    tensor0SBundle_vector r
  let : VectorBundle 𝕜 (Tensor0SModel s 𝕜 E) (fun y : M => Tensor0SSpace s I y) :=
    tensor0SBundle_vector s
  have hxR : x ∈ (_root_.FiberBundle.trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀).baseSet := hx
  have hxS : x ∈ (_root_.FiberBundle.trivializationAt (Tensor0SModel s 𝕜 E)
      (fun x => Tensor0SSpace s I x) x₀).baseSet := hx
  rw [hom_trivializationAt_apply (RingHom.id 𝕜)
    (F₁ := Tensor0SModel r 𝕜 E) (E₁ := fun y => Tensor0SSpace r I y)
    (F₂ := Tensor0SModel s 𝕜 E) (E₂ := fun y => Tensor0SSpace s I y)]
  rw [ContinuousLinearMap.inCoordinates_eq hxR hxS]
  change (((_root_.FiberBundle.trivializationAt (Tensor0SModel s 𝕜 E)
      (fun x => Tensor0SSpace s I x) x₀).continuousLinearEquivAt 𝕜 x hxS)
        (T (((_root_.FiberBundle.trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).continuousLinearEquivAt 𝕜 x hxR).symm β))) v =
      (T ((_root_.FiberBundle.trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x β))
        (fun a => (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v a))
  have hβ :
      ((_root_.FiberBundle.trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).continuousLinearEquivAt 𝕜 x hxR).symm β =
        (_root_.FiberBundle.trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x β :=
    congrFun ((_root_.FiberBundle.trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀).symm_continuousLinearEquivAt_eq hxR) β
  rw [hβ]
  exact Tensor0SSpace.continuousLinearEquivAt_apply
    (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x) s hx _ v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TensorRSSpace.trivializationAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TensorRSSpace.trivializationAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TensorRSSpace.trivializationAt_apply ``Submission.DifferentialGeometry.Tensor0SBundle.TensorRSSpace.trivializationAt_apply

theorem trivializationAt_basis_coord {d r s : ℕ}
    (bE : Module.Basis (Fin d) 𝕜 E)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : TensorRSSpace r s I x)
    (ρ : Fin r → Fin d) (σ : Fin s → Fin d) :
    letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
    (((_root_.FiberBundle.trivializationAt (TensorRSModel r s 𝕜 E)
        (fun x => TensorRSSpace r s I x) x₀) ⟨x, T⟩).2
        ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) bE r) ρ))
        (fun a : Fin s => bE (σ a)) =
      (T ((_root_.FiberBundle.trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x
          ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) bE r) ρ)))
        (fun a => (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (bE (σ a))) := by
  let := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  exact trivializationAt_apply (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x) r s hx T
    ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) bE r) ρ)
    (fun a : Fin s => bE (σ a))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TensorRSSpace.trivializationAt_basis_coord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TensorRSSpace.trivializationAt_basis_coord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TensorRSSpace.trivializationAt_basis_coord ``Submission.DifferentialGeometry.Tensor0SBundle.TensorRSSpace.trivializationAt_basis_coord

end TensorRSSpace

end Trivialization

end

end Tensor0SBundle
end DifferentialGeometry
