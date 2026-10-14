import Submission.DifferentialGeometry.Tensor.RSTensor.Field
import Submission.DifferentialGeometry.Tensor.RSTensor.Algebra.Contraction
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
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.TensorProduct
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Section
import Submission.DifferentialGeometry.Tensor.Product.Basis
import Submission.DifferentialGeometry.Tensor.Product.Bundle
import Submission.DifferentialGeometry.Tensor.Product.Pretrivialization
import Submission.DifferentialGeometry.Tensor.Product.Defs
import Submission.DifferentialGeometry.Tensor.Product.HomEquiv
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Submission.DifferentialGeometry.Tensor.Alternating.Curry
import Submission.DifferentialGeometry.Tensor.Alternating.Flip
import Submission.DifferentialGeometry.Tensor.Multilinear.Flip
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Mul
import Submission.DifferentialGeometry.Tensor.Alternating.Reindexing.Domain
import Mathlib.LinearAlgebra.Alternating.Basic
import Submission.DifferentialGeometry.Tensor.Alternating.Shuffle.Decomposition
import Submission.DifferentialGeometry.Tensor.Alternating.Shuffle.Split
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Group
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Tactic.Cases
import Mathlib.Topology.FiberBundle.Basic
import Submission.DifferentialGeometry.Tensor.Product.Fiber
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Submission.DifferentialGeometry.Bundle.Section
import Submission.DifferentialGeometry.Tensor.Multilinear.PredualBasis
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Submission.Bundle.Submission.Trivialization.continuousMultilinearMap then
    throwError "Refusing to shadow existing declaration Submission.Bundle.Submission.Trivialization.continuousMultilinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `Submission.Bundle.Submission.Trivialization.continuousMultilinearMap ``Submission.Bundle.Trivialization.continuousMultilinearMap

namespace DifferentialGeometry.Tensor.RSTensor
noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle

open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable (n : WithTop ℕ∞)
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

private noncomputable def to02Tensor_eCLM :
    (E →L[ℝ] ℝ) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ :=
  (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.RSTensor.to02Tensor_eCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.RSTensor.to02Tensor_eCLM target :: scope.openDecls } }

private noncomputable def to02Tensor_uCLM :
    (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) ℝ).symm.toContinuousLinearMap

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.RSTensor.to02Tensor_uCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.RSTensor.to02Tensor_uCLM target :: scope.openDecls } }

private noncomputable def to02TensorFiber {x : M}
    (A : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    Tensor0SSpace 2 I x :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x).symm
    ((to02Tensor_eCLM (E := E)).comp A).uncurryLeft

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.RSTensor.to02TensorFiber
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.RSTensor.to02TensorFiber target :: scope.openDecls } }

private lemma to02Tensor_trivialization_eq {x₀ x : M}
    (A : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) :
    (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (fun y => Tensor0SBundle.Tensor0SSpace 2 I y) x₀
      ⟨x, to02TensorFiber (I := I) (M := M) A⟩).2
      =
    (to02Tensor_uCLM (E := E)) ((to02Tensor_eCLM (E := E)).comp
      ((_root_.FiberBundle.trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀ ⟨x, A⟩).2)) := by
  let e₀ := _root_.FiberBundle.trivializationAt E (TangentSpace I) x₀
  rw [show to02TensorFiber (I := I) (M := M) A =
      ((to02Tensor_eCLM (E := E)).comp A).uncurryLeft from
    tensor0SSpaceFiberContinuousLinearEquiv_symm_apply (I := I) 2 x _]
  ext m
  change (((e₀.continuousMultilinearMap ℝ 2)
      ⟨x, ((to02Tensor_eCLM (E := E)).comp
        A).uncurryLeft⟩).2) m = _
  rw [_root_.Submission.Bundle.Trivialization.continuousMultilinearMap_apply]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ]
  have hx' : x ∈ (_root_.FiberBundle.trivializationAt (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hx, by simp⟩
  rw [hom_trivializationAt_apply]
  change (to02Tensor_eCLM (E := E)) (A
      ((Trivialization.symmL ℝ e₀ x) (m 0)))
      (Fin.tail fun i => (Trivialization.symmL ℝ e₀ x) (m i)) =
    (to02Tensor_eCLM (E := E)) (ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ) x₀ x x₀ x
      A (m 0))
      (Fin.tail m)
  change A ((Trivialization.symmL ℝ e₀ x) (m 0))
      ((Trivialization.symmL ℝ e₀ x) (Fin.tail m 0)) =
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ) x₀ x x₀ x A (m 0) (Fin.tail m 0)
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  dsimp only [e₀]
  simp only [Trivialization.symmL_apply (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀) hx,
    Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.RSTensor.to02Tensor_trivialization_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.RSTensor.to02Tensor_trivialization_eq target :: scope.openDecls } }

theorem joint_to02 {S : Set ℝ}
    (A : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] TangentSpace I p.1 →L[ℝ] ℝ)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x) p.1
        (((continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap.comp
          (A p)).uncurryLeft))
      ((Set.univ : Set M) ×ˢ S) := by
  let := Tensor0SBundle.tensor0SBundleTopology
    (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  intro p₀ hp₀
  rw [_root_.Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  let eCLM := to02Tensor_eCLM (E := E)
  let uCLM := to02Tensor_uCLM (E := E)
  have htriv := (_root_.Bundle.contMDiffWithinAt_totalSpace
    (F := E →L[ℝ] E →L[ℝ] ℝ)
    (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)).mp
      (hA p₀ hp₀)
  have hcurried : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) ∞
      (fun p : M × ℝ => eCLM.comp
        ((_root_.FiberBundle.trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          p₀.1 ⟨p.1, A p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    (contMDiffWithinAt_const (c := eCLM)).clm_comp htriv.2
  have hconverted : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞
      (fun p : M × ℝ => uCLM (eCLM.comp
        ((_root_.FiberBundle.trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          p₀.1 ⟨p.1, A p⟩).2)))
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    uCLM.contMDiff.contMDiffAt.comp_contMDiffWithinAt p₀ hcurried
  refine hconverted.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in
        nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) p₀.1).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) p₀.1).open_baseSet.mem_nhds
          (_root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) p₀.1))
    filter_upwards [hbase] with p hp
    exact to02Tensor_trivialization_eq (I := I) (M := M)
      (A := A p) hp
  · exact to02Tensor_trivialization_eq (I := I) (M := M)
      (A := A p₀) (_root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) p₀.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.RSTensor.joint_to02 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.RSTensor.joint_to02"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.RSTensor.joint_to02 ``Submission.DifferentialGeometry.Tensor.RSTensor.joint_to02

open _root_.Bundle _root_.Bundle.ContMDiffRiemannianMetric in
def _root_.Submission.Bundle.ContMDiffRiemannianMetric.toTensor0S
    {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [hM : IsManifold I (n + 1) M]
    (g : _root_.Bundle.ContMDiffRiemannianMetric I n E (TangentSpace I : M -> Type _)) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (I := I) (M := M) (n := n) 2 := by
  unfold Tensor0SBundle.Tensor0SField
  letI := Tensor0SBundle.tensor0SBundleTopology
    (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  let eCLM := to02Tensor_eCLM (E := E)
  let uCLM := to02Tensor_uCLM (E := E)
  let gI := _root_.Bundle.ContMDiffRiemannianMetric.inner g
  exact ⟨fun x => to02TensorFiber (I := I) (M := M) (gI x), by
    rcases hM with ⟨⟩
    let : IsManifold I (n + 1) M := IsManifold.mk
    have := Tensor0SBundle.tensor0SBundle_smooth
      (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := n) 2
    intro x₀
    refine (_root_.Bundle.contMDiffAt_section (F := Tensor0SModel 2 ℝ E)
      (E := fun x : M => Tensor0SSpace 2 I x)
      (s := fun x => to02TensorFiber (I := I) (M := M) (gI x)) x₀).mpr ?_
    have hTriv := (_root_.Bundle.contMDiffAt_section (F := E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        (s := gI) (x₀ := x₀)).mp (g.contMDiff.contMDiffAt (x := x₀))
    have hCurried :
        ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) n
          (fun x => eCLM.comp ((_root_.FiberBundle.trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
            (fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x₀
            ⟨x, gI x⟩).2)) x₀ := by
      exact (contMDiffAt_const (c := eCLM)).clm_comp hTriv
    refine (uCLM.contMDiffAt.comp x₀ hCurried).congr_of_eventuallyEq ?_
    filter_upwards [(_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
      (_root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x₀)] with x hx
    exact to02Tensor_trivialization_eq (I := I) (M := M)
      (A := gI x) (x := x) (x₀ := x₀) hx⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Bundle.ContMDiffRiemannianMetric
  let env ← Lean.getEnv
  if env.contains `Bundle.ContMDiffRiemannianMetric.toTensor0S then
    throwError "Refusing to shadow existing declaration Bundle.ContMDiffRiemannianMetric.toTensor0S"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.ContMDiffRiemannianMetric.toTensor0S ``Submission.Bundle.ContMDiffRiemannianMetric.toTensor0S

open _root_.Bundle _root_.Bundle.ContMDiffRiemannianMetric in
@[simp]
theorem _root_.Submission.Bundle.ContMDiffRiemannianMetric.toTensor0S_apply
    {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [IsManifold I (n + 1) M]
    (g : _root_.Bundle.ContMDiffRiemannianMetric I n E (TangentSpace I : M -> Type _))
    (x : M) (v : Fin 2 -> TangentSpace I x) :
    g.toTensor0S (I := I) (n := n) x v =
      (_root_.Bundle.ContMDiffRiemannianMetric.inner g) x (v 0) (v 1) := by
  simp only [_root_.Submission.Bundle.ContMDiffRiemannianMetric.toTensor0S,
    tensor0SBundleFiber.eq_1, id_eq, Fin.isValue]
  change ((_root_.Bundle.ContMDiffRiemannianMetric.inner g) x (v 0)) (Fin.tail v 0) =
    ((_root_.Bundle.ContMDiffRiemannianMetric.inner g) x (v 0)) (v 1)
  simp [Fin.tail]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.ContMDiffRiemannianMetric.toTensor0S_apply then
    throwError "Refusing to shadow existing declaration Bundle.ContMDiffRiemannianMetric.toTensor0S_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.ContMDiffRiemannianMetric.toTensor0S_apply ``Submission.Bundle.ContMDiffRiemannianMetric.toTensor0S_apply

end

end DifferentialGeometry.Tensor.RSTensor
