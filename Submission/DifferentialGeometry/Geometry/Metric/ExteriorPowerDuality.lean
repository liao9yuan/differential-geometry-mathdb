import Submission.DifferentialGeometry.Geometry.Metric.ExteriorPowerBundle
import Submission.DifferentialGeometry.Geometry.Metric.BundleAlternating
import Submission.DifferentialGeometry.Analysis.InnerProductSpace.HilbertSchmidt
import Submission.DifferentialGeometry.Tensor.Alternating.Bundle.Defs
import Submission.DifferentialGeometry.Bundle.Hom.Regularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.RealInnerProductSpace _root_.Topology

namespace exteriorPower
open _root_.exteriorPower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

open _root_.exteriorPower in
private instance alternatingFiniteDimensional (k : ℕ) :
    FiniteDimensional ℝ (E [⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
    (Module.finBasis ℝ E)).finiteDimensional_of_finite

run_cmd do
  let target := ``Submission.exteriorPower.alternatingFiniteDimensional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `exteriorPower.alternatingFiniteDimensional target :: scope.openDecls } }

open _root_.exteriorPower in
private def evaluationLinearMap (k : ℕ) :
    (⋀[ℝ]^k E) →ₗ[ℝ] (E [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
  (_root_.exteriorPower.alternatingMapLinearEquiv.toLinearMap.comp
    (ContinuousAlternatingMap.toAlternatingMapLinear (R := ℝ))).flip

run_cmd do
  let target := ``Submission.exteriorPower.evaluationLinearMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `exteriorPower.evaluationLinearMap target :: scope.openDecls } }

open _root_.exteriorPower in
private theorem evaluationLinearMap_injective (k : ℕ) :
    Function.Injective (evaluationLinearMap (E := E) k) := by
  intro u v h
  have heq (w : ⋀[ℝ]^k E) : ⟪w, u⟫ = ⟪w, v⟫ := by
    have ht := LinearMap.congr_fun h (musicalEquiv k w)
    change _root_.exteriorPower.alternatingMapLinearEquiv (musicalEquiv k w).toAlternatingMap u =
      _root_.exteriorPower.alternatingMapLinearEquiv (musicalEquiv k w).toAlternatingMap v at ht
    simpa only [alternatingMapLinearEquiv_musicalEquiv] using ht
  exact ext_inner_left ℝ heq

run_cmd do
  let target := ``Submission.exteriorPower.evaluationLinearMap_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `exteriorPower.evaluationLinearMap_injective target :: scope.openDecls } }

open _root_.exteriorPower in
def alternatingDualEquiv (k : ℕ) :
    (⋀[ℝ]^k E) ≃L[ℝ] ((E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) := by
  let L := (LinearEquiv.ofInjectiveOfFinrankEq (evaluationLinearMap (E := E) k)
    (evaluationLinearMap_injective (E := E) k) (by
      rw [Module.finrank_linearMap, Module.finrank_self, mul_one,
        ContinuousAlternatingMap.finrank_continuousAlternatingMap, exteriorPower.finrank_eq])).trans
      LinearMap.toContinuousLinearMap
  exact L.toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.alternatingDualEquiv then
    throwError "Refusing to shadow existing declaration exteriorPower.alternatingDualEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.alternatingDualEquiv ``Submission.exteriorPower.alternatingDualEquiv

open _root_.exteriorPower in
theorem alternatingDualEquiv_apply (k : ℕ) (u : ⋀[ℝ]^k E) (a : E [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingDualEquiv k u a = _root_.exteriorPower.alternatingMapLinearEquiv a.toAlternatingMap u := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.alternatingDualEquiv_apply then
    throwError "Refusing to shadow existing declaration exteriorPower.alternatingDualEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.alternatingDualEquiv_apply ``Submission.exteriorPower.alternatingDualEquiv_apply

open _root_.exteriorPower in
theorem alternatingDualEquiv_ιMulti_apply (k : ℕ) (u : Fin k → E)
    (a : E [⋀^Fin k]→L[ℝ] ℝ) : alternatingDualEquiv k (_root_.exteriorPower.ιMulti ℝ k u) a = a u :=
  _root_.exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.alternatingDualEquiv_ιMulti_apply then
    throwError "Refusing to shadow existing declaration exteriorPower.alternatingDualEquiv_ιMulti_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.alternatingDualEquiv_ιMulti_apply ``Submission.exteriorPower.alternatingDualEquiv_ιMulti_apply

open _root_.exteriorPower in
theorem alternatingDualEquiv_map_apply
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (k : ℕ) (f : E →L[ℝ] F) (u : ⋀[ℝ]^k E) (a : F [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingDualEquiv k (_root_.exteriorPower.map k f.toLinearMap u) a =
      alternatingDualEquiv k u (a.compContinuousLinearMap f) := by
  have h : (_root_.exteriorPower.alternatingMapLinearEquiv a.toAlternatingMap).comp (_root_.exteriorPower.map k f.toLinearMap) =
      alternatingMapLinearEquiv (a.compContinuousLinearMap f).toAlternatingMap := by
    apply _root_.exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      _root_.exteriorPower.map_apply_ιMulti, _root_.exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rfl
  exact LinearMap.congr_fun h u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.alternatingDualEquiv_map_apply then
    throwError "Refusing to shadow existing declaration exteriorPower.alternatingDualEquiv_map_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.alternatingDualEquiv_map_apply ``Submission.exteriorPower.alternatingDualEquiv_map_apply

end exteriorPower

namespace Bundle
open _root_.Bundle

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (V : B → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

open _root_.Bundle in
theorem alternatingRiemannianMetric_musicalEquiv_left (k : ℕ) (x : B)
    (u : ⋀[ℝ]^k (V x)) (a : V x [⋀^Fin k]→L[ℝ] ℝ) :
    letI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
    (alternatingRiemannianMetric (F := F) V k).inner x (exteriorPower.musicalEquiv k u) a =
      (k.factorial : ℝ) * exteriorPower.alternatingDualEquiv k u a := by
  let : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  rw [alternatingRiemannianMetric_inner_eq_factorial_mul_exterior_inner,
    ContinuousLinearEquiv.symm_apply_apply]
  congr 1
  rw [real_inner_comm, exteriorPower.alternatingDualEquiv_apply]
  have h := exteriorPower.alternatingMapLinearEquiv_musicalEquiv k
    ((exteriorPower.musicalEquiv k).symm a) u
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.alternatingRiemannianMetric_musicalEquiv_left then
    throwError "Refusing to shadow existing declaration Bundle.alternatingRiemannianMetric_musicalEquiv_left"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.alternatingRiemannianMetric_musicalEquiv_left ``Submission.Bundle.alternatingRiemannianMetric_musicalEquiv_left


open _root_.Bundle in
theorem hilbertSchmidtInner_musicalEquiv_conjugate (k : ℕ) (x : B) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI : _root_.Bundle.RiemannianBundle
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) :=
      ⟨alternatingRiemannianMetric (F := F) V k⟩
    letI alternatingNorm : ∀ y, NormedAddCommGroup (V y [⋀^Fin k]→L[ℝ] ℝ) :=
      fun y => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) y
    letI : ∀ y, SeminormedAddCommGroup (V y [⋀^Fin k]→L[ℝ] ℝ) :=
      fun y => (alternatingNorm y).toSeminormedAddCommGroup
    letI : ∀ y, InnerProductSpace ℝ (V y [⋀^Fin k]→L[ℝ] ℝ) :=
      fun y => Bundle.instInnerProductSpaceReal
        (E := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) y
    let e := exteriorPower.musicalEquiv (E := V x) k
    ∀ A C : (⋀[ℝ]^k (V x)) →L[ℝ] ⋀[ℝ]^k (V x),
      @ContinuousLinearMap.hilbertSchmidtInner _ _ (alternatingNorm x) _ _ (alternatingNorm x) _
          (e.toContinuousLinearMap.comp (A.comp e.symm.toContinuousLinearMap))
          (e.toContinuousLinearMap.comp (C.comp e.symm.toContinuousLinearMap)) =
        ContinuousLinearMap.hilbertSchmidtInner A C := by
  let : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let : _root_.Bundle.RiemannianBundle
      (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) :=
    ⟨alternatingRiemannianMetric (F := F) V k⟩
  let alternatingNorm : ∀ y, NormedAddCommGroup (V y [⋀^Fin k]→L[ℝ] ℝ) :=
    fun y => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) y
  let : ∀ y, SeminormedAddCommGroup (V y [⋀^Fin k]→L[ℝ] ℝ) :=
    fun y => (alternatingNorm y).toSeminormedAddCommGroup
  let : ∀ y, InnerProductSpace ℝ (V y [⋀^Fin k]→L[ℝ] ℝ) :=
    fun y => Bundle.instInnerProductSpaceReal
      (E := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) y
  let : FiniteDimensional ℝ (V x [⋀^Fin k]→L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
      (Module.finBasis ℝ (V x))).finiteDimensional_of_finite
  dsimp only
  intro A C
  have hinner (u v : ⋀[ℝ]^k (V x)) :
      @_root_.Inner.inner ℝ _ (by infer_instance : Inner ℝ (V x [⋀^Fin k]→L[ℝ] ℝ))
        (exteriorPower.musicalEquiv k u) (exteriorPower.musicalEquiv k v) =
        (k.factorial : ℝ) * _root_.Inner.inner ℝ u v := by
    change (alternatingRiemannianMetric (F := F) V k).inner x
      (exteriorPower.musicalEquiv k u) (exteriorPower.musicalEquiv k v) = _
    rw [alternatingRiemannianMetric_inner_eq_factorial_mul_exterior_inner,
      ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
  exact @ContinuousLinearMap.hilbertSchmidtInner_conjugate_of_inner_eq_mul
    (⋀[ℝ]^k (V x)) (V x [⋀^Fin k]→L[ℝ] ℝ) _ _ _ (alternatingNorm x) _ _
    (exteriorPower.musicalEquiv k) (k.factorial : ℝ) (Nat.cast_pos.mpr k.factorial_pos)
    hinner A C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.hilbertSchmidtInner_musicalEquiv_conjugate then
    throwError "Refusing to shadow existing declaration Bundle.hilbertSchmidtInner_musicalEquiv_conjugate"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.hilbertSchmidtInner_musicalEquiv_conjugate ``Submission.Bundle.hilbertSchmidtInner_musicalEquiv_conjugate

end Bundle
