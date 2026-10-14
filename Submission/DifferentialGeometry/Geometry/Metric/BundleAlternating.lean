import Submission.DifferentialGeometry.Geometry.Metric.BundleMultilinear
import Submission.DifferentialGeometry.Geometry.Metric.ExteriorPower
import Submission.DifferentialGeometry.Tensor.Alternating.BundleMaps
import Submission.DifferentialGeometry.Tensor.Alternating.Coordinates.Basis

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.Manifold _root_.ContDiff

namespace Bundle
open _root_.Bundle

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (V : B → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

open _root_.Bundle in
private def alternatingToMultilinear (k : ℕ) (x : B) :
    (V x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] Bundle.continuousMultilinearMap ℝ k F V x :=
  (Bundle.continuousMultilinearMap.fiberContinuousLinearEquiv (F := F) k x).symm.toContinuousLinearMap.comp
    (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ)

run_cmd do
  let target := ``Submission.Bundle.alternatingToMultilinear
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Bundle.alternatingToMultilinear target :: scope.openDecls } }

open _root_.Bundle in
def alternatingRiemannianMetric (k : ℕ) :
    _root_.Bundle.RiemannianMetric (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) where
  inner x := (ContinuousLinearMap.precomp ℝ (alternatingToMultilinear V k x)).comp
    (((multilinearRiemannianMetric V k).inner x).comp (alternatingToMultilinear V k x))
  symm x a b := (multilinearRiemannianMetric V k).symm x _ _
  pos x a ha := (multilinearRiemannianMetric V k).pos x _ (by
    intro h
    apply ha
    exact ContinuousAlternatingMap.toContinuousMultilinearMap_injective h)
  continuousAt x := by
    have hg : ContinuousAt
        (fun T => (multilinearRiemannianMetric (F := F) V k).inner x T T)
        (alternatingToMultilinear (F := F) V k x 0) := by
      simpa only [map_zero] using (multilinearRiemannianMetric (F := F) V k).continuousAt x
    exact hg.comp (alternatingToMultilinear V k x).continuous.continuousAt
  isVonNBounded x := by
    let p : Bundle.continuousMultilinearMap ℝ k F V x →L[ℝ] V x [⋀^Fin k]→L[ℝ] ℝ :=
      ContinuousMultilinearMap.alternatizationCLM.comp
        (Bundle.continuousMultilinearMap.fiberContinuousLinearEquiv (F := F) k x).toContinuousLinearMap
    apply ((multilinearRiemannianMetric V k).isVonNBounded x).image p |>.subset
    intro a ha
    refine ⟨a.toContinuousMultilinearMap, ha, ?_⟩
    exact ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.alternatingRiemannianMetric then
    throwError "Refusing to shadow existing declaration Bundle.alternatingRiemannianMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.alternatingRiemannianMetric ``Submission.Bundle.alternatingRiemannianMetric

open _root_.Bundle in
@[simp]
theorem alternatingRiemannianMetric_inner (k : ℕ) (x : B)
    (a b : V x [⋀^Fin k]→L[ℝ] ℝ) :
    (alternatingRiemannianMetric (F := F) V k).inner x a b =
      (multilinearRiemannianMetric (F := F) V k).inner x
        a.toContinuousMultilinearMap b.toContinuousMultilinearMap := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.alternatingRiemannianMetric_inner then
    throwError "Refusing to shadow existing declaration Bundle.alternatingRiemannianMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.alternatingRiemannianMetric_inner ``Submission.Bundle.alternatingRiemannianMetric_inner

open _root_.Bundle in
theorem alternatingRiemannianMetric_inner_eq_sum {ι : Type*} [Fintype ι]
    (k : ℕ) (x : B) (e : OrthonormalBasis ι ℝ (V x))
    (a b : V x [⋀^Fin k]→L[ℝ] ℝ) :
    (alternatingRiemannianMetric (F := F) V k).inner x a b =
      ∑ j : Fin k → ι, a (fun i => e (j i)) * b (fun i => e (j i)) :=
  multilinearRiemannianMetric_inner_eq_sum V k x e _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.alternatingRiemannianMetric_inner_eq_sum then
    throwError "Refusing to shadow existing declaration Bundle.alternatingRiemannianMetric_inner_eq_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.alternatingRiemannianMetric_inner_eq_sum ``Submission.Bundle.alternatingRiemannianMetric_inner_eq_sum

open _root_.Bundle in
theorem alternatingRiemannianMetric_inner_eq_factorial_mul_exterior_inner
    (k : ℕ) (x : B) (a b : V x [⋀^Fin k]→L[ℝ] ℝ) :
    letI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
    (alternatingRiemannianMetric (F := F) V k).inner x a b =
      (k.factorial : ℝ) * _root_.Inner.inner ℝ ((exteriorPower.musicalEquiv k).symm a)
        ((exteriorPower.musicalEquiv k).symm b) := by
  let : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  rw [alternatingRiemannianMetric_inner_eq_sum V k x (stdOrthonormalBasis ℝ (V x))]
  exact exteriorPower.sum_mul_eq_factorial_mul_inner k (stdOrthonormalBasis ℝ (V x)) a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.alternatingRiemannianMetric_inner_eq_factorial_mul_exterior_inner then
    throwError "Refusing to shadow existing declaration Bundle.alternatingRiemannianMetric_inner_eq_factorial_mul_exterior_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.alternatingRiemannianMetric_inner_eq_factorial_mul_exterior_inner ``Submission.Bundle.alternatingRiemannianMetric_inner_eq_factorial_mul_exterior_inner

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  [ChartedSpace HB B] {n : ℕ∞ω} [ContMDiffVectorBundle n F V IB]
  [IsContMDiffRiemannianBundle IB n F V]

open _root_.Bundle in
theorem contMDiff_alternatingRiemannianMetric_inner (k : ℕ) :
    ContMDiff IB (IB.prod 𝓘(ℝ, (F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ]
        (F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)) n
      (fun x => (⟨x, (alternatingRiemannianMetric (F := F) V k).inner x⟩ :
        _root_.Bundle.TotalSpace ((F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
          (fun x => (V x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (V x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ))) := by
  let _ : FiniteDimensional ℝ (F [⋀^Fin k]→L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
      (Module.finBasis ℝ F)).finiteDimensional_of_finite
  let _ : _root_.Bundle.RiemannianBundle (Bundle.continuousMultilinearMap ℝ k F V) :=
    ⟨multilinearRiemannianMetric V k⟩
  let tensorNorm : ∀ x, NormedAddCommGroup (Bundle.continuousMultilinearMap ℝ k F V x) :=
    fun x => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := Bundle.continuousMultilinearMap ℝ k F V) x
  let _ : ∀ x, SeminormedAddCommGroup (Bundle.continuousMultilinearMap ℝ k F V x) :=
    fun x => (tensorNorm x).toSeminormedAddCommGroup
  let _ : ∀ x, InnerProductSpace ℝ (Bundle.continuousMultilinearMap ℝ k F V x) :=
    fun x => Bundle.instInnerProductSpaceReal (E := Bundle.continuousMultilinearMap ℝ k F V) x
  have hi : ContMDiff IB
      (IB.prod 𝓘(ℝ, (F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)) n
      (fun x => (⟨x, alternatingToMultilinear V k x⟩ : _root_.Bundle.TotalSpace
        ((F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
          (fun x => (V x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ]
            Bundle.continuousMultilinearMap ℝ k F V x))) :=
    ContMDiff.clm_bundle_of_map (ContMDiff.alternating_bundle_toMultilinear contMDiff_id)
  have h := (contMDiff_multilinearRiemannianMetric_inner V k).clm_bundle_bilinearComp
    (F₁ := ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
    (F₂ := ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ) (F₃ := ℝ)
    (F₄ := F [⋀^Fin k]→L[ℝ] ℝ) (F₅ := F [⋀^Fin k]→L[ℝ] ℝ)
    (U₁ := Bundle.continuousMultilinearMap ℝ k F V)
    (U₂ := Bundle.continuousMultilinearMap ℝ k F V) (U₃ := Bundle.Trivial B ℝ)
    (U₄ := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ))
    (U₅ := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) hi hi
  exact h.congr fun x => by
    apply TotalSpace.mk_inj.mpr
    ext a b
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.contMDiff_alternatingRiemannianMetric_inner then
    throwError "Refusing to shadow existing declaration Bundle.contMDiff_alternatingRiemannianMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.contMDiff_alternatingRiemannianMetric_inner ``Submission.Bundle.contMDiff_alternatingRiemannianMetric_inner

open _root_.Bundle in
def alternatingContMDiffRiemannianMetric (k : ℕ) :
    _root_.Bundle.ContMDiffRiemannianMetric IB n (F [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) where
  inner := (alternatingRiemannianMetric V k).inner
  symm := (alternatingRiemannianMetric V k).symm
  pos := (alternatingRiemannianMetric V k).pos
  isVonNBounded := (alternatingRiemannianMetric V k).isVonNBounded
  contMDiff := contMDiff_alternatingRiemannianMetric_inner V k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.alternatingContMDiffRiemannianMetric then
    throwError "Refusing to shadow existing declaration Bundle.alternatingContMDiffRiemannianMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.alternatingContMDiffRiemannianMetric ``Submission.Bundle.alternatingContMDiffRiemannianMetric

open _root_.Bundle in
@[simp]
theorem alternatingContMDiffRiemannianMetric_toRiemannianMetric (k : ℕ) :
    (alternatingContMDiffRiemannianMetric (IB := IB) (n := n) (F := F) V k).toRiemannianMetric =
      alternatingRiemannianMetric V k := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.alternatingContMDiffRiemannianMetric_toRiemannianMetric then
    throwError "Refusing to shadow existing declaration Bundle.alternatingContMDiffRiemannianMetric_toRiemannianMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.alternatingContMDiffRiemannianMetric_toRiemannianMetric ``Submission.Bundle.alternatingContMDiffRiemannianMetric_toRiemannianMetric

end Bundle
