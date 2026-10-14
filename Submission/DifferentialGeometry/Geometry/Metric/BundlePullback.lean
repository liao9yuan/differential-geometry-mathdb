import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.InnerProductSpace.LinearMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace Bundle.RiemannianMetric
open _root_.Bundle _root_.Bundle.RiemannianMetric

section Pullback

variable {B C : Type*} {V : B → Type*} {W : C → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]

open _root_.Bundle _root_.Bundle.RiemannianMetric in
@[ext]
theorem ext {g h : _root_.Bundle.RiemannianMetric V}
    (hinner : ∀ x v w, g.inner x v w = h.inner x v w) : g = h := by
  cases g
  cases h
  congr 1
  funext x
  ext v w
  exact hinner x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.RiemannianMetric.ext then
    throwError "Refusing to shadow existing declaration Bundle.RiemannianMetric.ext"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.RiemannianMetric.ext ``Submission.Bundle.RiemannianMetric.ext

open _root_.Bundle _root_.Bundle.RiemannianMetric in
def pullback (g : _root_.Bundle.RiemannianMetric W) (f : B → C) (e : ∀ x, V x ≃L[ℝ] W (f x)) :
    _root_.Bundle.RiemannianMetric V where
  inner x := (ContinuousLinearMap.precomp ℝ (e x).toContinuousLinearMap).comp
    ((g.inner (f x)).comp (e x).toContinuousLinearMap)
  symm x v w := g.symm (f x) (e x v) (e x w)
  pos x v hv := g.pos (f x) (e x v) ((e x).map_ne_zero_iff.mpr hv)
  continuousAt x := by
    have hg : ContinuousAt (fun w => g.inner (f x) w w) (e x 0) := by
      simpa only [map_zero] using g.continuousAt (f x)
    exact hg.comp (e x).continuous.continuousAt
  isVonNBounded x := by
    have h := (g.isVonNBounded (f x)).image (e x).symm.toContinuousLinearMap
    have heq : {v : V x | g.inner (f x) (e x v) (e x v) < 1} =
        (e x).symm '' {w : W (f x) | g.inner (f x) w w < 1} := by
      ext v
      constructor
      · intro hv
        exact ⟨e x v, hv, (e x).symm_apply_apply v⟩
      · rintro ⟨w, hw, rfl⟩
        change g.inner (f x) (e x ((e x).symm w)) (e x ((e x).symm w)) < 1
        simpa only [(e x).apply_symm_apply, Set.mem_ofPred_eq] using hw
    change Bornology.IsVonNBounded ℝ {v : V x | g.inner (f x) (e x v) (e x v) < 1}
    rw [heq]
    exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.RiemannianMetric.pullback then
    throwError "Refusing to shadow existing declaration Bundle.RiemannianMetric.pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.RiemannianMetric.pullback ``Submission.Bundle.RiemannianMetric.pullback

open _root_.Bundle _root_.Bundle.RiemannianMetric in
@[simp]
theorem pullback_inner (g : _root_.Bundle.RiemannianMetric W) (f : B → C)
    (e : ∀ x, V x ≃L[ℝ] W (f x)) (x : B) (v w : V x) :
    (g.pullback f e).inner x v w = g.inner (f x) (e x v) (e x w) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.RiemannianMetric.pullback_inner then
    throwError "Refusing to shadow existing declaration Bundle.RiemannianMetric.pullback_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.RiemannianMetric.pullback_inner ``Submission.Bundle.RiemannianMetric.pullback_inner

open _root_.Bundle _root_.Bundle.RiemannianMetric in
@[simp]
theorem pullback_id (g : _root_.Bundle.RiemannianMetric V) :
    g.pullback id (fun x => ContinuousLinearEquiv.refl ℝ (V x)) = g := by
  apply ext
  intro x v w
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.RiemannianMetric.pullback_id then
    throwError "Refusing to shadow existing declaration Bundle.RiemannianMetric.pullback_id"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.RiemannianMetric.pullback_id ``Submission.Bundle.RiemannianMetric.pullback_id

open _root_.Bundle _root_.Bundle.RiemannianMetric in
theorem pullback_comp {A : Type*} {U : A → Type*}
    [∀ x, AddCommGroup (U x)] [∀ x, Module ℝ (U x)] [∀ x, TopologicalSpace (U x)]
    (g : _root_.Bundle.RiemannianMetric W) (f : B → C) (e : ∀ x, V x ≃L[ℝ] W (f x))
    (q : A → B) (d : ∀ x, U x ≃L[ℝ] V (q x)) :
    (g.pullback f e).pullback q d =
      g.pullback (f ∘ q) (fun x => (d x).trans (e (q x))) := by
  apply ext
  intro x v w
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.RiemannianMetric.pullback_comp then
    throwError "Refusing to shadow existing declaration Bundle.RiemannianMetric.pullback_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.RiemannianMetric.pullback_comp ``Submission.Bundle.RiemannianMetric.pullback_comp

end Pullback

section InnerProduct

variable {B : Type*} (V : B → Type*)
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]

open _root_.Bundle _root_.Bundle.RiemannianMetric in
def ofInnerProductSpace : _root_.Bundle.RiemannianMetric V where
  inner _ := innerSL ℝ
  symm _ v w := real_inner_comm w v
  pos _ _ hv := real_inner_self_pos.mpr hv
  continuousAt _ := (continuous_id.inner continuous_id).continuousAt
  isVonNBounded x := by
    have hset : {v : V x | Inner.inner ℝ v v < 1} = Metric.ball 0 1 := by
      ext v
      simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right, real_inner_self_eq_norm_sq]
      constructor <;> intro h <;> nlinarith [norm_nonneg v]
    change Bornology.IsVonNBounded ℝ {v : V x | Inner.inner ℝ v v < 1}
    rw [hset]
    exact NormedSpace.isVonNBounded_ball ℝ (V x) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.RiemannianMetric.ofInnerProductSpace then
    throwError "Refusing to shadow existing declaration Bundle.RiemannianMetric.ofInnerProductSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.RiemannianMetric.ofInnerProductSpace ``Submission.Bundle.RiemannianMetric.ofInnerProductSpace

open _root_.Bundle _root_.Bundle.RiemannianMetric in
@[simp]
theorem ofInnerProductSpace_inner (x : B) (v w : V x) :
    (ofInnerProductSpace V).inner x v w = Inner.inner ℝ v w := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.RiemannianMetric.ofInnerProductSpace_inner then
    throwError "Refusing to shadow existing declaration Bundle.RiemannianMetric.ofInnerProductSpace_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.RiemannianMetric.ofInnerProductSpace_inner ``Submission.Bundle.RiemannianMetric.ofInnerProductSpace_inner

end InnerProduct

section Isometry

open scoped _root_.Bundle _root_.Submission.Bundle

variable {B C : Type*} {V : B → Type*} {W : C → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousConstSMul ℝ (V x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousConstSMul ℝ (W x)]

open _root_.Bundle _root_.Bundle.RiemannianMetric in
def toLinearIsometryEquiv (g : _root_.Bundle.RiemannianMetric W) (h : _root_.Bundle.RiemannianMetric V)
    (f : B → C) (e : ∀ x, V x ≃L[ℝ] W (f x))
    (he : ∀ x v w, g.inner (f x) (e x v) (e x w) = h.inner x v w) :
    letI : _root_.Bundle.RiemannianBundle V := ⟨h⟩
    letI sourceNorm : ∀ x, NormedAddCommGroup (V x) := fun x =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
    letI : ∀ x, SeminormedAddCommGroup (V x) := fun x => (sourceNorm x).toSeminormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℝ (V x) := fun x => Bundle.instInnerProductSpaceReal x
    letI : _root_.Bundle.RiemannianBundle W := ⟨g⟩
    letI targetNorm : ∀ x, NormedAddCommGroup (W x) := fun x =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
    letI : ∀ x, SeminormedAddCommGroup (W x) := fun x => (targetNorm x).toSeminormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℝ (W x) := fun x => Bundle.instInnerProductSpaceReal x
    ∀ x, V x ≃ₗᵢ[ℝ] W (f x) := by
  letI : _root_.Bundle.RiemannianBundle V := ⟨h⟩
  letI sourceNorm : ∀ x, NormedAddCommGroup (V x) := fun x =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
  letI : ∀ x, SeminormedAddCommGroup (V x) := fun x => (sourceNorm x).toSeminormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℝ (V x) := fun x => Bundle.instInnerProductSpaceReal x
  letI : _root_.Bundle.RiemannianBundle W := ⟨g⟩
  letI targetNorm : ∀ x, NormedAddCommGroup (W x) := fun x =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
  letI : ∀ x, SeminormedAddCommGroup (W x) := fun x => (targetNorm x).toSeminormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℝ (W x) := fun x => Bundle.instInnerProductSpaceReal x
  intro x
  exact { (e x).toLinearEquiv with
    norm_map' := (LinearMap.norm_map_iff_inner_map_map (e x).toLinearEquiv.toLinearMap).mpr (he x) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.RiemannianMetric.toLinearIsometryEquiv then
    throwError "Refusing to shadow existing declaration Bundle.RiemannianMetric.toLinearIsometryEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.RiemannianMetric.toLinearIsometryEquiv ``Submission.Bundle.RiemannianMetric.toLinearIsometryEquiv

open _root_.Bundle _root_.Bundle.RiemannianMetric in
theorem toLinearIsometryEquiv_toLinearEquiv
    (g : _root_.Bundle.RiemannianMetric W) (h : _root_.Bundle.RiemannianMetric V)
    (f : B → C) (e : ∀ x, V x ≃L[ℝ] W (f x))
    (he : ∀ x v w, g.inner (f x) (e x v) (e x w) = h.inner x v w) (x : B) :
    letI : _root_.Bundle.RiemannianBundle V := ⟨h⟩
    letI : _root_.Bundle.RiemannianBundle W := ⟨g⟩
    (g.toLinearIsometryEquiv h f e he x).toLinearEquiv = (e x).toLinearEquiv := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.RiemannianMetric.toLinearIsometryEquiv_toLinearEquiv then
    throwError "Refusing to shadow existing declaration Bundle.RiemannianMetric.toLinearIsometryEquiv_toLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.RiemannianMetric.toLinearIsometryEquiv_toLinearEquiv ``Submission.Bundle.RiemannianMetric.toLinearIsometryEquiv_toLinearEquiv

open _root_.Bundle _root_.Bundle.RiemannianMetric in
theorem toLinearIsometryEquiv_apply
    (g : _root_.Bundle.RiemannianMetric W) (h : _root_.Bundle.RiemannianMetric V)
    (f : B → C) (e : ∀ x, V x ≃L[ℝ] W (f x))
    (he : ∀ x v w, g.inner (f x) (e x v) (e x w) = h.inner x v w)
    (x : B) (v : V x) :
    g.toLinearIsometryEquiv h f e he x v = e x v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.RiemannianMetric.toLinearIsometryEquiv_apply then
    throwError "Refusing to shadow existing declaration Bundle.RiemannianMetric.toLinearIsometryEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.RiemannianMetric.toLinearIsometryEquiv_apply ``Submission.Bundle.RiemannianMetric.toLinearIsometryEquiv_apply

open _root_.Bundle _root_.Bundle.RiemannianMetric in
theorem toLinearIsometryEquiv_symm_apply
    (g : _root_.Bundle.RiemannianMetric W) (h : _root_.Bundle.RiemannianMetric V)
    (f : B → C) (e : ∀ x, V x ≃L[ℝ] W (f x))
    (he : ∀ x v w, g.inner (f x) (e x v) (e x w) = h.inner x v w)
    (x : B) (w : W (f x)) :
    letI : _root_.Bundle.RiemannianBundle V := ⟨h⟩
    letI : _root_.Bundle.RiemannianBundle W := ⟨g⟩
    (g.toLinearIsometryEquiv h f e he x).toLinearEquiv.symm w = (e x).symm w := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.RiemannianMetric.toLinearIsometryEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration Bundle.RiemannianMetric.toLinearIsometryEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.RiemannianMetric.toLinearIsometryEquiv_symm_apply ``Submission.Bundle.RiemannianMetric.toLinearIsometryEquiv_symm_apply

end Isometry

end Bundle.RiemannianMetric
