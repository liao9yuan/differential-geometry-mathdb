import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Local
import Submission.DifferentialGeometry.Geometry.Metric.Completeness
import Submission.DifferentialGeometry.Geometry.Metric.Construction.SmoothMetricFromCoefficients
import Submission.DifferentialGeometry.Geometry.Metric.Construction.BumpExtension
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import Submission.DifferentialGeometry.Topology.Manifold.Quotient
import Submission.DifferentialGeometry.Topology.Covering.DeckDiffeomorph
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Homotopy.Lifting

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N]

theorem infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.infty_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.infty_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.infty_ne_zero ``Submission.DifferentialGeometry.infty_ne_zero

noncomputable def localPushInner
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f) (x : M) :
    TangentSpace I (f x) →L[Real] TangentSpace I (f x) →L[Real] Real :=
  let D : TangentSpace I (f x) →L[Real] TangentSpace I x :=
    (hf.mfderivToContinuousLinearEquiv infty_ne_zero x).symm
  (ContinuousLinearMap.precomp Real D).comp ((g.inner x).comp D)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.localPushInner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.localPushInner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.localPushInner ``Submission.DifferentialGeometry.localPushInner

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
theorem localPushInner_apply
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f) (x : M)
    (v w : TangentSpace I (f x)) :
    localPushInner g f hf x v w =
      g.inner x
        ((hf.mfderivToContinuousLinearEquiv infty_ne_zero x).symm v)
        ((hf.mfderivToContinuousLinearEquiv infty_ne_zero x).symm w) := by
  simp only [localPushInner, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.localPushInner_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.localPushInner_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.localPushInner_apply ``Submission.DifferentialGeometry.localPushInner_apply

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
private theorem cast_bilinear_symm
    {x y : N} (hxy : x = y)
    (b : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real)
    (hb : ∀ v w, b v w = b w v) (v w : TangentSpace I y) :
    (hxy ▸ b) v w = (hxy ▸ b) w v := by
  cases hxy
  exact hb v w

run_cmd do
  let target := ``Submission.DifferentialGeometry.cast_bilinear_symm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.cast_bilinear_symm target :: scope.openDecls } }

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
private theorem cast_bilinear_pos
    {x y : N} (hxy : x = y)
    (b : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real)
    (hb : ∀ v, v ≠ 0 → 0 < b v v) (v : TangentSpace I y) (hv : v ≠ 0) :
    0 < (hxy ▸ b) v v := by
  cases hxy
  exact hb v hv

run_cmd do
  let target := ``Submission.DifferentialGeometry.cast_bilinear_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.cast_bilinear_pos target :: scope.openDecls } }

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
private theorem cast_continuousLinearEquiv_apply
    {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module Real V]
    {x y : N} (hxy : x = y)
    (e : V ≃L[Real] TangentSpace I x) (v : V) :
    (hxy ▸ e) v = hxy ▸ e v := by
  cases hxy
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.cast_continuousLinearEquiv_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.cast_continuousLinearEquiv_apply target :: scope.openDecls } }

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
private theorem cast_tangent_eq_of_heq
    {x y : N} (hxy : x = y)
    (v : TangentSpace I x) (w : TangentSpace I y)
    (hvw : HEq v w) : hxy ▸ v = w := by
  cases hxy
  exact eq_of_heq hvw

run_cmd do
  let target := ``Submission.DifferentialGeometry.cast_tangent_eq_of_heq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.cast_tangent_eq_of_heq target :: scope.openDecls } }

def metricFiberCompatible
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f) : Prop :=
  ∀ (x y : M) (hxy : f x = f y),
    hxy ▸ localPushInner g f hf x = localPushInner g f hf y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricFiberCompatible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricFiberCompatible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricFiberCompatible ``Submission.DifferentialGeometry.metricFiberCompatible

theorem pullbackMetric_localPullMetric_of_comp_eq
    [T2Space M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {P : Type*} [TopologicalSpace P] [ChartedSpace G P] [IsManifold J ∞ P]
    (g : SmoothRiemannianMetric J P) (f : M → P)
    (hf : IsLocalDiffeomorph I J ∞ f) (Φ : M ≃ₘ⟮I, I⟯ M)
    (hcomp : f ∘ (Φ : M → M) = f) :
    Diffeomorph.pullbackMetric (localPullMetric g f hf) Φ = localPullMetric g f hf := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner, localPullMetric_inner, localPullMetric_inner]
  have hd := mfderiv_comp x
    (hf.contMDiff.mdifferentiableAt (by simp))
    (Φ.contMDiff.mdifferentiableAt (by simp))
  have hv := ContinuousLinearMap.ext_iff.mp hd v
  have hw := ContinuousLinearMap.ext_iff.mp hd w
  simp only [ContinuousLinearMap.comp_apply] at hv hw
  rw [← hv, ← hw]
  exact congrArg (fun f : M → P =>
    g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w)) hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.pullbackMetric_localPullMetric_of_comp_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.pullbackMetric_localPullMetric_of_comp_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.pullbackMetric_localPullMetric_of_comp_eq ``Submission.DifferentialGeometry.pullbackMetric_localPullMetric_of_comp_eq

private noncomputable def chosenPreimage
    {f : M → N} (hsurj : Function.Surjective f) (y : N) : M :=
  Classical.choose (hsurj y)

run_cmd do
  let target := ``Submission.DifferentialGeometry.chosenPreimage
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.chosenPreimage target :: scope.openDecls } }

omit [TopologicalSpace M] [TopologicalSpace N] in
private theorem chosenPreimage_spec
    {f : M → N} (hsurj : Function.Surjective f) (y : N) :
    f (chosenPreimage hsurj y) = y :=
  Classical.choose_spec (hsurj y)

run_cmd do
  let target := ``Submission.DifferentialGeometry.chosenPreimage_spec
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.chosenPreimage_spec target :: scope.openDecls } }

noncomputable def descendedInner
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f) (y : N) :
    TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real :=
  chosenPreimage_spec hsurj y ▸
    localPushInner g f hf (chosenPreimage hsurj y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.descendedInner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.descendedInner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.descendedInner ``Submission.DifferentialGeometry.descendedInner

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
theorem descendedInner_eq_localPushInner
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f)
    (hcompat : metricFiberCompatible g f hf) (x : M) :
    descendedInner g f hf hsurj (f x) = localPushInner g f hf x := by
  exact hcompat (chosenPreimage hsurj (f x)) x
    (chosenPreimage_spec hsurj (f x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.descendedInner_eq_localPushInner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.descendedInner_eq_localPushInner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.descendedInner_eq_localPushInner ``Submission.DifferentialGeometry.descendedInner_eq_localPushInner

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
theorem descendedInner_eq_localPushInner_of_eq
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f)
    (hcompat : metricFiberCompatible g f hf)
    (x : M) (y : N) (hxy : f x = y) :
    descendedInner g f hf hsurj y = hxy ▸ localPushInner g f hf x := by
  cases hxy
  exact descendedInner_eq_localPushInner g f hf hsurj hcompat x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.descendedInner_eq_localPushInner_of_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.descendedInner_eq_localPushInner_of_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.descendedInner_eq_localPushInner_of_eq ``Submission.DifferentialGeometry.descendedInner_eq_localPushInner_of_eq

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
theorem cast_localPushInner_apply
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (x : M) (y : N) (hxy : f x = y)
    (v w : TangentSpace I y) :
    (hxy ▸ localPushInner g f hf x) v w =
      g.inner x
        ((hxy ▸ hf.mfderivToContinuousLinearEquiv infty_ne_zero x).symm v)
        ((hxy ▸ hf.mfderivToContinuousLinearEquiv infty_ne_zero x).symm w) := by
  cases hxy
  exact localPushInner_apply g f hf x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.cast_localPushInner_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.cast_localPushInner_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.cast_localPushInner_apply ``Submission.DifferentialGeometry.cast_localPushInner_apply

omit [IsManifold I ∞ N] in
theorem localPushInner_eq_of_fiber_preserving_isometry
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (Phi : M ≃ₘ⟮I, I⟯ M)
    (hcomp : f ∘ (Phi : M → M) = f)
    (hmetric : Diffeomorph.pullbackMetric g Phi = g)
    (x : M) :
    congrFun hcomp x ▸ localPushInner g f hf (Phi x) =
      localPushInner g f hf x := by
  let hmap : f (Phi x) = f x := congrFun hcomp x
  let A : TangentSpace I (Phi x) ≃L[Real] TangentSpace I (f x) :=
    hmap ▸ hf.mfderivToContinuousLinearEquiv infty_ne_zero (Phi x)
  let B : TangentSpace I x ≃L[Real] TangentSpace I (f x) :=
    hf.mfderivToContinuousLinearEquiv infty_ne_zero x
  let C : TangentSpace I x ≃L[Real] TangentSpace I (Phi x) :=
    Phi.mfderivToContinuousLinearEquiv infty_ne_zero x
  have hchain := mfderiv_comp x
    (hf.contMDiff.mdifferentiableAt infty_ne_zero)
    (Phi.contMDiff.mdifferentiableAt infty_ne_zero)
  rw [hcomp] at hchain
  have hAC (u : TangentSpace I x) : A (C u) = B u := by
    have hu := ContinuousLinearMap.ext_iff.mp hchain u
    change A (C u) = B u
    dsimp only [A, B, C]
    rw [cast_continuousLinearEquiv_apply]
    change hmap ▸ mfderiv I I f (Phi x) (mfderiv I I Phi x u) =
      mfderiv I I f x u
    exact cast_tangent_eq_of_heq hmap _ _ (heq_of_eq hu.symm)
  have hinv (v : TangentSpace I (f x)) : A.symm v = C (B.symm v) := by
    apply A.injective
    rw [A.apply_symm_apply, hAC, B.apply_symm_apply]
  have hisometry (u z : TangentSpace I x) :
      g.inner (Phi x) (C u) (C z) = g.inner x u z := by
    have h := Diffeomorph.pullbackMetric_inner g Phi x u z
    rw [hmetric] at h
    change g.inner (Phi x) (mfderiv I I Phi x u)
      (mfderiv I I Phi x z) = g.inner x u z
    exact h.symm
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [cast_localPushInner_apply, localPushInner_apply]
  change g.inner (Phi x) (A.symm v) (A.symm w) =
    g.inner x (B.symm v) (B.symm w)
  rw [hinv, hinv]
  exact hisometry (B.symm v) (B.symm w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.localPushInner_eq_of_fiber_preserving_isometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.localPushInner_eq_of_fiber_preserving_isometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.localPushInner_eq_of_fiber_preserving_isometry ``Submission.DifferentialGeometry.localPushInner_eq_of_fiber_preserving_isometry

omit [IsManifold I ∞ N] in
theorem metricFiberCompatible_of_coveringDeckGroup_invariant
    [T2Space M] [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f) (hcover : IsCoveringMap f)
    (hinvariant : ∀ γ : coveringDeckGroup f,
      Diffeomorph.pullbackMetric g (coveringDeckGroupDiffeomorph hf γ) = g) :
    metricFiberCompatible g f hf := by
  intro x y hxy
  obtain ⟨γ, hγ⟩ := (coveringDeckGroup_apply_eq_iff hcover).mp hxy
  subst x
  let Φ := coveringDeckGroupDiffeomorph hf γ
  have hcomp : f ∘ (Φ : M → M) = f := by
    funext z
    exact coveringDeckGroup_map γ z
  exact localPushInner_eq_of_fiber_preserving_isometry g f hf Φ hcomp (hinvariant γ) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricFiberCompatible_of_coveringDeckGroup_invariant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricFiberCompatible_of_coveringDeckGroup_invariant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricFiberCompatible_of_coveringDeckGroup_invariant ``Submission.DifferentialGeometry.metricFiberCompatible_of_coveringDeckGroup_invariant

omit [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] in
theorem metricFiberCompatible_quotientMk_of_invariant
    {G : Type*} [Group G] [MulAction G M]
    [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M]
    [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M]
    [ContMDiffConstSMul I ∞ G M]
    (g : SmoothRiemannianMetric I M)
    (hinvariant : ∀ gamma : G,
      Diffeomorph.pullbackMetric g
        (MulAction.smulDiffeomorph (n := ∞) I gamma) = g) :
    metricFiberCompatible g
      (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M)
      (MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
        (n := ∞) I) := by
  let q : M → MulAction.orbitRel.Quotient G M := Quotient.mk''
  let hq : IsLocalDiffeomorph I I ∞ q :=
    MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul I
  change metricFiberCompatible g q hq
  intro x y hxy
  obtain ⟨gamma, hgamma⟩ :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.apply_eq_iff_mem_orbit.mp
      hxy
  subst x
  let Phi : M ≃ₘ⟮I, I⟯ M :=
    MulAction.smulDiffeomorph (n := ∞) I gamma
  have hcomp : q ∘ (Phi : M → M) = q := by
    funext z
    exact MulAction.orbitRel.Quotient.quotient_smul_eq
  exact localPushInner_eq_of_fiber_preserving_isometry
    g q hq Phi hcomp (hinvariant gamma) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricFiberCompatible_quotientMk_of_invariant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricFiberCompatible_quotientMk_of_invariant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricFiberCompatible_quotientMk_of_invariant ``Submission.DifferentialGeometry.metricFiberCompatible_quotientMk_of_invariant

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
private theorem descendedInner_symm
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f) (y : N)
    (v w : TangentSpace I y) :
    descendedInner g f hf hsurj y v w =
      descendedInner g f hf hsurj y w v := by
  let x := chosenPreimage hsurj y
  let hxy : f x = y := chosenPreimage_spec hsurj y
  change (hxy ▸ localPushInner g f hf x) v w =
    (hxy ▸ localPushInner g f hf x) w v
  apply cast_bilinear_symm hxy
  intro a b
  rw [localPushInner_apply, localPushInner_apply]
  exact g.symm x _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.descendedInner_symm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.descendedInner_symm target :: scope.openDecls } }

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
private theorem descendedInner_pos
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f) (y : N)
    (v : TangentSpace I y) (hv : v ≠ 0) :
    0 < descendedInner g f hf hsurj y v v := by
  let x := chosenPreimage hsurj y
  let hxy : f x = y := chosenPreimage_spec hsurj y
  change 0 < (hxy ▸ localPushInner g f hf x) v v
  apply cast_bilinear_pos hxy _ _ v hv
  intro a ha
  rw [localPushInner_apply]
  apply g.pos
  exact (hf.mfderivToContinuousLinearEquiv infty_ne_zero x).symm.map_ne_zero_iff.mpr ha

run_cmd do
  let target := ``Submission.DifferentialGeometry.descendedInner_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.descendedInner_pos target :: scope.openDecls } }

noncomputable def tangentOpenEquiv
    (U : _root_.TopologicalSpace.Opens N) (x : U) :
    TangentSpace I (x : N) ≃L[Real] TangentSpace I x :=
  (tangentSpaceModelContinuousLinearEquiv (I := I) (x : N)).trans
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tangentOpenEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tangentOpenEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tangentOpenEquiv ``Submission.DifferentialGeometry.tangentOpenEquiv

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
theorem mfderiv_subtype_val_tangentOpenEquiv
    (U : _root_.TopologicalSpace.Opens N) (x : U) (v : TangentSpace I (x : N)) :
    mfderiv I I (Subtype.val : U → N) x (tangentOpenEquiv U x v) = v := by
  rw [mfderiv_subtype_val_apply]
  apply (tangentSpaceModelContinuousLinearEquiv (I := I) (x : N)).injective
  change tangentSpaceModelContinuousLinearEquiv (I := I) (x : N)
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
        (tangentSpaceModelContinuousLinearEquiv (I := I) (x : N) v)) =
    tangentSpaceModelContinuousLinearEquiv (I := I) (x : N) v
  rw [tangentSpaceModelContinuousLinearEquiv_symm_apply]
  exact tangentSpaceModelContinuousLinearEquiv_apply (I := I) (x : N) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.mfderiv_subtype_val_tangentOpenEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.mfderiv_subtype_val_tangentOpenEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.mfderiv_subtype_val_tangentOpenEquiv ``Submission.DifferentialGeometry.mfderiv_subtype_val_tangentOpenEquiv

structure LocalSection
    (I : ModelWithCorners Real E H)
    (f : M → N) (y : N) where
  U : _root_.TopologicalSpace.Opens N
  V : _root_.TopologicalSpace.Opens M
  s : U ≃ₘ⟮I, I⟯ V
  mem : y ∈ U
  isSec : ∀ z : U, f ((s z : V) : M) = (z : N)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalSection ``Submission.DifferentialGeometry.LocalSection

noncomputable def LocalSection.ofLocal
    (f : M → N) (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f) (y : N) : LocalSection I f y := by
  let x := chosenPreimage hsurj y
  have hxy : f x = y := chosenPreimage_spec hsurj y
  let Phi := Classical.choose (hf x)
  have hx : x ∈ Phi.source := (Classical.choose_spec (hf x)).1
  have hPhi : Set.EqOn f Phi Phi.source := (Classical.choose_spec (hf x)).2
  let V : _root_.TopologicalSpace.Opens M := ⟨Phi.source, Phi.open_source⟩
  let U : _root_.TopologicalSpace.Opens N :=
    ⟨(Phi : M → N) '' (V : Set M), image_opens_isOpen Phi Set.Subset.rfl⟩
  let e : V ≃ₘ⟮I, I⟯ U :=
    DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Phi Set.Subset.rfl
  refine
    { U := U
      V := V
      s := e.symm
      mem := ?_
      isSec := ?_ }
  · exact ⟨x, hx, (hPhi hx).symm.trans hxy⟩
  · intro z
    have hz : (((e.symm z : V) : M)) ∈ Phi.source := (e.symm z).2
    calc
      f ((e.symm z : V) : M) = Phi ((e.symm z : V) : M) := hPhi hz
      _ = (z : N) := congrArg Subtype.val (e.apply_symm_apply z)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.LocalSection
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalSection.ofLocal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalSection.ofLocal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalSection.ofLocal ``Submission.DifferentialGeometry.LocalSection.ofLocal

namespace LocalSection

variable {f : M → N} {y : N} (S : LocalSection I f y)

def toSource : S.U → M := fun z => ((S.s z : S.V) : M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalSection.toSource then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalSection.toSource"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalSection.toSource ``Submission.DifferentialGeometry.LocalSection.toSource

omit [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I ∞ N] in
theorem toSource_contMDiff : ContMDiff I I ∞ S.toSource := by
  exact (contMDiff_subtype_val (I := I)).comp S.s.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalSection.toSource_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalSection.toSource_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalSection.toSource_contMDiff ``Submission.DifferentialGeometry.LocalSection.toSource_contMDiff

omit [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I ∞ N] in
theorem mfderiv_toSource_apply
    (z : S.U) (v : TangentSpace I z) :
    mfderiv I I S.toSource z v = mfderiv I I S.s z v := by
  have hval : MDifferentiableAt I I
      (Subtype.val : S.V → M) (S.s z) :=
    (contMDiff_subtype_val (I := I)).mdifferentiableAt infty_ne_zero
  have hs : MDifferentiableAt I I (S.s : S.U → S.V) z :=
    S.s.contMDiff.mdifferentiableAt infty_ne_zero
  rw [show S.toSource = (Subtype.val : S.V → M) ∘ (S.s : S.U → S.V) from rfl,
    mfderiv_comp_apply z hval hs v, mfderiv_subtype_val_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalSection.mfderiv_toSource_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalSection.mfderiv_toSource_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalSection.mfderiv_toSource_apply ``Submission.DifferentialGeometry.LocalSection.mfderiv_toSource_apply

omit [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I ∞ N] in
theorem dproj_sec
    (hf : IsLocalDiffeomorph I I ∞ f) (z : S.U) :
    (mfderiv I I f (S.toSource z)).comp (mfderiv I I S.toSource z) =
      mfderiv I I (Subtype.val : S.U → N) z := by
  have hcomp := mfderiv_comp z
    (hf.contMDiff.mdifferentiableAt infty_ne_zero)
    (S.toSource_contMDiff.mdifferentiableAt infty_ne_zero)
  have heq : f ∘ S.toSource = (Subtype.val : S.U → N) := by
    funext z'
    exact S.isSec z'
  rw [heq] at hcomp
  exact hcomp.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalSection.dproj_sec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalSection.dproj_sec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalSection.dproj_sec ``Submission.DifferentialGeometry.LocalSection.dproj_sec

omit [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I ∞ N] in
theorem inverse_mfderiv_eq
    (hf : IsLocalDiffeomorph I I ∞ f) (z : S.U)
    (hsec : f (S.toSource z) = (z : N))
    (v : TangentSpace I (z : N)) :
    (hsec ▸ hf.mfderivToContinuousLinearEquiv
        infty_ne_zero (S.toSource z)).symm v =
      mfderiv I I S.toSource z (tangentOpenEquiv S.U z v) := by
  have hright := ContinuousLinearMap.ext_iff.mp (S.dproj_sec hf z)
    (tangentOpenEquiv S.U z v)
  simp only [ContinuousLinearMap.comp_apply] at hright
  rw [hsec] at hright
  rw [mfderiv_subtype_val_tangentOpenEquiv] at hright
  let D : TangentSpace I (S.toSource z) ≃L[Real] TangentSpace I (z : N) :=
    hsec ▸ hf.mfderivToContinuousLinearEquiv infty_ne_zero (S.toSource z)
  change D.symm v = mfderiv I I S.toSource z (tangentOpenEquiv S.U z v)
  apply D.symm_apply_eq.mpr
  rw [show D (mfderiv I I S.toSource z (tangentOpenEquiv S.U z v)) =
      hsec ▸ (hf.mfderivToContinuousLinearEquiv
        infty_ne_zero (S.toSource z))
          (mfderiv I I S.toSource z (tangentOpenEquiv S.U z v)) by
        exact cast_continuousLinearEquiv_apply hsec _ _]
  have heq :
      (hf.mfderivToContinuousLinearEquiv infty_ne_zero (S.toSource z))
          (mfderiv I I S.toSource z (tangentOpenEquiv S.U z v)) =
        mfderiv I I f (S.toSource z)
          (mfderiv I I S.toSource z (tangentOpenEquiv S.U z v)) := by
    have hcoe := hf.mfderivToContinuousLinearEquiv_coe
      infty_ne_zero (S.toSource z)
    exact congrArg
      (fun L : TangentSpace I (S.toSource z) →L[Real]
          TangentSpace I (f (S.toSource z)) =>
        L (mfderiv I I S.toSource z (tangentOpenEquiv S.U z v))) hcoe
  rw [heq]
  exact (cast_tangent_eq_of_heq hsec _ _ (heq_of_eq hright)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalSection.inverse_mfderiv_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalSection.inverse_mfderiv_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalSection.inverse_mfderiv_eq ``Submission.DifferentialGeometry.LocalSection.inverse_mfderiv_eq

theorem pullback_inner_eval
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (z : S.U)
    (v w : TangentSpace I z) :
    (Diffeomorph.pullbackMetricCross
        (g.restrictOpen (I := I) S.V) S.s).inner z v w =
      g.inner (S.toSource z)
        (mfderiv I I S.toSource z v)
        (mfderiv I I S.toSource z w) := by
  rw [Diffeomorph.pullbackMetricCross_inner,
    SmoothRiemannianMetric.restrictOpen_inner,
    S.mfderiv_toSource_apply, S.mfderiv_toSource_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalSection.pullback_inner_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalSection.pullback_inner_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalSection.pullback_inner_eval ``Submission.DifferentialGeometry.LocalSection.pullback_inner_eval

theorem descendedInner_locally_eq
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f)
    (hcompat : metricFiberCompatible g f hf)
    (z : S.U) (v w : TangentSpace I (z : N)) :
    descendedInner g f hf hsurj (z : N) v w =
      (Diffeomorph.pullbackMetricCross
        (g.restrictOpen (I := I) S.V) S.s).inner z
          (tangentOpenEquiv S.U z v) (tangentOpenEquiv S.U z w) := by
  have hsec := S.isSec z
  change f (S.toSource z) = (z : N) at hsec
  rw [show descendedInner g f hf hsurj (z : N) =
      hsec ▸ localPushInner g f hf (S.toSource z) from
        descendedInner_eq_localPushInner_of_eq
          g f hf hsurj hcompat (S.toSource z) (z : N) hsec]
  rw [cast_localPushInner_apply, S.pullback_inner_eval]
  rw [S.inverse_mfderiv_eq hf z hsec,
    S.inverse_mfderiv_eq hf z hsec]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalSection.descendedInner_locally_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalSection.descendedInner_locally_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalSection.descendedInner_locally_eq ``Submission.DifferentialGeometry.LocalSection.descendedInner_locally_eq

end LocalSection

private theorem descendedInner_coeff
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f)
    (hcompat : metricFiberCompatible g f hf)
    (x₀ : N) (i j : Fin (Module.finrank Real E)) :
    ContMDiffOn I (modelWithCornersSelf Real Real) ∞
      (fun x => descendedInner g f hf hsurj x
        (Geometry.frameVec (I := I) x₀ i x)
        (Geometry.frameVec (I := I) x₀ j x))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet := by
  intro y hy
  let S := LocalSection.ofLocal f hf hsurj y
  apply ContMDiffAt.contMDiffWithinAt
  refine (contMDiffAt_subtype_iff (U := S.U)
    (x := ⟨y, S.mem⟩)).mp ?_
  have hfun :
      (fun z : S.U => descendedInner g f hf hsurj (z : N)
        (Geometry.frameVec (I := I) x₀ i (z : N))
        (Geometry.frameVec (I := I) x₀ j (z : N))) =
      fun z : S.U =>
        (Diffeomorph.pullbackMetricCross
          (g.restrictOpen (I := I) S.V) S.s).inner z
          (tangentOpenEquiv S.U z
            (Geometry.frameVec (I := I) x₀ i (z : N)))
          (tangentOpenEquiv S.U z
            (Geometry.frameVec (I := I) x₀ j (z : N))) := by
    funext z
    exact S.descendedInner_locally_eq g hf hsurj hcompat z _ _
  rw [hfun]
  exact CovariantDerivative.metric_inner_contMDiffAt
    (Diffeomorph.pullbackMetricCross
      (g.restrictOpen (I := I) S.V) S.s)
    (Geometry.frameVec_sub_cmdiffAt (I := I) S.U x₀ i hy S.mem)
    (Geometry.frameVec_sub_cmdiffAt (I := I) S.U x₀ j hy S.mem)
    (le_refl _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.descendedInner_coeff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.descendedInner_coeff target :: scope.openDecls } }

noncomputable def descendedMetric
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f)
    (hcompat : metricFiberCompatible g f hf) :
    SmoothRiemannianMetric I N :=
  (Geometry.smoothMetric_of_localCoeff
    (descendedInner g f hf hsurj)
    (descendedInner_symm g f hf hsurj)
    (descendedInner_pos g f hf hsurj)
    (descendedInner_coeff g f hf hsurj hcompat)).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.descendedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.descendedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.descendedMetric ``Submission.DifferentialGeometry.descendedMetric

theorem descendedMetric_inner
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f)
    (hcompat : metricFiberCompatible g f hf)
    (y : N) (v w : TangentSpace I y) :
    (descendedMetric g f hf hsurj hcompat).inner y v w =
      descendedInner g f hf hsurj y v w :=
  (Geometry.smoothMetric_of_localCoeff
    (descendedInner g f hf hsurj)
    (descendedInner_symm g f hf hsurj)
    (descendedInner_pos g f hf hsurj)
    (descendedInner_coeff g f hf hsurj hcompat)).choose_spec y v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.descendedMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.descendedMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.descendedMetric_inner ``Submission.DifferentialGeometry.descendedMetric_inner

theorem localPullMetric_descendedMetric
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f)
    (hcompat : metricFiberCompatible g f hf) :
    localPullMetric (descendedMetric g f hf hsurj hcompat) f hf = g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, descendedMetric_inner,
    descendedInner_eq_localPushInner g f hf hsurj hcompat,
    localPushInner_apply]
  let D := hf.mfderivToContinuousLinearEquiv infty_ne_zero x
  change g.inner x (D.symm (mfderiv I I f x v))
      (D.symm (mfderiv I I f x w)) = g.inner x v w
  have hcoe : (D : TangentSpace I x →L[Real] TangentSpace I (f x)) =
      mfderiv I I f x := hf.mfderivToContinuousLinearEquiv_coe infty_ne_zero x
  rw [← hcoe]
  have hv : D.symm ((D : TangentSpace I x →L[Real]
      TangentSpace I (f x)) v) = v := D.symm_apply_apply v
  have hw : D.symm ((D : TangentSpace I x →L[Real]
      TangentSpace I (f x)) w) = w := D.symm_apply_apply w
  rw [hv, hw]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.localPullMetric_descendedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.localPullMetric_descendedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.localPullMetric_descendedMetric ``Submission.DifferentialGeometry.localPullMetric_descendedMetric

theorem localPullMetric_injective_of_surjective
    [T2Space M]
    (f : M → N) (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f)
    {g h : SmoothRiemannianMetric I N}
    (heq : localPullMetric g f hf = localPullMetric h f hf) : g = h := by
  apply SmoothRiemannianMetric.ext_inner
  intro y v w
  obtain ⟨x, rfl⟩ := hsurj y
  let D := hf.mfderivToContinuousLinearEquiv infty_ne_zero x
  have hinner := congrArg
    (fun k : SmoothRiemannianMetric I M =>
      k.inner x (D.symm v) (D.symm w)) heq
  rw [localPullMetric_inner, localPullMetric_inner] at hinner
  have hcoe : (D : TangentSpace I x →L[Real] TangentSpace I (f x)) =
      mfderiv I I f x := hf.mfderivToContinuousLinearEquiv_coe infty_ne_zero x
  rw [← hcoe] at hinner
  have hv : (D : TangentSpace I x →L[Real]
      TangentSpace I (f x)) (D.symm v) = v := D.apply_symm_apply v
  have hw : (D : TangentSpace I x →L[Real]
      TangentSpace I (f x)) (D.symm w) = w := D.apply_symm_apply w
  rw [hv, hw] at hinner
  exact hinner

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.localPullMetric_injective_of_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.localPullMetric_injective_of_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.localPullMetric_injective_of_surjective ``Submission.DifferentialGeometry.localPullMetric_injective_of_surjective

theorem exists_unique_metric_of_surjective_localDiffeomorph
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f)
    (hcompat : metricFiberCompatible g f hf) :
    ∃! h : SmoothRiemannianMetric I N, localPullMetric h f hf = g := by
  refine ⟨descendedMetric g f hf hsurj hcompat,
    localPullMetric_descendedMetric g f hf hsurj hcompat, ?_⟩
  intro h hh
  exact localPullMetric_injective_of_surjective f hf hsurj
    (hh.trans (localPullMetric_descendedMetric g f hf hsurj hcompat).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exists_unique_metric_of_surjective_localDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exists_unique_metric_of_surjective_localDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exists_unique_metric_of_surjective_localDiffeomorph ``Submission.DifferentialGeometry.exists_unique_metric_of_surjective_localDiffeomorph

section CoveringCompleteness

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
  [IsManifold J ∞ P]

private theorem exists_lift_edist_lt
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric J P)
    {f : M → P}
    (hf : IsLocalDiffeomorph I J ∞ f)
    (hcover : IsCoveringMap f)
    (hpull : localPullMetric h f hf = g)
    {r : ENNReal} {x : M} {y z : P}
    (hxy : f x = y)
    (hdist : riemannianEDistOf (I := J) h y z < r) :
    ∃ x' : M, f x' = z ∧
      riemannianEDistOf (I := I) g x x' < r := by
  rw [edistOf_iInf] at hdist
  simp only [iInf_lt_iff, exists_prop] at hdist
  obtain ⟨gamma, hgamma, hgammaLen⟩ := hdist
  let gammaLiftC := hcover.liftPath gamma.toContinuousMap x
    (gamma.source.trans hxy.symm)
  let x' : M := gammaLiftC 1
  let gammaLift : Path x x' :=
    { toContinuousMap := gammaLiftC
      source' := hcover.liftPath_zero gamma.toContinuousMap x
        (gamma.source.trans hxy.symm)
      target' := rfl }
  have hproj : f ∘ (gammaLift : unitInterval → M) = gamma :=
    hcover.liftPath_lifts gamma.toContinuousMap x
      (gamma.source.trans hxy.symm)
  have hgammaLift : CMDiff 1 gammaLift := by
    refine hf.contMDiff_of_continuous_of_comp gammaLift.continuous ?_ (by norm_num)
    rw [hproj]
    exact hgamma
  have hx' : f x' = z := by
    exact (congrFun hproj 1).trans gamma.target
  refine ⟨x', hx', lt_of_le_of_lt ?_ hgammaLen⟩
  rw [edistOf_iInf]
  refine iInf_le_of_le gammaLift (iInf_le_of_le hgammaLift ?_)
  apply le_of_eq
  rw [← hproj]
  apply MeasureTheory.lintegral_congr
  intro t
  have hder := mfderiv_comp_apply t
    (hf.contMDiff.contMDiffAt.mdifferentiableAt (by norm_num))
    (hgammaLift.contMDiffAt.mdifferentiableAt (by norm_num)) 1
  congr 2
  calc
    g.inner (gammaLift t) (mfderiv% gammaLift t 1)
        (mfderiv% gammaLift t 1) =
        (localPullMetric h f hf).inner (gammaLift t)
          (mfderiv% gammaLift t 1) (mfderiv% gammaLift t 1) := by
      rw [hpull]
    _ = h.inner (f (gammaLift t))
          (mfderiv I J f (gammaLift t) (mfderiv% gammaLift t 1))
          (mfderiv I J f (gammaLift t) (mfderiv% gammaLift t 1)) :=
      localPullMetric_inner h f hf _ _ _
    _ = h.inner ((f ∘ (gammaLift : unitInterval → M)) t)
          (mfderiv% (f ∘ (gammaLift : unitInterval → M)) t 1)
          (mfderiv% (f ∘ (gammaLift : unitInterval → M)) t 1) := by
      simp only [Function.comp_apply]
      rw [hder]

run_cmd do
  let target := ``Submission.DifferentialGeometry.exists_lift_edist_lt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.exists_lift_edist_lt target :: scope.openDecls } }

theorem le_edistOf_of_coveringMap_localPullMetric
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric J P)
    {f : M → P}
    (hf : IsLocalDiffeomorph I J ∞ f)
    (hcover : IsCoveringMap f)
    (hpull : localPullMetric h f hf = g)
    {r : ENNReal} (x : M) (z : P)
    (hlower : ∀ x' : M, f x' = z → r ≤ riemannianEDistOf (I := I) g x x') :
    r ≤ riemannianEDistOf (I := J) h (f x) z := by
  by_contra! hlt
  obtain ⟨x', hx', hshort⟩ := exists_lift_edist_lt g h hf hcover hpull rfl hlt
  exact (not_lt_of_ge (hlower x' hx')) hshort

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.le_edistOf_of_coveringMap_localPullMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.le_edistOf_of_coveringMap_localPullMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.le_edistOf_of_coveringMap_localPullMetric ``Submission.DifferentialGeometry.le_edistOf_of_coveringMap_localPullMetric

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem RiemannianMetricComplete.of_coveringMap_localPullMetric
    [FiniteDimensional Real F]
    [T2Space M] [SigmaCompactSpace M]
    [T2Space P] [SigmaCompactSpace P]
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric J P)
    {f : M → P}
    (hf : IsLocalDiffeomorph I J ∞ f)
    (hcover : IsCoveringMap f)
    (hsurj : Function.Surjective f)
    (hpull : localPullMetric h f hf = g)
    (hg : RiemannianMetricComplete (I := I) g) :
    RiemannianMetricComplete (I := J) h := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let _ : CompleteSpace F := FiniteDimensional.complete Real F
  let : IsManifold J 1 P :=
    IsManifold.of_le (I := J) (M := P) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : TopologicalSpace.MetrizableSpace P := Manifold.metrizableSpace J P
  let : T3Space P := inferInstance
  refine ⟨?_⟩
  let : _root_.Bundle.RiemannianBundle (fun y : P => TangentSpace J y) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F
      (fun y : P => TangentSpace J y) :=
    ⟨h.inner, h.contMDiff.continuous, by intro y v w; rfl⟩
  let : EMetricSpace P := EMetricSpace.ofRiemannianMetric J P
  refine EMetric.complete_of_cauchySeq_tendsto (α := P) fun s hs => ?_
  let d : ℕ → NNReal := fun n => (2⁻¹ : NNReal) ^ n
  have hdPos (n : ℕ) : 0 < (d n : ENNReal) := by
    positivity
  obtain ⟨phi, hphiMono, hphiStep⟩ :=
    hs.subseq_mem (fun n => edist_mem_uniformity (hdPos n))
  have htargetStep (n : ℕ) :
      riemannianEDistOf (I := J) h (s (phi n)) (s (phi (n + 1))) <
        (d n : ENNReal) := by
    change _root_.EDist.edist (s (phi n)) (s (phi (n + 1))) < (d n : ENNReal)
    rw [_root_.PseudoEMetricSpace.edist_comm]
    exact hphiStep n
  let x0 : {x : M // f x = s (phi 0)} :=
    ⟨Classical.choose (hsurj (s (phi 0))),
      Classical.choose_spec (hsurj (s (phi 0)))⟩
  have hnext (n : ℕ) (x : {x : M // f x = s (phi n)}) :
      ∃ y : M, f y = s (phi (n + 1)) ∧
        riemannianEDistOf (I := I) g x y < (d n : ENNReal) :=
    exists_lift_edist_lt g h hf hcover hpull x.property (htargetStep n)
  let next (n : ℕ) (x : {x : M // f x = s (phi n)}) :
      {y : M // f y = s (phi (n + 1)) ∧
        riemannianEDistOf (I := I) g x y < (d n : ENNReal)} :=
    ⟨Classical.choose (hnext n x), Classical.choose_spec (hnext n x)⟩
  let x : (n : ℕ) → {x : M // f x = s (phi n)} := fun n =>
    Nat.rec (motive := fun k => {x : M // f x = s (phi k)}) x0
      (fun k xk => ⟨(next k xk).1, (next k xk).2.1⟩) n
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : _root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun y : M => TangentSpace I y) :=
    ⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hg.complete
  have hxStep (n : ℕ) : _root_.EDist.edist (x n : M) (x (n + 1) : M) ≤ (d n : ENNReal) := by
    change riemannianEDistOf (I := I) g (x n : M) (x (n + 1) : M) ≤
      (d n : ENNReal)
    change riemannianEDistOf (I := I) g (x n : M) (next n (x n)).1 ≤
      (d n : ENNReal)
    exact (next n (x n)).2.2.le
  have hdSummable : Summable d := by
    simpa only [d] using
      (NNReal.summable_geometric (r := (2⁻¹ : NNReal)) (by norm_num))
  have hxCauchy : CauchySeq (fun n => (x n : M)) :=
    cauchySeq_of_edist_le_of_summable d hxStep hdSummable
  obtain ⟨xLimit, hxLimit⟩ := cauchySeq_tendsto_of_complete hxCauchy
  refine ⟨f xLimit, tendsto_nhds_of_cauchySeq_of_subseq hs
    hphiMono.tendsto_atTop ?_⟩
  have hprojected :
      Filter.Tendsto (fun n => f (x n : M)) Filter.atTop (𝓝 (f xLimit)) :=
    (hf.contMDiff.continuous.tendsto xLimit).comp hxLimit
  have heq : (fun n => f (x n : M)) = s ∘ phi := by
    funext n
    exact (x n).property
  rw [← heq]
  exact hprojected

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.RiemannianMetricComplete.of_coveringMap_localPullMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.RiemannianMetricComplete.of_coveringMap_localPullMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.RiemannianMetricComplete.of_coveringMap_localPullMetric ``Submission.DifferentialGeometry.RiemannianMetricComplete.of_coveringMap_localPullMetric

end CoveringCompleteness

end DifferentialGeometry
