import Submission.DifferentialGeometry.Geometry.Connection.ConnectionForm
import Mathlib.Analysis.Calculus.Deriv.Mul

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Filter _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace CovariantDerivative
open _root_.CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

open _root_.CovariantDerivative in
private theorem derivWithin_comp_eq_mvfderiv
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {γ : ℝ → M} {f : M → G} {J : Set ℝ} {t : ℝ}
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ J t)
    (hf : MDifferentiableAt I 𝓘(ℝ, G) f (γ t))
    (hJ : UniqueDiffWithinAt ℝ J t) :
    derivWithin (fun s => f (γ s)) J t =
      mvfderiv I f (γ t)
        (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1)) := by
  have h := congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ]
      TangentSpace 𝓘(ℝ, G) (f (γ t)) =>
        NormedSpace.fromTangentSpace (f (γ t))
          (L ((NormedSpace.fromTangentSpace t).symm 1)))
    (mfderiv_comp_mfderivWithin t hf hγ hJ.uniqueMDiffWithinAt)
  rw [mfderivWithin_eq_fderivWithin] at h
  exact h

run_cmd do
  let target := ``Submission.CovariantDerivative.derivWithin_comp_eq_mvfderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `CovariantDerivative.derivWithin_comp_eq_mvfderiv target :: scope.openDecls } }

open _root_.CovariantDerivative in
private theorem mfderivWithin_curve_eq_zero_of_not_uniqueDiffWithinAt
    (γ : ℝ → M) {J : Set ℝ} {t : ℝ} (hJ : ¬UniqueDiffWithinAt ℝ J t) :
    mfderivWithin 𝓘(ℝ, ℝ) I γ J t = 0 := by
  by_cases hd : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ J t
  · exact hd.mfderivWithin.trans
      (fderivWithin_zero_of_not_uniqueDiffWithinAt
        (f := writtenInExtChartAt 𝓘(ℝ, ℝ) I t γ)
        (show ¬UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t from
          fun h => hJ h.uniqueDiffWithinAt))
  · exact mfderivWithin_zero_of_not_mdifferentiableWithinAt hd

run_cmd do
  let target := ``Submission.CovariantDerivative.mfderivWithin_curve_eq_zero_of_not_uniqueDiffWithinAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `CovariantDerivative.mfderivWithin_curve_eq_zero_of_not_uniqueDiffWithinAt target :: scope.openDecls } }

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [FiniteDimensional ℝ F] [ContMDiffVectorBundle 1 F V I]

open _root_.CovariantDerivative in
def derivAlongWithin (cov : CovariantDerivative I F V)
    (γ : ℝ → M) (Z : ∀ t : ℝ, V (γ t)) (J : Set ℝ) (t : ℝ) : V (γ t) :=
  let e := _root_.FiberBundle.trivializationAt F V (γ t)
  e.symmL ℝ (γ t)
    (derivWithin (fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)) J t +
      cov.connectionForm e (γ t)
      (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))
        (e.continuousLinearMapAt ℝ (γ t) (Z t)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.derivAlongWithin then
    throwError "Refusing to shadow existing declaration CovariantDerivative.derivAlongWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.derivAlongWithin ``Submission.CovariantDerivative.derivAlongWithin

open _root_.CovariantDerivative in
theorem derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt
    (cov : CovariantDerivative I F V)
    (γ : ℝ → M) (Z : ∀ t : ℝ, V (γ t)) {J : Set ℝ} {t : ℝ}
    (hJ : ¬UniqueDiffWithinAt ℝ J t) :
    cov.derivAlongWithin γ Z J t = 0 := by
  have hγ := mfderivWithin_curve_eq_zero_of_not_uniqueDiffWithinAt (I := I) γ hJ
  simp only [derivAlongWithin, derivWithin_zero_of_not_uniqueDiffWithinAt hJ, hγ,
    zero_apply, map_zero, zero_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt then
    throwError "Refusing to shadow existing declaration CovariantDerivative.derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt ``Submission.CovariantDerivative.derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiniteDimensional ℝ F] in
open _root_.CovariantDerivative in
private theorem differentiableWithinAt_trivialization_coord_along
    (e : _root_.Bundle.Trivialization F (TotalSpace.proj : _root_.Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)}
    {J : Set ℝ} {t : ℝ} (he : γ t ∈ e.baseSet)
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z s⟩ : _root_.Bundle.TotalSpace F V)) J t) :
    DifferentiableWithinAt ℝ (fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)) J t := by
  have h := (e.mdifferentiableWithinAt_totalSpace_iff I
    (fun s => (⟨γ s, Z s⟩ : _root_.Bundle.TotalSpace F V)) (e.mem_source.mpr he)).mp hZ
  apply mdifferentiableWithinAt_iff_differentiableWithinAt.mp
  apply h.2.congr_of_eventuallyEq
  · filter_upwards [h.1.continuousWithinAt.preimage_mem_nhdsWithin
      (e.open_baseSet.mem_nhds he)] with s hs
    exact e.continuousLinearMapAt_apply_of_mem ℝ hs (Z s)
  · exact e.continuousLinearMapAt_apply_of_mem ℝ he (Z t)

run_cmd do
  let target := ``Submission.CovariantDerivative.differentiableWithinAt_trivialization_coord_along
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `CovariantDerivative.differentiableWithinAt_trivialization_coord_along target :: scope.openDecls } }

open _root_.CovariantDerivative in
private theorem derivAlongWithin_coordChange
    (cov : CovariantDerivative I F V)
    (e e' : _root_.Bundle.Trivialization F (TotalSpace.proj : _root_.Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)} {J : Set ℝ} {t : ℝ}
    (he : γ t ∈ e.baseSet) (he' : γ t ∈ e'.baseSet)
    (hJ : UniqueDiffWithinAt ℝ J t)
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z s⟩ : _root_.Bundle.TotalSpace F V)) J t) :
    e'.coordChangeL ℝ e (γ t)
        (derivWithin (fun s => e'.continuousLinearMapAt ℝ (γ s) (Z s)) J t +
          cov.connectionForm e' (γ t)
            (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))
            (e'.continuousLinearMapAt ℝ (γ t) (Z t))) =
      derivWithin (fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)) J t +
        cov.connectionForm e (γ t)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))
          (e.continuousLinearMapAt ℝ (γ t) (Z t)) := by
  let R : M → F →L[ℝ] F := fun x => e'.coordChangeL ℝ e x
  let z : ℝ → F := fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)
  let z' : ℝ → F := fun s => e'.continuousLinearMapAt ℝ (γ s) (Z s)
  let X := mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1)
  have hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ J t :=
    ((e.mdifferentiableWithinAt_totalSpace_iff I
      (fun s => (⟨γ s, Z s⟩ : _root_.Bundle.TotalSpace F V)) (e.mem_source.mpr he)).mp hZ).1
  have hR : MDifferentiableAt I 𝓘(ℝ, F →L[ℝ] F) R (γ t) :=
    (contMDiffAt_coordChangeL (IB := I) (n := 1) he' he).mdifferentiableAt (by simp)
  have hRγ : DifferentiableWithinAt ℝ (fun s => R (γ s)) J t :=
    mdifferentiableWithinAt_iff_differentiableWithinAt.mp
      (hR.comp_mdifferentiableWithinAt t hγ)
  have hz' : DifferentiableWithinAt ℝ z' J t :=
    differentiableWithinAt_trivialization_coord_along e' he' hZ
  have hcoord (s : ℝ) (hs : γ s ∈ e.baseSet) (hs' : γ s ∈ e'.baseSet) :
      z s = R (γ s) (z' s) := by
    dsimp only [z, z', R]
    simp only [ContinuousLinearEquiv.coe_coe]
    rw [e'.coordChangeL_apply' e ⟨hs', hs⟩, ← e'.mk_symm hs',
      ← e'.symmL_apply (R := ℝ) hs', e'.symmL_continuousLinearMapAt hs',
      e.continuousLinearMapAt_apply_of_mem ℝ hs]
  have heq : z =ᶠ[𝓝[J] t] (fun s => R (γ s) (z' s)) := by
    filter_upwards [hγ.continuousWithinAt.preimage_mem_nhdsWithin
      (e.open_baseSet.mem_nhds he), hγ.continuousWithinAt.preimage_mem_nhdsWithin
      (e'.open_baseSet.mem_nhds he')] with s hs hs'
    exact hcoord s hs hs'
  have hDz : derivWithin z J t =
      derivWithin (fun s => R (γ s)) J t (z' t) + R (γ t) (derivWithin z' J t) := by
    rw [heq.derivWithin_eq (hcoord t he he'), derivWithin_clm_apply hRγ hz']
  have hDR : derivWithin (fun s => R (γ s)) J t (z' t) =
      mvfderiv I (fun x => R x (z' t)) (γ t) X := by
    have h := derivWithin_comp_eq_mvfderiv hγ
      (hR.clm_apply (mdifferentiableAt_const (c := z' t))) hJ
    rw [derivWithin_clm_apply hRγ (differentiableWithinAt_const (z' t)),
      derivWithin_fun_const, Pi.zero_apply, map_zero, add_zero] at h
    exact h
  have htrans := cov.connectionForm_coordChange e e' he he' X (z' t)
  change R (γ t) (cov.connectionForm e' (γ t) X (z' t)) =
    mvfderiv I (fun x => R x (z' t)) (γ t) X +
      cov.connectionForm e (γ t) X (R (γ t) (z' t)) at htrans
  change R (γ t) (derivWithin z' J t + cov.connectionForm e' (γ t) X (z' t)) =
    derivWithin z J t + cov.connectionForm e (γ t) X (z t)
  rw [map_add, htrans, ← hcoord t he he', hDz, hDR]
  abel

run_cmd do
  let target := ``Submission.CovariantDerivative.derivAlongWithin_coordChange
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `CovariantDerivative.derivAlongWithin_coordChange target :: scope.openDecls } }

open _root_.CovariantDerivative in
private theorem derivAlongWithin_coord_of_uniqueDiffWithinAt (cov : CovariantDerivative I F V)
    (e : _root_.Bundle.Trivialization F (TotalSpace.proj : _root_.Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)}
    {J : Set ℝ} {t : ℝ} (he : γ t ∈ e.baseSet)
    (hJ : UniqueDiffWithinAt ℝ J t)
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z s⟩ : _root_.Bundle.TotalSpace F V)) J t) :
    e.continuousLinearMapAt ℝ (γ t) (cov.derivAlongWithin γ Z J t) =
      derivWithin (fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)) J t +
        cov.connectionForm e (γ t)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))
          (e.continuousLinearMapAt ℝ (γ t) (Z t)) := by
  let e₀ := _root_.FiberBundle.trivializationAt F V (γ t)
  have he₀ : γ t ∈ e₀.baseSet := FiberBundle.mem_baseSet_trivializationAt F V (γ t)
  have h := derivAlongWithin_coordChange cov e e₀ he he₀ hJ hZ
  rw [e₀.coordChangeL_apply' e ⟨he₀, he⟩, ← e₀.mk_symm he₀,
    ← e₀.symmL_apply (R := ℝ) he₀, ← e.continuousLinearMapAt_apply_of_mem ℝ he] at h
  exact h

run_cmd do
  let target := ``Submission.CovariantDerivative.derivAlongWithin_coord_of_uniqueDiffWithinAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `CovariantDerivative.derivAlongWithin_coord_of_uniqueDiffWithinAt target :: scope.openDecls } }

open _root_.CovariantDerivative in
theorem derivAlongWithin_coord (cov : CovariantDerivative I F V)
    (e : _root_.Bundle.Trivialization F (TotalSpace.proj : _root_.Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)}
    {J : Set ℝ} {t : ℝ} (he : γ t ∈ e.baseSet)
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z s⟩ : _root_.Bundle.TotalSpace F V)) J t) :
    e.continuousLinearMapAt ℝ (γ t) (cov.derivAlongWithin γ Z J t) =
      derivWithin (fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)) J t +
        cov.connectionForm e (γ t)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))
          (e.continuousLinearMapAt ℝ (γ t) (Z t)) := by
  by_cases hJ : UniqueDiffWithinAt ℝ J t
  · exact derivAlongWithin_coord_of_uniqueDiffWithinAt cov e he hJ hZ
  · simp only [cov.derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt γ Z hJ,
      derivWithin_zero_of_not_uniqueDiffWithinAt hJ,
      mfderivWithin_curve_eq_zero_of_not_uniqueDiffWithinAt (I := I) γ hJ, zero_apply, map_zero,
      zero_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.derivAlongWithin_coord then
    throwError "Refusing to shadow existing declaration CovariantDerivative.derivAlongWithin_coord"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.derivAlongWithin_coord ``Submission.CovariantDerivative.derivAlongWithin_coord

open _root_.CovariantDerivative in
theorem derivAlongWithin_eq (cov : CovariantDerivative I F V)
    (e : _root_.Bundle.Trivialization F (TotalSpace.proj : _root_.Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)}
    {J : Set ℝ} {t : ℝ} (he : γ t ∈ e.baseSet)
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z s⟩ : _root_.Bundle.TotalSpace F V)) J t) :
    cov.derivAlongWithin γ Z J t = e.symmL ℝ (γ t)
      (derivWithin (fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)) J t +
        cov.connectionForm e (γ t)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))
          (e.continuousLinearMapAt ℝ (γ t) (Z t))) := by
  rw [← cov.derivAlongWithin_coord e he hZ, e.symmL_continuousLinearMapAt he]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.derivAlongWithin_eq then
    throwError "Refusing to shadow existing declaration CovariantDerivative.derivAlongWithin_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.derivAlongWithin_eq ``Submission.CovariantDerivative.derivAlongWithin_eq

open _root_.CovariantDerivative in
theorem derivAlongWithin_section (cov : CovariantDerivative I F V)
    {γ : ℝ → M} {σ : ∀ x : M, V x} {J : Set ℝ} {t : ℝ}
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ J t)
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (T% σ) (γ t)) :
    cov.derivAlongWithin γ (fun s => σ (γ s)) J t =
      cov σ (γ t)
        (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1)) := by
  by_cases hJ : UniqueDiffWithinAt ℝ J t
  · let e := _root_.FiberBundle.trivializationAt F V (γ t)
    have he : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V (γ t)
    have hZ := hσ.comp_mdifferentiableWithinAt t hγ
    rw [cov.derivAlongWithin_eq e he hZ]
    have hσ' : MDifferentiableAt I 𝓘(ℝ, F)
        (fun x => e.continuousLinearMapAt ℝ x (σ x)) (γ t) := by
      apply ((e.mdifferentiableAt_section_iff I σ he).mp hσ).congr_of_eventuallyEq
      filter_upwards [e.open_baseSet.mem_nhds he] with x hx
      exact e.continuousLinearMapAt_apply_of_mem ℝ hx (σ x)
    rw [derivWithin_comp_eq_mvfderiv hγ hσ' hJ,
      ← cov.covariant_derivative_coord e he hσ, e.symmL_continuousLinearMapAt he]
  · simp only [cov.derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt γ _ hJ,
      mfderivWithin_curve_eq_zero_of_not_uniqueDiffWithinAt (I := I) γ hJ, zero_apply, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.derivAlongWithin_section then
    throwError "Refusing to shadow existing declaration CovariantDerivative.derivAlongWithin_section"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.derivAlongWithin_section ``Submission.CovariantDerivative.derivAlongWithin_section

open _root_.CovariantDerivative in
theorem derivAlongWithin_singleton (cov : CovariantDerivative I F V)
    (γ : ℝ → M) (Z : ∀ t : ℝ, V (γ t)) (t : ℝ) :
    cov.derivAlongWithin γ Z {t} t = 0 := by
  apply cov.derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt
  simp only [uniqueDiffWithinAt_iff_accPt, accPt_principal_iff_nhdsWithin,
    _root_.Set.sdiff_self, nhdsWithin_empty, _root_.Filter.not_neBot]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.derivAlongWithin_singleton then
    throwError "Refusing to shadow existing declaration CovariantDerivative.derivAlongWithin_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.derivAlongWithin_singleton ``Submission.CovariantDerivative.derivAlongWithin_singleton

open _root_.CovariantDerivative in
theorem derivAlongWithin_congr_of_eventuallyEq (cov : CovariantDerivative I F V)
    {γ : ℝ → M} {Z W : ∀ t : ℝ, V (γ t)} {J : Set ℝ} {t : ℝ}
    (hZW : ∀ᶠ s in 𝓝[J] t, Z s = W s) (ht : Z t = W t) :
    cov.derivAlongWithin γ Z J t = cov.derivAlongWithin γ W J t := by
  let e := _root_.FiberBundle.trivializationAt F V (γ t)
  have heq : (fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)) =ᶠ[𝓝[J] t]
      (fun s => e.continuousLinearMapAt ℝ (γ s) (W s)) := by
    filter_upwards [hZW] with s hs
    rw [hs]
  dsimp only [derivAlongWithin]
  rw [heq.derivWithin_eq (congrArg (e.continuousLinearMapAt ℝ (γ t)) ht), ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.derivAlongWithin_congr_of_eventuallyEq then
    throwError "Refusing to shadow existing declaration CovariantDerivative.derivAlongWithin_congr_of_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.derivAlongWithin_congr_of_eventuallyEq ``Submission.CovariantDerivative.derivAlongWithin_congr_of_eventuallyEq

open _root_.CovariantDerivative in
theorem derivAlongWithin_congr (cov : CovariantDerivative I F V)
    {γ : ℝ → M} {Z W : ∀ t : ℝ, V (γ t)} {J : Set ℝ} {t : ℝ}
    (hZW : ∀ s ∈ J, Z s = W s) (ht : Z t = W t) :
    cov.derivAlongWithin γ Z J t = cov.derivAlongWithin γ W J t := by
  apply cov.derivAlongWithin_congr_of_eventuallyEq _ ht
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact hZW s hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.derivAlongWithin_congr then
    throwError "Refusing to shadow existing declaration CovariantDerivative.derivAlongWithin_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.derivAlongWithin_congr ``Submission.CovariantDerivative.derivAlongWithin_congr

open _root_.CovariantDerivative in
theorem derivAlongWithin_mono (cov : CovariantDerivative I F V)
    {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)} {J K : Set ℝ} {t : ℝ}
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z s⟩ : _root_.Bundle.TotalSpace F V)) J t)
    (hK : UniqueDiffWithinAt ℝ K t) (hKJ : K ⊆ J) :
    cov.derivAlongWithin γ Z K t = cov.derivAlongWithin γ Z J t := by
  let e := _root_.FiberBundle.trivializationAt F V (γ t)
  have he : γ t ∈ e.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt F V (γ t)
  have hγ := ((e.mdifferentiableWithinAt_totalSpace_iff I
    (fun s => (⟨γ s, Z s⟩ : _root_.Bundle.TotalSpace F V)) (e.mem_source.mpr he)).mp hZ).1
  have hcoord := differentiableWithinAt_trivialization_coord_along e he hZ
  rw [cov.derivAlongWithin_eq e he (hZ.mono hKJ), cov.derivAlongWithin_eq e he hZ,
    hγ.mfderivWithin_mono hK.uniqueMDiffWithinAt hKJ,
    (hcoord.hasDerivWithinAt.mono hKJ).derivWithin hK]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.derivAlongWithin_mono then
    throwError "Refusing to shadow existing declaration CovariantDerivative.derivAlongWithin_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.derivAlongWithin_mono ``Submission.CovariantDerivative.derivAlongWithin_mono

open _root_.CovariantDerivative in
theorem derivAlongWithin_congr_set (cov : CovariantDerivative I F V)
    {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)} {J K : Set ℝ} {t : ℝ}
    (hJK : J =ᶠ[𝓝 t] K) :
    cov.derivAlongWithin γ Z J t = cov.derivAlongWithin γ Z K t := by
  dsimp only [derivAlongWithin]
  rw [derivWithin_congr_set hJK, mfderivWithin_congr_set hJK]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.derivAlongWithin_congr_set then
    throwError "Refusing to shadow existing declaration CovariantDerivative.derivAlongWithin_congr_set"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.derivAlongWithin_congr_set ``Submission.CovariantDerivative.derivAlongWithin_congr_set

open _root_.CovariantDerivative in
theorem derivAlongWithin_eq_zero_mono (cov : CovariantDerivative I F V)
    {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)} {J K : Set ℝ} {t : ℝ}
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z s⟩ : _root_.Bundle.TotalSpace F V)) J t)
    (hKJ : K ⊆ J) (hpar : cov.derivAlongWithin γ Z J t = 0) :
    cov.derivAlongWithin γ Z K t = 0 := by
  by_cases hK : UniqueDiffWithinAt ℝ K t
  · rw [cov.derivAlongWithin_mono hZ hK hKJ, hpar]
  · exact cov.derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt γ Z hK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.derivAlongWithin_eq_zero_mono then
    throwError "Refusing to shadow existing declaration CovariantDerivative.derivAlongWithin_eq_zero_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.derivAlongWithin_eq_zero_mono ``Submission.CovariantDerivative.derivAlongWithin_eq_zero_mono

open _root_.CovariantDerivative in
theorem hasDerivWithinAt_coord (cov : CovariantDerivative I F V)
    (e : _root_.Bundle.Trivialization F (TotalSpace.proj : _root_.Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)}
    {J : Set ℝ} {t : ℝ} (he : γ t ∈ e.baseSet)
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z s⟩ : _root_.Bundle.TotalSpace F V)) J t) :
    HasDerivWithinAt (fun s => e.continuousLinearMapAt ℝ (γ s) (Z s))
      (e.continuousLinearMapAt ℝ (γ t) (cov.derivAlongWithin γ Z J t) -
        cov.connectionForm e (γ t)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))
          (e.continuousLinearMapAt ℝ (γ t) (Z t))) J t := by
  have hcoord := differentiableWithinAt_trivialization_coord_along e he hZ
  rw [cov.derivAlongWithin_coord e he hZ, add_sub_cancel_right]
  exact hcoord.hasDerivWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.hasDerivWithinAt_coord then
    throwError "Refusing to shadow existing declaration CovariantDerivative.hasDerivWithinAt_coord"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.hasDerivWithinAt_coord ``Submission.CovariantDerivative.hasDerivWithinAt_coord

open _root_.CovariantDerivative in
private theorem parallel_piecewise_at
    (cov : CovariantDerivative I F V) {γ : ℝ → M} {Z W : ∀ t : ℝ, V (γ t)}
    {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ (_root_.Set.Icc a b) c)
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, Z t⟩ : _root_.Bundle.TotalSpace F V)) (_root_.Set.Icc a c) c)
    (hW : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, W t⟩ : _root_.Bundle.TotalSpace F V)) (_root_.Set.Icc c b) c)
    (hZpar : cov.derivAlongWithin γ Z (_root_.Set.Icc a c) c = 0)
    (hWpar : cov.derivAlongWithin γ W (_root_.Set.Icc c b) c = 0) (hZW : Z c = W c) :
    let U : ∀ t : ℝ, V (γ t) := fun t => if t ≤ c then Z t else W t
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, U t⟩ : _root_.Bundle.TotalSpace F V)) (_root_.Set.Icc a b) c ∧
      cov.derivAlongWithin γ U (_root_.Set.Icc a b) c = 0 := by
  let U : ∀ t : ℝ, V (γ t) := fun t => if t ≤ c then Z t else W t
  change MDifferentiableWithinAt _ _ (fun t => (⟨γ t, U t⟩ : _root_.Bundle.TotalSpace F V)) _ _ ∧ _
  let e := _root_.FiberBundle.trivializationAt F V (γ c)
  have he : γ c ∈ e.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt F V (γ c)
  let D := -cov.connectionForm e (γ c)
    (mfderivWithin 𝓘(ℝ, ℝ) I γ (_root_.Set.Icc a b) c ((NormedSpace.fromTangentSpace c).symm 1))
    (e.continuousLinearMapAt ℝ (γ c) (Z c))
  have hleft : _root_.Set.Icc a c ⊆ _root_.Set.Icc a b := _root_.Set.Icc_subset_Icc_right hcb.le
  have hright : _root_.Set.Icc c b ⊆ _root_.Set.Icc a b := _root_.Set.Icc_subset_Icc_left hac.le
  have hDZ : HasDerivWithinAt (fun t => e.continuousLinearMapAt ℝ (γ t) (Z t))
      D (_root_.Set.Icc a c) c := by
    have h := cov.hasDerivWithinAt_coord e he hZ
    rw [hZpar, map_zero, zero_sub,
      hγ.mfderivWithin_mono (uniqueDiffOn_Icc hac c (right_mem_Icc.mpr hac.le)).uniqueMDiffWithinAt
        hleft] at h
    exact h
  have hDW : HasDerivWithinAt (fun t => e.continuousLinearMapAt ℝ (γ t) (W t))
      D (_root_.Set.Icc c b) c := by
    have h := cov.hasDerivWithinAt_coord e he hW
    rw [hWpar, map_zero, zero_sub,
      hγ.mfderivWithin_mono (uniqueDiffOn_Icc hcb c (left_mem_Icc.mpr hcb.le)).uniqueMDiffWithinAt
        hright, ← hZW] at h
    exact h
  have hUZ (t : ℝ) (ht : t ∈ _root_.Set.Icc a c) : U t = Z t := if_pos ht.2
  have hUW (t : ℝ) (ht : t ∈ _root_.Set.Icc c b) : U t = W t := by
    dsimp only [U]
    split_ifs with htc
    · have htc' : t = c := le_antisymm htc ht.1
      subst t
      exact hZW
    · rfl
  have hDU : HasDerivWithinAt (fun t => e.continuousLinearMapAt ℝ (γ t) (U t))
      D (_root_.Set.Icc a b) c := by
    rw [← _root_.Set.Icc_union_Icc_eq_Icc hac.le hcb.le]
    exact (hDZ.congr (fun t ht => congrArg (e.continuousLinearMapAt ℝ (γ t)) (hUZ t ht))
      (congrArg (e.continuousLinearMapAt ℝ (γ c)) (hUZ c (right_mem_Icc.mpr hac.le)))).union
      (hDW.congr (fun t ht => congrArg (e.continuousLinearMapAt ℝ (γ t)) (hUW t ht))
        (congrArg (e.continuousLinearMapAt ℝ (γ c)) (hUW c (left_mem_Icc.mpr hcb.le))))
  have hUM : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, U t⟩ : _root_.Bundle.TotalSpace F V)) (_root_.Set.Icc a b) c := by
    apply (e.mdifferentiableWithinAt_totalSpace_iff I
      (fun t => (⟨γ t, U t⟩ : _root_.Bundle.TotalSpace F V)) (e.mem_source.mpr he)).mpr
    refine ⟨hγ, ?_⟩
    have hcoord : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F)
        (fun t => e.continuousLinearMapAt ℝ (γ t) (U t)) (_root_.Set.Icc a b) c :=
      mdifferentiableWithinAt_iff_differentiableWithinAt.mpr hDU.differentiableWithinAt
    apply hcoord.congr_of_eventuallyEq
    · filter_upwards [hγ.continuousWithinAt.preimage_mem_nhdsWithin
        (e.open_baseSet.mem_nhds he)] with t ht
      exact (e.continuousLinearMapAt_apply_of_mem ℝ ht (U t)).symm
    · exact (e.continuousLinearMapAt_apply_of_mem ℝ he (U c)).symm
  refine ⟨hUM, ?_⟩
  rw [cov.derivAlongWithin_eq e he hUM,
    hDU.derivWithin (uniqueDiffOn_Icc (hac.trans hcb) c ⟨hac.le, hcb.le⟩),
    hUZ c (right_mem_Icc.mpr hac.le)]
  simp only [D, neg_add_cancel, map_zero]

run_cmd do
  let target := ``Submission.CovariantDerivative.parallel_piecewise_at
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `CovariantDerivative.parallel_piecewise_at target :: scope.openDecls } }

open _root_.CovariantDerivative in
theorem parallel_piecewise_on_Icc
    (cov : CovariantDerivative I F V) {γ : ℝ → M} {Z W : ∀ t : ℝ, V (γ t)}
    {a b c : ℝ} (hc : c ∈ _root_.Set.Icc a b)
    (hγ : MDifferentiableOn 𝓘(ℝ, ℝ) I γ (_root_.Set.Icc a b))
    (hZ : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, Z t⟩ : _root_.Bundle.TotalSpace F V)) (_root_.Set.Icc a c))
    (hW : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, W t⟩ : _root_.Bundle.TotalSpace F V)) (_root_.Set.Icc c b))
    (hZpar : ∀ t ∈ _root_.Set.Icc a c, cov.derivAlongWithin γ Z (_root_.Set.Icc a c) t = 0)
    (hWpar : ∀ t ∈ _root_.Set.Icc c b, cov.derivAlongWithin γ W (_root_.Set.Icc c b) t = 0)
    (hZW : Z c = W c) :
    let U : ∀ t : ℝ, V (γ t) := fun t => if t ≤ c then Z t else W t
    MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, U t⟩ : _root_.Bundle.TotalSpace F V)) (_root_.Set.Icc a b) ∧
      ∀ t ∈ _root_.Set.Icc a b, cov.derivAlongWithin γ U (_root_.Set.Icc a b) t = 0 := by
  let U : ∀ t : ℝ, V (γ t) := fun t => if t ≤ c then Z t else W t
  change MDifferentiableOn _ _ (fun t => (⟨γ t, U t⟩ : _root_.Bundle.TotalSpace F V)) _ ∧ _
  by_cases hac : a = c
  · subst c
    have hUW (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) : U t = W t := by
      dsimp only [U]
      split_ifs with hta
      · have hta' : t = a := le_antisymm hta ht.1
        subst t
        exact hZW
      · rfl
    refine ⟨hW.congr (fun t ht => congrArg (fun v => (⟨γ t, v⟩ : _root_.Bundle.TotalSpace F V)) (hUW t ht)), ?_⟩
    intro t ht
    rw [cov.derivAlongWithin_congr hUW (hUW t ht)]
    exact hWpar t ht
  by_cases hcb : c = b
  · subst c
    have hUZ (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) : U t = Z t := if_pos ht.2
    refine ⟨hZ.congr (fun t ht => congrArg (fun v => (⟨γ t, v⟩ : _root_.Bundle.TotalSpace F V)) (hUZ t ht)), ?_⟩
    intro t ht
    rw [cov.derivAlongWithin_congr hUZ (hUZ t ht)]
    exact hZpar t ht
  have hac' : a < c := lt_of_le_of_ne hc.1 hac
  have hcb' : c < b := lt_of_le_of_ne hc.2 hcb
  suffices ∀ t ∈ _root_.Set.Icc a b,
      MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun s => (⟨γ s, U s⟩ : _root_.Bundle.TotalSpace F V)) (_root_.Set.Icc a b) t ∧
        cov.derivAlongWithin γ U (_root_.Set.Icc a b) t = 0 from
    ⟨fun t ht => (this t ht).1, fun t ht => (this t ht).2⟩
  intro t ht
  rcases lt_trichotomy t c with htc | htc | hct
  · have hts : t ∈ _root_.Set.Icc a c := ⟨ht.1, htc.le⟩
    have hdom : _root_.Set.Icc a c =ᶠ[𝓝 t] _root_.Set.Icc a b := by
      filter_upwards [Iio_mem_nhds htc] with s hs
      exact propext ⟨fun h => ⟨h.1, h.2.trans hc.2⟩, fun h => ⟨h.1, hs.le⟩⟩
    have hZfull : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun s => (⟨γ s, Z s⟩ : _root_.Bundle.TotalSpace F V)) (_root_.Set.Icc a b) t :=
      (mdifferentiableWithinAt_congr_set hdom).mp (hZ t hts)
    have hUZ : ∀ᶠ s in 𝓝[_root_.Set.Icc a b] t, U s = Z s := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds htc)] with s hs
      exact if_pos hs.le
    have hUZt : U t = Z t := if_pos htc.le
    refine ⟨hZfull.congr_of_eventuallyEq ?_ ?_, ?_⟩
    · exact hUZ.mono fun s hs => congrArg (fun v => (⟨γ s, v⟩ : _root_.Bundle.TotalSpace F V)) hs
    · exact congrArg (fun v => (⟨γ t, v⟩ : _root_.Bundle.TotalSpace F V)) hUZt
    · rw [cov.derivAlongWithin_congr_of_eventuallyEq hUZ hUZt,
        ← cov.derivAlongWithin_congr_set (γ := γ) (Z := Z) hdom]
      exact hZpar t hts
  · subst t
    exact parallel_piecewise_at cov hac' hcb' (hγ c hc)
      (hZ c (right_mem_Icc.mpr hc.1)) (hW c (left_mem_Icc.mpr hc.2))
      (hZpar c (right_mem_Icc.mpr hc.1)) (hWpar c (left_mem_Icc.mpr hc.2)) hZW
  · have hts : t ∈ _root_.Set.Icc c b := ⟨hct.le, ht.2⟩
    have hdom : _root_.Set.Icc c b =ᶠ[𝓝 t] _root_.Set.Icc a b := by
      filter_upwards [Ioi_mem_nhds hct] with s hs
      exact propext ⟨fun h => ⟨hc.1.trans h.1, h.2⟩, fun h => ⟨hs.le, h.2⟩⟩
    have hWfull : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun s => (⟨γ s, W s⟩ : _root_.Bundle.TotalSpace F V)) (_root_.Set.Icc a b) t :=
      (mdifferentiableWithinAt_congr_set hdom).mp (hW t hts)
    have hUW : ∀ᶠ s in 𝓝[_root_.Set.Icc a b] t, U s = W s := by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hct)] with s hs
      exact if_neg (not_le.mpr hs)
    have hUWt : U t = W t := if_neg (not_le.mpr hct)
    refine ⟨hWfull.congr_of_eventuallyEq ?_ ?_, ?_⟩
    · exact hUW.mono fun s hs => congrArg (fun v => (⟨γ s, v⟩ : _root_.Bundle.TotalSpace F V)) hs
    · exact congrArg (fun v => (⟨γ t, v⟩ : _root_.Bundle.TotalSpace F V)) hUWt
    · rw [cov.derivAlongWithin_congr_of_eventuallyEq hUW hUWt,
        ← cov.derivAlongWithin_congr_set (γ := γ) (Z := W) hdom]
      exact hWpar t hts

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.parallel_piecewise_on_Icc then
    throwError "Refusing to shadow existing declaration CovariantDerivative.parallel_piecewise_on_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.parallel_piecewise_on_Icc ``Submission.CovariantDerivative.parallel_piecewise_on_Icc

end CovariantDerivative
