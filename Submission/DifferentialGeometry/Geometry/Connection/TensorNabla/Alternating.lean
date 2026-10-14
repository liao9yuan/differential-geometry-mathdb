import Submission.DifferentialGeometry.Tensor.Alternating.BundleComp
import Submission.DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import Submission.DifferentialGeometry.Tensor.Alternating.BundleMaps
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Pullback
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Basic
import Submission.DifferentialGeometry.Tensor.Alternating.Coordinates.Basis

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace CovariantDerivative
open _root_.CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

open _root_.CovariantDerivative in
def alternating (cov : CovariantDerivative I F V) (k : ℕ) :
    CovariantDerivative I (F [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) where
  toFun a x := ContinuousMultilinearMap.alternatizationCLM.comp
    ((Bundle.continuousMultilinearMap.fiberContinuousLinearEquiv (F := F) k x).toContinuousLinearMap.comp
      (multilinear cov k (fun y => (a y).toContinuousMultilinearMap) x))
  isCovariantDerivativeOnUniv := by
    constructor
    · intro a b x ha hb hx
      have hc := (multilinear cov k).isCovariantDerivativeOnUniv.add
        ha.alternating_bundle_toMultilinear hb.alternating_bundle_toMultilinear
      ext X v
      change ContinuousMultilinearMap.alternatizationCLM
        (multilinear cov k
          ((fun y => (a y).toContinuousMultilinearMap) +
            (fun y => (b y).toContinuousMultilinearMap)) x X) v = _
      rw [hc]
      simp only [add_apply, map_add, ContinuousAlternatingMap.add_apply]
      rfl
    · intro a f x ha hf hx
      have hc := (multilinear cov k).isCovariantDerivativeOnUniv.leibniz
        ha.alternating_bundle_toMultilinear hf
      ext X v
      change ContinuousMultilinearMap.alternatizationCLM
        (multilinear cov k (f • (fun y => (a y).toContinuousMultilinearMap)) x X) v = _
      rw [hc]
      simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
        map_add, map_smul, ContinuousAlternatingMap.add_apply,
        ContinuousAlternatingMap.smul_apply,
        ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap]
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.alternating then
    throwError "Refusing to shadow existing declaration CovariantDerivative.alternating"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.alternating ``Submission.CovariantDerivative.alternating

open _root_.CovariantDerivative in
theorem alternating_apply (cov : CovariantDerivative I F V) (k : ℕ)
    (a : ∀ x, V x [⋀^Fin k]→L[ℝ] ℝ) (x : M) (X : TangentSpace I x) :
    alternating cov k a x X = ContinuousMultilinearMap.alternatizationCLM
      (multilinear cov k (fun y => (a y).toContinuousMultilinearMap) x X) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.alternating_apply then
    throwError "Refusing to shadow existing declaration CovariantDerivative.alternating_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.alternating_apply ``Submission.CovariantDerivative.alternating_apply

open _root_.CovariantDerivative in
private theorem multilinear_map_eq_zero_of_eq
    (cov : CovariantDerivative I F V) (k : ℕ)
    {a : ∀ x, V x [⋀^Fin k]→L[ℝ] ℝ} {x : M}
    (ha : MDifferentiableAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ))
      (fun y => (⟨y, a y⟩ : _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)))) x)
    (X : TangentSpace I x) (v : Fin k → V x) (i j : Fin k)
    (hv : v i = v j) (hij : i ≠ j) :
    multilinear cov k (fun y => (a y).toContinuousMultilinearMap) x X v = 0 := by
  classical
  choose Z hZ using fun l : Fin k =>
    ContMDiffSection.exists_eq_at (I := I) (F := F) (V := V) (n := (⊤ : ℕ∞)) x (v l)
  let Y := Function.update Z j (Z i)
  have hYx (l : Fin k) : Y l x = v l := by
    by_cases hl : l = j
    · subst l
      simp only [Y, Function.update_self]
      exact (hZ i).trans hv
    · simpa only [Y, Function.update_of_ne hl] using hZ l
  have hYij : Y i = Y j := by simp only [Y, Function.update_of_ne hij, Function.update_self]
  have hvalue (y : M) : Y i y = Y j y := congrArg (fun σ => σ y) hYij
  have hscalar : (fun y => a y (fun l => Y l y)) = fun _ => (0 : ℝ) := by
    funext y
    exact (a y).map_eq_zero_of_eq _ (hvalue y) hij
  let W := cov (fun y => Y i y) x X
  let f : Fin k → ℝ := fun l =>
    a x (Function.update (fun l => Y l x) l (cov (fun y => Y l y) x X))
  have hother (l : Fin k) (hli : l ≠ i) (hlj : l ≠ j) : f l = 0 := by
    apply (a x).map_eq_zero_of_eq _ (i := i) (j := j) _ hij
    simpa only [Function.update_of_ne hli.symm, Function.update_of_ne hlj.symm] using hvalue x
  have hswap :
      Function.update (fun l => Y l x) i W ∘ Equiv.swap i j =
        Function.update (fun l => Y l x) j W := by
    funext l
    by_cases hli : l = i
    · subst l
      simpa only [Function.comp_apply, Equiv.swap_apply_left, Function.update_of_ne hij.symm,
        Function.update_of_ne hij] using (hvalue x).symm
    · by_cases hlj : l = j
      · subst l
        simp only [Function.comp_apply, Equiv.swap_apply_right, Function.update_self]
      · simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hli hlj,
          Function.update_of_ne hli, Function.update_of_ne hlj]
  have hpair : f j + f i = 0 := by
    have h := (a x).toAlternatingMap.map_swap_add
      (Function.update (fun l => Y l x) i W) hij
    rw [hswap] at h
    simpa only [f, W, hYij, ContinuousAlternatingMap.coe_toAlternatingMap] using h
  have hsum : ∑ l, f l = 0 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
      ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
    have hzero : ∑ l ∈ (Finset.univ.erase i).erase j, f l = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      exact hother l (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
        (Finset.mem_erase.mp hl).1
    rw [hzero, zero_add, hpair]
  have h := multilinear_apply cov k (fun l y => Y l y)
    ha.alternating_bundle_toMultilinear (fun l => (Y l).mdifferentiableAt) X
  change multilinear cov k (fun y => (a y).toContinuousMultilinearMap) x X
    (fun l => Y l x) = mvfderiv (I := I) (fun y => a y (fun l => Y l y)) x X - ∑ l, f l at h
  rw [hscalar, hsum, mvfderiv_const, zero_apply, sub_zero] at h
  simpa only [hYx] using h

run_cmd do
  let target := ``Submission.CovariantDerivative.multilinear_map_eq_zero_of_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `CovariantDerivative.multilinear_map_eq_zero_of_eq target :: scope.openDecls } }

open _root_.CovariantDerivative in
theorem alternating_toMultilinear
    (cov : CovariantDerivative I F V) (k : ℕ)
    {a : ∀ x, V x [⋀^Fin k]→L[ℝ] ℝ} {x : M}
    (ha : MDifferentiableAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ))
      (fun y => (⟨y, a y⟩ : _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)))) x)
    (X : TangentSpace I x) :
    (alternating cov k a x X).toContinuousMultilinearMap =
      multilinear cov k (fun y => (a y).toContinuousMultilinearMap) x X := by
  let S : V x [⋀^Fin k]→L[ℝ] ℝ :=
    ⟨multilinear cov k (fun y => (a y).toContinuousMultilinearMap) x X,
      fun v i j hv hij => multilinear_map_eq_zero_of_eq cov k ha X v i j hv hij⟩
  have h := ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap S
  exact congrArg ContinuousAlternatingMap.toContinuousMultilinearMap h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.alternating_toMultilinear then
    throwError "Refusing to shadow existing declaration CovariantDerivative.alternating_toMultilinear"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.alternating_toMultilinear ``Submission.CovariantDerivative.alternating_toMultilinear

open _root_.CovariantDerivative in
theorem alternating_apply_of_mdifferentiableAt
    (cov : CovariantDerivative I F V) (k : ℕ)
    {a : ∀ x, V x [⋀^Fin k]→L[ℝ] ℝ} (Y : Fin k → ∀ x, V x) {x : M}
    (ha : MDifferentiableAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ))
      (fun y => (⟨y, a y⟩ : _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)))) x)
    (hY : ∀ i, MDifferentiableAt I (I.prod 𝓘(ℝ, F))
      (fun y => (⟨y, Y i y⟩ : _root_.Bundle.TotalSpace F V)) x)
    (X : TangentSpace I x) :
    alternating cov k a x X (fun i => Y i x) =
      mvfderiv (I := I) (fun y => a y (fun i => Y i y)) x X -
        ∑ i, a x (Function.update (fun j => Y j x) i (cov (Y i) x X)) := by
  change (alternating cov k a x X).toContinuousMultilinearMap (fun i => Y i x) = _
  rw [alternating_toMultilinear cov k ha X]
  exact multilinear_apply cov k Y ha.alternating_bundle_toMultilinear hY X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.alternating_apply_of_mdifferentiableAt then
    throwError "Refusing to shadow existing declaration CovariantDerivative.alternating_apply_of_mdifferentiableAt"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.alternating_apply_of_mdifferentiableAt ``Submission.CovariantDerivative.alternating_apply_of_mdifferentiableAt

open _root_.CovariantDerivative in
instance alternating_contMDiff (cov : CovariantDerivative I F V)
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] (k : ℕ) :
    _root_.CovariantDerivative.ContMDiffCovariantDerivative (alternating cov k) ∞ where
  contMDiff := by
    constructor
    intro a ha
    let : CompleteSpace E := FiniteDimensional.complete ℝ E
    let : FiniteDimensional ℝ (F [⋀^Fin k]→L[ℝ] ℝ) :=
      (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
        (Module.finBasis ℝ F)).finiteDimensional_of_finite
    have ha' := ha.alternating_bundle_toMultilinear
    have hc := (inferInstance : _root_.CovariantDerivative.ContMDiffCovariantDerivative (multilinear cov k) ∞).contMDiff.contMDiff ha'
    have hglobal := contMDiffOn_univ.mp hc
    apply ContMDiff.contMDiffOn
    apply DifferentialGeometry.Geometry.Connection.Realization.contMDiff_clm_section_of_pointwise
      (I := I) (M := M)
    intro Y
    have h := (hglobal.clm_bundle_apply Y.contMDiff).multilinear_bundle_alternatization
    exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.alternating_contMDiff then
    throwError "Refusing to shadow existing declaration CovariantDerivative.alternating_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.alternating_contMDiff ``Submission.CovariantDerivative.alternating_contMDiff

end CovariantDerivative

namespace CovariantDerivative
open _root_.CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle ∞ F₁ V₁ I]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle ∞ F₂ V₂ I]

open _root_.CovariantDerivative in
theorem alternating_pullbackFiberwiseLinearEquiv
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : _root_.Bundle.TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))))
    (cov : CovariantDerivative I F₂ V₂) (k : ℕ)
    {a : ∀ x, V₂ x [⋀^Fin k]→L[ℝ] ℝ} {x : M}
    (ha : MDifferentiableAt I (I.prod 𝓘(ℝ, F₂ [⋀^Fin k]→L[ℝ] ℝ))
      (fun y => (⟨y, a y⟩ : _root_.Bundle.TotalSpace (F₂ [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F₂ V₂ ℝ (Bundle.Trivial M ℝ)))) x)
    (X : TangentSpace I x) :
    alternating
      (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) k
      (fun y => (a y).compContinuousLinearMap (φ y).toContinuousLinearMap) x X =
      (alternating cov k a x X).compContinuousLinearMap (φ x).toContinuousLinearMap := by
  rw [alternating_apply, alternating_apply]
  have h := multilinear_pullbackFiberwiseLinearEquiv φ hφ cov k
    ha.alternating_bundle_toMultilinear X
  change ContinuousMultilinearMap.alternatizationCLM
    (multilinear
      (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) k
      (fun y => ((a y).toContinuousMultilinearMap).compContinuousLinearMap
        (fun _ => (φ y).toContinuousLinearMap)) x X) = _
  rw [h, ContinuousMultilinearMap.alternatizationCLM_compContinuousLinearMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.alternating_pullbackFiberwiseLinearEquiv then
    throwError "Refusing to shadow existing declaration CovariantDerivative.alternating_pullbackFiberwiseLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.alternating_pullbackFiberwiseLinearEquiv ``Submission.CovariantDerivative.alternating_pullbackFiberwiseLinearEquiv

open _root_.CovariantDerivative in
theorem alternating_secondCovDeriv_pullbackFiberwiseLinearEquiv
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : _root_.Bundle.TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))))
    (cov : CovariantDerivative I F₂ V₂) [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (base : CovariantDerivative I E (TangentSpace I : M → Type _)) (k : ℕ)
    {T : ∀ x, V₂ x [⋀^Fin k]→L[ℝ] ℝ} {x : M}
    (hT : ContMDiffAt I
      (I.prod 𝓘(ℝ, F₂ [⋀^Fin k]→L[ℝ] ℝ)) 2
      (fun y => (⟨y, T y⟩ : _root_.Bundle.TotalSpace
        (F₂ [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F₂ V₂ ℝ (Bundle.Trivial M ℝ)))) x)
    {Y : ∀ y, TangentSpace I y}
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Y) x)
    (X : TangentSpace I x) :
    let D := alternating
      (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) k
    let U := fun y => (T y).compContinuousLinearMap (φ y).toContinuousLinearMap
    D (fun y => D U y (Y y)) x X - D U x (base Y x X) =
      (alternating cov k (fun y => alternating cov k T y (Y y)) x X -
        alternating cov k T x (base Y x X)).compContinuousLinearMap
          (φ x).toContinuousLinearMap := by
  let _ : FiniteDimensional ℝ (F₂ [⋀^Fin k]→L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
      (Module.finBasis ℝ F₂)).finiteDimensional_of_finite
  let D := alternating
    (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) k
  let U := fun y => (T y).compContinuousLinearMap (φ y).toContinuousLinearMap
  let W := fun y => alternating cov k T y (Y y)
  have hTc := (inferInstance : _root_.CovariantDerivative.ContMDiffCovariantDerivative (alternating cov k) ∞).contMDiffAt
    (m := 1) hT (by norm_num)
  have hW := (hTc.mdifferentiableAt (by norm_num)).clm_bundle_apply hY
  have hφx := (hφ x).mdifferentiableAt (by norm_num)
  have hPW := hW.alternating_bundle_comp hφx
  have hTnear : ∀ᶠ y in 𝓝 x, MDifferentiableAt I
      (I.prod 𝓘(ℝ, F₂ [⋀^Fin k]→L[ℝ] ℝ))
      (fun z => (⟨z, T z⟩ : _root_.Bundle.TotalSpace
        (F₂ [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F₂ V₂ ℝ (Bundle.Trivial M ℝ)))) y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp
      (hT.of_le (by norm_num))).mono (fun _ hy => hy.mdifferentiableAt (by simp))
  have heq : ∀ᶠ y in 𝓝 x, D U y (Y y) =
      (W y).compContinuousLinearMap (φ y).toContinuousLinearMap := by
    filter_upwards [hTnear] with y hy
    exact alternating_pullbackFiberwiseLinearEquiv φ hφ cov k hy (Y y)
  have hleft : MDifferentiableAt I
      (I.prod 𝓘(ℝ, F₁ [⋀^Fin k]→L[ℝ] ℝ))
      (fun y => (⟨y, D U y (Y y)⟩ : _root_.Bundle.TotalSpace
        (F₁ [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F₁ V₁ ℝ (Bundle.Trivial M ℝ)))) x := by
    apply hPW.congr_of_eventuallyEq
    filter_upwards [heq] with y hy
    exact congrArg (fun v => (⟨y, v⟩ : _root_.Bundle.TotalSpace
      (F₁ [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) F₁ V₁ ℝ (Bundle.Trivial M ℝ)))) hy
  have houter := D.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hleft hPW Filter.univ_mem heq
  change D (fun y => D U y (Y y)) x X - D U x (base Y x X) = _
  rw [houter, alternating_pullbackFiberwiseLinearEquiv φ hφ cov k hW X,
    alternating_pullbackFiberwiseLinearEquiv φ hφ cov k
      (hT.mdifferentiableAt (by norm_num)) (base Y x X)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.alternating_secondCovDeriv_pullbackFiberwiseLinearEquiv then
    throwError "Refusing to shadow existing declaration CovariantDerivative.alternating_secondCovDeriv_pullbackFiberwiseLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.alternating_secondCovDeriv_pullbackFiberwiseLinearEquiv ``Submission.CovariantDerivative.alternating_secondCovDeriv_pullbackFiberwiseLinearEquiv


end CovariantDerivative

namespace DifferentialGeometry.Geometry.Connection

open _root_.CovariantDerivative _root_.Submission.CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

def alternatingCovariantDerivative
    (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative I (E [⋀^Fin s]→L[Real] Real)
      (fun x : M ↦ TangentSpace I x [⋀^Fin s]→L[Real] Real) where
  toFun a x :=
    ContinuousLinearMap.comp
      ContinuousMultilinearMap.alternatizationCLM
      (ContinuousLinearMap.comp
        (Tensor0SBundle.tensor0SSpaceFiberContinuousLinearEquiv
          (I := I) s x).toContinuousLinearMap
        ((Tensor0SNabla.tensor0SCovariantDerivative I M s cov)
          (fun y ↦ (a y).toContinuousMultilinearMap) x))
  isCovariantDerivativeOnUniv := by
    have heq : (fun a x =>
        ContinuousLinearMap.comp
          ContinuousMultilinearMap.alternatizationCLM
          (ContinuousLinearMap.comp
            (Tensor0SBundle.tensor0SSpaceFiberContinuousLinearEquiv
              (I := I) s x).toContinuousLinearMap
            ((Tensor0SNabla.tensor0SCovariantDerivative I M s cov)
              (fun y ↦ (a y).toContinuousMultilinearMap) x))
        ) = (cov.alternating s).toFun := by
      funext a x
      rw [Tensor0SNabla.tensor0SCovariantDerivative_eq_multilinear]
      rfl
    rw [heq]
    exact (cov.alternating s).isCovariantDerivativeOnUniv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.alternatingCovariantDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.alternatingCovariantDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.alternatingCovariantDerivative ``Submission.DifferentialGeometry.Geometry.Connection.alternatingCovariantDerivative

omit [CompleteSpace E] in
theorem alternatingCovariantDerivative_eq_alternating
    (s : ℕ) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    alternatingCovariantDerivative (I := I) s cov = cov.alternating s := by
  ext a x X v
  change ContinuousMultilinearMap.alternatizationCLM
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov
      (fun y => (a y).toContinuousMultilinearMap) x X) v = _
  rw [Tensor0SNabla.tensor0SCovariantDerivative_eq_multilinear]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.alternatingCovariantDerivative_eq_alternating then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.alternatingCovariantDerivative_eq_alternating"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.alternatingCovariantDerivative_eq_alternating ``Submission.DifferentialGeometry.Geometry.Connection.alternatingCovariantDerivative_eq_alternating

noncomputable instance alternatingCovariantDerivative_contMDiff
    (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative.ContMDiffCovariantDerivative
      (alternatingCovariantDerivative (I := I) s cov) ∞ := by
  rw [alternatingCovariantDerivative_eq_alternating]
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.alternatingCovariantDerivative_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.alternatingCovariantDerivative_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.alternatingCovariantDerivative_contMDiff ``Submission.DifferentialGeometry.Geometry.Connection.alternatingCovariantDerivative_contMDiff

end DifferentialGeometry.Geometry.Connection
