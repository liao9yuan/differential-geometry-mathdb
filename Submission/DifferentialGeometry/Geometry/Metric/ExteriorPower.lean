import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Mathlib.Analysis.InnerProductSpace.Dual
import Submission.DifferentialGeometry.Tensor.Alternating.Coordinates.Basis

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.BigOperators _root_.RealInnerProductSpace

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
private def musicalInverse (k : ℕ) :
    (E [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ⋀[ℝ]^k E := by
  let _ : CompleteSpace (⋀[ℝ]^k E) := FiniteDimensional.complete ℝ _
  exact (InnerProductSpace.toDual ℝ (⋀[ℝ]^k E)).symm.toLinearEquiv.toLinearMap.comp
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      (_root_.exteriorPower.alternatingMapLinearEquiv.toLinearMap.comp
        (ContinuousAlternatingMap.toAlternatingMapLinear (R := ℝ))))

run_cmd do
  let target := ``Submission.exteriorPower.musicalInverse
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `exteriorPower.musicalInverse target :: scope.openDecls } }

open _root_.exteriorPower in
private theorem musicalInverse_injective (k : ℕ) :
    Function.Injective (musicalInverse (E := E) k) := by
  let _ : CompleteSpace (⋀[ℝ]^k E) := FiniteDimensional.complete ℝ _
  exact (InnerProductSpace.toDual ℝ (⋀[ℝ]^k E)).symm.injective.comp
    (LinearMap.toContinuousLinearMap.injective.comp
      (_root_.exteriorPower.alternatingMapLinearEquiv.injective.comp
        ContinuousAlternatingMap.toAlternatingMap_injective))

run_cmd do
  let target := ``Submission.exteriorPower.musicalInverse_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `exteriorPower.musicalInverse_injective target :: scope.openDecls } }

open _root_.exteriorPower in
def musicalEquiv (k : ℕ) : (⋀[ℝ]^k E) ≃L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ :=
  (LinearEquiv.ofInjectiveOfFinrankEq (musicalInverse k) (musicalInverse_injective k)
    (by rw [ContinuousAlternatingMap.finrank_continuousAlternatingMap,
      exteriorPower.finrank_eq])).symm.toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.musicalEquiv then
    throwError "Refusing to shadow existing declaration exteriorPower.musicalEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.musicalEquiv ``Submission.exteriorPower.musicalEquiv

open _root_.exteriorPower in
theorem inner_musicalEquiv_symm_ιMulti (k : ℕ)
    (a : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) :
    ⟪(musicalEquiv k).symm a, _root_.exteriorPower.ιMulti ℝ k v⟫ = a v := by
  let _ : CompleteSpace (⋀[ℝ]^k E) := FiniteDimensional.complete ℝ _
  change ⟪(InnerProductSpace.toDual ℝ (⋀[ℝ]^k E)).symm
    (LinearMap.toContinuousLinearMap (_root_.exteriorPower.alternatingMapLinearEquiv a.toAlternatingMap)),
      _root_.exteriorPower.ιMulti ℝ k v⟫ = a v
  rw [InnerProductSpace.toDual_symm_apply]
  exact _root_.exteriorPower.alternatingMapLinearEquiv_apply_ιMulti a.toAlternatingMap v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.inner_musicalEquiv_symm_ιMulti then
    throwError "Refusing to shadow existing declaration exteriorPower.inner_musicalEquiv_symm_ιMulti"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.inner_musicalEquiv_symm_ιMulti ``Submission.exteriorPower.inner_musicalEquiv_symm_ιMulti

open _root_.exteriorPower in
theorem musicalEquiv_apply (k : ℕ) (u : ⋀[ℝ]^k E) (v : Fin k → E) :
    musicalEquiv k u v = ⟪u, _root_.exteriorPower.ιMulti ℝ k v⟫ := by
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using
    (inner_musicalEquiv_symm_ιMulti k (musicalEquiv k u) v).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.musicalEquiv_apply then
    throwError "Refusing to shadow existing declaration exteriorPower.musicalEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.musicalEquiv_apply ``Submission.exteriorPower.musicalEquiv_apply

open _root_.exteriorPower in
theorem musicalEquiv_ιMulti_apply (k : ℕ) (u v : Fin k → E) :
    musicalEquiv k (_root_.exteriorPower.ιMulti ℝ k u) v =
      Matrix.det (Matrix.of fun i j => ⟪u j, v i⟫) := by
  rw [musicalEquiv_apply, _root_.exteriorPower.inner_ιMulti_ιMulti]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.musicalEquiv_ιMulti_apply then
    throwError "Refusing to shadow existing declaration exteriorPower.musicalEquiv_ιMulti_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.musicalEquiv_ιMulti_apply ``Submission.exteriorPower.musicalEquiv_ιMulti_apply

open _root_.exteriorPower in
theorem alternatingMapLinearEquiv_musicalEquiv (k : ℕ) (u v : ⋀[ℝ]^k E) :
    alternatingMapLinearEquiv (musicalEquiv k u).toAlternatingMap v = ⟪u, v⟫ := by
  have h : _root_.exteriorPower.alternatingMapLinearEquiv (musicalEquiv k u).toAlternatingMap =
      innerₗ (⋀[ℝ]^k E) u := by
    apply _root_.exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    exact (_root_.exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ w).trans (musicalEquiv_apply k u w)
  exact LinearMap.congr_fun h v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.alternatingMapLinearEquiv_musicalEquiv then
    throwError "Refusing to shadow existing declaration exteriorPower.alternatingMapLinearEquiv_musicalEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.alternatingMapLinearEquiv_musicalEquiv ``Submission.exteriorPower.alternatingMapLinearEquiv_musicalEquiv

omit [FiniteDimensional ℝ E] in
open _root_.exteriorPower in
private theorem sum_mul_prod_inner {ι : Type*} [Fintype ι]
    (k : ℕ) (e : OrthonormalBasis ι ℝ E)
    (a : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) :
    (∑ j : Fin k → ι, a (fun i => e (j i)) *
      ∏ i, ⟪v i, e (j i)⟫) = a v := by
  classical
  have h := a.toContinuousMultilinearMap.map_sum
    (fun i j => ⟪v i, e j⟫ • e j)
  have he : (fun i => ∑ j, ⟪v i, e j⟫ • e j) = v := by
    funext i
    simpa only [real_inner_comm] using e.sum_repr' (v i)
  rw [he] at h
  simpa only [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_comm,
    ContinuousAlternatingMap.coe_toContinuousMultilinearMap] using h.symm

run_cmd do
  let target := ``Submission.exteriorPower.sum_mul_prod_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `exteriorPower.sum_mul_prod_inner target :: scope.openDecls } }

open _root_.exteriorPower in
private theorem sum_mul_musicalEquiv_ιMulti {ι : Type*} [Fintype ι]
    (k : ℕ) (e : OrthonormalBasis ι ℝ E)
    (a : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) :
    (∑ j : Fin k → ι, a (fun i => e (j i)) *
      musicalEquiv k (_root_.exteriorPower.ιMulti ℝ k v) (fun i => e (j i))) =
        (k.factorial : ℝ) * a v := by
  classical
  have hdet (j : Fin k → ι) :
      musicalEquiv k (_root_.exteriorPower.ιMulti ℝ k v) (fun i => e (j i)) =
        Matrix.det (Matrix.of fun i l => ⟪v i, e (j l)⟫) := by
    rw [musicalEquiv_ιMulti_apply, ← Matrix.det_transpose]
    rfl
  simp only [hdet, Matrix.det_apply, Matrix.of_apply,
    Finset.mul_sum, Units.smul_def, zsmul_eq_mul]
  rw [Finset.sum_comm]
  have hterm (σ : Equiv.Perm (Fin k)) :
      (∑ j : Fin k → ι, a (fun i => e (j i)) *
        ((σ.sign : ℝ) * ∏ i, ⟪v (σ i), e (j i)⟫)) = a v := by
    calc
      _ = (σ.sign : ℝ) *
          ∑ j : Fin k → ι, a (fun i => e (j i)) *
            ∏ i, ⟪v (σ i), e (j i)⟫ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (σ.sign : ℝ) * a (v ∘ σ) :=
        congrArg ((σ.sign : ℝ) * ·) (sum_mul_prod_inner k e a (v ∘ σ))
      _ = a v := by
        change (σ.sign : ℝ) * a.toAlternatingMap (v ∘ σ) = a.toAlternatingMap v
        rw [a.toAlternatingMap.map_perm v σ]
        simp only [Units.smul_def, zsmul_eq_mul, ← mul_assoc]
        norm_cast
        rw [Int.units_mul_self]
        simp
  calc
    _ = ∑ _σ : Equiv.Perm (Fin k), a v :=
      Finset.sum_congr rfl (fun σ _ => hterm σ)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, nsmul_eq_mul]

run_cmd do
  let target := ``Submission.exteriorPower.sum_mul_musicalEquiv_ιMulti
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `exteriorPower.sum_mul_musicalEquiv_ιMulti target :: scope.openDecls } }

open _root_.exteriorPower in
theorem sum_mul_eq_factorial_mul_inner {ι : Type*} [Fintype ι]
    (k : ℕ) (e : OrthonormalBasis ι ℝ E)
    (a b : E [⋀^Fin k]→L[ℝ] ℝ) :
    (∑ j : Fin k → ι, a (fun i => e (j i)) * b (fun i => e (j i))) =
      (k.factorial : ℝ) * ⟪(musicalEquiv k).symm a, (musicalEquiv k).symm b⟫ := by
  classical
  let L : (⋀[ℝ]^k E) →ₗ[ℝ] ℝ :=
    { toFun := fun w => ∑ j : Fin k → ι,
        a (fun i => e (j i)) * musicalEquiv k w (fun i => e (j i))
      map_add' := fun w z => by
        simp only [map_add, ContinuousAlternatingMap.add_apply, mul_add,
          Finset.sum_add_distrib]
      map_smul' := fun c w => by
        simp only [map_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring }
  let R : (⋀[ℝ]^k E) →ₗ[ℝ] ℝ :=
    (k.factorial : ℝ) • innerₗ (⋀[ℝ]^k E) ((musicalEquiv k).symm a)
  have h : L = R := by
    apply _root_.exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change (∑ j : Fin k → ι, a (fun i => e (j i)) *
      musicalEquiv k (_root_.exteriorPower.ιMulti ℝ k v) (fun i => e (j i))) =
        (k.factorial : ℝ) * ⟪(musicalEquiv k).symm a, _root_.exteriorPower.ιMulti ℝ k v⟫
    rw [inner_musicalEquiv_symm_ιMulti]
    exact sum_mul_musicalEquiv_ιMulti k e a v
  have heval := LinearMap.congr_fun h ((musicalEquiv k).symm b)
  simpa only [L, R, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul,
    ContinuousLinearEquiv.apply_symm_apply] using heval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.sum_mul_eq_factorial_mul_inner then
    throwError "Refusing to shadow existing declaration exteriorPower.sum_mul_eq_factorial_mul_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.sum_mul_eq_factorial_mul_inner ``Submission.exteriorPower.sum_mul_eq_factorial_mul_inner

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

open _root_.exteriorPower in
theorem inner_map_linearIsometry (k : ℕ) (f : E →ₗᵢ[ℝ] F)
    (u v : ⋀[ℝ]^k E) :
    ⟪exteriorPower.map k f.toLinearMap u,
      exteriorPower.map k f.toLinearMap v⟫ = ⟪u, v⟫ := by
  let m : (⋀[ℝ]^k E) →ₗ[ℝ] (⋀[ℝ]^k F) := exteriorPower.map k f.toLinearMap
  have h_for (u : Fin k → E) :
      (innerₗ (⋀[ℝ]^k F) (m (_root_.exteriorPower.ιMulti ℝ k u))).comp m =
        innerₗ (⋀[ℝ]^k E) (_root_.exteriorPower.ιMulti ℝ k u) := by
    apply _root_.exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change ⟪m (_root_.exteriorPower.ιMulti ℝ k u), m (_root_.exteriorPower.ιMulti ℝ k v)⟫ =
      ⟪ιMulti ℝ k u, _root_.exteriorPower.ιMulti ℝ k v⟫
    rw [_root_.exteriorPower.map_apply_ιMulti, _root_.exteriorPower.map_apply_ιMulti, _root_.exteriorPower.inner_ιMulti_ιMulti,
      _root_.exteriorPower.inner_ιMulti_ιMulti]
    apply congrArg Matrix.det
    funext i j
    change ⟪f (u j), f (v i)⟫ = ⟪u j, v i⟫
    exact f.inner_map_map _ _
  let B : (⋀[ℝ]^k E) →ₗ[ℝ] (⋀[ℝ]^k E →ₗ[ℝ] ℝ) :=
    { toFun := fun x => (innerₗ (⋀[ℝ]^k F) (m x)).comp m
      map_add' := by intros; ext y; simp
      map_smul' := by intros; ext y; simp [smul_eq_mul] }
  let C : (⋀[ℝ]^k E) →ₗ[ℝ] (⋀[ℝ]^k E →ₗ[ℝ] ℝ) :=
    { toFun := fun x => innerₗ (⋀[ℝ]^k E) x
      map_add' := by intros; ext y; simp
      map_smul' := by intros; ext y; simp [smul_eq_mul] }
  have hBC : B = C := by
    apply _root_.exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro u
    change (innerₗ (⋀[ℝ]^k F) (m (_root_.exteriorPower.ιMulti ℝ k u))).comp m =
      innerₗ (⋀[ℝ]^k E) (_root_.exteriorPower.ιMulti ℝ k u)
    exact h_for u
  exact LinearMap.congr_fun (LinearMap.congr_fun hBC u) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.inner_map_linearIsometry then
    throwError "Refusing to shadow existing declaration exteriorPower.inner_map_linearIsometry"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.inner_map_linearIsometry ``Submission.exteriorPower.inner_map_linearIsometry

open _root_.exteriorPower in
theorem musicalEquiv_map_apply (k : ℕ) (f : E →ₗᵢ[ℝ] F)
    (u : ⋀[ℝ]^k E) (v : Fin k → E) :
    musicalEquiv k (E := F) (exteriorPower.map k f.toLinearMap u)
        (fun i => f (v i)) = musicalEquiv k (E := E) u v := by
  rw [musicalEquiv_apply, musicalEquiv_apply]
  have hm : exteriorPower.map k f.toLinearMap (_root_.exteriorPower.ιMulti ℝ k v) =
      ιMulti ℝ k (fun i => f (v i)) := by
    rw [_root_.exteriorPower.map_apply_ιMulti]
    rfl
  rw [← hm]
  exact inner_map_linearIsometry k f u (_root_.exteriorPower.ιMulti ℝ k v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.musicalEquiv_map_apply then
    throwError "Refusing to shadow existing declaration exteriorPower.musicalEquiv_map_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.musicalEquiv_map_apply ``Submission.exteriorPower.musicalEquiv_map_apply

open _root_.exteriorPower in
theorem musicalEquiv_map (k : ℕ) (f : E ≃ₗᵢ[ℝ] F) (u : ⋀[ℝ]^k E) :
    musicalEquiv k (_root_.exteriorPower.map k f.toLinearEquiv.toLinearMap u) =
      (musicalEquiv k u).compContinuousLinearMap
        f.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousAlternatingMap.ext
  intro v
  have h := musicalEquiv_map_apply k f.toLinearIsometry u (fun i => f.symm (v i))
  change musicalEquiv k (_root_.exteriorPower.map k f.toLinearIsometry.toLinearMap u) v =
    musicalEquiv k u (fun i => f.symm (v i))
  simpa only [LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.apply_symm_apply] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.musicalEquiv_map then
    throwError "Refusing to shadow existing declaration exteriorPower.musicalEquiv_map"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.musicalEquiv_map ``Submission.exteriorPower.musicalEquiv_map

open _root_.exteriorPower in
theorem map_musicalEquiv_symm (k : ℕ) (f : E ≃ₗᵢ[ℝ] F)
    (a : E [⋀^Fin k]→L[ℝ] ℝ) :
    _root_.exteriorPower.map k f.toLinearEquiv.toLinearMap ((musicalEquiv k).symm a) =
      (musicalEquiv k).symm (a.compContinuousLinearMap
        f.symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply (musicalEquiv k).injective
  rw [musicalEquiv_map, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.map_musicalEquiv_symm then
    throwError "Refusing to shadow existing declaration exteriorPower.map_musicalEquiv_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.map_musicalEquiv_symm ``Submission.exteriorPower.map_musicalEquiv_symm

end exteriorPower
