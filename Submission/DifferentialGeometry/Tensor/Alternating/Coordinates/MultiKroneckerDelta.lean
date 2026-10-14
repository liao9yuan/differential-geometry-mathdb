import Submission.DifferentialGeometry.Tensor.Alternating.Reindexing.Permutation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Equiv.Perm _root_.Submission.Equiv.Perm

namespace Fin
open _root_.Fin


open _root_.Fin in
noncomputable def multiKroneckerDelta {R : Type*} [CommRing R] {k n : ℕ}
    (I J : Fin k → Fin n) : R :=
  Matrix.det (fun i j : Fin k => if I i = J j then 1 else 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Fin.multiKroneckerDelta then
    throwError "Refusing to shadow existing declaration Fin.multiKroneckerDelta"
  Lean.modifyEnv fun env => Lean.addAlias env `Fin.multiKroneckerDelta ``Submission.Fin.multiKroneckerDelta

variable {R : Type*} [CommRing R] {k n : ℕ}

open _root_.Fin in
theorem multiKroneckerDelta_comp_perm
    {J : Fin k → Fin n} (hJ : Function.Injective J)
    (σ : Equiv.Perm (Fin k)) :
    multiKroneckerDelta (R := R) (J ∘ ⇑σ) J = (Equiv.Perm.sign σ : R) := by
  unfold multiKroneckerDelta
  simp only [Function.comp, hJ.eq_iff]
  rw [show (fun i j : Fin k => if σ i = j then (1 : R) else 0) =
    (1 : Matrix (Fin k) (Fin k) R).submatrix (⇑σ) id from by
    ext i j; simp [Matrix.submatrix_apply, Matrix.one_apply]]
  rw [Matrix.det_permute, Matrix.det_one, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Fin.multiKroneckerDelta_comp_perm then
    throwError "Refusing to shadow existing declaration Fin.multiKroneckerDelta_comp_perm"
  Lean.modifyEnv fun env => Lean.addAlias env `Fin.multiKroneckerDelta_comp_perm ``Submission.Fin.multiKroneckerDelta_comp_perm

open _root_.Fin in
theorem multiKroneckerDelta_eq_zero_of_not_injective_left
    {I J : Fin k → Fin n} (hI : ¬Function.Injective I) :
    multiKroneckerDelta (R := R) I J = 0 := by
  unfold multiKroneckerDelta
  obtain ⟨i₁, i₂, heq, hne⟩ := Function.not_injective_iff.mp hI
  exact Matrix.det_zero_of_row_eq hne (funext fun j => by rw [heq])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Fin.multiKroneckerDelta_eq_zero_of_not_injective_left then
    throwError "Refusing to shadow existing declaration Fin.multiKroneckerDelta_eq_zero_of_not_injective_left"
  Lean.modifyEnv fun env => Lean.addAlias env `Fin.multiKroneckerDelta_eq_zero_of_not_injective_left ``Submission.Fin.multiKroneckerDelta_eq_zero_of_not_injective_left

open _root_.Fin in
theorem multiKroneckerDelta_eq_zero_of_not_injective_right
    {I J : Fin k → Fin n} (hJ : ¬Function.Injective J) :
    multiKroneckerDelta (R := R) I J = 0 := by
  unfold multiKroneckerDelta
  obtain ⟨j₁, j₂, heq, hne⟩ := Function.not_injective_iff.mp hJ
  exact Matrix.det_zero_of_column_eq hne (fun r => by rw [heq])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Fin.multiKroneckerDelta_eq_zero_of_not_injective_right then
    throwError "Refusing to shadow existing declaration Fin.multiKroneckerDelta_eq_zero_of_not_injective_right"
  Lean.modifyEnv fun env => Lean.addAlias env `Fin.multiKroneckerDelta_eq_zero_of_not_injective_right ``Submission.Fin.multiKroneckerDelta_eq_zero_of_not_injective_right

open _root_.Fin in
theorem multiKroneckerDelta_eq_zero
    {I J : Fin k → Fin n}
    (h : ∀ σ : Equiv.Perm (Fin k), I ≠ J ∘ ⇑σ) :
    multiKroneckerDelta (R := R) I J = 0 := by
  by_cases hI : Function.Injective I
  · by_cases hJ : Function.Injective J
    · have ⟨i, hi⟩ : ∃ i, ∀ j, I i ≠ J j := by
        by_contra hall
        push Not at hall
        choose f hf using hall
        have hf_inj : Function.Injective f :=
          fun a b hab => hI (by rw [hf a, hf b, hab])
        exact h (Equiv.ofBijective f
          ((Fintype.bijective_iff_injective_and_card f).mpr
            ⟨hf_inj, rfl⟩)) (funext hf)
      unfold multiKroneckerDelta
      exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => if_neg (hi j))
    · exact multiKroneckerDelta_eq_zero_of_not_injective_right hJ
  · exact multiKroneckerDelta_eq_zero_of_not_injective_left hI

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Fin.multiKroneckerDelta_eq_zero then
    throwError "Refusing to shadow existing declaration Fin.multiKroneckerDelta_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Fin.multiKroneckerDelta_eq_zero ``Submission.Fin.multiKroneckerDelta_eq_zero

open _root_.Fin in
theorem multiKroneckerDelta_symm (I J : Fin k → Fin n) :
    multiKroneckerDelta (R := R) I J = multiKroneckerDelta J I := by
  unfold multiKroneckerDelta
  conv_lhs => erw [← Matrix.det_transpose]
  congr 1; ext i j
  change (if I j = J i then (1 : R) else 0) =
    (if J i = I j then 1 else 0)
  by_cases h : I j = J i
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (mt Eq.symm h)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Fin.multiKroneckerDelta_symm then
    throwError "Refusing to shadow existing declaration Fin.multiKroneckerDelta_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Fin.multiKroneckerDelta_symm ``Submission.Fin.multiKroneckerDelta_symm

open _root_.Fin in
theorem multiKroneckerDelta_comp_perm_left
    (I : Fin k → Fin n) (J : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) :
    multiKroneckerDelta (R := R) (I ∘ ⇑σ) J =
    (Equiv.Perm.sign σ : R) * multiKroneckerDelta I J := by
  unfold multiKroneckerDelta
  set M : Matrix (Fin k) (Fin k) R := fun i j => if I i = J j then 1 else 0
  have : (fun i j : Fin k => if (I ∘ ⇑σ) i = J j then (1 : R) else 0) = M.submatrix σ id := by
    ext i j
    rfl
  rw [this, Matrix.det_permute]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Fin.multiKroneckerDelta_comp_perm_left then
    throwError "Refusing to shadow existing declaration Fin.multiKroneckerDelta_comp_perm_left"
  Lean.modifyEnv fun env => Lean.addAlias env `Fin.multiKroneckerDelta_comp_perm_left ``Submission.Fin.multiKroneckerDelta_comp_perm_left

open _root_.Fin in
theorem multiKroneckerDelta_addCases_comm
    {d m n : ℕ} (I : Fin m → Fin d) (J : Fin n → Fin d)
    (v : Fin (m + n) → Fin d) :
    multiKroneckerDelta (R := R) (Fin.addCases J I)
      (v ∘ ⇑Fin.finAddCongr) =
    (-1 : R) ^ (m * n) *
      multiKroneckerDelta (Fin.addCases I J) v := by
  simp only [multiKroneckerDelta]
  erw [← Matrix.det_reindex_self Fin.finAddCongr]
  set τ := addCasesSwapPerm m n
  set M : Matrix (Fin (m + n)) (Fin (m + n)) R :=
    fun i j => if Fin.addCases I J i = v j then 1 else 0
  have h_eq : (Matrix.reindex Fin.finAddCongr Fin.finAddCongr)
      (fun i j =>
        if Fin.addCases J I i =
          (v ∘ ⇑Fin.finAddCongr) j then (1 : R) else 0) =
      M.submatrix τ id := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [      Function.comp_apply, M]
    have h_idx : @Fin.addCases n m (fun _ => Fin d) J I ((@Fin.finAddCongr n m).symm ⟨i, hi⟩) =
        @Fin.addCases m n (fun _ => Fin d) I J (τ ⟨i, hi⟩) := by
      unfold Fin.addCases Fin.finAddCongr finCongr τ addCasesSwapPerm
      simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
      by_cases h1 : i < n
      · simp only [h1, dite_true]
        have h2 : ¬(m + i < m) := by omega
        simp_all
      · simp only [h1, dite_false]
        have h2 : i - n < m := by omega
        simp_all
    change (if Fin.addCases J I (Fin.finAddCongr.symm ⟨i, hi⟩) = v ⟨j, hj⟩
      then (1 : R) else 0) =
      (if Fin.addCases I J (τ ⟨i, hi⟩) = v ⟨j, hj⟩ then 1 else 0)
    rw [h_idx]
  rw [h_eq, Matrix.det_permute]
  have h_sign : (↑(Equiv.Perm.sign τ) : R) = (-1 : R) ^ (m * n) := by
    rw [addCasesSwapPerm_sign]
    push_cast
    rfl
  rw [h_sign]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Fin.multiKroneckerDelta_addCases_comm then
    throwError "Refusing to shadow existing declaration Fin.multiKroneckerDelta_addCases_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `Fin.multiKroneckerDelta_addCases_comm ``Submission.Fin.multiKroneckerDelta_addCases_comm

open _root_.Fin in
theorem multiKroneckerDelta_addCases_assoc
    {d m n p : ℕ} (I : Fin m → Fin d) (J : Fin n → Fin d) (K : Fin p → Fin d)
    (v : Fin (m + n + p) → Fin d) :
    multiKroneckerDelta (R := R)
      (fun i => Fin.addCases I (fun j => Fin.addCases J K j) i)
      (v ∘ ⇑Fin.finAssoc.symm) =
    multiKroneckerDelta
      (fun i => Fin.addCases (fun j => Fin.addCases I J j) K i) v := by
  have h_add (i : Fin (m + n + p)) :
      @Fin.addCases m (n + p) (fun _ => Fin d) I
          (fun j => @Fin.addCases n p (fun _ => Fin d) J K j)
          (@Fin.finAssoc m n p i) =
        @Fin.addCases (m + n) p (fun _ => Fin d)
          (fun j => @Fin.addCases m n (fun _ => Fin d) I J j) K i := by
    refine Fin.addCases ?_ ?_ i
    · intro q
      refine Fin.addCases ?_ ?_ q
      · intro a
        have h : @Fin.finAssoc m n p (Fin.castAdd p (Fin.castAdd n a)) =
            Fin.castAdd (n + p) a := by
          apply Fin.ext
          rfl
        rw [h]
        exact (@Fin.addCases_left m (n + p) (fun _ => Fin d) I
          (fun j => @Fin.addCases n p (fun _ => Fin d) J K j) a).trans
          ((@Fin.addCases_left m n (fun _ => Fin d) I J a).symm.trans
            (@Fin.addCases_left (m + n) p (fun _ => Fin d)
              (fun j => @Fin.addCases m n (fun _ => Fin d) I J j)
              K (Fin.castAdd n a)).symm)
      · intro b
        have h : @Fin.finAssoc m n p (Fin.castAdd p (Fin.natAdd m b)) =
            Fin.natAdd m (Fin.castAdd p b) := by
          apply Fin.ext
          rfl
        rw [h]
        exact (@Fin.addCases_right m (n + p) (fun _ => Fin d) I
          (fun j => @Fin.addCases n p (fun _ => Fin d) J K j)
          (Fin.castAdd p b)).trans
          ((@Fin.addCases_left n p (fun _ => Fin d) J K b).trans
            ((@Fin.addCases_right m n (fun _ => Fin d) I J b).symm.trans
              (@Fin.addCases_left (m + n) p (fun _ => Fin d)
                (fun j => @Fin.addCases m n (fun _ => Fin d) I J j)
                K (Fin.natAdd m b)).symm))
    · intro c
      have h : @Fin.finAssoc m n p (Fin.natAdd (m + n) c) =
          Fin.natAdd m (Fin.natAdd n c) := by
        apply Fin.ext
        change (m + n) + c = m + (n + c)
        omega
      rw [h]
      exact (@Fin.addCases_right m (n + p) (fun _ => Fin d) I
        (fun j => @Fin.addCases n p (fun _ => Fin d) J K j)
        (Fin.natAdd n c)).trans
        ((@Fin.addCases_right n p (fun _ => Fin d) J K c).trans
          (@Fin.addCases_right (m + n) p (fun _ => Fin d)
            (fun j => @Fin.addCases m n (fun _ => Fin d) I J j) K c).symm)
  simp only [multiKroneckerDelta]
  erw [← Matrix.det_reindex_self Fin.finAssoc]
  congr 1
  ext i j
  change
    (if Fin.addCases I (fun q => Fin.addCases J K q) i =
        v ((@Fin.finAssoc m n p).symm j) then (1 : R) else 0) =
      (if Fin.addCases (fun q => Fin.addCases I J q) K
          ((@Fin.finAssoc m n p).symm i) =
        v ((@Fin.finAssoc m n p).symm j) then 1 else 0)
  rw [← h_add ((@Fin.finAssoc m n p).symm i), Equiv.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Fin.multiKroneckerDelta_addCases_assoc then
    throwError "Refusing to shadow existing declaration Fin.multiKroneckerDelta_addCases_assoc"
  Lean.modifyEnv fun env => Lean.addAlias env `Fin.multiKroneckerDelta_addCases_assoc ``Submission.Fin.multiKroneckerDelta_addCases_assoc

variable {𝕜 : Type*} [Field 𝕜]

open _root_.Classical in
open _root_.Fin in
theorem multiKroneckerDelta_cauchyBinet [CharZero 𝕜]
    {d m p : ℕ} (I : Fin m → Fin d) (J : Fin p → Fin d) (v : Fin (m + p) → Fin d) :
    ((↑(m.factorial * p.factorial) : 𝕜))⁻¹ •
      ∑ σ : Equiv.Perm (Fin (m + p)),
        Equiv.Perm.sign σ • (multiKroneckerDelta (R := 𝕜) I (v ∘ ⇑σ ∘ Fin.castAdd p) *
          multiKroneckerDelta (R := 𝕜) J (v ∘ ⇑σ ∘ Fin.natAdd m)) =
    multiKroneckerDelta (Fin.addCases I J) v := by
  have h_ne : (↑(m.factorial * p.factorial) : 𝕜) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_pos (Nat.factorial_pos m) (Nat.factorial_pos p)).ne'
  rw [inv_smul_eq_iff₀ h_ne]
  let A (σ : Equiv.Perm (Fin (m + p))) : Matrix (Fin m) (Fin m) 𝕜 :=
    fun i j => if I i = v (σ (Fin.castAdd p j)) then 1 else 0
  let B (σ : Equiv.Perm (Fin (m + p))) : Matrix (Fin p) (Fin p) 𝕜 :=
    fun i j => if J i = v (σ (Fin.natAdd m j)) then 1 else 0
  set M : Matrix (Fin (m + p)) (Fin (m + p)) 𝕜 :=
    fun a b => if Fin.addCases I J a = v b then 1 else 0 with hM_def
  change
    ∑ σ : Equiv.Perm (Fin (m + p)),
        Equiv.Perm.sign σ • (Matrix.det (A σ) * Matrix.det (B σ)) =
      (↑(m.factorial * p.factorial) : 𝕜) • Matrix.det M
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul,
    Nat.cast_smul_eq_nsmul 𝕜, nsmul_eq_mul]
  have h1 : ∀ (α : Equiv.Perm (Fin m)) (σ : Equiv.Perm (Fin (m + p))) (i : Fin m),
      A σ (α i) i =
      M (Fin.castAdd p (α i)) (σ (Fin.castAdd p i)) :=
    fun _ _ _ => by simp [A, hM_def, Fin.addCases_left]
  have h2 : ∀ (β : Equiv.Perm (Fin p)) (σ : Equiv.Perm (Fin (m + p))) (j : Fin p),
      B σ (β j) j =
      M (Fin.natAdd m (β j)) (σ (Fin.natAdd m j)) :=
    fun _ _ _ => by simp [B, hM_def, Fin.addCases_right]
  simp_rw [h1, h2]
  have h_inner : ∀ α : Equiv.Perm (Fin m), ∀ β : Equiv.Perm (Fin p),
      ∀ σ : Equiv.Perm (Fin (m + p)),
      ↑↑(Equiv.Perm.sign σ) * (↑↑(Equiv.Perm.sign α) *
        ∏ i, M (Fin.castAdd p (α i)) (σ (Fin.castAdd p i))) *
      (↑↑(Equiv.Perm.sign β) *
        ∏ i, M (Fin.natAdd m (β i)) (σ (Fin.natAdd m i))) =
      ↑↑(Equiv.Perm.sign α) * ↑↑(Equiv.Perm.sign β) *
      (↑↑(Equiv.Perm.sign σ) *
        ((∏ i, M (Fin.castAdd p (α i)) (σ (Fin.castAdd p i))) *
         (∏ i, M (Fin.natAdd m (β i)) (σ (Fin.natAdd m i))))) := by
    intros; ring
  have h_sum : ∀ α : Equiv.Perm (Fin m), ∀ β : Equiv.Perm (Fin p),
      ∑ σ : Equiv.Perm (Fin (m + p)),
        ↑↑(Equiv.Perm.sign σ) * (↑↑(Equiv.Perm.sign α) *
          ∏ i, M (Fin.castAdd p (α i)) (σ (Fin.castAdd p i))) *
        (↑↑(Equiv.Perm.sign β) *
          ∏ i, M (Fin.natAdd m (β i)) (σ (Fin.natAdd m i))) =
      M.det := by
    intro α β
    simp_rw [h_inner α β, ← Finset.mul_sum, inner_sum_eq_det M α β]
    have hsα : (↑↑(Equiv.Perm.sign α) : 𝕜) * ↑↑(Equiv.Perm.sign α) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign α) with h | h <;> simp [h]
    have hsβ : (↑↑(Equiv.Perm.sign β) : 𝕜) * ↑↑(Equiv.Perm.sign β) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign β) with h | h <;> simp [h]
    calc ↑↑(Equiv.Perm.sign α) * ↑↑(Equiv.Perm.sign β) *
          (↑↑(Equiv.Perm.sign α) * ↑↑(Equiv.Perm.sign β) * M.det)
        = (↑↑(Equiv.Perm.sign α) * ↑↑(Equiv.Perm.sign α)) *
          ((↑↑(Equiv.Perm.sign β) * ↑↑(Equiv.Perm.sign β)) * M.det) := by ring
      _ = 1 * (1 * M.det) := by rw [hsα, hsβ]
      _ = M.det := by ring
  simp_rw [Fintype.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ (α := Equiv.Perm (Fin (m + p))))]
  simp_rw [show ∀ α : Equiv.Perm (Fin m),
    ∑ σ : Equiv.Perm (Fin (m + p)), ∑ β : Equiv.Perm (Fin p),
      ↑↑(Equiv.Perm.sign σ) *
        ((↑↑(Equiv.Perm.sign α) * ∏ i, M (Fin.castAdd p (α i)) (σ (Fin.castAdd p i))) *
          (↑↑(Equiv.Perm.sign β) * ∏ i, M (Fin.natAdd m (β i)) (σ (Fin.natAdd m i)))) =
    ∑ β : Equiv.Perm (Fin p), ∑ σ : Equiv.Perm (Fin (m + p)),
      ↑↑(Equiv.Perm.sign σ) *
        ((↑↑(Equiv.Perm.sign α) * ∏ i, M (Fin.castAdd p (α i)) (σ (Fin.castAdd p i))) *
          (↑↑(Equiv.Perm.sign β) * ∏ i, M (Fin.natAdd m (β i)) (σ (Fin.natAdd m i))))
    from fun _ => Finset.sum_comm]
  simp_rw [show ∀ (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin p))
    (σ : Equiv.Perm (Fin (m + p))),
    ↑↑(Equiv.Perm.sign σ) *
      ((↑↑(Equiv.Perm.sign α) * ∏ i, M (Fin.castAdd p (α i)) (σ (Fin.castAdd p i))) *
        (↑↑(Equiv.Perm.sign β) * ∏ i, M (Fin.natAdd m (β i)) (σ (Fin.natAdd m i)))) =
    ↑↑(Equiv.Perm.sign σ) * (↑↑(Equiv.Perm.sign α) *
      ∏ i, M (Fin.castAdd p (α i)) (σ (Fin.castAdd p i))) *
    (↑↑(Equiv.Perm.sign β) *
      ∏ i, M (Fin.natAdd m (β i)) (σ (Fin.natAdd m i))) from fun _ _ _ => by ring,
    h_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [show M.det = ∑ σ, ↑↑(Equiv.Perm.sign σ) *
    ∏ i, (if Fin.addCases I J (σ i) = v i then (1 : 𝕜) else 0) from by
      rw [Matrix.det_apply]; congr 1; ext σ
      simp [Units.smul_def, zsmul_eq_mul, hM_def]]
  simp only [Finset.smul_sum, nsmul_eq_mul, Nat.cast_mul]
  congr 1; ext σ; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Fin.multiKroneckerDelta_cauchyBinet then
    throwError "Refusing to shadow existing declaration Fin.multiKroneckerDelta_cauchyBinet"
  Lean.modifyEnv fun env => Lean.addAlias env `Fin.multiKroneckerDelta_cauchyBinet ``Submission.Fin.multiKroneckerDelta_cauchyBinet

end Fin
