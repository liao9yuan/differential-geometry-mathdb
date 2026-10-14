import Mathlib.GroupTheory.Perm.Fin

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.Topology.SphereSeparation

def eraseLastPermutation {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin n) :=
  (finSuccAboveEquiv (Fin.last n)).trans <|
    ((σ.subtypeEquiv fun x => by
      exact not_congr σ.injective.eq_iff.symm)).trans
      (finSuccAboveEquiv (σ (Fin.last n))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.eraseLastPermutation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.eraseLastPermutation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.eraseLastPermutation ``Submission.DifferentialGeometry.Topology.SphereSeparation.eraseLastPermutation

@[simp]
theorem succAbove_eraseLastPermutation {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    (σ (Fin.last n)).succAbove (eraseLastPermutation σ i) =
      σ i.castSucc := by
  change ((finSuccAboveEquiv (σ (Fin.last n)))
    ((finSuccAboveEquiv (σ (Fin.last n))).symm
      ((σ.subtypeEquiv fun x => by
        exact not_congr σ.injective.eq_iff.symm)
        (finSuccAboveEquiv (Fin.last n) i)))).1 = _
  rw [Equiv.apply_symm_apply]
  change σ ((finSuccAboveEquiv (Fin.last n) i).1) = σ i.castSucc
  rw [finSuccAboveEquiv_apply]
  simp only [Fin.succAbove_last_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.succAbove_eraseLastPermutation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.succAbove_eraseLastPermutation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.succAbove_eraseLastPermutation ``Submission.DifferentialGeometry.Topology.SphereSeparation.succAbove_eraseLastPermutation


def extendLastPermutation {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  τ.extendDomain Fin.castSuccEmb.toEquivRange

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.extendLastPermutation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.extendLastPermutation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.extendLastPermutation ``Submission.DifferentialGeometry.Topology.SphereSeparation.extendLastPermutation

@[simp]
theorem extendLastPermutation_apply_castSucc {n : ℕ}
    (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    extendLastPermutation τ i.castSucc = (τ i).castSucc := by
  change extendLastPermutation τ (Fin.castSuccEmb.toEquivRange i).1 =
    (Fin.castSuccEmb.toEquivRange (τ i)).1
  exact Equiv.Perm.extendDomain_apply_image τ Fin.castSuccEmb.toEquivRange i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.extendLastPermutation_apply_castSucc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.extendLastPermutation_apply_castSucc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.extendLastPermutation_apply_castSucc ``Submission.DifferentialGeometry.Topology.SphereSeparation.extendLastPermutation_apply_castSucc

@[simp]
theorem extendLastPermutation_apply_last {n : ℕ}
    (τ : Equiv.Perm (Fin n)) :
    extendLastPermutation τ (Fin.last n) = Fin.last n := by
  apply Equiv.Perm.extendDomain_apply_not_subtype
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.extendLastPermutation_apply_last then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.extendLastPermutation_apply_last"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.extendLastPermutation_apply_last ``Submission.DifferentialGeometry.Topology.SphereSeparation.extendLastPermutation_apply_last

@[simp]
theorem sign_extendLastPermutation {n : ℕ}
    (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (extendLastPermutation τ) = Equiv.Perm.sign τ := by
  exact Equiv.Perm.sign_extendDomain _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sign_extendLastPermutation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sign_extendLastPermutation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sign_extendLastPermutation ``Submission.DifferentialGeometry.Topology.SphereSeparation.sign_extendLastPermutation

theorem extendLast_eraseLast_trans_cycleIcc {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) :
    (extendLastPermutation (eraseLastPermutation σ)).trans
        (Fin.cycleIcc (σ (Fin.last n)) (Fin.last n)) = σ := by
  apply Equiv.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Equiv.trans_apply, extendLastPermutation_apply_last]
    exact Fin.cycleIcc_of_last (Fin.le_last _)
  · simp only [Equiv.trans_apply, extendLastPermutation_apply_castSucc]
    calc
      Fin.cycleIcc (σ (Fin.last n)) (Fin.last n)
          ((eraseLastPermutation σ j).castSucc) =
          (σ (Fin.last n)).succAbove (eraseLastPermutation σ j) := by
            simpa [Function.comp_apply] using congrFun
              (Fin.cycleIcc_comp_succAbove
                (σ (Fin.last n)) (Fin.last n) (Fin.le_last _))
              (eraseLastPermutation σ j)
      _ = σ j.castSucc := succAbove_eraseLastPermutation σ j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.extendLast_eraseLast_trans_cycleIcc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.extendLast_eraseLast_trans_cycleIcc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.extendLast_eraseLast_trans_cycleIcc ``Submission.DifferentialGeometry.Topology.SphereSeparation.extendLast_eraseLast_trans_cycleIcc

theorem sign_eq_sign_eraseLastPermutation_mul {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm.sign σ =
      Equiv.Perm.sign (eraseLastPermutation σ) *
        (-1 : ℤˣ) ^ ((Fin.last n : ℕ) - (σ (Fin.last n) : ℕ)) := by
  have hsign := congrArg Equiv.Perm.sign
    (extendLast_eraseLast_trans_cycleIcc σ)
  rw [Equiv.Perm.sign_trans, sign_extendLastPermutation,
    Fin.sign_cycleIcc_of_le (Fin.le_last _)] at hsign
  calc
    Equiv.Perm.sign σ =
        (-1 : ℤˣ) ^ ((Fin.last n : ℕ) - (σ (Fin.last n) : ℕ)) *
          Equiv.Perm.sign (eraseLastPermutation σ) := hsign.symm
    _ = _ := mul_comm _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sign_eq_sign_eraseLastPermutation_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sign_eq_sign_eraseLastPermutation_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sign_eq_sign_eraseLastPermutation_mul ``Submission.DifferentialGeometry.Topology.SphereSeparation.sign_eq_sign_eraseLastPermutation_mul

end DifferentialGeometry.Topology.SphereSeparation
