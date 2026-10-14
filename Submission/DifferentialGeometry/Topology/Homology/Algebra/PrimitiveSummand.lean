/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.LinearAlgebra.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry

theorem surjective_snd_of_equiv_prod_fst_eq_zero
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : (A × ℤ) ≃+ (ℤ × B)) (he : ∀ a : A, (e (a, 0)).1 = 0) :
    Function.Surjective (fun a : A => (e (a, 0)).2) := by
  have hfst (a : A) (n : ℤ) : (e (a, n)).1 = n * (e (0, 1)).1 := by
    have hsplit : (a, n) = (a, 0) + n • ((0 : A), (1 : ℤ)) := by simp
    rw [hsplit, map_add, map_zsmul]
    change (e (a, 0)).1 + n • (e (0, 1)).1 = _
    simp only [he, zero_add, zsmul_eq_mul, Int.cast_id]
  have hnz : (e (0, 1)).1 ≠ 0 := by
    obtain ⟨⟨a, n⟩, h⟩ := e.surjective (1, 0)
    intro hz
    have hfirst := congrArg Prod.fst h
    rw [hfst, hz, _root_.MulZeroClass.mul_zero] at hfirst
    exact zero_ne_one hfirst
  intro b
  obtain ⟨⟨a, n⟩, h⟩ := e.surjective (0, b)
  have hn : n = 0 := by
    have hfirst := congrArg Prod.fst h
    rw [hfst] at hfirst
    exact (mul_eq_zero.mp hfirst).resolve_right hnz
  subst n
  exact ⟨a, congrArg Prod.snd h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.surjective_snd_of_equiv_prod_fst_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.surjective_snd_of_equiv_prod_fst_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.surjective_snd_of_equiv_prod_fst_eq_zero ``Submission.DifferentialGeometry.surjective_snd_of_equiv_prod_fst_eq_zero

end DifferentialGeometry
