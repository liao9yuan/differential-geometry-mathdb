import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace LinearMap
open _root_.LinearMap

open _root_.LinearMap in
theorem injective_convex_combination_of_eqOn_ker
    {𝕜 E F : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
    (A B : E →ₗ[𝕜] F) (l : E →ₗ[𝕜] 𝕜) (m : F →ₗ[𝕜] 𝕜)
    (hA : Function.Injective A) (hagree : ∀ v, l v = 0 → A v = B v)
    {a b t : 𝕜} (ha : 0 < a) (hb : 0 < b)
    (hAl : m.comp A = a • l) (hBl : m.comp B = b • l)
    (ht : t ∈ Set.Icc (0 : 𝕜) 1) :
    Function.Injective ((1 - t) • A + t • B) := by
  have hpos : 0 < (1 - t) * a + t * b := by
    by_cases hzero : t = 0
    · simpa only [hzero, sub_zero, one_mul, _root_.MulZeroClass.zero_mul, add_zero] using ha
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) ha.le)
        (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm hzero)) hb)
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hma : m (A v) = a * l v := congrArg (fun L : E →ₗ[𝕜] 𝕜 => L v) hAl
  have hmb : m (B v) = b * l v := congrArg (fun L : E →ₗ[𝕜] 𝕜 => L v) hBl
  have hmv := congrArg m hv
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    smul_eq_mul, map_zero, hma, hmb] at hmv
  have hlv : l v = 0 := by
    apply (mul_eq_zero.mp (show ((1 - t) * a + t * b) * l v = 0 by nlinarith)).resolve_left
    exact hpos.ne'
  have hv' : A v = 0 := by
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, ← hagree v hlv,
      ← add_smul, sub_add_cancel, one_smul] using hv
  exact hA (hv'.trans (map_zero A).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LinearMap.injective_convex_combination_of_eqOn_ker then
    throwError "Refusing to shadow existing declaration LinearMap.injective_convex_combination_of_eqOn_ker"
  Lean.modifyEnv fun env => Lean.addAlias env `LinearMap.injective_convex_combination_of_eqOn_ker ``Submission.LinearMap.injective_convex_combination_of_eqOn_ker


open _root_.LinearMap in
theorem injective_convex_combination_of_eqOn_ker_id
    {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E]
    (B : E →ₗ[𝕜] E) (l : E →ₗ[𝕜] 𝕜) {n : E} (hn : l n = 1)
    (hfixed : ∀ v, l v = 0 → B v = v) (hpos : 0 < l (B n))
    {t : 𝕜} (ht : t ∈ Set.Icc (0 : 𝕜) 1) :
    Function.Injective ((1 - t) • (LinearMap.id : E →ₗ[𝕜] E) + t • B) := by
  have hBl : l.comp B = l (B n) • l := by
    ext v
    have hk : l (v - l v • n) = 0 := by simp [hn]
    have heq := congrArg l (hfixed _ hk)
    simp only [map_sub, map_smul, smul_eq_mul, hn, mul_one] at heq
    change l (B v) = l (B n) * l v
    nlinarith [heq]
  exact injective_convex_combination_of_eqOn_ker LinearMap.id B l l Function.injective_id
    (fun v hv => (hfixed v hv).symm) zero_lt_one hpos (by simp) hBl ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LinearMap.injective_convex_combination_of_eqOn_ker_id then
    throwError "Refusing to shadow existing declaration LinearMap.injective_convex_combination_of_eqOn_ker_id"
  Lean.modifyEnv fun env => Lean.addAlias env `LinearMap.injective_convex_combination_of_eqOn_ker_id ``Submission.LinearMap.injective_convex_combination_of_eqOn_ker_id
end LinearMap
