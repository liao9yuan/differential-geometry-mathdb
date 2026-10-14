import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
namespace DifferentialGeometry.Topology


theorem exists_small_injective_add {n : ℕ} (a : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Fin n → ℝ, ‖p‖ < ε ∧ _root_.Function.Injective (fun i => a i + p i) := by
  classical
  let B : Set ℝ := _root_.Set.range (fun q : Fin n × Fin n => (a q.2 - a q.1) / ((q.1.val : ℝ) - q.2.val))
  have hB : B.Finite := _root_.Set.finite_range _
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hI : (_root_.Set.Ioo (0 : ℝ) (ε / ((n : ℝ) + 1))).Infinite := _root_.Set.Ioo_infinite (div_pos hε hn)
  obtain ⟨t,htI,htB⟩ := (hI.sdiff hB).nonempty
  let p : Fin n → ℝ := fun i => t * i.val
  have hp : ‖p‖ < ε := by
    apply (pi_norm_lt_iff hε).mpr
    intro i
    have hi : (i.val : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (le_trans i.isLt.le (Nat.le_succ n))
    have hsmall : t * ((n : ℝ) + 1) < ε := (lt_div_iff₀ hn).mp htI.2
    change ‖t * (i.val : ℝ)‖ < ε
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg htI.1.le (Nat.cast_nonneg _))]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hi htI.1.le) hsmall
  refine ⟨p,hp,?_⟩
  intro i j hij
  by_contra hne
  have hden : (i.val : ℝ) - j.val ≠ 0 := by
    intro he
    apply hne
    apply Fin.ext
    exact_mod_cast (sub_eq_zero.mp he)
  have ht : t = (a j - a i) / ((i.val : ℝ) - j.val) := by
    apply (eq_div_iff hden).mpr
    change a i + t * i.val = a j + t * j.val at hij
    nlinarith
  apply htB
  exact ⟨(i,j),ht.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_small_injective_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_small_injective_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_small_injective_add ``Submission.DifferentialGeometry.Topology.exists_small_injective_add

end DifferentialGeometry.Topology

namespace Set
open _root_.Set

open _root_.Set _root_.Set.Finite in
theorem Finite.exists_finite_disjoint_inter_Ioo_nonempty
    {α : Type*} [Preorder α] [DenselyOrdered α] {s : Set α} (hs : s.Finite) :
    ∃ t : Set α, t.Finite ∧ Disjoint s t ∧
      ∀ a ∈ s, ∀ b ∈ s, a < b → (t ∩ _root_.Set.Ioo a b).Nonempty := by
  let P := {p : α × α | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2}
  have hP : P.Finite := (hs.prod hs).subset (fun _ hp => ⟨hp.1, hp.2.1⟩)
  let _ := hP.fintype
  have hex (p : P) : ∃ c : α, c ∈ _root_.Set.Ioo p.val.1 p.val.2 ∧ c ∉ s :=
    (_root_.Set.Ioo_infinite p.property.2.2).exists_notMem_finite hs
  choose c hc using hex
  refine ⟨range c, _root_.Set.finite_range c, ?_, ?_⟩
  · rw [_root_.Set.disjoint_left]
    rintro x hxs ⟨p, rfl⟩
    exact (hc p).2 hxs
  · intro a ha b hb hab
    let p : P := ⟨(a, b), ha, hb, hab⟩
    exact ⟨c p, _root_.Set.mem_range_self p, (hc p).1⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Set.Finite
  let env ← Lean.getEnv
  if env.contains `Set.Finite.exists_finite_disjoint_inter_Ioo_nonempty then
    throwError "Refusing to shadow existing declaration Set.Finite.exists_finite_disjoint_inter_Ioo_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `Set.Finite.exists_finite_disjoint_inter_Ioo_nonempty ``Submission.Set.Finite.exists_finite_disjoint_inter_Ioo_nonempty

end Set
