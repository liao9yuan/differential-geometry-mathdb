import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set

noncomputable section

variable {α : Type*} [LinearOrder α]

theorem level_set_eq_interval_of_monotoneOn_left_constant
    {f : ℝ → α} {a b : ℝ} {q : α}
    (hmono : MonotoneOn f (_root_.Set.Icc a b))
    (hleft : ∀ t ∈ _root_.Set.Ioc a b, ∃ ε > 0,
      ∀ s ∈ _root_.Set.Icc a b, t - ε < s → s ≤ t → f s = f t)
    (hne : {t | t ∈ _root_.Set.Icc a b ∧ f t = q}.Nonempty) :
    ∃ l u : ℝ, a ≤ l ∧ l ≤ u ∧ u ≤ b ∧
      ({t | t ∈ _root_.Set.Icc a b ∧ f t = q} = _root_.Set.Icc a u ∧ f a = q ∨
        {t | t ∈ _root_.Set.Icc a b ∧ f t = q} = _root_.Set.Ioc l u ∧ f a ≠ q) := by
  let C := {t | t ∈ _root_.Set.Icc a b ∧ f t = q}
  have hCne : C.Nonempty := hne
  have hCbelow : BddBelow C := ⟨a, fun t ht => ht.1.1⟩
  have hCabove : BddAbove C := ⟨b, fun t ht => ht.1.2⟩
  let l := _root_.InfSet.sInf C
  let u := _root_.SupSet.sSup C
  have hal : a ≤ l := le_csInf hCne (fun t ht => ht.1.1)
  have hub : u ≤ b := csSup_le hCne (fun t ht => ht.1.2)
  obtain ⟨z, hz⟩ := hCne
  have hCne : C.Nonempty := ⟨z, hz⟩
  have hlz : l ≤ z := csInf_le hCbelow hz
  have hzu : z ≤ u := le_csSup hCabove hz
  have hlu : l ≤ u := hlz.trans hzu
  have hau : a ≤ u := hal.trans hlu
  have hu : u ∈ C := by
    by_cases hua : u = a
    · have hza : z = a := le_antisymm (hzu.trans_eq hua) hz.1.1
      simpa only [hua, hza] using hz
    · have hau' : a < u := lt_of_le_of_ne hau (Ne.symm hua)
      obtain ⟨ε, hε, hconst⟩ := hleft u ⟨hau', hub⟩
      obtain ⟨w, hw, huw⟩ := exists_lt_of_lt_csSup hCne
        (show u - ε < _root_.SupSet.sSup C by dsimp [u]; linarith)
      have hwu : w ≤ u := le_csSup hCabove hw
      exact ⟨⟨hau, hub⟩, (hconst w hw.1 huw hwu).symm.trans hw.2⟩
  refine ⟨l, u, hal, hlu, hub, ?_⟩
  by_cases hqa : f a = q
  · left
    refine ⟨?_, hqa⟩
    ext t
    constructor
    · intro ht
      exact ⟨ht.1.1, le_csSup hCabove ht⟩
    · intro ht
      have htab : t ∈ _root_.Set.Icc a b := ⟨ht.1, ht.2.trans hub⟩
      have hat : f a ≤ f t := hmono ⟨le_rfl, hau.trans hub⟩ htab ht.1
      have htu : f t ≤ f u := hmono htab hu.1 ht.2
      exact ⟨htab, le_antisymm (htu.trans_eq hu.2) (hqa.symm.trans_le hat)⟩
  · right
    have hlnot : l ∉ C := by
      intro hl
      have hla : l ≠ a := by
        intro heq
        exact hqa (heq ▸ hl.2)
      have hal' : a < l := lt_of_le_of_ne hal (Ne.symm hla)
      obtain ⟨ε, hε, hconst⟩ := hleft l ⟨hal', hlu.trans hub⟩
      obtain ⟨w, hw, hwl⟩ := exists_between
        (max_lt hal' (show l - ε < l by linarith))
      have hwab : w ∈ _root_.Set.Icc a b :=
        ⟨(le_max_left a (l - ε)).trans hw.le, hwl.le.trans (hlu.trans hub)⟩
      have hwC : w ∈ C :=
        ⟨hwab, (hconst w hwab ((le_max_right a (l - ε)).trans_lt hw) hwl.le).trans hl.2⟩
      exact (not_lt_of_ge (csInf_le hCbelow hwC)) hwl
    refine ⟨?_, hqa⟩
    ext t
    constructor
    · intro ht
      exact ⟨lt_of_le_of_ne (csInf_le hCbelow ht)
        (fun heq => hlnot (heq ▸ ht)), le_csSup hCabove ht⟩
    · intro ht
      obtain ⟨w, hw, hwt⟩ := exists_lt_of_csInf_lt hCne
        (show _root_.InfSet.sInf C < t from ht.1)
      have htab : t ∈ _root_.Set.Icc a b := ⟨hal.trans ht.1.le, ht.2.trans hub⟩
      have hwt' : f w ≤ f t := hmono hw.1 htab hwt.le
      have htu : f t ≤ f u := hmono htab hu.1 ht.2
      exact ⟨htab, le_antisymm (htu.trans_eq hu.2) (hw.2.symm.trans_le hwt')⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `level_set_eq_interval_of_monotoneOn_left_constant then
    throwError "Refusing to shadow existing declaration level_set_eq_interval_of_monotoneOn_left_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `level_set_eq_interval_of_monotoneOn_left_constant ``Submission.level_set_eq_interval_of_monotoneOn_left_constant


theorem exists_finite_level_set_partition_of_monotoneOn_left_constant
    {f : ℝ → α} {a b : ℝ}
    (hfinite : (f '' _root_.Set.Icc a b).Finite)
    (hmono : MonotoneOn f (_root_.Set.Icc a b))
    (hleft : ∀ t ∈ _root_.Set.Ioc a b, ∃ ε > 0,
      ∀ s ∈ _root_.Set.Icc a b, t - ε < s → s ≤ t → f s = f t) :
    ∃ Q : Finset α,
      _root_.Set.Icc a b = ⋃ q ∈ Q, {t | t ∈ _root_.Set.Icc a b ∧ f t = q} ∧
      (Q : Set α).PairwiseDisjoint (fun q => {t | t ∈ _root_.Set.Icc a b ∧ f t = q}) ∧
      ∀ q ∈ Q, {t | t ∈ _root_.Set.Icc a b ∧ f t = q}.Nonempty ∧
        ∃ l u : ℝ, a ≤ l ∧ l ≤ u ∧ u ≤ b ∧
          ({t | t ∈ _root_.Set.Icc a b ∧ f t = q} = _root_.Set.Icc a u ∧ f a = q ∨
            {t | t ∈ _root_.Set.Icc a b ∧ f t = q} = _root_.Set.Ioc l u ∧ f a ≠ q) := by
  classical
  refine ⟨hfinite.toFinset, ?_, ?_, ?_⟩
  · ext t
    constructor
    · intro ht
      exact mem_iUnion.mpr ⟨f t, mem_iUnion.mpr
        ⟨hfinite.mem_toFinset.mpr ⟨t, ht, rfl⟩, ht, rfl⟩⟩
    · intro ht
      obtain ⟨q, hq⟩ := mem_iUnion.mp ht
      obtain ⟨_, hqt⟩ := mem_iUnion.mp hq
      exact hqt.1
  · intro q hq r hr hqr
    apply Set.disjoint_left.mpr
    intro t htq htr
    exact hqr (htq.2.symm.trans htr.2)
  · intro q hq
    obtain ⟨t, ht, htq⟩ := hfinite.mem_toFinset.mp hq
    have hne : {t | t ∈ _root_.Set.Icc a b ∧ f t = q}.Nonempty := ⟨t, ht, htq⟩
    exact ⟨hne, level_set_eq_interval_of_monotoneOn_left_constant hmono hleft hne⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exists_finite_level_set_partition_of_monotoneOn_left_constant then
    throwError "Refusing to shadow existing declaration exists_finite_level_set_partition_of_monotoneOn_left_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `exists_finite_level_set_partition_of_monotoneOn_left_constant ``Submission.exists_finite_level_set_partition_of_monotoneOn_left_constant

theorem exists_finite_level_set_partition_of_monotoneOn_left_constant_nat
    {f : ℝ → ℕ} {a b : ℝ}
    (hmono : MonotoneOn f (_root_.Set.Icc a b))
    (hleft : ∀ t ∈ _root_.Set.Ioc a b, ∃ ε > 0,
      ∀ s ∈ _root_.Set.Icc a b, t - ε < s → s ≤ t → f s = f t) :
    ∃ Q : Finset ℕ,
      _root_.Set.Icc a b = ⋃ q ∈ Q, {t | t ∈ _root_.Set.Icc a b ∧ f t = q} ∧
      (Q : Set ℕ).PairwiseDisjoint (fun q => {t | t ∈ _root_.Set.Icc a b ∧ f t = q}) ∧
      ∀ q ∈ Q, {t | t ∈ _root_.Set.Icc a b ∧ f t = q}.Nonempty ∧
        ∃ l u : ℝ, a ≤ l ∧ l ≤ u ∧ u ≤ b ∧
          ({t | t ∈ _root_.Set.Icc a b ∧ f t = q} = _root_.Set.Icc a u ∧ f a = q ∨
            {t | t ∈ _root_.Set.Icc a b ∧ f t = q} = _root_.Set.Ioc l u ∧ f a ≠ q) := by
  have hfinite : (f '' _root_.Set.Icc a b).Finite := (_root_.Set.finite_Iic (f b)).subset (by
    rintro q ⟨t, ht, rfl⟩
    exact hmono ht ⟨ht.1.trans ht.2, le_rfl⟩ ht.2)
  exact exists_finite_level_set_partition_of_monotoneOn_left_constant hfinite hmono hleft

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exists_finite_level_set_partition_of_monotoneOn_left_constant_nat then
    throwError "Refusing to shadow existing declaration exists_finite_level_set_partition_of_monotoneOn_left_constant_nat"
  Lean.modifyEnv fun env => Lean.addAlias env `exists_finite_level_set_partition_of_monotoneOn_left_constant_nat ``Submission.exists_finite_level_set_partition_of_monotoneOn_left_constant_nat
