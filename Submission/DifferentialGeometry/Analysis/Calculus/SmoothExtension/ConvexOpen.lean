import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff

namespace DifferentialGeometry.Analysis

open _root_.Set

theorem exists_contDiff_range_subset_eqOn_eqOn_compl
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {K U : Set V} (hK : IsCompact K) (hU : IsOpen U) (hconv : Convex ℝ U)
    (hKU : K ⊆ U) {z : V} (hz : z ∈ U) :
    ∃ r : V → V, ContDiff ℝ ∞ r ∧ _root_.Set.range r ⊆ U ∧ _root_.Set.EqOn r id K ∧
      EqOn r (fun _ => z) Uᶜ := by
  obtain ⟨χ, hχ, -, hχone, hχsupp, hχrange⟩ := exists_bump_compact hK hU hKU
  refine ⟨fun x => χ x • x + (1 - χ x) • z,
    (hχ.smul contDiff_id).add ((contDiff_const.sub hχ).smul contDiff_const), ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    by_cases hx : χ x = 0
    · simpa only [hx, zero_smul, sub_zero, one_smul, zero_add] using hz
    · have hχx : χ x ∈ _root_.Set.Icc (0 : ℝ) 1 := hχrange ⟨x, rfl⟩
      exact hconv (hχsupp (subset_tsupport χ hx)) hz hχx.1
        (sub_nonneg.mpr hχx.2) (by ring)
  · intro x hx
    simp only [hχone.self_of_nhdsSet hx, Pi.one_apply, one_smul, sub_self,
      zero_smul, add_zero, id_eq]
  · intro x hx
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hχsupp h))
    simp only [hχx, zero_smul, sub_zero, one_smul, zero_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_contDiff_range_subset_eqOn_eqOn_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_contDiff_range_subset_eqOn_eqOn_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_contDiff_range_subset_eqOn_eqOn_compl ``Submission.DifferentialGeometry.Analysis.exists_contDiff_range_subset_eqOn_eqOn_compl

theorem exists_contDiff_range_subset_eqOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {K U : Set V} (hK : IsCompact K) (hU : IsOpen U) (hconv : Convex ℝ U)
    (hKU : K ⊆ U) (hne : U.Nonempty) :
    ∃ r : V → V, ContDiff ℝ ∞ r ∧ _root_.Set.range r ⊆ U ∧ _root_.Set.EqOn r id K := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨r, hr, hrU, hrK, -⟩ :=
    exists_contDiff_range_subset_eqOn_eqOn_compl hK hU hconv hKU hz
  exact ⟨r, hr, hrU, hrK⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_contDiff_range_subset_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_contDiff_range_subset_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_contDiff_range_subset_eqOn ``Submission.DifferentialGeometry.Analysis.exists_contDiff_range_subset_eqOn

theorem exists_contDiff_range_subset_eqOn_nhds_Ioo
    {a b c : ℝ} (hac : a < c) (hcb : c < b) :
    ∃ ψ : ℝ → ℝ, ∃ ε > 0, ContDiff ℝ ∞ ψ ∧ _root_.Set.range ψ ⊆ _root_.Set.Ioo a b ∧
      _root_.Set.Ioo (c - ε) (c + ε) ⊆ _root_.Set.Ioo a b ∧
      EqOn ψ id (_root_.Set.Ioo (c - ε) (c + ε)) ∧ _root_.Set.EqOn ψ (fun _ => c) (_root_.Set.Ioo a b)ᶜ := by
  let ε := _root_.Min.min (c - a) (b - c) / 2
  have hε : 0 < ε := half_pos (lt_min (sub_pos.mpr hac) (sub_pos.mpr hcb))
  have hsub : _root_.Set.Icc (c - ε) (c + ε) ⊆ _root_.Set.Ioo a b := by
    intro t ht
    dsimp [ε] at *
    constructor <;> linarith [ht.1, ht.2, min_le_left (c - a) (b - c), min_le_right (c - a) (b - c)]
  obtain ⟨ψ, hψ, hψrange, hψid, hψout⟩ :=
    exists_contDiff_range_subset_eqOn_eqOn_compl _root_.CompactIccSpace.isCompact_Icc isOpen_Ioo
      (convex_Ioo a b) hsub ⟨hac, hcb⟩
  have hεsub : _root_.Set.Ioo (c - ε) (c + ε) ⊆ _root_.Set.Icc (c - ε) (c + ε) := _root_.Set.Ioo_subset_Icc_self
  exact ⟨ψ, ε, hε, hψ, hψrange, hεsub.trans hsub, hψid.mono hεsub, hψout⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_contDiff_range_subset_eqOn_nhds_Ioo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_contDiff_range_subset_eqOn_nhds_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_contDiff_range_subset_eqOn_nhds_Ioo ``Submission.DifferentialGeometry.Analysis.exists_contDiff_range_subset_eqOn_nhds_Ioo

end DifferentialGeometry.Analysis
