/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CircleFourPoints
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscutExtension
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.FourArcSphere
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeModel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_param_of_sdiff_eq_inter_isOpen {S J W O : Set E} (hS : IsPLSphere 2 S)
    (hJ : IsPLSphere 1 J) (hJW : J ⊆ W) (hWS : W ⊆ S) (hWc : IsClosed W) (hO : IsOpen O)
    (hWO : W \ J = S ∩ O) (hne : (W \ J).Nonempty) (hne' : (S \ W).Nonempty) :
    ∃ r : (Fin 3 → ℝ) → E, IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) W ∧
      r '' stdSimplexBoundary 2 = J := by
  obtain ⟨D₁, D₂, hU, hI, f₁, f₂, hf₁, hf₂, hb₁, hb₂⟩ :=
    exists_disk_decomposition_of_isPLSphere_one_subset_two hS hJ (hJW.trans hWS)
  have hside : ∀ (D : Set E) (f : (Fin 3 → ℝ) → E), D ⊆ S →
      IsPLHomeomorphOn f (stdSimplex ℝ (Fin 3)) D → f '' stdSimplexBoundary 2 = J →
        D \ J ⊆ O ∨ D \ J ⊆ Wᶜ := by
    intro D f hDS hf hb
    have hc : IsPreconnected (D \ J) := by
      rw [← hb]
      exact hf.isConnected_sdiff_image_stdSimplexBoundary.isPreconnected
    refine isPreconnected_iff_subset_of_disjoint.mp hc O Wᶜ hO hWc.isOpen_compl ?_ ?_
    · intro x hx
      by_cases hxW : x ∈ W
      · have hxO : x ∈ S ∩ O := hWO ▸ ⟨hxW, hx.2⟩
        exact Or.inl hxO.2
      · exact Or.inr hxW
    · ext x
      simp only [_root_.Set.mem_inter_iff, _root_.Set.mem_empty_iff_false, iff_false, not_and]
      intro hx hxO hxW
      have hxWJ : x ∈ W \ J := hWO ▸ ⟨hDS hx.1, hxO⟩
      exact hxW hxWJ.1
  have hD₁S : D₁ ⊆ S := hU ▸ _root_.Set.subset_union_left
  have hD₂S : D₂ ⊆ S := hU ▸ _root_.Set.subset_union_right
  have hJD₁ : J ⊆ D₁ := hI ▸ _root_.Set.inter_subset_left
  have hJD₂ : J ⊆ D₂ := hI ▸ _root_.Set.inter_subset_right
  obtain ⟨y, hyS, hyW⟩ := hne'
  obtain ⟨x, hxW, hxJ⟩ := hne
  have hyJ : y ∉ J := fun h => hyW (hJW h)
  have heq : ∀ (Da Db : Set E), Da ∪ Db = S → J ⊆ Da → Da \ J ⊆ O → Db \ J ⊆ Wᶜ →
      Da ⊆ S → W = Da := by
    intro Da Db hDab hJDa hDaO hDbW hDaS
    apply Subset.antisymm
    · intro z hzW
      by_cases hzJ : z ∈ J
      · exact hJDa hzJ
      · rcases (hDab.symm ▸ hWS hzW : z ∈ Da ∪ Db) with hz | hz
        · exact hz
        · exact absurd hzW (hDbW ⟨hz, hzJ⟩)
    · intro z hz
      by_cases hzJ : z ∈ J
      · exact hJW hzJ
      · have hzO : z ∈ S ∩ O := ⟨hDaS hz, hDaO ⟨hz, hzJ⟩⟩
        exact (hWO ▸ hzO : z ∈ W \ J).1
  rcases hside D₁ f₁ hD₁S hf₁ hb₁ with h₁ | h₁ <;> rcases hside D₂ f₂ hD₂S hf₂ hb₂ with h₂ | h₂
  · exfalso
    rcases (hU.symm ▸ hyS : y ∈ D₁ ∪ D₂) with hy | hy
    · exact hyW (hWO ▸ (⟨hyS, h₁ ⟨hy, hyJ⟩⟩ : y ∈ S ∩ O) : y ∈ W \ J).1
    · exact hyW (hWO ▸ (⟨hyS, h₂ ⟨hy, hyJ⟩⟩ : y ∈ S ∩ O) : y ∈ W \ J).1
  · exact ⟨f₁, heq D₁ D₂ hU hJD₁ h₁ h₂ hD₁S ▸ hf₁, hb₁⟩
  · exact ⟨f₂, heq D₂ D₁ ((_root_.Set.union_comm _ _).trans hU) hJD₂ h₂ h₁ hD₂S ▸ hf₂, hb₂⟩
  · exfalso
    rcases (hU.symm ▸ hWS hxW : x ∈ D₁ ∪ D₂) with hx | hx
    · exact h₁ ⟨hx, hxJ⟩ hxW
    · exact h₂ ⟨hx, hxJ⟩ hxW

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_param_of_sdiff_eq_inter_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_param_of_sdiff_eq_inter_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_param_of_sdiff_eq_inter_isOpen ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_param_of_sdiff_eq_inter_isOpen

theorem exists_isPLHomeomorphOn_crosscut_move {W J β e : Set E} {u : (Fin 3 → ℝ) → E}
    (hu : IsPLHomeomorphOn u (stdSimplex ℝ (Fin 3)) W) (huJ : u '' stdSimplexBoundary 2 = J)
    {γ δ : ℝ → E} (hγ : IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) β) (hδ : IsPLHomeomorphOn δ (_root_.Set.Icc 0 1) e)
    (hβW : β ⊆ W) (heW : e ⊆ W) (hβJ : β ∩ J = {γ 0, γ 1}) (heJ : e ∩ J = {γ 0, γ 1})
    (h0 : δ 0 = γ 0) (h1 : δ 1 = γ 1) :
    ∃ H : E → E, IsPLHomeomorphOn H W W ∧ _root_.Set.EqOn H id J ∧ H '' β = e := by
  have hJ : IsPLSphere 1 J := huJ ▸ hu.isPLSphere_image_stdSimplexBoundary
  have hβ : IsPLBall 1 β := (isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hγ
  have hmem0 : (0 : ℝ) ∈ _root_.Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hmem1 : (1 : ℝ) ∈ _root_.Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hk : IsPLHomeomorphOn (δ ∘ Function.invFunOn γ (_root_.Set.Icc 0 1)) β e := hγ.symm.trans hδ
  have hk0 : (δ ∘ Function.invFunOn γ (_root_.Set.Icc 0 1)) (γ 0) = γ 0 := by
    simp only [Function.comp_apply, hγ.bijOn.invOn_invFunOn.1 hmem0, h0]
  have hk1 : (δ ∘ Function.invFunOn γ (_root_.Set.Icc 0 1)) (γ 1) = γ 1 := by
    simp only [Function.comp_apply, hγ.bijOn.invOn_invFunOn.1 hmem1, h1]
  obtain ⟨f, hf, hfJ, hfβ⟩ := exists_isPLHomeomorphOn_union hJ.isPolyhedron hβ.isPolyhedron
    hJ.isPolyhedron.isPLHomeomorphOn_id hk
    (by
      rw [_root_.Set.inter_comm, hβJ]
      rintro x (rfl | rfl)
      · exact hk0.symm
      · exact hk1.symm)
    (by
      rw [_root_.Set.inter_comm J β, hβJ, _root_.Set.inter_comm J e, heJ]
      rintro y (rfl | rfl)
      · exact ⟨γ 0, Or.inl rfl, rfl⟩
      · exact ⟨γ 1, Or.inr rfl, rfl⟩)
  have hfJ' : f '' J = J := (hfJ.image_eq).trans (_root_.Set.image_id J)
  have hfβ' : f '' β = e := hfβ.image_eq.trans hk.image_eq
  obtain ⟨G, hG, hGf⟩ := exists_isPLHomeomorphOn_eqOn_disk_crosscut hu huJ hu huJ hγ hβW
    (by rw [hβJ]) heW hf hfJ' hfβ'
  exact ⟨G, hG, fun x hx => (hGf (Or.inl hx)).trans (hfJ hx),
    (hGf.mono _root_.Set.subset_union_right).image_eq.trans hfβ'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_crosscut_move then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_crosscut_move"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_crosscut_move ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_crosscut_move

end Generic

theorem fourSpokeModelLeaf_add_one (k : Fin 4) :
    fourSpokeModelLeaf (k + 1) = (-(fourSpokeModelLeaf k).2, (fourSpokeModelLeaf k).1) := by
  rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl
  · change fourSpokeModelLeaf 1 = _
    simp [fourSpokeModelLeaf]
  · change fourSpokeModelLeaf 2 = _
    simp [fourSpokeModelLeaf]
  · change fourSpokeModelLeaf 3 = _
    simp [fourSpokeModelLeaf]
  · change fourSpokeModelLeaf 0 = _
    simp [fourSpokeModelLeaf]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_add_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_add_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_add_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_add_one

theorem fourSpokeModelLeaf_add_two (k : Fin 4) :
    fourSpokeModelLeaf (k + 2) = -fourSpokeModelLeaf k := by
  rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl
  · change fourSpokeModelLeaf 2 = _
    simp [fourSpokeModelLeaf]
  · change fourSpokeModelLeaf 3 = _
    simp [fourSpokeModelLeaf]
  · change fourSpokeModelLeaf 0 = _
    simp [fourSpokeModelLeaf]
  · change fourSpokeModelLeaf 1 = _
    simp [fourSpokeModelLeaf]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_add_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_add_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_add_two ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_add_two

theorem fourSpokeModelLeaf_add_three (k : Fin 4) :
    fourSpokeModelLeaf (k + 3) = ((fourSpokeModelLeaf k).2, -(fourSpokeModelLeaf k).1) := by
  rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl
  · change fourSpokeModelLeaf 3 = _
    simp [fourSpokeModelLeaf]
  · change fourSpokeModelLeaf 0 = _
    simp [fourSpokeModelLeaf]
  · change fourSpokeModelLeaf 1 = _
    simp [fourSpokeModelLeaf]
  · change fourSpokeModelLeaf 2 = _
    simp [fourSpokeModelLeaf]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_add_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_add_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_add_three ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_add_three

theorem fourSpokeModelLeaf_norm (k : Fin 4) :
    (fourSpokeModelLeaf k).1 * (fourSpokeModelLeaf k).1 +
      (fourSpokeModelLeaf k).2 * (fourSpokeModelLeaf k).2 = 1 := by
  rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl <;> norm_num [fourSpokeModelLeaf]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_norm ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_norm

theorem fin_four_ne_add_one (k : Fin 4) : k ≠ k + 1 := by
  rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl <;> decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fin_four_ne_add_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fin_four_ne_add_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fin_four_ne_add_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fin_four_ne_add_one

theorem fin_four_add_one_add_one (k : Fin 4) : k + 1 + 1 = k + 2 := by
  rw [add_assoc]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fin_four_add_one_add_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fin_four_add_one_add_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fin_four_add_one_add_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fin_four_add_one_add_one

def tubeLeafCoord (k : Fin 4) (p : ℝ × ℝ) : ℝ :=
  p.1 * (fourSpokeModelLeaf k).1 + p.2 * (fourSpokeModelLeaf k).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord

theorem continuous_tubeLeafCoord (k : Fin 4) : Continuous (tubeLeafCoord k) :=
  (continuous_fst.mul continuous_const).add (continuous_snd.mul continuous_const)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.continuous_tubeLeafCoord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.continuous_tubeLeafCoord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.continuous_tubeLeafCoord ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.continuous_tubeLeafCoord

theorem tubeLeafCoord_smul (k : Fin 4) (c : ℝ) (p : ℝ × ℝ) :
    tubeLeafCoord k (c • p) = c * tubeLeafCoord k p := by
  simp only [tubeLeafCoord, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_smul ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_smul

theorem tubeLeafCoord_add (k : Fin 4) (p q : ℝ × ℝ) :
    tubeLeafCoord k (p + q) = tubeLeafCoord k p + tubeLeafCoord k q := by
  simp only [tubeLeafCoord, Prod.fst_add, Prod.snd_add]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add

theorem tubeLeafCoord_add_one (k : Fin 4) (p : ℝ × ℝ) :
    tubeLeafCoord (k + 1) p =
      -(p.1 * (fourSpokeModelLeaf k).2) + p.2 * (fourSpokeModelLeaf k).1 := by
  rw [tubeLeafCoord, fourSpokeModelLeaf_add_one]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add_one

theorem tubeLeafCoord_add_two (k : Fin 4) (p : ℝ × ℝ) :
    tubeLeafCoord (k + 2) p = -tubeLeafCoord k p := by
  rw [tubeLeafCoord, fourSpokeModelLeaf_add_two, tubeLeafCoord, Prod.fst_neg, Prod.snd_neg]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add_two ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add_two

theorem tubeLeafCoord_self (k : Fin 4) : tubeLeafCoord k (fourSpokeModelLeaf k) = 1 :=
  fourSpokeModelLeaf_norm k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_self ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_self

theorem tubeLeafCoord_add_one_self (k : Fin 4) :
    tubeLeafCoord (k + 1) (fourSpokeModelLeaf k) = 0 := by
  rw [tubeLeafCoord_add_one]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add_one_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add_one_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add_one_self ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add_one_self

theorem tubeLeafCoord_self_add_one (k : Fin 4) :
    tubeLeafCoord k (fourSpokeModelLeaf (k + 1)) = 0 := by
  rw [tubeLeafCoord, fourSpokeModelLeaf_add_one]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_self_add_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_self_add_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_self_add_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_self_add_one

theorem tubeLeafCoord_add_one_add_one (k : Fin 4) :
    tubeLeafCoord (k + 1) (fourSpokeModelLeaf (k + 1)) = 1 := by
  rw [tubeLeafCoord_add_one, fourSpokeModelLeaf_add_one]
  linear_combination fourSpokeModelLeaf_norm k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add_one_add_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add_one_add_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add_one_add_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeLeafCoord_add_one_add_one

theorem eq_tubeLeafCoord_smul_add (k : Fin 4) (p : ℝ × ℝ) :
    p = tubeLeafCoord k p • fourSpokeModelLeaf k +
      tubeLeafCoord (k + 1) p • fourSpokeModelLeaf (k + 1) := by
  rw [tubeLeafCoord_add_one, fourSpokeModelLeaf_add_one]
  obtain ⟨x, y⟩ := p
  have hn := fourSpokeModelLeaf_norm k
  refine Prod.ext ?_ ?_
  · simp only [tubeLeafCoord, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    linear_combination (-x) * hn
  · simp only [tubeLeafCoord, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    linear_combination (-y) * hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eq_tubeLeafCoord_smul_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eq_tubeLeafCoord_smul_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eq_tubeLeafCoord_smul_add ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eq_tubeLeafCoord_smul_add

theorem smul_fourSpokeModelLeaf_mem_spliceSquare_iff (k : Fin 4) (c : ℝ) :
    c • fourSpokeModelLeaf k ∈ spliceSquare ↔ -1 ≤ c ∧ c ≤ 1 := by
  rw [mem_spliceSquare]
  rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl <;>
    simp only [fourSpokeModelLeaf, Prod.smul_mk, smul_eq_mul, mul_one, _root_.MulZeroClass.mul_zero, mul_neg] <;>
    constructor <;> intro h <;> first
      | exact ⟨by linarith [h.1.1, h.1.2, h.2.1, h.2.2], by linarith [h.1.1, h.1.2, h.2.1, h.2.2]⟩
      | exact ⟨⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩, by linarith [h.1, h.2],
          by linarith [h.1, h.2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.smul_fourSpokeModelLeaf_mem_spliceSquare_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.smul_fourSpokeModelLeaf_mem_spliceSquare_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.smul_fourSpokeModelLeaf_mem_spliceSquare_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.smul_fourSpokeModelLeaf_mem_spliceSquare_iff

theorem smul_fourSpokeModelLeaf_mem_spliceSquareBoundary_iff (k : Fin 4) {c : ℝ} (hc : 0 ≤ c) :
    c • fourSpokeModelLeaf k ∈ spliceSquareBoundary ↔ c = 1 := by
  rw [mem_spliceSquareBoundary, smul_fourSpokeModelLeaf_mem_spliceSquare_iff]
  rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl <;>
    simp only [fourSpokeModelLeaf, Prod.smul_mk, smul_eq_mul, mul_one, _root_.MulZeroClass.mul_zero, mul_neg] <;>
    constructor
  all_goals first
    | (rintro ⟨-, h⟩
       rcases h with h | h | h | h <;> linarith)
    | (rintro rfl
       norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.smul_fourSpokeModelLeaf_mem_spliceSquareBoundary_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.smul_fourSpokeModelLeaf_mem_spliceSquareBoundary_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.smul_fourSpokeModelLeaf_mem_spliceSquareBoundary_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.smul_fourSpokeModelLeaf_mem_spliceSquareBoundary_iff

theorem mem_tubeCellSphere_iff {p : (ℝ × ℝ) × ℝ} :
    p ∈ tubeCellSphere ↔ (p.1 ∈ spliceSquare ∧ (p.2 = 0 ∨ p.2 = 1)) ∨
      (p.1 ∈ spliceSquareBoundary ∧ 0 ≤ p.2 ∧ p.2 ≤ 1) := by
  simp only [tubeCellSphere, _root_.Set.mem_union, _root_.Set.mem_prod, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_Icc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_tubeCellSphere_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_tubeCellSphere_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_tubeCellSphere_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_tubeCellSphere_iff

theorem mem_tubeCellArc_iff_tubeLeafCoord (k : Fin 4) {p : (ℝ × ℝ) × ℝ} :
    p ∈ tubeCellArc k ↔ p ∈ tubeCellSphere ∧ tubeLeafCoord (k + 1) p.1 = 0 ∧
      0 ≤ tubeLeafCoord k p.1 := by
  constructor
  · intro hp
    refine ⟨tubeCellArc_subset_tubeCellSphere k hp, ?_⟩
    obtain ⟨c, z, hc, -, -, rfl⟩ := mem_tubeMeridian_iff.mp hp
    rw [tubeLeafCoord_smul, tubeLeafCoord_smul, tubeLeafCoord_add_one_self, tubeLeafCoord_self]
    exact ⟨mul_zero c, by linarith [hc.1]⟩
  · rintro ⟨hS, h0, hc⟩
    have hp1 : p.1 = tubeLeafCoord k p.1 • fourSpokeModelLeaf k := by
      conv_lhs => rw [eq_tubeLeafCoord_smul_add k p.1, h0, zero_smul, add_zero]
    refine mem_tubeMeridian_iff.mpr ⟨tubeLeafCoord k p.1, p.2, ?_⟩
    rcases mem_tubeCellSphere_iff.mp hS with ⟨hsq, hz⟩ | ⟨hbd, hz0, hz1⟩
    · rw [hp1, smul_fourSpokeModelLeaf_mem_spliceSquare_iff] at hsq
      refine ⟨⟨hc, hsq.2⟩, ?_, Or.inr hz, Prod.ext hp1 rfl⟩
      rcases hz with h | h <;> rw [h] <;> norm_num
    · rw [hp1, smul_fourSpokeModelLeaf_mem_spliceSquareBoundary_iff k hc] at hbd
      refine ⟨⟨hc, hbd.le⟩, ⟨hz0, hz1⟩, Or.inl hbd, Prod.ext hp1 rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_tubeCellArc_iff_tubeLeafCoord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_tubeCellArc_iff_tubeLeafCoord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_tubeCellArc_iff_tubeLeafCoord ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_tubeCellArc_iff_tubeLeafCoord

def tubeSector (k : Fin 4) : Set ((ℝ × ℝ) × ℝ) :=
  tubeCellSphere ∩ {p | 0 ≤ tubeLeafCoord k p.1 ∧ 0 ≤ tubeLeafCoord (k + 1) p.1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeSector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeSector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeSector ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeSector

theorem isClosed_tubeCellSphere : IsClosed tubeCellSphere :=
  isPLSphere_tubeCellSphere.isPolyhedron.isCompact.isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isClosed_tubeCellSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isClosed_tubeCellSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isClosed_tubeCellSphere ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isClosed_tubeCellSphere

theorem isClosed_tubeSector (k : Fin 4) : IsClosed (tubeSector k) :=
  isClosed_tubeCellSphere.inter
    ((isClosed_le continuous_const ((continuous_tubeLeafCoord k).comp continuous_fst)).inter
      (isClosed_le continuous_const ((continuous_tubeLeafCoord (k + 1)).comp continuous_fst)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isClosed_tubeSector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isClosed_tubeSector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isClosed_tubeSector ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isClosed_tubeSector

theorem tubeCellArc_subset_tubeSector (k : Fin 4) : tubeCellArc k ⊆ tubeSector k := by
  intro p hp
  obtain ⟨hS, h0, hc⟩ := (mem_tubeCellArc_iff_tubeLeafCoord k).mp hp
  exact ⟨hS, hc, h0.ge⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeCellArc_subset_tubeSector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeCellArc_subset_tubeSector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeCellArc_subset_tubeSector ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeCellArc_subset_tubeSector

theorem tubeCellArc_add_one_subset_tubeSector (k : Fin 4) :
    tubeCellArc (k + 1) ⊆ tubeSector k := by
  intro p hp
  obtain ⟨hS, h0, hc⟩ := (mem_tubeCellArc_iff_tubeLeafCoord (k + 1)).mp hp
  rw [fin_four_add_one_add_one, tubeLeafCoord_add_two, neg_eq_zero] at h0
  exact ⟨hS, h0.ge, hc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeCellArc_add_one_subset_tubeSector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeCellArc_add_one_subset_tubeSector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeCellArc_add_one_subset_tubeSector ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeCellArc_add_one_subset_tubeSector

theorem tubeSector_sdiff (k : Fin 4) :
    tubeSector k \ (tubeCellArc k ∪ tubeCellArc (k + 1)) =
      tubeCellSphere ∩ {p | 0 < tubeLeafCoord k p.1 ∧ 0 < tubeLeafCoord (k + 1) p.1} := by
  ext p
  constructor
  · rintro ⟨⟨hS, h1, h2⟩, hn⟩
    refine ⟨hS, lt_of_le_of_ne h1 fun h => hn (Or.inr ?_), lt_of_le_of_ne h2 fun h => hn
      (Or.inl ((mem_tubeCellArc_iff_tubeLeafCoord k).mpr ⟨hS, h.symm, h1⟩))⟩
    refine (mem_tubeCellArc_iff_tubeLeafCoord (k + 1)).mpr ⟨hS, ?_, h2⟩
    rw [fin_four_add_one_add_one, tubeLeafCoord_add_two, ← h, neg_zero]
  · rintro ⟨hS, h1, h2⟩
    refine ⟨⟨hS, h1.le, h2.le⟩, ?_⟩
    rintro (h | h)
    · exact h2.ne' ((mem_tubeCellArc_iff_tubeLeafCoord k).mp h).2.1
    · have h' := ((mem_tubeCellArc_iff_tubeLeafCoord (k + 1)).mp h).2.1
      rw [fin_four_add_one_add_one, tubeLeafCoord_add_two, neg_eq_zero] at h'
      exact h1.ne' h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeSector_sdiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeSector_sdiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeSector_sdiff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeSector_sdiff

end DifferentialGeometry.Topology.PiecewiseLinear
