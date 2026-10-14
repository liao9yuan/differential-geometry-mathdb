import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Regular

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

section

variable {Z F : Type*} [TopologicalSpace Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : Z → F →L[ℝ] F →L[ℝ] ℝ} {K : Set Z}

open _root_.ContinuousOn in
theorem ContinuousOn.exists_uniform_bilin_quadratic_lower_bound
    (hB : ContinuousOn (fun p : Z × F => B p.1 p.2 p.2) (K ×ˢ (_root_.Set.univ : Set F)))
    (hK : IsCompact K) (hpos : ∀ x ∈ K, ∀ v : F, v ≠ 0 → 0 < B x v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v : F, c * ‖v‖ ^ 2 ≤ B x v v := by
  have hcpt := hK.prod (isCompact_sphere (0 : F) 1)
  have hc : ContinuousOn (fun p : Z × F => B p.1 p.2 p.2)
      (K ×ˢ Metric.sphere (0 : F) 1) :=
    hB.mono (_root_.Set.prod_mono Subset.rfl (_root_.Set.subset_univ _))
  have hp : ∀ p ∈ K ×ˢ Metric.sphere (0 : F) 1, 0 < B p.1 p.2 p.2 := by
    intro p hp
    apply hpos p.1 hp.1 p.2
    intro hzero
    have hn := hp.2
    rw [hzero, Metric.mem_sphere, dist_self] at hn
    exact zero_ne_one hn
  obtain ⟨c, hcpos, hcbound⟩ := hcpt.exists_forall_le' hc hp
  refine ⟨c, hcpos, ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · subst v
    simp
  · have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : F) 1 := by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv,
        Real.norm_eq_abs, abs_norm, inv_mul_cancel₀ hvnorm]
    have hbound := hcbound (x, ‖v‖⁻¹ • v) ⟨hx, hu⟩
    calc
      c * ‖v‖ ^ 2 ≤ B x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hbound (sq_nonneg ‖v‖)
      _ = B x v v := by
        simp only [map_smul, smul_apply, smul_eq_mul]
        field_simp

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContinuousOn
  let env ← Lean.getEnv
  if env.contains `ContinuousOn.exists_uniform_bilin_quadratic_lower_bound then
    throwError "Refusing to shadow existing declaration ContinuousOn.exists_uniform_bilin_quadratic_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousOn.exists_uniform_bilin_quadratic_lower_bound ``Submission.ContinuousOn.exists_uniform_bilin_quadratic_lower_bound

omit [TopologicalSpace Z] in
open _root_.ContinuousLinearMap in
theorem ContinuousLinearMap.isCoercive_of_posDef
    (B : F →L[ℝ] F →L[ℝ] ℝ) (hpos : ∀ v : F, v ≠ 0 → 0 < B v v) :
    IsCoercive B := by
  have hc : ContinuousOn (fun p : Unit × F => B p.2 p.2)
      ((_root_.Set.univ : Set Unit) ×ˢ (_root_.Set.univ : Set F)) :=
    ((B.continuous.comp continuous_snd).clm_apply continuous_snd).continuousOn
  obtain ⟨c, hcpos, hbound⟩ := hc.exists_uniform_bilin_quadratic_lower_bound
    isCompact_univ (fun _ _ v hv => hpos v hv)
  refine ⟨c, hcpos, ?_⟩
  intro v
  simpa only [pow_two, mul_assoc] using hbound () (_root_.Set.mem_univ _) v

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContinuousLinearMap
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.isCoercive_of_posDef then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.isCoercive_of_posDef"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.isCoercive_of_posDef ``Submission.ContinuousLinearMap.isCoercive_of_posDef

end

theorem IsCoercive.isBounded_le
    {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    {B : F →L[ℝ] F →L[ℝ] ℝ} (hB : IsCoercive B) (r : ℝ) :
    Bornology.IsBounded {v : F | B v v ≤ r} := by
  obtain ⟨c, hcpos, hbound⟩ := hB
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max (r / c) 1 + 1, ?_⟩
  intro v hv
  change B v v ≤ r at hv
  have hn : ‖v‖ ^ 2 ≤ r / c := by
    apply (le_div_iff₀ hcpos).mpr
    nlinarith [hbound v]
  have hr := le_max_left (r / c) 1
  have hone := le_max_right (r / c) 1
  nlinarith [sq_nonneg (‖v‖ - 1)]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsCoercive
  let env ← Lean.getEnv
  if env.contains `IsCoercive.isBounded_le then
    throwError "Refusing to shadow existing declaration IsCoercive.isBounded_le"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.isBounded_le ``Submission.IsCoercive.isBounded_le

section

variable {Z E : Type*} [TopologicalSpace Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.ContinuousOn in
theorem ContinuousOn.exists_uniform_bilin_quadratic_bounds
    {B : Z → E →L[ℝ] E →L[ℝ] ℝ} {K : Set Z}
    (hB : ContinuousOn B K) (hK : IsCompact K)
    (hpos : ∀ z ∈ K, ∀ v : E, v ≠ 0 → 0 < B z v v) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z ∈ K, ∀ v : E,
      C⁻¹ * ‖v‖ ^ 2 ≤ B z v v ∧ B z v v ≤ C * ‖v‖ ^ 2 := by
  have hc : ContinuousOn (fun p : Z × E => B p.1 p.2 p.2) (K ×ˢ _root_.Set.univ) :=
    ((hB.comp continuous_fst.continuousOn (fun _ hp => hp.1)).clm_apply
      continuous_snd.continuousOn).clm_apply continuous_snd.continuousOn
  obtain ⟨c, hcp, hc⟩ := hc.exists_uniform_bilin_quadratic_lower_bound hK hpos
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hB
  let C := _root_.Max.max 1 (_root_.Max.max c⁻¹ A)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  have hcC : C⁻¹ ≤ c := (inv_le_comm₀ hCpos hcp).mpr
    ((le_max_left _ _).trans (le_max_right _ _))
  have hAC : A ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC1, fun z hz v => ⟨?_, ?_⟩⟩
  · exact (mul_le_mul_of_nonneg_right hcC (sq_nonneg ‖v‖)).trans (hc z hz v)
  · calc
      B z v v ≤ ‖B z v v‖ := le_abs_self _
      _ ≤ ‖B z‖ * ‖v‖ * ‖v‖ := (B z).le_opNorm₂ v v
      _ ≤ C * ‖v‖ ^ 2 := by
        simpa only [pow_two, mul_assoc] using
          mul_le_mul_of_nonneg_right ((hA z hz).trans hAC) (sq_nonneg ‖v‖)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousOn.exists_uniform_bilin_quadratic_bounds then
    throwError "Refusing to shadow existing declaration ContinuousOn.exists_uniform_bilin_quadratic_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousOn.exists_uniform_bilin_quadratic_bounds ``Submission.ContinuousOn.exists_uniform_bilin_quadratic_bounds

open _root_.ContinuousOn in
theorem ContinuousOn.exists_uniform_bilin_quadratic_bounds_nhds
    [LocallyCompactSpace Z] [RegularSpace Z]
    {B : Z → E →L[ℝ] E →L[ℝ] ℝ} {U K : Set Z}
    (hB : ContinuousOn B U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hpos : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < B z v v) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ W : Set Z, IsOpen W ∧ K ⊆ W ∧ closure W ⊆ U ∧
      IsCompact (closure W) ∧ ∀ z ∈ closure W, ∀ v : E,
        C⁻¹ * ‖v‖ ^ 2 ≤ B z v v ∧ B z v v ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨W, hW, hKW, hWU, hcW⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨C, hC, hb⟩ := (hB.mono hWU).exists_uniform_bilin_quadratic_bounds hcW
    (fun z hz => hpos z (hWU hz))
  exact ⟨C, hC, W, hW, hKW, hWU, hcW, hb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousOn.exists_uniform_bilin_quadratic_bounds_nhds then
    throwError "Refusing to shadow existing declaration ContinuousOn.exists_uniform_bilin_quadratic_bounds_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousOn.exists_uniform_bilin_quadratic_bounds_nhds ``Submission.ContinuousOn.exists_uniform_bilin_quadratic_bounds_nhds

end
