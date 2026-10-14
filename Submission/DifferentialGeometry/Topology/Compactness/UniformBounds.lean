import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter _root_.Topology

namespace DifferentialGeometry.Topology.Compactness

theorem exists_pos_uniform_lower_bound
    {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    {K : Set P} (hK : IsCompact K) {d : P × Q → ℝ} {q₀ : Q}
    (hd : ∀ p ∈ K, ContinuousAt d (p, q₀))
    (hpos : ∀ p ∈ K, 0 < d (p, q₀)) :
    ∃ m > 0, ∃ V ∈ 𝓝 q₀, ∀ p ∈ K, ∀ q ∈ V, m ≤ d (p, q) := by
  have hc : ContinuousOn (fun p ↦ d (p, q₀)) K := by
    intro p hp
    exact ((hd p hp).comp (f := fun z : P ↦ (z, q₀))
      (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  obtain ⟨m₀, hm₀, hm⟩ := hK.exists_forall_le' hc hpos
  have hnear : {z : P × Q | m₀ / 2 < d z} ∈ (𝓝ˢ K) ×ˢ 𝓝 q₀ := by
    apply hK.mem_nhdsSet_prod_of_forall
    intro p hp
    rw [← nhds_prod_eq]
    exact (hd p hp).preimage_mem_nhds (isOpen_Ioi.mem_nhds (by
      have h := hm p hp
      change m₀ / 2 < d (p, q₀)
      linarith))
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_prod_iff.mp hnear
  refine ⟨m₀ / 2, half_pos hm₀, V, hV, ?_⟩
  intro p hp q hq
  exact (hUV ⟨subset_of_mem_nhdsSet hU hp, hq⟩).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Compactness.exists_pos_uniform_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Compactness.exists_pos_uniform_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Compactness.exists_pos_uniform_lower_bound ``Submission.DifferentialGeometry.Topology.Compactness.exists_pos_uniform_lower_bound

set_option backward.isDefEq.respectTransparency false in
theorem exists_pos_uniform_lower_bound_on_Icc
    {P : Type*} [TopologicalSpace P] {K : Set P} (hK : IsCompact K)
    {d : P × ℝ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hd : ContinuousOn d (K ×ˢ _root_.Set.Icc 0 ρ))
    (hpos : ∀ p ∈ K, 0 < d (p, 0)) :
    ∃ ε > 0, ε ≤ ρ ∧ ∃ m > 0,
      ∀ p ∈ K, ∀ r ∈ _root_.Set.Icc 0 ε, m ≤ d (p, r) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let t₀ : _root_.Set.Icc (0 : ℝ) ρ := ⟨0, le_rfl, hρ.le⟩
  let d' : K × _root_.Set.Icc (0 : ℝ) ρ → ℝ := fun z ↦ d (z.1.1, z.2.1)
  have hd' : Continuous d' := hd.comp_continuous
    (continuous_subtype_val.prodMap continuous_subtype_val) (fun z ↦ ⟨z.1.2, z.2.2⟩)
  obtain ⟨m, hm, V, hV, hb⟩ := exists_pos_uniform_lower_bound isCompact_univ
    (q₀ := t₀) (fun _ _ ↦ hd'.continuousAt) (fun p _ ↦ hpos p.1 p.2)
  have hV' : V ∈ _root_.Filter.comap (Subtype.val : _root_.Set.Icc (0 : ℝ) ρ → ℝ) (𝓝 0) := by
    simpa only [t₀, nhds_subtype_eq_comap] using hV
  obtain ⟨S, hS, hSV⟩ := mem_comap.mp hV'
  obtain ⟨r₀, hr₀, hrS⟩ := Metric.mem_nhds_iff.mp hS
  let ε := _root_.Min.min ρ (r₀ / 2)
  refine ⟨ε, lt_min hρ (half_pos hr₀), min_le_left _ _, m, hm, ?_⟩
  intro p hp r hr
  let t : _root_.Set.Icc (0 : ℝ) ρ := ⟨r, hr.1, hr.2.trans (min_le_left _ _)⟩
  apply hb (⟨p, hp⟩ : K) (_root_.Set.mem_univ _) t
  apply hSV
  apply hrS
  change _root_.Dist.dist r 0 < r₀
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hr.1]
  exact lt_of_le_of_lt (hr.2.trans (min_le_right _ _)) (half_lt_self hr₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Compactness.exists_pos_uniform_lower_bound_on_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Compactness.exists_pos_uniform_lower_bound_on_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Compactness.exists_pos_uniform_lower_bound_on_Icc ``Submission.DifferentialGeometry.Topology.Compactness.exists_pos_uniform_lower_bound_on_Icc

end DifferentialGeometry.Topology.Compactness
