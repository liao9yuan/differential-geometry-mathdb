import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.UnitInterval

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Set
open scoped _root_.Topology _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

theorem eVariationOn_comp_le_of_locally_lipschitzOn
    {f : X → Y} {γ : ℝ → X} {a b : ℝ} {C : ℝ≥0}
    (hγ : ContinuousOn γ (_root_.Set.Icc a b))
    (hf : ∀ x ∈ γ '' _root_.Set.Icc a b, ∃ s ∈ 𝓝 x, LipschitzOnWith C f s) :
    eVariationOn (f ∘ γ) (_root_.Set.Icc a b) ≤ C * eVariationOn γ (_root_.Set.Icc a b) := by
  by_cases hab : a ≤ b
  · have hloc : ∀ t : _root_.Set.Icc a b, ∃ V : Set X,
        IsOpen V ∧ γ t ∈ V ∧ LipschitzOnWith C f V := by
      intro t
      obtain ⟨s, hs, hfs⟩ := hf (γ t) ⟨t, t.property, rfl⟩
      obtain ⟨V, hVs, hVo, htV⟩ := mem_nhds_iff.mp hs
      exact ⟨V, hVo, htV, hfs.mono hVs⟩
    choose V hVo htV hfV using hloc
    let curve : _root_.Set.Icc a b → X := fun t => γ t
    have hc : Continuous curve := hγ.domRestrict
    obtain ⟨t, ht0, htm, ⟨n, htn⟩, htV'⟩ :=
      exists_monotone_Icc_subset_open_cover_Icc hab
        (c := fun i => curve ⁻¹' V i)
        (fun i => hc.isOpen_preimage _ (hVo i)) (by
          intro i _
          exact mem_iUnion.mpr ⟨i, htV i⟩)
    let u : ℕ → ℝ := fun i => t i
    have hu : Monotone u := fun i j hij => htm hij
    have hu0 : u 0 = a := ht0
    have hun : u n = b := htn n le_rfl
    have hpiece (i : ℕ) :
        eVariationOn (f ∘ γ) (_root_.Set.Icc (u i) (u (i + 1))) ≤
          C * eVariationOn γ (_root_.Set.Icc (u i) (u (i + 1))) := by
      obtain ⟨j, hj⟩ := htV' i
      apply (hfV j).comp_eVariationOn_le
      intro z hz
      have hzab : z ∈ _root_.Set.Icc a b :=
        ⟨(t i).property.1.trans hz.1, hz.2.trans (t (i + 1)).property.2⟩
      exact hj (show (⟨z, hzab⟩ : _root_.Set.Icc a b) ∈ _root_.Set.Icc (t i) (t (i + 1)) from hz)
    calc
      eVariationOn (f ∘ γ) (_root_.Set.Icc a b) =
          ∑ i ∈ Finset.range n, eVariationOn (f ∘ γ) (_root_.Set.Icc (u i) (u (i + 1))) := by
        rw [eVariationOn.sum' (f ∘ γ) hu, hu0, hun]
      _ ≤ ∑ i ∈ Finset.range n, C * eVariationOn γ (_root_.Set.Icc (u i) (u (i + 1))) :=
        Finset.sum_le_sum fun i _ => hpiece i
      _ = C * eVariationOn γ (_root_.Set.Icc a b) := by
        rw [← Finset.mul_sum, eVariationOn.sum' γ hu, hu0, hun]
  · simp [_root_.Set.Icc_eq_empty_of_lt (lt_of_not_ge hab)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.eVariationOn_comp_le_of_locally_lipschitzOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.eVariationOn_comp_le_of_locally_lipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.eVariationOn_comp_le_of_locally_lipschitzOn ``Submission.DifferentialGeometry.Topology.eVariationOn_comp_le_of_locally_lipschitzOn

theorem boundedVariationOn_comp_of_locally_lipschitzOn
    {f : X → Y} {γ : ℝ → X} {a b : ℝ} {C : ℝ≥0}
    (hγ : ContinuousOn γ (_root_.Set.Icc a b))
    (hf : ∀ x ∈ γ '' _root_.Set.Icc a b, ∃ s ∈ 𝓝 x, LipschitzOnWith C f s)
    (hvar : BoundedVariationOn γ (_root_.Set.Icc a b)) :
    BoundedVariationOn (f ∘ γ) (_root_.Set.Icc a b) :=
  ne_top_of_le_ne_top (by finiteness)
    (eVariationOn_comp_le_of_locally_lipschitzOn hγ hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.boundedVariationOn_comp_of_locally_lipschitzOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.boundedVariationOn_comp_of_locally_lipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.boundedVariationOn_comp_of_locally_lipschitzOn ``Submission.DifferentialGeometry.Topology.boundedVariationOn_comp_of_locally_lipschitzOn


theorem IsCompact.exists_uniform_lipschitzOnWith_nhds
    {K : Set X} (hK : IsCompact K) {f : X → Y}
    (hf : ∀ x ∈ K, ∃ L : ℝ≥0, ∃ s ∈ 𝓝 x, LipschitzOnWith L f s) :
    ∃ L : ℝ≥0, ∀ x ∈ K, ∃ s ∈ 𝓝 x, LipschitzOnWith L f s := by
  classical
  choose L V hV hLip using hf
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx => interior (V x hx))
    (fun x hx => interior_mem_nhds.mpr (hV x hx))
  refine ⟨t.sup (fun x => L x x.property), ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht hx)
  refine ⟨interior (V y y.property), isOpen_interior.mem_nhds hxy, ?_⟩
  intro z hz w hw
  exact (hLip y y.property (interior_subset hz) (interior_subset hw)).trans
    (mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.mpr (Finset.le_sup (f := fun x : K => L x x.property) hy)) zero_le)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.IsCompact
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.IsCompact.exists_uniform_lipschitzOnWith_nhds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.IsCompact.exists_uniform_lipschitzOnWith_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.IsCompact.exists_uniform_lipschitzOnWith_nhds ``Submission.DifferentialGeometry.Topology.IsCompact.exists_uniform_lipschitzOnWith_nhds

end DifferentialGeometry.Topology
