import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.Real.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter
open scoped _root_.Topology

open _root_.IsCompact in
private theorem IsCompact.exists_prod_Icc_inter_subset_of_local_cylinder
    {X : Type*} [TopologicalSpace X] {K B C : Set X} (hK : IsCompact K)
    {S N : Set (X × ℝ)} (hS : IsClosed S) (hN : IsOpen N) {a : ℝ}
    (hzero : S ∩ (K ×ˢ {a}) ⊆ B ×ˢ _root_.Set.univ)
    (hBN : B ×ˢ {a} ⊆ N) (hcylinder : N ∩ S ⊆ C ×ˢ _root_.Set.univ) :
    ∃ ε > 0, (K ×ˢ _root_.Set.Icc (a - ε) (a + ε)) ∩ S ⊆ C ×ˢ univ := by
  have hcover : K ×ˢ {a} ⊆ N ∪ Sᶜ := by
    intro p hp
    by_cases hs : p ∈ S
    · exact Or.inl (hBN ⟨(hzero ⟨hs, hp⟩).1, hp.2⟩)
    · exact Or.inr hs
  obtain ⟨U, V, _, hV, hKU, haV, hUV⟩ :=
    generalized_tube_lemma hK isCompact_singleton (hN.union hS.isOpen_compl) hcover
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV a (haV (_root_.Set.mem_singleton a))
  refine ⟨r / 2, half_pos hr, ?_⟩
  rintro ⟨x, t⟩ ⟨⟨hx, ht⟩, hs⟩
  have htV : t ∈ V := hball (by
    rw [Metric.mem_ball, Real.dist_eq]
    have hbound : |t - a| ≤ r / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact hbound.trans_lt (half_lt_self hr))
  rcases hUV ⟨hKU hx, htV⟩ with hn | hn
  · exact hcylinder ⟨hn, hs⟩
  · exact False.elim (hn hs)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsCompact
  let target := ``Submission.IsCompact.exists_prod_Icc_inter_subset_of_local_cylinder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `IsCompact.exists_prod_Icc_inter_subset_of_local_cylinder target :: scope.openDecls } }

open _root_.IsCompact in
theorem IsCompact.exists_disjoint_interior_prod_Icc_of_boundary_collar
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {S N : Set (X × ℝ)} (hS : IsClosed S) (hN : IsOpen N) {a : ℝ}
    (hzero : Disjoint S (interior K ×ˢ {a}))
    (hBN : frontier K ×ˢ {a} ⊆ N)
    (hcollar : N ∩ S ⊆ (interior K)ᶜ ×ˢ _root_.Set.univ) :
    ∃ ε > 0, Disjoint S (interior K ×ˢ _root_.Set.Icc (a - ε) (a + ε)) := by
  have hcontact : S ∩ (K ×ˢ {a}) ⊆ frontier K ×ˢ univ := by
    rintro ⟨x, t⟩ ⟨hs, hx, ht⟩
    refine ⟨⟨subset_closure hx, ?_⟩, _root_.Set.mem_univ _⟩
    exact fun hi => Set.disjoint_left.mp hzero hs ⟨hi, ht⟩
  obtain ⟨ε, hε, hεS⟩ := hK.exists_prod_Icc_inter_subset_of_local_cylinder
    hS hN hcontact hBN hcollar
  refine ⟨ε, hε, Set.disjoint_left.mpr ?_⟩
  rintro ⟨x, t⟩ hs ⟨hx, ht⟩
  exact (hεS ⟨⟨interior_subset hx, ht⟩, hs⟩).1 hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCompact.exists_disjoint_interior_prod_Icc_of_boundary_collar then
    throwError "Refusing to shadow existing declaration IsCompact.exists_disjoint_interior_prod_Icc_of_boundary_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.exists_disjoint_interior_prod_Icc_of_boundary_collar ``Submission.IsCompact.exists_disjoint_interior_prod_Icc_of_boundary_collar

open _root_.Continuous in
theorem Continuous.disjoint_range_prod_singleton_of_not_isLocalMax
    {X M : Type*} [TopologicalSpace X] [TopologicalSpace M]
    {e : M → X × ℝ} (he : Continuous e) {U : Set X} (hU : IsOpen U)
    {a b : ℝ} (hab : a < b)
    (hupper : Disjoint (_root_.Set.range e) (U ×ˢ _root_.Set.Ioc a b))
    (hregular : ∀ x, (e x).1 ∈ U → (e x).2 = a →
      ¬ IsLocalMax (fun y => (e y).2) x) :
    Disjoint (_root_.Set.range e) (U ×ˢ {a}) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨x, rfl⟩ ⟨hx, ht⟩
  have heq : (e x).2 = a := mem_singleton_iff.mp ht
  apply hregular x hx heq
  have hxn : ∀ᶠ y in 𝓝 x, (e y).1 ∈ U :=
    (he.fst.continuousAt).preimage_mem_nhds (hU.mem_nhds hx)
  have htn : ∀ᶠ y in 𝓝 x, (e y).2 < b :=
    (he.snd.continuousAt).preimage_mem_nhds (Iio_mem_nhds (heq ▸ hab))
  filter_upwards [hxn, htn] with y hy hyt
  rw [heq]
  by_contra hn
  exact Set.disjoint_left.mp hupper (_root_.Set.mem_range_self y) ⟨hy, lt_of_not_ge hn, hyt.le⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Continuous
  let env ← Lean.getEnv
  if env.contains `Continuous.disjoint_range_prod_singleton_of_not_isLocalMax then
    throwError "Refusing to shadow existing declaration Continuous.disjoint_range_prod_singleton_of_not_isLocalMax"
  Lean.modifyEnv fun env => Lean.addAlias env `Continuous.disjoint_range_prod_singleton_of_not_isLocalMax ``Submission.Continuous.disjoint_range_prod_singleton_of_not_isLocalMax

open _root_.Continuous in
theorem Continuous.exists_disjoint_interior_prod_Icc_of_boundary_collar
    {X M : Type*} [TopologicalSpace X] [TopologicalSpace M]
    {e : M → X × ℝ} (he : Continuous e) (hclosed : IsClosed (_root_.Set.range e))
    {K : Set X} (hK : IsCompact K) {a b : ℝ} (hab : a < b)
    (hupper : Disjoint (_root_.Set.range e) (interior K ×ˢ _root_.Set.Ioc a b))
    (hregular : ∀ x, (e x).1 ∈ interior K → (e x).2 = a →
      ¬ IsLocalMax (fun y => (e y).2) x)
    {N : Set (X × ℝ)} (hN : IsOpen N)
    (hBN : frontier K ×ˢ {a} ⊆ N)
    (hcollar : N ∩ _root_.Set.range e ⊆ (interior K)ᶜ ×ˢ _root_.Set.univ) :
    ∃ ε > 0, Disjoint (_root_.Set.range e) (interior K ×ˢ _root_.Set.Icc (a - ε) (a + ε)) :=
  hK.exists_disjoint_interior_prod_Icc_of_boundary_collar hclosed hN
    (he.disjoint_range_prod_singleton_of_not_isLocalMax isOpen_interior hab hupper hregular)
    hBN hcollar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Continuous.exists_disjoint_interior_prod_Icc_of_boundary_collar then
    throwError "Refusing to shadow existing declaration Continuous.exists_disjoint_interior_prod_Icc_of_boundary_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `Continuous.exists_disjoint_interior_prod_Icc_of_boundary_collar ``Submission.Continuous.exists_disjoint_interior_prod_Icc_of_boundary_collar

open _root_.Continuous in
theorem Continuous.disjoint_range_interior_prod_Icc_of_boundary_collar
    {X M : Type*} [TopologicalSpace X] [TopologicalSpace M]
    {e : M → X × ℝ} (he : Continuous e) (hclosed : IsClosed (_root_.Set.range e))
    {K : Set X} (hK : IsCompact K) {a b : ℝ}
    (hupper : Disjoint (_root_.Set.range e) (interior K ×ˢ {b}))
    (hregular : ∀ x, (e x).1 ∈ interior K → (e x).2 ∈ _root_.Set.Ico a b →
      ¬ IsLocalMax (fun y => (e y).2) x)
    {N : Set (X × ℝ)} (hN : IsOpen N)
    (hBN : frontier K ×ˢ _root_.Set.Icc a b ⊆ N)
    (hcollar : N ∩ _root_.Set.range e ⊆ (interior K)ᶜ ×ˢ _root_.Set.univ) :
    Disjoint (_root_.Set.range e) (interior K ×ˢ _root_.Set.Icc a b) := by
  let C := (K ×ˢ _root_.Set.Icc a b) ∩ _root_.Set.range e ∩ Nᶜ
  have hC : IsCompact C :=
    ((hK.prod _root_.CompactIccSpace.isCompact_Icc).inter_right hclosed).inter_right hN.isClosed_compl
  apply Set.disjoint_left.mpr
  intro p hp hpt
  have hpC : p ∈ C := ⟨⟨⟨interior_subset hpt.1, hpt.2⟩, hp⟩,
    fun hn => (hcollar ⟨hn, hp⟩).1 hpt.1⟩
  obtain ⟨q, hq, hmax⟩ := hC.exists_isMaxOn ⟨p, hpC⟩ continuous_snd.continuousOn
  have hqint : q.1 ∈ interior K := by
    by_contra hn
    exact hq.2 (hBN ⟨⟨subset_closure hq.1.1.1, hn⟩, hq.1.1.2⟩)
  have hqb : q.2 < b := lt_of_le_of_ne hq.1.1.2.2 (by
    intro heq
    exact Set.disjoint_left.mp hupper hq.1.2 ⟨hqint, mem_singleton_iff.mpr heq⟩)
  obtain ⟨x, rfl⟩ := hq.1.2
  apply hregular x hqint ⟨hq.1.1.2.1, hqb⟩
  have hxn : ∀ᶠ y in 𝓝 x, (e y).1 ∈ interior K :=
    (he.fst.continuousAt).preimage_mem_nhds (isOpen_interior.mem_nhds hqint)
  have htn : ∀ᶠ y in 𝓝 x, (e y).2 < b :=
    (he.snd.continuousAt).preimage_mem_nhds (Iio_mem_nhds hqb)
  filter_upwards [hxn, htn] with y hy hyt
  by_cases hay : a ≤ (e y).2
  · apply hmax
    exact ⟨⟨⟨interior_subset hy, hay, hyt.le⟩, _root_.Set.mem_range_self y⟩,
      fun hn => (hcollar ⟨hn, _root_.Set.mem_range_self y⟩).1 hy⟩
  · exact (lt_of_not_ge hay).le.trans hq.1.1.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Continuous.disjoint_range_interior_prod_Icc_of_boundary_collar then
    throwError "Refusing to shadow existing declaration Continuous.disjoint_range_interior_prod_Icc_of_boundary_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `Continuous.disjoint_range_interior_prod_Icc_of_boundary_collar ``Submission.Continuous.disjoint_range_interior_prod_Icc_of_boundary_collar
