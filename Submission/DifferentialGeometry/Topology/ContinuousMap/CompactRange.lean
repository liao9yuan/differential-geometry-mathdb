import Submission.DifferentialGeometry.Topology.UniformConvergence
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.ContinuousMap.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric

namespace ContinuousMap
open _root_.ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [PseudoMetricSpace Y] [LocallyCompactSpace Y]

open _root_.ContinuousMap in
theorem exists_isCompact_range_subset_of_dist_le
    (f : C(X, Y)) {U : Set Y} (hU : IsOpen U) (hf : _root_.Set.range f ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : Set Y, IsCompact K ∧ K ⊆ U ∧
      ∀ g : C(X, Y), _root_.Dist.dist g f ≤ δ → _root_.Set.range g ⊆ K := by
  have hcompact : IsCompact (_root_.Set.range f) := isCompact_range f.continuous
  obtain ⟨ε, hε, hεU⟩ := hcompact.exists_cthickening_subset_open hU hf
  obtain ⟨η, hη, hηcompact⟩ := hcompact.exists_isCompact_cthickening
  let δ := _root_.Min.min ε η
  refine ⟨δ, lt_min hε hη, _root_.Metric.cthickening δ (_root_.Set.range f), ?_, ?_, ?_⟩
  · exact hηcompact.of_isClosed_subset _root_.Metric.isClosed_cthickening
      (_root_.Metric.cthickening_mono (min_le_right ε η) (_root_.Set.range f))
  · exact (_root_.Metric.cthickening_mono (min_le_left ε η) (_root_.Set.range f)).trans hεU
  · intro g hg y hy
    obtain ⟨x, rfl⟩ := hy
    exact _root_.Metric.mem_cthickening_of_dist_le (g x) (f x) δ (_root_.Set.range f)
      (_root_.Set.mem_range_self x) ((_root_.ContinuousMap.dist_apply_le_dist x).trans hg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMap.exists_isCompact_range_subset_of_dist_le then
    throwError "Refusing to shadow existing declaration ContinuousMap.exists_isCompact_range_subset_of_dist_le"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMap.exists_isCompact_range_subset_of_dist_le ``Submission.ContinuousMap.exists_isCompact_range_subset_of_dist_le

end ContinuousMap

open _root_.ContinuousAt in
theorem ContinuousAt.exists_isCompact_range_subset
    {X Y Z : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [TopologicalSpace Z]
    {F : Z → C(X, Y)} {z : Z} (hF : ContinuousAt F z)
    {U : Set Y} (hU : IsOpen U) (hz : _root_.Set.range (F z) ⊆ U) :
    ∃ K : Set Y, IsCompact K ∧ K ⊆ U ∧
      ∀ᶠ w in nhds z, _root_.Set.range (F w) ⊆ K := by
  obtain ⟨K, hK, hzK, hKU⟩ :=
    exists_compact_between (isCompact_range (F z).continuous) hU hz
  refine ⟨K, hK, hKU, ?_⟩
  exact (hF.eventually
    (ContinuousMap.eventually_range_subset isOpen_interior hzK)).mono
      fun w hw => hw.trans interior_subset

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContinuousAt
  let env ← Lean.getEnv
  if env.contains `ContinuousAt.exists_isCompact_range_subset then
    throwError "Refusing to shadow existing declaration ContinuousAt.exists_isCompact_range_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAt.exists_isCompact_range_subset ``Submission.ContinuousAt.exists_isCompact_range_subset

open _root_.Filter _root_.Set

namespace TendstoUniformlyOn
open _root_.TendstoUniformlyOn

variable {X S A E : Type*} [TopologicalSpace A] [CompactSpace A]
  [PseudoMetricSpace E] {l : Filter X} {K : Set S}
  {q : X → S → C(A, E)} {q₀ : S → C(A, E)}

open _root_.TendstoUniformlyOn in
theorem continuousMap_eval (hq : TendstoUniformlyOn q q₀ l K) :
    TendstoUniformlyOn (fun x (p : S × A) => q x p.1 p.2)
      (fun p : S × A => q₀ p.1 p.2) l (K ×ˢ _root_.Set.univ) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hq ε hε] with x hx p hp
  exact (ContinuousMap.dist_apply_le_dist p.2).trans_lt (hx p.1 hp.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TendstoUniformlyOn.continuousMap_eval then
    throwError "Refusing to shadow existing declaration TendstoUniformlyOn.continuousMap_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `TendstoUniformlyOn.continuousMap_eval ``Submission.TendstoUniformlyOn.continuousMap_eval

variable [TopologicalSpace S] [LocallyCompactSpace E]

open _root_.TendstoUniformlyOn in
theorem exists_isCompact_eventually_forall_eval_mem
    (hq : TendstoUniformlyOn q q₀ l K) (hK : IsCompact K)
    (hq₀ : ContinuousOn q₀ K) {U : Set E} (hU : IsOpen U)
    (hmap : ∀ s ∈ K, ∀ a, q₀ s a ∈ U) :
    ∃ L : Set E, IsCompact L ∧ L ⊆ U ∧
      (∀ s ∈ K, ∀ a, q₀ s a ∈ interior L) ∧
      ∀ᶠ x in l, ∀ s ∈ K, ∀ a, q x s a ∈ L := by
  have hq₀eval : ContinuousOn (fun p : S × A => q₀ p.1 p.2) (K ×ˢ _root_.Set.univ) :=
    continuous_eval.comp_continuousOn (hq₀.prodMap continuousOn_id)
  have hq₀U : _root_.Set.MapsTo (fun p : S × A => q₀ p.1 p.2) (K ×ˢ _root_.Set.univ) U :=
    fun p hp => hmap p.1 hp.1 p.2
  obtain ⟨L, hL, hLU, hq₀L, hqL⟩ :=
    hq.continuousMap_eval.exists_isCompact_eventually_mapsTo_of_isCompact
      (hK.prod isCompact_univ) hq₀eval hU hq₀U
  refine ⟨L, hL, hLU, ?_, ?_⟩
  · intro s hs a
    exact hq₀L (x := (s, a)) ⟨hs, _root_.Set.mem_univ a⟩
  · filter_upwards [hqL] with x hx s hs a
    exact hx (x := (s, a)) ⟨hs, _root_.Set.mem_univ a⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TendstoUniformlyOn.exists_isCompact_eventually_forall_eval_mem then
    throwError "Refusing to shadow existing declaration TendstoUniformlyOn.exists_isCompact_eventually_forall_eval_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `TendstoUniformlyOn.exists_isCompact_eventually_forall_eval_mem ``Submission.TendstoUniformlyOn.exists_isCompact_eventually_forall_eval_mem

end TendstoUniformlyOn
