import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.Finite

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open _root_.Set _root_.Filter
open scoped _root_.Topology

open _root_.IsCompact in
theorem IsCompact.eventually_forall_of_locally_eventually_on_compacts
    {X α : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    {K : Set X} (hK : IsCompact K) {l : Filter α} {P : α → X → Prop}
    (hP : ∀ x ∈ K, ∃ U ∈ 𝓝 x,
      ∀ L ⊆ U, IsCompact L → ∀ᶠ a in l, ∀ y ∈ L, P a y) :
    ∀ᶠ a in l, ∀ x ∈ K, P a x := by
  have hprod : ∀ᶠ p : α × X in l ×ˢ 𝓝ˢ K, P p.1 p.2 := by
    apply hK.mem_prod_nhdsSet_of_forall
    intro x hx
    obtain ⟨U, hUx, hU⟩ := hP x hx
    obtain ⟨L, hLx, hLU, hLc⟩ := local_compact_nhds hUx
    exact eventually_prod_iff.mpr
      ⟨fun a => ∀ y ∈ L, P a y, hU L hLU hLc,
        fun y => y ∈ L, hLx, fun {a} ha {y} hy => ha y hy⟩
  exact hprod.curry.mono fun _ h => h.self_of_nhdsSet

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsCompact
  let env ← Lean.getEnv
  if env.contains `IsCompact.eventually_forall_of_locally_eventually_on_compacts then
    throwError "Refusing to shadow existing declaration IsCompact.eventually_forall_of_locally_eventually_on_compacts"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.eventually_forall_of_locally_eventually_on_compacts ``Submission.IsCompact.eventually_forall_of_locally_eventually_on_compacts

open _root_.IsCompact in
theorem IsCompact.eventually_mapsTo_of_locally_eventually_eqOn
    {X α ι : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    {Y : α → Type*} {K : Set X} (hK : IsCompact K) {l : Filter α}
    (F : ∀ a, X → Y a) (f : ι → ∀ a, X → Y a)
    (U : ι → Set X) (T : ∀ a, Set (Y a))
    (hcover : ∀ x ∈ K, ∃ i, U i ∈ 𝓝 x)
    (heq : ∀ i L, L ⊆ U i → IsCompact L →
      ∀ᶠ a in l, _root_.Set.EqOn (F a) (f i a) L)
    (hmem : ∀ i L, L ⊆ U i → IsCompact L →
      ∀ᶠ a in l, _root_.Set.MapsTo (f i a) L (T a)) :
    ∀ᶠ a in l, _root_.Set.MapsTo (F a) K (T a) := by
  apply hK.eventually_forall_of_locally_eventually_on_compacts
  intro x hx
  obtain ⟨i, hi⟩ := hcover x hx
  refine ⟨U i, hi, ?_⟩
  intro L hLU hLc
  filter_upwards [heq i L hLU hLc, hmem i L hLU hLc] with a heq hmem y hy
  rw [heq hy]
  exact hmem hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCompact.eventually_mapsTo_of_locally_eventually_eqOn then
    throwError "Refusing to shadow existing declaration IsCompact.eventually_mapsTo_of_locally_eventually_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.eventually_mapsTo_of_locally_eventually_eqOn ``Submission.IsCompact.eventually_mapsTo_of_locally_eventually_eqOn

end

section

open _root_.Set _root_.Filter

open _root_.IsCompact in
theorem IsCompact.exists_open_eventually_forall
    {X α : Type*} [TopologicalSpace X] {K V : Set X} {l : Filter α}
    {P : α → X → Prop} (hK : IsCompact K)
    (hP : ∀ x ∈ K, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      ∀ᶠ a in l, ∀ y ∈ W, P a y) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ W ⊆ V ∧
      ∀ᶠ a in l, ∀ y ∈ W, P a y := by
  classical
  choose W hWo hxW hWV hWP using fun x : K => hP x x.property
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover W hWo (fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩)
  refine ⟨⋃ x ∈ t, W x, isOpen_biUnion fun x _ => hWo x, ht, ?_, ?_⟩
  · exact _root_.Set.iUnion₂_subset fun x _ => hWV x
  · filter_upwards [(_root_.Filter.eventually_all_finset t).mpr (fun x _ => hWP x)] with a ha
    intro y hy
    obtain ⟨x, hxt, hyW⟩ := mem_iUnion₂.mp hy
    exact ha x hxt y hyW

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCompact.exists_open_eventually_forall then
    throwError "Refusing to shadow existing declaration IsCompact.exists_open_eventually_forall"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.exists_open_eventually_forall ``Submission.IsCompact.exists_open_eventually_forall

end
