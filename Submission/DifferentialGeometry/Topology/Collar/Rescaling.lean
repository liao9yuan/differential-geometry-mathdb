import Mathlib.Topology.Homeomorph.Lemmas
import Submission.DifferentialGeometry.Topology.Maps.CompactModification
import Mathlib.Topology.Instances.Real.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Topology _root_.Filter
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Topology.Collar

variable {B X : Type*} [TopologicalSpace B] [TopologicalSpace X] {ε : ℝ}

def rescale (c : B × _root_.Set.Icc (0 : ℝ) ε → X) (hc : _root_.Topology.IsEmbedding c)
    (σ : C(_root_.Set.Icc (0 : ℝ) ε, _root_.Set.Icc (0 : ℝ) ε)) (x : X) : X := by
  classical
  exact if hx : x ∈ _root_.Set.range c then
    let q := hc.toHomeomorph.symm ⟨x, hx⟩
    c (q.1, σ q.2)
  else x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Collar.rescale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Collar.rescale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Collar.rescale ``Submission.DifferentialGeometry.Topology.Collar.rescale


theorem rescale_apply (c : B × _root_.Set.Icc (0 : ℝ) ε → X) (hc : _root_.Topology.IsEmbedding c)
    (σ : C(_root_.Set.Icc (0 : ℝ) ε, _root_.Set.Icc (0 : ℝ) ε)) (q : B × _root_.Set.Icc (0 : ℝ) ε) :
    rescale c hc σ (c q) = c (q.1, σ q.2) := by
  simp only [rescale, dif_pos (_root_.Set.mem_range_self q), hc.toHomeomorph_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Collar.rescale_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Collar.rescale_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Collar.rescale_apply ``Submission.DifferentialGeometry.Topology.Collar.rescale_apply


theorem rescale_of_not_mem (c : B × _root_.Set.Icc (0 : ℝ) ε → X) (hc : _root_.Topology.IsEmbedding c)
    (σ : C(_root_.Set.Icc (0 : ℝ) ε, _root_.Set.Icc (0 : ℝ) ε)) {x : X} (hx : x ∉ _root_.Set.range c) :
    rescale c hc σ x = x := dif_neg hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Collar.rescale_of_not_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Collar.rescale_of_not_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Collar.rescale_of_not_mem ``Submission.DifferentialGeometry.Topology.Collar.rescale_of_not_mem

private theorem continuousOn_rescale_range (c : B × _root_.Set.Icc (0 : ℝ) ε → X) (hc : _root_.Topology.IsEmbedding c)
    (σ : C(_root_.Set.Icc (0 : ℝ) ε, _root_.Set.Icc (0 : ℝ) ε)) :
    ContinuousOn (rescale c hc σ) (_root_.Set.range c) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hh := hc.toHomeomorph.symm.continuous
  have h := hc.continuous.comp (hh.fst.prodMk (σ.continuous.comp hh.snd))
  exact h.congr (fun x => by simp only [Set.domRestrict, rescale, dif_pos x.property, Function.comp_apply])

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Collar.continuousOn_rescale_range
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Collar.continuousOn_rescale_range target :: scope.openDecls } }

private theorem rescale_eq_self_off_core (c : B × _root_.Set.Icc (0 : ℝ) ε → X) (hc : _root_.Topology.IsEmbedding c)
    (σ : C(_root_.Set.Icc (0 : ℝ) ε, _root_.Set.Icc (0 : ℝ) ε)) {k : ℝ}
    (hσ : ∀ t : _root_.Set.Icc (0 : ℝ) ε, k ≤ t.val → σ t = t)
    {x : X} (hx : x ∉ c '' {q | (q.2 : ℝ) ≤ k}) : rescale c hc σ x = x := by
  by_cases hxc : x ∈ _root_.Set.range c
  · obtain ⟨q, rfl⟩ := hxc
    have ht : k ≤ q.2.val := le_of_lt (lt_of_not_ge (fun ht => hx ⟨q, ht, rfl⟩))
    rw [rescale_apply, hσ q.2 ht]
  · exact rescale_of_not_mem c hc σ hxc

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Collar.rescale_eq_self_off_core
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Collar.rescale_eq_self_off_core target :: scope.openDecls } }

theorem continuous_rescale [CompactSpace B] [T2Space X]
    (c : B × _root_.Set.Icc (0 : ℝ) ε → X) (hc : _root_.Topology.IsEmbedding c)
    (σ : C(_root_.Set.Icc (0 : ℝ) ε, _root_.Set.Icc (0 : ℝ) ε)) {k δ : ℝ}
    (hkδ : k < δ) (hopen : IsOpen (c '' {q | (q.2 : ℝ) < δ}))
    (hσ : ∀ t : _root_.Set.Icc (0 : ℝ) ε, k ≤ t.val → σ t = t) :
    Continuous (rescale c hc σ) := by
  let K := c '' {q | (q.2 : ℝ) ≤ k}
  have hK : IsCompact K :=
    ((isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const).isCompact).image
      hc.continuous
  have hKsub : K ⊆ c '' {q | (q.2 : ℝ) < δ} := _root_.Set.image_mono (fun _ hq => hq.trans_lt hkδ)
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ c '' {q | (q.2 : ℝ) < δ}
  · exact (continuousOn_rescale_range c hc σ).continuousAt
      (_root_.Filter.mem_of_superset (hopen.mem_nhds hx) (_root_.Set.image_subset_range _ _))
  · have hxK : x ∉ K := fun h => hx (hKsub h)
    apply continuousAt_id.congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
    exact rescale_eq_self_off_core c hc σ hσ hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Collar.continuous_rescale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Collar.continuous_rescale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Collar.continuous_rescale ``Submission.DifferentialGeometry.Topology.Collar.continuous_rescale


theorem isClosedMap_rescale [CompactSpace B] [T2Space X]
    (c : B × _root_.Set.Icc (0 : ℝ) ε → X) (hc : _root_.Topology.IsEmbedding c)
    (σ : C(_root_.Set.Icc (0 : ℝ) ε, _root_.Set.Icc (0 : ℝ) ε)) {k δ : ℝ}
    (hkδ : k < δ) (hopen : IsOpen (c '' {q | (q.2 : ℝ) < δ}))
    (hσ : ∀ t : _root_.Set.Icc (0 : ℝ) ε, k ≤ t.val → σ t = t) :
    IsClosedMap (rescale c hc σ) := by
  have hK : IsCompact (c '' {q | (q.2 : ℝ) ≤ k}) :=
    ((isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const).isCompact).image
      hc.continuous
  exact DifferentialGeometry.Topology.isClosedMap_of_compact_modification
    (continuous_rescale c hc σ hkδ hopen hσ) hK
    (fun _ hx => rescale_eq_self_off_core c hc σ hσ hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Collar.isClosedMap_rescale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Collar.isClosedMap_rescale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Collar.isClosedMap_rescale ``Submission.DifferentialGeometry.Topology.Collar.isClosedMap_rescale


theorem injective_rescale (c : B × _root_.Set.Icc (0 : ℝ) ε → X) (hc : _root_.Topology.IsEmbedding c)
    (σ : C(_root_.Set.Icc (0 : ℝ) ε, _root_.Set.Icc (0 : ℝ) ε)) (hσ : _root_.Function.Injective σ) :
    Injective (rescale c hc σ) := by
  intro x y h
  by_cases hx : x ∈ _root_.Set.range c
  · obtain ⟨p, rfl⟩ := hx
    rw [rescale_apply] at h
    by_cases hy : y ∈ _root_.Set.range c
    · obtain ⟨q, rfl⟩ := hy
      rw [rescale_apply] at h
      have hh := hc.injective h
      have hf := congrArg (fun r : B × _root_.Set.Icc (0 : ℝ) ε => r.1) hh
      have ht := congrArg (fun r : B × _root_.Set.Icc (0 : ℝ) ε => r.2) hh
      exact congrArg c (Prod.ext hf (hσ ht))
    · rw [rescale_of_not_mem c hc σ hy] at h
      exact False.elim (hy ⟨(p.1, σ p.2), h⟩)
  · rw [rescale_of_not_mem c hc σ hx] at h
    by_cases hy : y ∈ _root_.Set.range c
    · obtain ⟨q, rfl⟩ := hy
      rw [rescale_apply] at h
      exact False.elim (hx ⟨(q.1, σ q.2), h.symm⟩)
    · rwa [rescale_of_not_mem c hc σ hy] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Collar.injective_rescale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Collar.injective_rescale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Collar.injective_rescale ``Submission.DifferentialGeometry.Topology.Collar.injective_rescale


theorem range_rescale (c : B × _root_.Set.Icc (0 : ℝ) ε → X) (hc : _root_.Topology.IsEmbedding c)
    (σ : C(_root_.Set.Icc (0 : ℝ) ε, _root_.Set.Icc (0 : ℝ) ε)) {a : ℝ}
    (hσ : _root_.Set.range σ = {t : _root_.Set.Icc (0 : ℝ) ε | a ≤ t.val}) :
    range (rescale c hc σ) = (_root_.Set.range c)ᶜ ∪ c '' {q | a ≤ (q.2 : ℝ)} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hx : x ∈ _root_.Set.range c
    · obtain ⟨q, rfl⟩ := hx
      rw [rescale_apply]
      have ht : σ q.2 ∈ _root_.Set.range σ := _root_.Set.mem_range_self q.2
      rw [hσ] at ht
      exact Or.inr ⟨(q.1, σ q.2), ht, rfl⟩
    · rw [rescale_of_not_mem c hc σ hx]
      exact Or.inl hx
  · rintro (hy | ⟨q, hq, rfl⟩)
    · exact ⟨y, rescale_of_not_mem c hc σ hy⟩
    · have ht : q.2 ∈ _root_.Set.range σ := by rw [hσ]; exact hq
      obtain ⟨t, ht⟩ := ht
      refine ⟨c (q.1, t), ?_⟩
      rw [rescale_apply, ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Collar.range_rescale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Collar.range_rescale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Collar.range_rescale ``Submission.DifferentialGeometry.Topology.Collar.range_rescale

theorem isClosedEmbedding_rescale [CompactSpace B] [T2Space X]
    (c : B × _root_.Set.Icc (0 : ℝ) ε → X) (hc : _root_.Topology.IsEmbedding c)
    (σ : C(_root_.Set.Icc (0 : ℝ) ε, _root_.Set.Icc (0 : ℝ) ε)) (hσinj : _root_.Function.Injective σ) {k δ : ℝ}
    (hkδ : k < δ) (hopen : IsOpen (c '' {q | (q.2 : ℝ) < δ}))
    (hσ : ∀ t : _root_.Set.Icc (0 : ℝ) ε, k ≤ t.val → σ t = t) :
    IsClosedEmbedding (rescale c hc σ) :=
  Topology.IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap.mpr
    ⟨continuous_rescale c hc σ hkδ hopen hσ, injective_rescale c hc σ hσinj,
      isClosedMap_rescale c hc σ hkδ hopen hσ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Collar.isClosedEmbedding_rescale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Collar.isClosedEmbedding_rescale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Collar.isClosedEmbedding_rescale ``Submission.DifferentialGeometry.Topology.Collar.isClosedEmbedding_rescale

end DifferentialGeometry.Topology.Collar
