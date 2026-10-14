import Submission.DifferentialGeometry.Topology.Morse.RegularLevel.Components

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.Morse

theorem image_superlevel_component_level_of_no_critical_values
    {E H M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace X]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {e : M → X × ℝ} (he : _root_.Topology.IsEmbedding e)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => (e x).2))
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact ((fun x => (e x).2) ⁻¹' _root_.Set.Icc a b))
    (hregular : ∀ x, (e x).2 ∈ _root_.Set.Icc a b → ¬ IsCriticalPointAt I (fun y => (e y).2) x)
    {p : M} (hp : b ≤ (e p).2) (Φ : ℝ → X → X)
    (hΦ : ∀ x, (e x).2 = a → ContinuousOn (fun t => Φ t (e x).1) (_root_.Set.Icc a b))
    (hΦa : _root_.Set.EqOn (Φ a) id ((fun x => (e x).1) '' {x | (e x).2 = a}))
    (hlevels : ∀ t ∈ _root_.Set.Icc a b,
      Φ t '' ((fun x => (e x).1) '' {x | (e x).2 = a}) =
        (fun x => (e x).1) '' {x | (e x).2 = t}) :
    ∀ t ∈ _root_.Set.Icc a b,
      Φ t '' ((fun x => (e x).1) ''
        (connectedComponentIn {x | a ≤ (e x).2} p ∩ {x | (e x).2 = a})) =
      (fun x => (e x).1) ''
        (connectedComponentIn {x | t ≤ (e x).2} p ∩ {x | (e x).2 = t}) := by
  let : PreconnectedSpace (_root_.Set.Icc a b) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hpath (x : M) (hx : (e x).2 = a) :
      ∃ γ : _root_.Set.Icc a b → M, Continuous γ ∧
        (∀ t, e (γ t) = (Φ t.val (e x).1, t.val)) ∧
        γ ⟨a, le_rfl, hab⟩ = x := by
    have hrange (t : _root_.Set.Icc a b) : (Φ t.val (e x).1, t.val) ∈ _root_.Set.range e := by
      have hm : Φ t.val (e x).1 ∈ (fun x => (e x).1) '' {x | (e x).2 = t.val} := by
        rw [← hlevels t.val t.property]
        exact ⟨(e x).1, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨y, hy, hyeq⟩ := hm
      exact ⟨y, Prod.ext hyeq hy⟩
    let γ : _root_.Set.Icc a b → M := fun t => he.toHomeomorph.symm
      ⟨(Φ t.val (e x).1, t.val), hrange t⟩
    have heq (t : _root_.Set.Icc a b) : e (γ t) = (Φ t.val (e x).1, t.val) :=
      congrArg Subtype.val (he.toHomeomorph.apply_symm_apply
        ⟨(Φ t.val (e x).1, t.val), hrange t⟩)
    refine ⟨γ, he.toHomeomorph.symm.continuous.comp
      (((continuousOn_iff_continuous_domRestrict.mp (hΦ x hx)).prodMk
        continuous_subtype_val).subtype_mk _), heq, ?_⟩
    apply he.injective
    rw [heq]
    exact Prod.ext (hΦa ⟨x, hx, rfl⟩) hx.symm
  have hpathmem (x : M) (hx : (e x).2 = a) (t : _root_.Set.Icc a b) :
      ∃ y ∈ connectedComponentIn {x | a ≤ (e x).2} x,
        e y = (Φ t.val (e x).1, t.val) := by
    obtain ⟨γ, hγ, heq, hγa⟩ := hpath x hx
    refine ⟨γ t, ?_, heq t⟩
    apply (isPreconnected_range hγ).subset_connectedComponentIn
      (show x ∈ _root_.Set.range γ from ⟨⟨a, le_rfl, hab⟩, hγa⟩)
    · rintro _ ⟨u, rfl⟩
      change a ≤ (e (γ u)).2
      rw [heq]
      exact u.property.1
    · exact _root_.Set.mem_range_self t
  intro t ht
  have hnested := connectedComponentIn_superlevel_inter_eq_of_no_critical_values hf ht.1
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (fun _ hx => ⟨hx.1, hx.2.trans ht.2⟩))
    (fun x hx => hregular x ⟨hx.1, hx.2.trans ht.2⟩) (ht.2.trans hp)
  apply Subset.antisymm
  · rintro _ ⟨_, ⟨x, ⟨hxC, hxlevel⟩, rfl⟩, rfl⟩
    obtain ⟨y, hyC, hyeq⟩ := hpathmem x hxlevel ⟨t, ht⟩
    have hylevel : (e y).2 = t := congrArg Prod.snd hyeq
    refine ⟨y, ⟨?_, hylevel⟩, congrArg Prod.fst hyeq⟩
    rw [← hnested]
    refine ⟨?_, hylevel.ge⟩
    rw [connectedComponentIn_eq hxC]
    exact hyC
  · rintro _ ⟨y, ⟨hyC, hylevel⟩, rfl⟩
    have hymem : (e y).1 ∈ (fun x => (e x).1) '' {x | (e x).2 = t} :=
      ⟨y, hylevel, rfl⟩
    rw [← hlevels t ht] at hymem
    obtain ⟨_, ⟨x, hxlevel, rfl⟩, hxy⟩ := hymem
    obtain ⟨z, hzC, hzeq⟩ := hpathmem x hxlevel ⟨t, ht⟩
    have hzy : z = y := he.injective (hzeq.trans (Prod.ext hxy hylevel.symm))
    subst z
    refine ⟨(e x).1, ⟨x, ⟨?_, hxlevel⟩, rfl⟩, hxy⟩
    have hyCa : y ∈ connectedComponentIn {x | a ≤ (e x).2} p :=
      connectedComponentIn_mono p (fun z hz => ht.1.trans (show t ≤ (e z).2 from hz)) hyC
    rw [connectedComponentIn_eq hyCa, ← connectedComponentIn_eq hzC]
    exact mem_connectedComponentIn hxlevel.ge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.image_superlevel_component_level_of_no_critical_values then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.image_superlevel_component_level_of_no_critical_values"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.image_superlevel_component_level_of_no_critical_values ``Submission.DifferentialGeometry.Topology.Morse.image_superlevel_component_level_of_no_critical_values

end DifferentialGeometry.Topology.Morse
