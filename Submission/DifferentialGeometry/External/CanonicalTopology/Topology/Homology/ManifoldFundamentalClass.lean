import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalOrientation
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ManifoldCompactHomology
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeEmpty
import Mathlib.Topology.Connected.Clopen
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.EuclideanLocalTop

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open _root_.Set _root_.Module
open scoped _root_.Topology

universe u

namespace DifferentialGeometry.Topology

private theorem absolute_restriction_apply
    {X : Type u} [TopologicalSpace X] (n : ℕ) {K L : Set X} (hLK : L ⊆ K)
    (a : integralSingularHomology n X) :
    integralRelativeHomologyMap n (ContinuousMap.id X)
      (show Kᶜ ⊆ Lᶜ from compl_subset_compl.mpr hLK)
      (integralAbsoluteToRelative n Kᶜ a) = integralAbsoluteToRelative n Lᶜ a := by
  have h := LinearMap.congr_fun (integralAbsoluteToRelative_natural n (ContinuousMap.id X)
    (show Kᶜ ⊆ Lᶜ from compl_subset_compl.mpr hLK)) a
  simpa only [LinearMap.comp_apply, integralSingularHomologyMap_id, LinearMap.id_apply] using h.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.absolute_restriction_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.absolute_restriction_apply target :: scope.openDecls } }

theorem exists_unique_absolute_class_of_locally_realized_family
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X] [CompactSpace X]
    (n : ℕ) (hn : _root_.Module.finrank ℝ E ≤ n) (μ : ∀ x : X, integralLocalHomology n x)
    (hlocal : ∀ x : X, ∃ L : Set X, IsCompact L ∧ x ∈ interior L ∧
      ∃ a : integralRelativeHomology n Lᶜ, ∀ y (hy : y ∈ L),
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show Lᶜ ⊆ ({y}ᶜ : Set X) from
            compl_subset_compl.mpr (singleton_subset_iff.mpr hy)) a = μ y) :
    ∃! a : integralSingularHomology n X, ∀ x : X,
      integralAbsoluteToRelative n ({x}ᶜ : Set X) a = μ x := by
  have hex := exists_unique_compact_class_of_locally_realized_family
    (E := E) n hn _root_.Set.univ isCompact_univ μ (fun x _ => by
      obtain ⟨L, hL, hx, a, ha⟩ := hlocal x
      exact ⟨L, hL, hx, a, fun y hy => ha y hy.2⟩)
  simp only [_root_.Set.mem_univ, forall_true_left] at hex
  obtain ⟨b, hb, huniq⟩ := hex
  have hbij : Function.Bijective (integralAbsoluteToRelative n (_root_.Set.univ : Set X)ᶜ) := by
    rw [_root_.Set.compl_univ]
    exact (integralAbsoluteToRelativeEmptyEquiv n X).bijective
  let e := LinearEquiv.ofBijective (integralAbsoluteToRelative n (_root_.Set.univ : Set X)ᶜ) hbij
  have hmap (a : integralSingularHomology n X) (x : X) :
      integralRelativeHomologyMap n (ContinuousMap.id X)
        (show (_root_.Set.univ : Set X)ᶜ ⊆ ({x}ᶜ : Set X) from
          compl_subset_compl.mpr (_root_.Set.subset_univ _)) (e a) =
      integralAbsoluteToRelative n ({x}ᶜ : Set X) a := by
    change integralRelativeHomologyMap n (ContinuousMap.id X)
      (show (_root_.Set.univ : Set X)ᶜ ⊆ ({x}ᶜ : Set X) from
          compl_subset_compl.mpr (_root_.Set.subset_univ _))
      (integralAbsoluteToRelative n (_root_.Set.univ : Set X)ᶜ a) = _
    exact absolute_restriction_apply n (_root_.Set.subset_univ {x}) a
  refine ⟨e.symm b, ?_, ?_⟩
  · intro x
    rw [← hmap, e.apply_symm_apply]
    exact hb x
  · intro a ha
    apply e.injective
    rw [e.apply_symm_apply]
    apply huniq
    intro x
    rw [hmap]
    exact ha x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_unique_absolute_class_of_locally_realized_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_unique_absolute_class_of_locally_realized_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_unique_absolute_class_of_locally_realized_family ``Submission.DifferentialGeometry.Topology.exists_unique_absolute_class_of_locally_realized_family

private theorem isOpen_absolute_local_zero_set
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (n : ℕ) (a : integralSingularHomology n X) :
    IsOpen {x : X | integralAbsoluteToRelative n ({x}ᶜ : Set X) a = 0} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨L, _, hxL, _, hz⟩ := exists_compact_neighborhood_relative_restriction_eq_zero
    n _root_.Set.univ _root_.Set.univ x (_root_.Set.mem_univ x) isOpen_univ (_root_.Set.mem_univ x)
    (integralAbsoluteToRelative n (_root_.Set.univ : Set X)ᶜ a)
    ((absolute_restriction_apply n (_root_.Set.subset_univ {x}) a).trans hx)
  rw [absolute_restriction_apply n _root_.Set.inter_subset_left] at hz
  filter_upwards [isOpen_interior.mem_nhds hxL] with y hy
  have hyL : ({y} : Set X) ⊆ _root_.Set.univ ∩ L :=
    singleton_subset_iff.mpr ⟨mem_univ y, interior_subset hy⟩
  rw [← absolute_restriction_apply n hyL a, hz, map_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.isOpen_absolute_local_zero_set
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.isOpen_absolute_local_zero_set target :: scope.openDecls } }

private theorem isClopen_absolute_local_zero_set_of_local_generators
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (n : ℕ) (μ a : integralSingularHomology n X)
    (hμ : ∀ x : X, Function.Bijective
      (fun k : ℤ => k • integralAbsoluteToRelative n ({x}ᶜ : Set X) μ)) :
    IsClopen {x : X | integralAbsoluteToRelative n ({x}ᶜ : Set X) a = 0} := by
  refine ⟨?_, isOpen_absolute_local_zero_set n a⟩
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨k, hk⟩ := (hμ x).2 (integralAbsoluteToRelative n ({x}ᶜ : Set X) a)
  change k • integralAbsoluteToRelative n ({x}ᶜ : Set X) μ =
    integralAbsoluteToRelative n ({x}ᶜ : Set X) a at hk
  have hzero : integralAbsoluteToRelative n ({x}ᶜ : Set X) (a - k • μ) = 0 := by
    rw [map_sub, map_zsmul, hk, sub_self]
  filter_upwards [(isOpen_absolute_local_zero_set n (a - k • μ)).mem_nhds hzero] with y hy
  intro hya
  change integralAbsoluteToRelative n ({y}ᶜ : Set X) a = 0 at hya
  have hk0 : k = 0 := by
    apply (hμ y).1
    change k • integralAbsoluteToRelative n ({y}ᶜ : Set X) μ =
      (0 : ℤ) • integralAbsoluteToRelative n ({y}ᶜ : Set X) μ
    rw [zero_smul]
    rw [map_sub, map_zsmul, hya] at hy
    exact neg_eq_zero.mp (by simpa only [zero_sub] using hy)
  apply hx
  change integralAbsoluteToRelative n ({x}ᶜ : Set X) a = 0
  rw [← hk, hk0, zero_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.isClopen_absolute_local_zero_set_of_local_generators
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.isClopen_absolute_local_zero_set_of_local_generators target :: scope.openDecls } }

private theorem absolute_eq_zero_of_local_restrictions
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X] [CompactSpace X]
    (n : ℕ) (hn : _root_.Module.finrank ℝ E ≤ n) (a : integralSingularHomology n X)
    (ha : ∀ x : X, integralAbsoluteToRelative n ({x}ᶜ : Set X) a = 0) : a = 0 := by
  have hz : integralAbsoluteToRelative n (_root_.Set.univ : Set X)ᶜ a = 0 := by
    apply integralRelativeHomology_eq_zero_of_local_restrictions
      (E := E) n hn _root_.Set.univ isCompact_univ
    intro x hx
    rw [absolute_restriction_apply n (_root_.Set.subset_univ {x})]
    exact ha x
  rw [_root_.Set.compl_univ] at hz
  apply (integralAbsoluteToRelativeEmptyEquiv n X).injective
  change integralAbsoluteToRelative n (∅ : Set X) a = integralAbsoluteToRelative n (∅ : Set X) 0
  simpa only [map_zero] using hz

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.absolute_eq_zero_of_local_restrictions
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.absolute_eq_zero_of_local_restrictions target :: scope.openDecls } }

theorem integralAbsoluteToRelative_bijective_of_local_generators
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X] [CompactSpace X]
    [PreconnectedSpace X] (n : ℕ) (hn : _root_.Module.finrank ℝ E ≤ n)
    (μ : integralSingularHomology n X)
    (hμ : ∀ y : X, Function.Bijective
      (fun k : ℤ => k • integralAbsoluteToRelative n ({y}ᶜ : Set X) μ)) (x : X) :
    Function.Bijective (integralAbsoluteToRelative n ({x}ᶜ : Set X)) := by
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace E X
  refine ⟨?_, ?_⟩
  · apply (injective_iff_map_eq_zero _).2
    intro a ha
    have heq := (isClopen_absolute_local_zero_set_of_local_generators n μ a hμ).eq_univ ⟨x, ha⟩
    apply absolute_eq_zero_of_local_restrictions (E := E) n hn a
    intro y
    have hy : y ∈ {y : X | integralAbsoluteToRelative n ({y}ᶜ : Set X) a = 0} := by
      rw [heq]
      exact _root_.Set.mem_univ y
    exact hy
  · intro b
    obtain ⟨k, hk⟩ := (hμ x).2 b
    exact ⟨k • μ, (map_zsmul _ _ _).trans hk⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralAbsoluteToRelative_bijective_of_local_generators then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralAbsoluteToRelative_bijective_of_local_generators"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralAbsoluteToRelative_bijective_of_local_generators ``Submission.DifferentialGeometry.Topology.integralAbsoluteToRelative_bijective_of_local_generators

private theorem absolute_generator_of_local_generators
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X] [CompactSpace X]
    [PreconnectedSpace X] (n : ℕ) (hn : _root_.Module.finrank ℝ E ≤ n)
    (μ : integralSingularHomology n X)
    (hμ : ∀ y : X, Function.Bijective
      (fun k : ℤ => k • integralAbsoluteToRelative n ({y}ᶜ : Set X) μ)) (x : X) :
    Function.Bijective (fun k : ℤ => k • μ) := by
  have hp := integralAbsoluteToRelative_bijective_of_local_generators (E := E) n hn μ hμ x
  refine ⟨?_, ?_⟩
  · intro k l h
    apply (hμ x).1
    have heq := congrArg (integralAbsoluteToRelative n ({x}ᶜ : Set X)) h
    simpa only [map_zsmul] using heq
  · intro a
    obtain ⟨k, hk⟩ := (hμ x).2 (integralAbsoluteToRelative n ({x}ᶜ : Set X) a)
    refine ⟨k, hp.1 ?_⟩
    simpa only [map_zsmul] using hk

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.absolute_generator_of_local_generators
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.absolute_generator_of_local_generators target :: scope.openDecls } }

theorem exists_unique_absolute_generator_of_locally_realized_family
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X] [CompactSpace X]
    [PreconnectedSpace X] [Nonempty X]
    (n : ℕ) (hn : _root_.Module.finrank ℝ E ≤ n) (μ : ∀ x : X, integralLocalHomology n x)
    (hgen : ∀ x : X, Function.Bijective (fun k : ℤ => k • μ x))
    (hlocal : ∀ x : X, ∃ L : Set X, IsCompact L ∧ x ∈ interior L ∧
      ∃ a : integralRelativeHomology n Lᶜ, ∀ y (hy : y ∈ L),
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show Lᶜ ⊆ ({y}ᶜ : Set X) from
            compl_subset_compl.mpr (singleton_subset_iff.mpr hy)) a = μ y) :
    ∃ a : integralSingularHomology n X,
      (∀ x : X, integralAbsoluteToRelative n ({x}ᶜ : Set X) a = μ x) ∧
      (∀ b : integralSingularHomology n X,
        (∀ x : X, integralAbsoluteToRelative n ({x}ᶜ : Set X) b = μ x) → b = a) ∧
      Function.Bijective (fun k : ℤ => k • a) ∧
      ∀ x : X, Function.Bijective (integralAbsoluteToRelative n ({x}ᶜ : Set X)) := by
  obtain ⟨a, ha, hu⟩ := exists_unique_absolute_class_of_locally_realized_family
    (E := E) n hn μ hlocal
  have hgena : ∀ x : X, Function.Bijective
      (fun k : ℤ => k • integralAbsoluteToRelative n ({x}ᶜ : Set X) a) := by
    intro x
    rw [ha x]
    exact hgen x
  exact ⟨a, ha, hu,
    absolute_generator_of_local_generators (E := E) n hn a hgena (Classical.arbitrary X),
    integralAbsoluteToRelative_bijective_of_local_generators (E := E) n hn a hgena⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_unique_absolute_generator_of_locally_realized_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_unique_absolute_generator_of_locally_realized_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_unique_absolute_generator_of_locally_realized_family ``Submission.DifferentialGeometry.Topology.exists_unique_absolute_generator_of_locally_realized_family

end DifferentialGeometry.Topology

open _root_.CategoryTheory _root_.Bundle
open scoped _root_.Manifold

namespace DifferentialGeometry.Topology

open _root_.Classical in
theorem exists_unique_absolute_generator_of_tangent_orientation_locality
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    [CompactSpace M] [PreconnectedSpace M] [Nonempty M]
    (o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E)))
    (ω : Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (c : integralLocalHomology (Module.finrank ℝ E) (0 : E))
    (hc : Function.Bijective (fun k : ℤ => k • c))
    (hlocal : ∀ p : M, ∃ (U : Set M) (hUs : U ⊆ (chartAt E p).source),
      IsOpen U ∧ p ∈ U ∧ ∀ (x : M) (hx : x ∈ U),
        (Orientation.map _
          ((_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
            (by simpa only [TangentBundle.trivializationAt_baseSet] using
              (hUs hx))).toLinearEquiv
          (o x)) =
          (Orientation.map _
          ((_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ p
            (by simpa only [TangentBundle.trivializationAt_baseSet] using
              (mem_chart_source E p))).toLinearEquiv
          (o p))) :
    ∃ a : integralSingularHomology (Module.finrank ℝ E) M,
      (∀ (p x : M) (hx : x ∈ (chartAt E p).source),
        ((integralRelativeHomologyMap (Module.finrank ℝ E)
          (toContinuousMap (Homeomorph.subRight (chartAt E p x)))
          (show _root_.Set.MapsTo (Homeomorph.subRight (chartAt E p x))
            ({chartAt E p x}ᶜ : Set E) ({0}ᶜ : Set E) from
              fun _ hz => sub_ne_zero.mpr hz)).comp
          (integralLocalHomologyOpenPartialHomeomorphIso (Module.finrank ℝ E)
            (chartAt E p) x hx).hom.hom)
          (integralAbsoluteToRelative (Module.finrank ℝ E) ({x}ᶜ : Set M) a) =
            if (Orientation.map _
          ((_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
            (by simpa only [TangentBundle.trivializationAt_baseSet] using
              hx)).toLinearEquiv
          (o x)) = ω then c else -c) ∧
      (∀ b : integralSingularHomology (Module.finrank ℝ E) M,
        (∀ (p x : M) (hx : x ∈ (chartAt E p).source),
          ((integralRelativeHomologyMap (Module.finrank ℝ E)
          (toContinuousMap (Homeomorph.subRight (chartAt E p x)))
          (show _root_.Set.MapsTo (Homeomorph.subRight (chartAt E p x))
            ({chartAt E p x}ᶜ : Set E) ({0}ᶜ : Set E) from
              fun _ hz => sub_ne_zero.mpr hz)).comp
          (integralLocalHomologyOpenPartialHomeomorphIso (Module.finrank ℝ E)
            (chartAt E p) x hx).hom.hom)
            (integralAbsoluteToRelative (Module.finrank ℝ E) ({x}ᶜ : Set M) b) =
              if (Orientation.map _
          ((_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
            (by simpa only [TangentBundle.trivializationAt_baseSet] using
              hx)).toLinearEquiv
          (o x)) = ω then c else -c) → b = a) ∧
      Function.Bijective (fun k : ℤ => k • a) ∧
      ∀ x : M, Function.Bijective
        (integralAbsoluteToRelative (Module.finrank ℝ E) ({x}ᶜ : Set M)) := by
  let normalizedChartLocalIso (n : ℕ) (p x : M) (hx : x ∈ (chartAt E p).source) :
      integralLocalHomology n x ≅ integralLocalHomology n (0 : E) :=
    integralLocalHomologyOpenPartialHomeomorphIso n (chartAt E p) x hx ≪≫
      integralRelativeHomologyHomeomorphIso n (Homeomorph.subRight (chartAt E p x))
        ({chartAt E p x}ᶜ : Set E) {0}ᶜ
        (fun _ hz => sub_ne_zero.mpr hz)
        (fun z hz heq => by
          apply hz
          change z + chartAt E p x = chartAt E p x at heq
          exact add_right_cancel (heq.trans (zero_add _).symm))
  let tangentChartOrientation (p x : M) (hx : x ∈ (chartAt E p).source)
      (o : Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E))) :
      Orientation ℝ E (Fin (Module.finrank ℝ E)) :=
    Orientation.map _
      ((_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
        (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).toLinearEquiv o
  obtain ⟨μ, ⟨hmaps, hreal⟩, _⟩ :=
    exists_locally_realized_family_of_tangent_orientation_locality o ω c hlocal
  have hgen (x : M) : Function.Bijective (fun k : ℤ => k • μ x) := by
    let e := (normalizedChartLocalIso (Module.finrank ℝ E) x x
      (mem_chart_source E x)).toLinearEquiv
    let d := if tangentChartOrientation x x (mem_chart_source E x) (o x) = ω then c else -c
    have hd : Function.Bijective (fun k : ℤ => k • d) := by
      dsimp only [d]
      split_ifs
      · exact hc
      · refine ⟨?_, ?_⟩
        · intro k l h
          apply neg_injective
          apply hc.1
          simpa only [neg_zsmul, zsmul_neg] using h
        · intro b
          obtain ⟨k, hk⟩ := hc.2 b
          exact ⟨-k, by simpa only [neg_zsmul, zsmul_neg, neg_neg] using hk⟩
    have hmap (k : ℤ) : e (k • μ x) = k • d := by
      rw [map_zsmul]
      change k • (normalizedChartLocalIso (Module.finrank ℝ E) x x
        (mem_chart_source E x)).hom.hom (μ x) = k • d
      have hcoord : (normalizedChartLocalIso (Module.finrank ℝ E) x x
          (mem_chart_source E x)).hom.hom (μ x) = d := hmaps x x (mem_chart_source E x)
      rw [hcoord]
    refine ⟨?_, ?_⟩
    · intro k l h
      apply hd.1
      change k • d = l • d
      change k • μ x = l • μ x at h
      rw [← hmap k, ← hmap l, h]
    · intro b
      obtain ⟨k, hk⟩ := hd.2 (e b)
      exact ⟨k, e.injective ((hmap k).trans hk)⟩
  obtain ⟨a, ha, hu, hga, hpa⟩ := exists_unique_absolute_generator_of_locally_realized_family
    (E := E) (Module.finrank ℝ E) le_rfl μ hgen hreal
  refine ⟨a, ?_, ?_, hga, hpa⟩
  · intro p x hx
    rw [ha x]
    exact hmaps p x hx
  · intro b hb
    apply hu b
    intro x
    apply (normalizedChartLocalIso (Module.finrank ℝ E) x x
      (mem_chart_source E x)).toLinearEquiv.injective
    exact (hb x x (mem_chart_source E x)).trans (hmaps x x (mem_chart_source E x)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_unique_absolute_generator_of_tangent_orientation_locality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_unique_absolute_generator_of_tangent_orientation_locality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_unique_absolute_generator_of_tangent_orientation_locality ``Submission.DifferentialGeometry.Topology.exists_unique_absolute_generator_of_tangent_orientation_locality

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

open _root_.Classical in
theorem exists_unique_absolute_generator_of_tangent_local_frames
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    [CompactSpace M] [PreconnectedSpace M] [Nonempty M]
    (o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E)))
    (ω : Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (c : integralLocalHomology (Module.finrank ℝ E) (0 : E))
    (hc : Function.Bijective (fun k : ℤ => k • c))
    (hframes : ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∃ s : Fin (Module.finrank ℝ E) → (x : M) → TangentSpace 𝓘(ℝ, E) x,
        ∃ hs : IsLocalFrameOn 𝓘(ℝ, E) E 0 s U,
          ∀ (x : M) (hx : x ∈ U), (hs.toBasisAt hx).orientation = o x) :
    ∃ a : integralSingularHomology (Module.finrank ℝ E) M,
      (∀ (p x : M) (hx : x ∈ (chartAt E p).source),
        ((integralRelativeHomologyMap (Module.finrank ℝ E)
          (toContinuousMap (Homeomorph.subRight (chartAt E p x)))
          (show _root_.Set.MapsTo (Homeomorph.subRight (chartAt E p x))
            ({chartAt E p x}ᶜ : Set E) ({0}ᶜ : Set E) from
              fun _ hz => sub_ne_zero.mpr hz)).comp
          (integralLocalHomologyOpenPartialHomeomorphIso (Module.finrank ℝ E)
            (chartAt E p) x hx).hom.hom)
          (integralAbsoluteToRelative (Module.finrank ℝ E) ({x}ᶜ : Set M) a) =
            if (Orientation.map _
          ((_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
            (by simpa only [TangentBundle.trivializationAt_baseSet] using
              hx)).toLinearEquiv
          (o x)) = ω then c else -c) ∧
      (∀ b : integralSingularHomology (Module.finrank ℝ E) M,
        (∀ (p x : M) (hx : x ∈ (chartAt E p).source),
          ((integralRelativeHomologyMap (Module.finrank ℝ E)
          (toContinuousMap (Homeomorph.subRight (chartAt E p x)))
          (show _root_.Set.MapsTo (Homeomorph.subRight (chartAt E p x))
            ({chartAt E p x}ᶜ : Set E) ({0}ᶜ : Set E) from
              fun _ hz => sub_ne_zero.mpr hz)).comp
          (integralLocalHomologyOpenPartialHomeomorphIso (Module.finrank ℝ E)
            (chartAt E p) x hx).hom.hom)
            (integralAbsoluteToRelative (Module.finrank ℝ E) ({x}ᶜ : Set M) b) =
              if (Orientation.map _
          ((_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
            (by simpa only [TangentBundle.trivializationAt_baseSet] using
              hx)).toLinearEquiv
          (o x)) = ω then c else -c) → b = a) ∧
      Function.Bijective (fun k : ℤ => k • a) ∧
      ∀ x : M, Function.Bijective
        (integralAbsoluteToRelative (Module.finrank ℝ E) ({x}ᶜ : Set M)) := by
  exact exists_unique_absolute_generator_of_tangent_orientation_locality o ω c hc
    (tangent_orientation_locality_of_local_frames o hframes)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_unique_absolute_generator_of_tangent_local_frames then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_unique_absolute_generator_of_tangent_local_frames"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_unique_absolute_generator_of_tangent_local_frames ``Submission.DifferentialGeometry.Topology.exists_unique_absolute_generator_of_tangent_local_frames

end DifferentialGeometry.Topology

end

section

open _root_.Bundle _root_.Module _root_.Set
open scoped _root_.Manifold

universe u

namespace DifferentialGeometry.Topology

theorem integralAbsoluteToRelative_bijective_of_simplyConnected
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    [CompactSpace M] [SimplyConnectedSpace M] (p : M) :
    Function.Bijective (integralAbsoluteToRelative (_root_.Module.finrank ℝ E) ({p}ᶜ : Set M)) := by
  let ω := (Module.finBasis ℝ E).orientation
  let ωp := Orientation.map (Fin (_root_.Module.finrank ℝ E))
    ((_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using
        mem_chart_source E p)).symm.toLinearEquiv ω
  obtain ⟨o, _, hlocal⟩ := exists_tangent_orientation_locality_of_simplyConnected p ωp
  obtain ⟨c, hc⟩ := exists_integralLocalHomology_generator (0 : E)
  obtain ⟨_, _, _, _, hpoints⟩ :=
    exists_unique_absolute_generator_of_tangent_orientation_locality o ω c hc hlocal
  exact hpoints p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralAbsoluteToRelative_bijective_of_simplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralAbsoluteToRelative_bijective_of_simplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralAbsoluteToRelative_bijective_of_simplyConnected ``Submission.DifferentialGeometry.Topology.integralAbsoluteToRelative_bijective_of_simplyConnected

theorem exists_unique_absolute_class_of_simplyConnected
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    [CompactSpace M] [SimplyConnectedSpace M] (p : M)
    (c : integralLocalHomology (_root_.Module.finrank ℝ E) p) :
    ∃! a : integralSingularHomology (_root_.Module.finrank ℝ E) M,
      integralAbsoluteToRelative (_root_.Module.finrank ℝ E) ({p}ᶜ : Set M) a = c := by
  have h := integralAbsoluteToRelative_bijective_of_simplyConnected (E := E) p
  obtain ⟨a, ha⟩ := h.2 c
  exact ⟨a, ha, fun b hb => h.1 (hb.trans ha.symm)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_unique_absolute_class_of_simplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_unique_absolute_class_of_simplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_unique_absolute_class_of_simplyConnected ``Submission.DifferentialGeometry.Topology.exists_unique_absolute_class_of_simplyConnected

end DifferentialGeometry.Topology

end
