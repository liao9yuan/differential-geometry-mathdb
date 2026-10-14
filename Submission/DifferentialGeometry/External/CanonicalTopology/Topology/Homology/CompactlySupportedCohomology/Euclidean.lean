import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.EuclideanCompactHomology
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.NormedLocalCapDuality
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactlySupportedCohomology.Cap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
noncomputable section

open _root_.TopologicalSpace _root_.Set _root_.Metric

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_compact_superset_with_bijective_point_map
    (n : ℕ) (p : E) (K : _root_.TopologicalSpace.Compacts E) :
    ∃ L : _root_.TopologicalSpace.Compacts E, K ≤ L ∧ ∃ hpL : ({p} : _root_.TopologicalSpace.Compacts E) ≤ L,
      Function.Bijective (integralRelativeCohomologyMap n (ContinuousMap.id E)
        (show _root_.Set.MapsTo (ContinuousMap.id E) (L : Set E)ᶜ ({p}ᶜ : Set E) from
          compl_subset_compl.mpr hpL)) := by
  obtain ⟨r, hr, hKr⟩ := K.isCompact.isBounded.subset_closedBall_lt 0 p
  let L : _root_.TopologicalSpace.Compacts E := ⟨closedBall p r, _root_.ProperSpace.isCompact_closedBall p r⟩
  have hp : p ∈ _root_.Metric.closedBall p r := _root_.Metric.mem_closedBall_self hr.le
  refine ⟨L, hKr, singleton_subset_iff.mpr hp, ?_⟩
  exact integralRelativeCohomologyMap_boundedStarConvex_bijective n hp
    ((convex_closedBall p r).starConvex hp) _root_.Metric.isBounded_closedBall

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.exists_compact_superset_with_bijective_point_map
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.exists_compact_superset_with_bijective_point_map target :: scope.openDecls } }

theorem integralRelativeToCompactlySupportedCohomology_singleton_bijective
    (n : ℕ) (p : E) :
    Function.Bijective (integralRelativeToCompactlySupportedCohomology n
      ({p} : _root_.TopologicalSpace.Compacts E)) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro α hα
    obtain ⟨K, hpK, hK⟩ :=
      (integralRelativeToCompactlySupportedCohomology_eq_zero_iff n {p} α).mp hα
    obtain ⟨L, hKL, hpL, hL⟩ := exists_compact_superset_with_bijective_point_map n p K
    apply hL.injective
    have hcomp := LinearMap.congr_fun (integralRelativeCohomologyMap_comp n
      (ContinuousMap.id E) (ContinuousMap.id E)
      (show _root_.Set.MapsTo (ContinuousMap.id E) (L : Set E)ᶜ (K : Set E)ᶜ from
        compl_subset_compl.mpr hKL)
      (show _root_.Set.MapsTo (ContinuousMap.id E) (K : Set E)ᶜ ({p}ᶜ : Set E) from
        compl_subset_compl.mpr hpK)) α
    simp only [LinearMap.comp_apply] at hcomp
    rw [hK, map_zero] at hcomp
    exact hcomp.trans (map_zero _).symm
  · intro α
    obtain ⟨K, β, rfl⟩ := integralCompactlySupportedCohomology_exists_representative n α
    obtain ⟨L, hKL, hpL, hL⟩ := exists_compact_superset_with_bijective_point_map n p K
    obtain ⟨γ, hγ⟩ := hL.surjective (integralRelativeCohomologyMap n
      (ContinuousMap.id E)
      (show _root_.Set.MapsTo (ContinuousMap.id E) (L : Set E)ᶜ (K : Set E)ᶜ from
        compl_subset_compl.mpr hKL) β)
    refine ⟨γ, ?_⟩
    rw [← integralRelativeToCompactlySupportedCohomology_map n {p} L hpL γ, hγ]
    exact integralRelativeToCompactlySupportedCohomology_map n K L hKL β

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeToCompactlySupportedCohomology_singleton_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeToCompactlySupportedCohomology_singleton_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeToCompactlySupportedCohomology_singleton_bijective ``Submission.DifferentialGeometry.Topology.integralRelativeToCompactlySupportedCohomology_singleton_bijective

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.Metric _root_.Module _root_.Set

universe u

namespace DifferentialGeometry.Topology

private theorem integralInnerProductRelativeCohomology_subsingleton
    (n : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hn : n ≠ _root_.Module.finrank ℝ E) :
    Subsingleton (integralRelativeCohomology n ({0}ᶜ : Set E)) := by
  by_cases hlarge : 2 ≤ _root_.Module.finrank ℝ E
  · have hd : _root_.Module.finrank ℝ E = (_root_.Module.finrank ℝ E - 2) + 2 := by omega
    exact integralEuclideanRelativeCohomology_subsingleton (_root_.Module.finrank ℝ E - 2) n E hd (by omega)
  by_cases hzero : _root_.Module.finrank ℝ E = 0
  · have hempty : ({0}ᶜ : Set E) = ∅ := by
      ext x
      constructor
      · intro hx
        exact (hx (finrank_zero_iff_forall_zero.mp hzero x)).elim
      · intro hx
        exact hx.elim
    rw [hempty]
    let _ := integralSingularCohomology_subsingleton_of_contractibleSpace E n (by omega)
    exact ⟨fun α β => (integralRelativeToAbsoluteCohomologyEmptyEquiv n E).injective
      (Subsingleton.elim _ _)⟩
  have hone : _root_.Module.finrank ℝ E = 1 := by omega
  cases n with
  | zero =>
      let v := unitSpherePointOfFinrankPos (E := E) (by omega)
      exact integralRelativeCohomology_zero_subsingleton_of_pathConnectedSpace
        ({0}ᶜ : Set E) ⟨(v : E), ne_zero_of_mem_unit_sphere v⟩
  | succ n =>
      cases n with
      | zero => exact (hn hone.symm).elim
      | succ n =>
          let _ := integralSphereCohomology_subsingleton 0 (n + 1) E hone (by omega) (by omega)
          let e := puncturedSpaceSphereHomotopyEquiv E
          have hs :=
            (integralRelativeCohomologyConnecting_bijective_of_contractibleSpace
              (n + 1) (by omega) ({0}ᶜ : Set E)).surjective.comp
                (integralSingularCohomologyMap_bijective_of_homotopyEquiv e (n + 1)).surjective
          have hz (α : integralRelativeCohomology (n + 2) ({0}ᶜ : Set E)) : α = 0 := by
            obtain ⟨β, rfl⟩ := hs α
            change integralRelativeCohomologyConnecting (n + 1) ({0}ᶜ : Set E)
              (integralSingularCohomologyMap (n + 1) e.toFun β) = 0
            rw [Subsingleton.elim β 0, map_zero, map_zero]
          exact ⟨fun α β => (hz α).trans (hz β).symm⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralInnerProductRelativeCohomology_subsingleton
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralInnerProductRelativeCohomology_subsingleton target :: scope.openDecls } }

private theorem integralRelativeCohomology_point_compl_subsingleton
    (n : ℕ) {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : E) (hn : n ≠ _root_.Module.finrank ℝ E) :
    Subsingleton (integralRelativeCohomology n ({p}ᶜ : Set E)) := by
  let ι := Module.Free.ChooseBasisIndex ℝ E
  let b : _root_.Module.Basis ι ℝ E := Module.Free.chooseBasis ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ ι :=
    b.equivFunL.trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let h := e.symm.toHomeomorph.trans (Homeomorph.addRight p)
  have hp : h 0 = p := by
    change e.symm 0 + p = p
    rw [map_zero, zero_add]
  have hd : n ≠ _root_.Module.finrank ℝ (EuclideanSpace ℝ ι) := by
    rw [← e.toLinearEquiv.finrank_eq]
    exact hn
  let _ := integralInnerProductRelativeCohomology_subsingleton n (EuclideanSpace ℝ ι) hd
  let f : ContinuousMap (EuclideanSpace ℝ ι) E := ⟨h, h.continuous⟩
  have hf : _root_.Set.MapsTo f ({0}ᶜ : Set (EuclideanSpace ℝ ι)) ({h 0}ᶜ : Set E) :=
    fun _ hx => h.injective.ne hx
  let g := h.subtype (p := fun x : EuclideanSpace ℝ ι => x ∈ ({0}ᶜ : Set (EuclideanSpace ℝ ι)))
    (q := fun y : E => y ∈ ({h 0}ᶜ : Set E)) (fun x => h.injective.ne_iff.symm)
  have hcoh : Function.Bijective (integralRelativeCohomologyMap n f hf) := by
    apply integralRelativeCohomologyMap_bijective_of_absolute_and_subspace
    · intro k
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv h.toHomotopyEquiv k
    · intro k
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv g.toHomotopyEquiv k
  have hout : Subsingleton (integralRelativeCohomology n ({h 0}ᶜ : Set E)) :=
    ⟨fun α β => hcoh.injective (Subsingleton.elim _ _)⟩
  rwa [hp] at hout

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralRelativeCohomology_point_compl_subsingleton
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralRelativeCohomology_point_compl_subsingleton target :: scope.openDecls } }

theorem integralCompactlySupportedCohomology_subsingleton_of_ne_finrank
    (n : ℕ) (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hn : n ≠ _root_.Module.finrank ℝ E) :
    Subsingleton (integralCompactlySupportedCohomology n E) := by
  let _ := integralRelativeCohomology_point_compl_subsingleton n (0 : E) hn
  have hs := (integralRelativeToCompactlySupportedCohomology_singleton_bijective n (0 : E)).surjective
  have hz (α : integralCompactlySupportedCohomology n E) : α = 0 := by
    obtain ⟨β, rfl⟩ := hs α
    rw [Subsingleton.elim β 0, map_zero]
  exact ⟨fun α β => (hz α).trans (hz β).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_ne_finrank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_ne_finrank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_ne_finrank ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_ne_finrank

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.TopologicalSpace _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_local_generator
    (p : E) (c : ∀ K : _root_.TopologicalSpace.Compacts E, integralRelativeHomology (_root_.Module.finrank ℝ E) (K : Set E)ᶜ)
    (hc : ∀ (K L : _root_.TopologicalSpace.Compacts E) (h : K ≤ L),
      integralRelativeHomologyMap (_root_.Module.finrank ℝ E) (ContinuousMap.id E)
        (show _root_.Set.MapsTo (ContinuousMap.id E) (L : Set E)ᶜ (K : Set E)ᶜ from
          compl_subset_compl.mpr h) (c L) = c K)
    (hp : Function.Bijective (fun z : ℤ => z • c {p})) :
    ∃! D : integralCompactlySupportedCohomology (_root_.Module.finrank ℝ E) E →ₗ[ℤ]
        integralSingularHomology 0 E,
      (∀ (K : _root_.TopologicalSpace.Compacts E) (α : integralRelativeCohomology (_root_.Module.finrank ℝ E) (K : Set E)ᶜ),
        D (integralRelativeToCompactlySupportedCohomology (_root_.Module.finrank ℝ E) K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set E)ᶜ (_root_.Module.finrank ℝ E) 0 α (c K)) ∧
      Function.Bijective D := by
  obtain ⟨D, hD, huniq⟩ :=
    exists_unique_integralCompactlySupportedCohomology_cap (_root_.Module.finrank ℝ E) 0 c hc
  have hcomp : Function.Bijective (fun α : integralRelativeCohomology (_root_.Module.finrank ℝ E)
      ({p}ᶜ : Set E) =>
        D (integralRelativeToCompactlySupportedCohomology (_root_.Module.finrank ℝ E) {p} α)) := by
    have heq : (fun α : integralRelativeCohomology (_root_.Module.finrank ℝ E) ({p}ᶜ : Set E) =>
        D (integralRelativeToCompactlySupportedCohomology (_root_.Module.finrank ℝ E) {p} α)) =
        fun α => integralRelativeCohomologyCapToAbsolute ({p}ᶜ : Set E)
          (_root_.Module.finrank ℝ E) 0 α (c {p}) := funext (hD {p})
    rw [heq]
    exact integralLocalHomology_cap_bijective_of_generator p (c {p}) hp
  have hbij : Function.Bijective D :=
    (Function.Bijective.of_comp_iff D
      (integralRelativeToCompactlySupportedCohomology_singleton_bijective
        (_root_.Module.finrank ℝ E) p)).mp hcomp
  exact ⟨D, ⟨hD, hbij⟩, fun D' hD' => huniq D' hD'.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_local_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_local_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_local_generator ``Submission.DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_local_generator

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.TopologicalSpace _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

theorem exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_local_generator_of_add_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k m : ℕ) (hkm : k + m = _root_.Module.finrank ℝ E) (p : E)
    (c : ∀ K : _root_.TopologicalSpace.Compacts E, integralRelativeHomology (k + m) (K : Set E)ᶜ)
    (hc : ∀ (K L : _root_.TopologicalSpace.Compacts E) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id E)
        (show _root_.Set.MapsTo (ContinuousMap.id E) (L : Set E)ᶜ (K : Set E)ᶜ from
          compl_subset_compl.mpr h) (c L) = c K)
    (hp : Function.Bijective (fun z : ℤ => z • c {p})) :
    ∃! D : integralCompactlySupportedCohomology k E →ₗ[ℤ] integralSingularHomology m E,
      (∀ (K : _root_.TopologicalSpace.Compacts E) (α : integralRelativeCohomology k (K : Set E)ᶜ),
        D (integralRelativeToCompactlySupportedCohomology k K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set E)ᶜ k m α (c K)) ∧
      Function.Bijective D := by
  by_cases hm : m = 0
  · subst m
    have hk : k = _root_.Module.finrank ℝ E := by simpa only [Nat.add_zero] using hkm
    subst k
    exact exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_local_generator
      p c hc hp
  obtain ⟨D, hD, huniq⟩ := exists_unique_integralCompactlySupportedCohomology_cap k m c hc
  let _ := integralCompactlySupportedCohomology_subsingleton_of_ne_finrank k E (by omega)
  let _ := integralSingularHomology_subsingleton_of_contractible m hm E
  have hbij : Function.Bijective D :=
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun β => ⟨0, Subsingleton.elim _ β⟩⟩
  exact ⟨D, ⟨hD, hbij⟩, fun D' hD' => huniq D' hD'.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_local_generator_of_add_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_local_generator_of_add_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_local_generator_of_add_eq ``Submission.DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_local_generator_of_add_eq

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.TopologicalSpace _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

theorem exists_integralCompactlySupportedCohomology_cap_bijective
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k m : ℕ) (hkm : k + m = _root_.Module.finrank ℝ E) :
    ∃ c : ∀ K : _root_.TopologicalSpace.Compacts E, integralRelativeHomology (k + m) (K : Set E)ᶜ,
      (∀ (K L : _root_.TopologicalSpace.Compacts E) (h : K ≤ L),
        integralRelativeHomologyMap (k + m) (ContinuousMap.id E)
          (show _root_.Set.MapsTo (ContinuousMap.id E) (L : Set E)ᶜ (K : Set E)ᶜ from
            compl_subset_compl.mpr h) (c L) = c K) ∧
      Function.Bijective (fun z : ℤ => z • c {0}) ∧
      ∃! D : integralCompactlySupportedCohomology k E →ₗ[ℤ] integralSingularHomology m E,
        (∀ (K : _root_.TopologicalSpace.Compacts E) (α : integralRelativeCohomology k (K : Set E)ᶜ),
          D (integralRelativeToCompactlySupportedCohomology k K α) =
            integralRelativeCohomologyCapToAbsolute (K : Set E)ᶜ k m α (c K)) ∧
        Function.Bijective D := by
  have hpoint := exists_integralLocalHomology_generator (0 : E)
  rw [← hkm] at hpoint
  obtain ⟨a, ha⟩ := hpoint
  obtain ⟨c, ⟨hc, hc0⟩, _⟩ :=
    exists_unique_compact_homology_family_of_local_class (k + m) (0 : E) a
  have hgen : Function.Bijective (fun z : ℤ => z • c {0}) := by
    rw [hc0]
    exact ha
  exact ⟨c, hc, hgen,
    exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_local_generator_of_add_eq
      k m hkm (0 : E) c hc hgen⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_integralCompactlySupportedCohomology_cap_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_integralCompactlySupportedCohomology_cap_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_integralCompactlySupportedCohomology_cap_bijective ``Submission.DifferentialGeometry.Topology.exists_integralCompactlySupportedCohomology_cap_bijective

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.TopologicalSpace _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

theorem exists_integralCompactlySupportedCohomology_top_cap_bijective
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ c : ∀ K : _root_.TopologicalSpace.Compacts E, integralRelativeHomology (_root_.Module.finrank ℝ E) (K : Set E)ᶜ,
      (∀ (K L : _root_.TopologicalSpace.Compacts E) (h : K ≤ L),
        integralRelativeHomologyMap (_root_.Module.finrank ℝ E) (ContinuousMap.id E)
          (show _root_.Set.MapsTo (ContinuousMap.id E) (L : Set E)ᶜ (K : Set E)ᶜ from
            compl_subset_compl.mpr h) (c L) = c K) ∧
      Function.Bijective (fun z : ℤ => z • c {0}) ∧
      ∃! D : integralCompactlySupportedCohomology (_root_.Module.finrank ℝ E) E →ₗ[ℤ]
          integralSingularHomology 0 E,
        (∀ (K : _root_.TopologicalSpace.Compacts E) (α : integralRelativeCohomology (_root_.Module.finrank ℝ E) (K : Set E)ᶜ),
          D (integralRelativeToCompactlySupportedCohomology (_root_.Module.finrank ℝ E) K α) =
            integralRelativeCohomologyCapToAbsolute (K : Set E)ᶜ (_root_.Module.finrank ℝ E) 0 α (c K)) ∧
        Function.Bijective D := by
  exact exists_integralCompactlySupportedCohomology_cap_bijective E (_root_.Module.finrank ℝ E) 0
    (Nat.add_zero (_root_.Module.finrank ℝ E))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_integralCompactlySupportedCohomology_top_cap_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_integralCompactlySupportedCohomology_top_cap_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_integralCompactlySupportedCohomology_top_cap_bijective ``Submission.DifferentialGeometry.Topology.exists_integralCompactlySupportedCohomology_top_cap_bijective

end DifferentialGeometry.Topology

end
