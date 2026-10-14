import Submission.DifferentialGeometry.Topology.Manifold.ChartBasis
import Submission.DifferentialGeometry.Topology.Homology.CompactHomologyFamily
import Submission.DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.EuclideanOpen

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.TopologicalSpace _root_.Submission.TopologicalSpace

universe u

namespace DifferentialGeometry.Topology

variable {E M : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

omit [ChartedSpace E M] in
private theorem compact_support_vanishing_of_chart_basis
    {B : Set (Set M)} (hB : _root_.TopologicalSpace.IsTopologicalBasis B)
    (hinter : ∀ U ∈ B, ∀ V ∈ B, U ∩ V ∈ B)
    (hchart : ∀ U ∈ B, ∃ S : Set E, IsOpen S ∧ Nonempty (U ≃ₜ S))
    (W : Set M) (hW : IsOpen W) (n : ℕ) (hn : Module.finrank ℝ E < n) :
    Subsingleton (integralCompactlySupportedCohomology n W) := by
  apply integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_basis hB
    (fun U hU V hV => Or.inl (hinter U hU V hV)) (Module.finrank ℝ E) ?_ hW n hn
  intro U hU k hk
  obtain ⟨S, hS, ⟨e⟩⟩ := hchart U hU
  let _ := integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_finrank_lt S hS k hk
  exact (integralCompactlySupportedCohomologyPushforward_homeomorph_bijective k e).injective.subsingleton

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.compact_support_vanishing_of_chart_basis
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.compact_support_vanishing_of_chart_basis target :: scope.openDecls } }

theorem integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_chartedSpace
    (W : Set M) (hW : IsOpen W) (n : ℕ) (hn : Module.finrank ℝ E < n) :
    Subsingleton (integralCompactlySupportedCohomology n W) := by
  obtain ⟨B, hB, hinter, hchart⟩ := ChartedSpace.exists_isTopologicalBasis_homeomorph_open E M
  exact compact_support_vanishing_of_chart_basis hB hinter hchart W hW n hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_chartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_chartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_chartedSpace ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_chartedSpace

theorem integralCompactlySupportedCohomology_subsingleton_of_chartedSpace
    (n : ℕ) (hn : Module.finrank ℝ E < n) :
    Subsingleton (integralCompactlySupportedCohomology n M) := by
  let _ := integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_chartedSpace
    (E := E) (_root_.Set.univ : Set M) isOpen_univ n hn
  exact (integralCompactlySupportedCohomologyPushforward_homeomorph_bijective n
    (Homeomorph.Set.univ M).symm).injective.subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_chartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_chartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_chartedSpace ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_chartedSpace

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.Set _root_.TopologicalSpace _root_.Submission.TopologicalSpace

universe u v

namespace DifferentialGeometry.Topology

variable {E M : Type u} {H : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [T2Space M]
  [ChartedSpace H M]

theorem integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_boundaryless
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (W : Set M) (hW : IsOpen W) (n : ℕ) (hn : Module.finrank ℝ E < n) :
    Subsingleton (integralCompactlySupportedCohomology n W) := by
  obtain ⟨B, hB, hinter, hchart⟩ := I.exists_isTopologicalBasis_homeomorph_open M
  exact compact_support_vanishing_of_chart_basis hB hinter hchart W hW n hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_boundaryless then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_boundaryless"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_boundaryless ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_boundaryless

theorem integralCompactlySupportedCohomology_subsingleton_of_boundaryless
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (n : ℕ) (hn : Module.finrank ℝ E < n) :
    Subsingleton (integralCompactlySupportedCohomology n M) := by
  let _ := integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_boundaryless
    I (_root_.Set.univ : Set M) isOpen_univ n hn
  exact (integralCompactlySupportedCohomologyPushforward_homeomorph_bijective n
    (Homeomorph.Set.univ M).symm).injective.subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_boundaryless then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_boundaryless"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_boundaryless ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_boundaryless

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.Set _root_.TopologicalSpace _root_.Submission.TopologicalSpace

namespace DifferentialGeometry.Topology

variable {E X : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]
  [TopologicalSpace X] [T2Space X]

private theorem compact_support_cap_bijective_of_chart_basis
    (B : Set (Set X)) (hB : _root_.TopologicalSpace.IsTopologicalBasis B)
    (hinter : ∀ U ∈ B, ∀ V ∈ B, U ∩ V ∈ B)
    (hchart : ∀ U ∈ B, ∃ S : Set E, IsOpen S ∧ Nonempty (U ≃ₜ S))
    (W : Set X) (hW : IsOpen W) (k m : ℕ) (hkm : k + m = Module.finrank ℝ E)
    (cW : ∀ K : _root_.TopologicalSpace.Compacts W, integralRelativeHomology (k + m) (K : Set W)ᶜ)
    (hcW : ∀ (K L : _root_.TopologicalSpace.Compacts W) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id W)
        (show (L : Set W)ᶜ ⊆ (K : Set W)ᶜ from compl_subset_compl.mpr h) (cW L) = cW K)
    (hpW : ∀ p : W, Function.Bijective (fun z : ℤ => z • cW {p}))
    (D : integralCompactlySupportedCohomology k W →ₗ[ℤ] integralSingularHomology m W)
    (hD : ∀ (K : _root_.TopologicalSpace.Compacts W) (α : integralRelativeCohomology k (K : Set W)ᶜ),
      D (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set W)ᶜ k m α (cW K)) :
    Function.Bijective D := by
  apply integralCompactlySupportedCohomology_cap_bijective_of_basis
    (Module.finrank ℝ E) B hB (fun U hU V hV => Or.inl (hinter U hU V hV))
    ?_ ?_ W hW k m hkm cW hcW hpW D hD
  · intro U hU i j hij c hc hp DU hDU
    obtain ⟨S, hS, ⟨e⟩⟩ := hchart U hU
    exact integralCompactlySupportedCohomology_cap_bijective_of_homeomorph
      i j e.symm c hc hp
      (fun cS hcS hpS DS hDS => integralCompactlySupportedCohomology_cap_bijective_of_isOpen
        S hS i j hij cS hcS hpS DS hDS) DU hDU
  · intro q hq S hS
    exact compact_support_vanishing_of_chart_basis hB hinter hchart S hS q hq

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.compact_support_cap_bijective_of_chart_basis
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.compact_support_cap_bijective_of_chart_basis target :: scope.openDecls } }

variable [ChartedSpace E X]

theorem integralCompactlySupportedCohomology_cap_bijective_of_isOpen_of_chartedSpace
    (W : Set X) (hW : IsOpen W) (k m : ℕ) (hkm : k + m = Module.finrank ℝ E)
    (cW : ∀ K : _root_.TopologicalSpace.Compacts W, integralRelativeHomology (k + m) (K : Set W)ᶜ)
    (hcW : ∀ (K L : _root_.TopologicalSpace.Compacts W) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id W)
        (show (L : Set W)ᶜ ⊆ (K : Set W)ᶜ from compl_subset_compl.mpr h) (cW L) = cW K)
    (hpW : ∀ p : W, Function.Bijective (fun z : ℤ => z • cW {p}))
    (D : integralCompactlySupportedCohomology k W →ₗ[ℤ] integralSingularHomology m W)
    (hD : ∀ (K : _root_.TopologicalSpace.Compacts W) (α : integralRelativeCohomology k (K : Set W)ᶜ),
      D (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set W)ᶜ k m α (cW K)) :
    Function.Bijective D := by
  obtain ⟨B, hB, hinter, hchart⟩ := ChartedSpace.exists_isTopologicalBasis_homeomorph_open E X
  exact compact_support_cap_bijective_of_chart_basis B hB hinter hchart
    W hW k m hkm cW hcW hpW D hD

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_cap_bijective_of_isOpen_of_chartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomology_cap_bijective_of_isOpen_of_chartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_cap_bijective_of_isOpen_of_chartedSpace ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomology_cap_bijective_of_isOpen_of_chartedSpace

theorem integralCompactlySupportedCohomology_cap_bijective_of_chartedSpace
    (k m : ℕ) (hkm : k + m = Module.finrank ℝ E)
    (cX : ∀ K : _root_.TopologicalSpace.Compacts X, integralRelativeHomology (k + m) (K : Set X)ᶜ)
    (hcX : ∀ (K L : _root_.TopologicalSpace.Compacts X) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id X)
        (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr h) (cX L) = cX K)
    (hpX : ∀ p : X, Function.Bijective (fun z : ℤ => z • cX {p}))
    (D : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology m X)
    (hD : ∀ (K : _root_.TopologicalSpace.Compacts X) (α : integralRelativeCohomology k (K : Set X)ᶜ),
      D (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k m α (cX K)) :
    Function.Bijective D := by
  apply integralCompactlySupportedCohomology_cap_bijective_of_homeomorph
    k m (Homeomorph.Set.univ X) cX hcX hpX ?_ D hD
  intro c hc hp DU hDU
  exact integralCompactlySupportedCohomology_cap_bijective_of_isOpen_of_chartedSpace
    (_root_.Set.univ : Set X) isOpen_univ k m hkm c hc hp DU hDU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_cap_bijective_of_chartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomology_cap_bijective_of_chartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_cap_bijective_of_chartedSpace ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomology_cap_bijective_of_chartedSpace

theorem exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_chartedSpace
    (k m : ℕ) (hkm : k + m = Module.finrank ℝ E)
    (cX : ∀ K : _root_.TopologicalSpace.Compacts X, integralRelativeHomology (k + m) (K : Set X)ᶜ)
    (hcX : ∀ (K L : _root_.TopologicalSpace.Compacts X) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id X)
        (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr h) (cX L) = cX K)
    (hpX : ∀ p : X, Function.Bijective (fun z : ℤ => z • cX {p})) :
    ∃! D : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology m X,
      (∀ (K : _root_.TopologicalSpace.Compacts X) (α : integralRelativeCohomology k (K : Set X)ᶜ),
        D (integralRelativeToCompactlySupportedCohomology k K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k m α (cX K)) ∧
      Function.Bijective D := by
  obtain ⟨D, hD, huniq⟩ := exists_unique_integralCompactlySupportedCohomology_cap k m cX hcX
  exact ⟨D, ⟨hD, integralCompactlySupportedCohomology_cap_bijective_of_chartedSpace
    k m hkm cX hcX hpX D hD⟩, fun D' hD' => huniq D' hD'.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_chartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_chartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_chartedSpace ``Submission.DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_chartedSpace

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.Set _root_.TopologicalSpace _root_.Submission.TopologicalSpace
open scoped _root_.Manifold

namespace DifferentialGeometry.Topology

theorem exists_integralCompactlySupportedCohomology_cap_bijective_of_simplyConnected
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    [SimplyConnectedSpace M]
    (k m : ℕ) (hkm : k + m = Module.finrank ℝ E) :
    ∃ c : ∀ K : _root_.TopologicalSpace.Compacts M, integralRelativeHomology (k + m) (K : Set M)ᶜ,
      (∀ (K L : _root_.TopologicalSpace.Compacts M) (h : K ≤ L),
        integralRelativeHomologyMap (k + m) (ContinuousMap.id M)
          (show (L : Set M)ᶜ ⊆ (K : Set M)ᶜ from compl_subset_compl.mpr h) (c L) = c K) ∧
      (∀ p : M, Function.Bijective (fun z : ℤ => z • c {p})) ∧
      ∃! D : integralCompactlySupportedCohomology k M →ₗ[ℤ] integralSingularHomology m M,
        (∀ (K : _root_.TopologicalSpace.Compacts M) (α : integralRelativeCohomology k (K : Set M)ᶜ),
          D (integralRelativeToCompactlySupportedCohomology k K α) =
            integralRelativeCohomologyCapToAbsolute (K : Set M)ᶜ k m α (c K)) ∧
        Function.Bijective D := by
  have hex := exists_compact_homology_family_of_simplyConnected (E := E) (M := M)
  rw [← hkm] at hex
  obtain ⟨c, hc, hp⟩ := hex
  exact ⟨c, hc, hp,
    exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_chartedSpace
      (E := E) k m hkm c hc hp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_integralCompactlySupportedCohomology_cap_bijective_of_simplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_integralCompactlySupportedCohomology_cap_bijective_of_simplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_integralCompactlySupportedCohomology_cap_bijective_of_simplyConnected ``Submission.DifferentialGeometry.Topology.exists_integralCompactlySupportedCohomology_cap_bijective_of_simplyConnected

end DifferentialGeometry.Topology

end
