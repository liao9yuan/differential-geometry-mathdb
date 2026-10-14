import Submission.DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.Manifold
import Submission.DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.CompactCap
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ManifoldHomologyGenerator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.Set _root_.TopologicalSpace _root_.Submission.TopologicalSpace
open scoped _root_.Manifold

namespace DifferentialGeometry.Topology

theorem integralSingularCohomologyCapProduct_bijective_of_chartedSpace_of_local_generators
    {E X : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace E X]
    (k m : ℕ) (hkm : k + m = Module.finrank ℝ E)
    (a : integralSingularHomology (k + m) X)
    (ha : ∀ p : X, Function.Bijective (fun z : ℤ =>
      z • integralAbsoluteToRelative (k + m) ({p}ᶜ : Set X) a)) :
    Function.Bijective (fun α : integralSingularCohomology k X =>
      integralSingularCohomologyCapProduct k m α a) := by
  let cX (K : _root_.TopologicalSpace.Compacts X) : integralRelativeHomology (k + m) (K : Set X)ᶜ :=
    integralAbsoluteToRelative (k + m) (K : Set X)ᶜ a
  have hcX (K L : _root_.TopologicalSpace.Compacts X) (h : K ≤ L) :
      integralRelativeHomologyMap (k + m) (ContinuousMap.id X)
        (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr h) (cX L) = cX K := by
    have hn := LinearMap.congr_fun (integralAbsoluteToRelative_natural (k + m)
      (ContinuousMap.id X)
      (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr h)) a
    simpa only [LinearMap.comp_apply, integralSingularHomologyMap_id,
      LinearMap.id_apply] using hn.symm
  obtain ⟨D, ⟨hD, _⟩, _⟩ := exists_unique_integralCompactlySupportedCohomology_cap_of_absolute k m a
  apply (integralCompactlySupportedCohomology_cap_bijective_iff_of_absolute k m a D hD).mp
  exact integralCompactlySupportedCohomology_cap_bijective_of_chartedSpace
    k m hkm cX hcX ha D hD

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyCapProduct_bijective_of_chartedSpace_of_local_generators then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyCapProduct_bijective_of_chartedSpace_of_local_generators"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyCapProduct_bijective_of_chartedSpace_of_local_generators ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyCapProduct_bijective_of_chartedSpace_of_local_generators

private theorem integralAbsoluteToRelative_generator_of_degree_eq
    {X : Type} [TopologicalSpace X] (n d : ℕ) (h : n = d)
    (a : integralSingularHomology d X)
    (ha : ∀ p : X, Function.Bijective (fun z : ℤ =>
      z • integralAbsoluteToRelative d ({p}ᶜ : Set X) a)) :
    ∀ p : X, Function.Bijective (fun z : ℤ => z • integralAbsoluteToRelative n ({p}ᶜ : Set X)
      ((_root_.CategoryTheory.eqToHom (congrArg (fun j => integralSingularHomology j X) h.symm)) a)) := by
  subst d
  exact ha

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralAbsoluteToRelative_generator_of_degree_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralAbsoluteToRelative_generator_of_degree_eq target :: scope.openDecls } }

theorem exists_integralSingularHomology_generator_with_cap_bijections_of_simplyConnected
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    [CompactSpace M] [SimplyConnectedSpace M] :
    ∃ a : integralSingularHomology (Module.finrank ℝ E) M,
      Function.Bijective (fun z : ℤ => z • a) ∧
      (∀ p : M, Function.Bijective (fun z : ℤ =>
        z • integralAbsoluteToRelative (Module.finrank ℝ E) ({p}ᶜ : Set M) a)) ∧
      ∀ (k m : ℕ) (hkm : k + m = Module.finrank ℝ E),
        Function.Bijective (fun α : integralSingularCohomology k M =>
          integralSingularCohomologyCapProduct k m α
            ((_root_.CategoryTheory.eqToHom (congrArg (fun j => integralSingularHomology j M) hkm.symm)) a)) := by
  obtain ⟨a, hgen, hpoints⟩ :=
    exists_integralSingularHomology_generator_of_simplyConnected (E := E) (M := M)
  refine ⟨a, hgen, hpoints, ?_⟩
  intro k m hkm
  apply integralSingularCohomologyCapProduct_bijective_of_chartedSpace_of_local_generators
    (E := E) (X := M) k m hkm
  exact integralAbsoluteToRelative_generator_of_degree_eq (k + m) (Module.finrank ℝ E)
    hkm a hpoints

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_integralSingularHomology_generator_with_cap_bijections_of_simplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_integralSingularHomology_generator_with_cap_bijections_of_simplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_integralSingularHomology_generator_with_cap_bijections_of_simplyConnected ``Submission.DifferentialGeometry.Topology.exists_integralSingularHomology_generator_with_cap_bijections_of_simplyConnected

theorem exists_integralSingularHomology_cap_bijective_of_simplyConnected
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (k m : ℕ) (hkm : k + m = Module.finrank ℝ E) :
    ∃ a : integralSingularHomology (k + m) M,
      Function.Bijective (fun α : integralSingularCohomology k M =>
        integralSingularCohomologyCapProduct k m α a) := by
  obtain ⟨a, _, _, ha⟩ :=
    exists_integralSingularHomology_generator_with_cap_bijections_of_simplyConnected
      (E := E) (M := M)
  exact ⟨(_root_.CategoryTheory.eqToHom (congrArg (fun j => integralSingularHomology j M) hkm.symm)) a,
    ha k m hkm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_integralSingularHomology_cap_bijective_of_simplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_integralSingularHomology_cap_bijective_of_simplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_integralSingularHomology_cap_bijective_of_simplyConnected ``Submission.DifferentialGeometry.Topology.exists_integralSingularHomology_cap_bijective_of_simplyConnected


end DifferentialGeometry.Topology

end
