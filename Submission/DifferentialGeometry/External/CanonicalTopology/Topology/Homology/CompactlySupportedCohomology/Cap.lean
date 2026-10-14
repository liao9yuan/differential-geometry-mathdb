import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactlySupportedCohomology.Defs
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCapToAbsoluteHomology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
noncomputable section

open _root_.TopologicalSpace _root_.Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private local instance compactSupportIntegerComm (P : Type*) [AddCommGroup P]
    [h : Module ℤ P] : @SMulCommClass ℤ ℤ P h.toSMul h.toSMul :=
  @smulCommClass_self ℤ P inferInstance h.toMulAction

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.compactSupportIntegerComm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.compactSupportIntegerComm target :: scope.openDecls } }

private local instance compactSupportIntegerLinearModule (P Q : Type*)
    [AddCommGroup P] [AddCommGroup Q] [Module ℤ P] [Module ℤ Q] :
    Module ℤ (P →ₗ[ℤ] Q) := LinearMap.module

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.compactSupportIntegerLinearModule
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.compactSupportIntegerLinearModule target :: scope.openDecls } }

theorem exists_unique_integralCompactlySupportedCohomology_cap
    (k m : ℕ) (c : ∀ K : _root_.TopologicalSpace.Compacts X, integralRelativeHomology (k + m) (K : Set X)ᶜ)
    (hc : ∀ (K L : _root_.TopologicalSpace.Compacts X) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
          compl_subset_compl.mpr h) (c L) = c K) :
    ∃! D : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology m X,
      ∀ (K : _root_.TopologicalSpace.Compacts X) (α : integralRelativeCohomology k (K : Set X)ᶜ),
        D (integralRelativeToCompactlySupportedCohomology k K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k m α (c K) := by
  classical
  let D : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology m X :=
    integralCompactlySupportedCohomologyDesc k
      (fun K => (integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k m).flip (c K))
      (by
        intro K L h α
        simp only [LinearMap.flip_apply]
        have hn := integralRelativeCohomologyCapToAbsolute_natural k m (ContinuousMap.id X)
          (show _root_.Set.MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
            compl_subset_compl.mpr h) α (c L)
        simpa only [integralSingularHomologyMap_id, LinearMap.id_apply, hc K L h] using hn)
  have hD (K : _root_.TopologicalSpace.Compacts X) (α : integralRelativeCohomology k (K : Set X)ᶜ) :
      D (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k m α (c K) := by
    exact integralCompactlySupportedCohomologyDesc_representative k _ _ K α
  refine ⟨D, hD, ?_⟩
  intro D' hD'
  exact integralCompactlySupportedCohomology_hom_ext k fun K α =>
    (hD' K α).trans (hD K α).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap ``Submission.DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap

theorem exists_unique_integralCompactlySupportedCohomology_cap_of_absolute
    (k m : ℕ) (c : integralSingularHomology (k + m) X) :
    ∃! D : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology m X,
      (∀ (K : _root_.TopologicalSpace.Compacts X) (α : integralRelativeCohomology k (K : Set X)ᶜ),
        D (integralRelativeToCompactlySupportedCohomology k K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k m α
            (integralAbsoluteToRelative (k + m) (K : Set X)ᶜ c)) ∧
      ∀ α : integralCompactlySupportedCohomology k X,
        D α = integralSingularCohomologyCapProduct k m
          (integralCompactlySupportedToSingularCohomology k X α) c := by
  let cK (K : _root_.TopologicalSpace.Compacts X) : integralRelativeHomology (k + m) (K : Set X)ᶜ :=
    integralAbsoluteToRelative (k + m) (K : Set X)ᶜ c
  have hK (K L : _root_.TopologicalSpace.Compacts X) (h : K ≤ L) :
      integralRelativeHomologyMap (k + m) (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
          compl_subset_compl.mpr h) (cK L) = cK K := by
    have hn := LinearMap.congr_fun (integralAbsoluteToRelative_natural (k + m)
      (ContinuousMap.id X)
      (show _root_.Set.MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
        compl_subset_compl.mpr h)) c
    simpa only [LinearMap.comp_apply, integralSingularHomologyMap_id,
      LinearMap.id_apply] using hn.symm
  obtain ⟨D, hD, huniq⟩ :=
    exists_unique_integralCompactlySupportedCohomology_cap (X := X) k m cK hK
  refine ⟨D, ⟨hD, ?_⟩, fun D' hD' => huniq D' hD'.1⟩
  intro α
  obtain ⟨K, β, rfl⟩ := integralCompactlySupportedCohomology_exists_representative k α
  rw [hD, integralCompactlySupportedToSingularCohomology_representative]
  exact integralRelativeCohomologyCapToAbsolute_absoluteToRelative (K : Set X)ᶜ k m β c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap_of_absolute then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap_of_absolute"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap_of_absolute ``Submission.DifferentialGeometry.Topology.exists_unique_integralCompactlySupportedCohomology_cap_of_absolute

end DifferentialGeometry.Topology

end
