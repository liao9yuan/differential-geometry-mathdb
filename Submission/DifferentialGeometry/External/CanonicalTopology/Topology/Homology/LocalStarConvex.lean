import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homotopy.StarConvexComplement
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeHomeomorphism
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeComparison
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainHomotopy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.ContinuousMap _root_.Set

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem integralSingularChainMap_quasiIso_of_homotopyEquiv
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) :
    QuasiIso (integralSingularChainMap e.toFun) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  exact (integralSingularHomologyHomotopyEquiv n e).bijective

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularChainMap_quasiIso_of_homotopyEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularChainMap_quasiIso_of_homotopyEquiv target :: scope.openDecls } }

private theorem integralBoundedStarConvexToLocalChainMap_quasiIso {K : Set E} {c : E}
    (hc : c ∈ K) (hs : StarConvex ℝ c K) (hK : Bornology.IsBounded K) :
    QuasiIso (integralRelativeChainMap (ContinuousMap.id E)
      (compl_subset_compl.mpr (singleton_subset_iff.mpr hc))) := by
  have hA : QuasiIso (integralSingularChainMap
      (singularPairRestriction (ContinuousMap.id E)
        (compl_subset_compl.mpr (singleton_subset_iff.mpr hc)))) :=
    integralSingularChainMap_quasiIso_of_homotopyEquiv
      (boundedStarConvexComplementHomotopyEquiv hc hs hK)
  have hE : QuasiIso (integralSingularChainMap (ContinuousMap.id E)) :=
    integralSingularChainMap_quasiIso_of_homotopyEquiv (ContinuousMap.HomotopyEquiv.refl E)
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (integralRelativeSequenceMap (ContinuousMap.id E)
      (compl_subset_compl.mpr (singleton_subset_iff.mpr hc)))
    (integralRelativeChainSequence_shortExact Kᶜ)
    (integralRelativeChainSequence_shortExact ({c}ᶜ : Set E)) hA hE

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralBoundedStarConvexToLocalChainMap_quasiIso
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralBoundedStarConvexToLocalChainMap_quasiIso target :: scope.openDecls } }

def integralBoundedStarConvexLocalHomologyIso (n : ℕ) {K : Set E} {c : E}
    (hc : c ∈ K) (hs : StarConvex ℝ c K) (hK : Bornology.IsBounded K) :
    integralRelativeHomology n Kᶜ ≅ integralLocalHomology n c := by
  let := integralBoundedStarConvexToLocalChainMap_quasiIso hc hs hK
  exact _root_.CategoryTheory.asIso (HomologicalComplex.homologyMap
    (integralRelativeChainMap (ContinuousMap.id E)
      (compl_subset_compl.mpr (singleton_subset_iff.mpr hc))) n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralBoundedStarConvexLocalHomologyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralBoundedStarConvexLocalHomologyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralBoundedStarConvexLocalHomologyIso ``Submission.DifferentialGeometry.Topology.integralBoundedStarConvexLocalHomologyIso

theorem integralBoundedStarConvexLocalHomologyIso_hom (n : ℕ) {K : Set E} {c : E}
    (hc : c ∈ K) (hs : StarConvex ℝ c K) (hK : Bornology.IsBounded K) :
    (integralBoundedStarConvexLocalHomologyIso n hc hs hK).hom.hom =
      integralRelativeHomologyMap n (ContinuousMap.id E)
        (show Kᶜ ⊆ ({c}ᶜ : Set E) from fun _ hx h => hx (h.symm ▸ hc)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralBoundedStarConvexLocalHomologyIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralBoundedStarConvexLocalHomologyIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralBoundedStarConvexLocalHomologyIso_hom ``Submission.DifferentialGeometry.Topology.integralBoundedStarConvexLocalHomologyIso_hom

theorem integralRelativeCohomologyMap_boundedStarConvex_bijective
    (n : ℕ) {K : Set E} {c : E}
    (hc : c ∈ K) (hs : StarConvex ℝ c K) (hK : Bornology.IsBounded K) :
    Function.Bijective (integralRelativeCohomologyMap n (ContinuousMap.id E)
      (compl_subset_compl.mpr (singleton_subset_iff.mpr hc))) := by
  let hf : _root_.Set.MapsTo (ContinuousMap.id E) Kᶜ ({c}ᶜ : Set E) :=
    compl_subset_compl.mpr (singleton_subset_iff.mpr hc)
  let e := boundedStarConvexComplementHomotopyEquiv hc hs hK
  have he : singularPairRestriction (ContinuousMap.id E) hf = e.toFun := by
    rw [boundedStarConvexComplementHomotopyEquiv_toFun]
    rfl
  change Function.Bijective (integralRelativeCohomologyMap n (ContinuousMap.id E) hf)
  apply integralRelativeCohomologyMap_bijective_of_absolute_and_subspace
  · intro k
    rw [integralSingularCohomologyMap_id]
    exact Function.bijective_id
  · intro k
    rw [he]
    exact integralSingularCohomologyMap_bijective_of_homotopyEquiv e k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomologyMap_boundedStarConvex_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomologyMap_boundedStarConvex_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomologyMap_boundedStarConvex_bijective ``Submission.DifferentialGeometry.Topology.integralRelativeCohomologyMap_boundedStarConvex_bijective

end DifferentialGeometry.Topology

end
