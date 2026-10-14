import Submission.DifferentialGeometry.Topology.Homology.Relative.ReducedMap
import Submission.DifferentialGeometry.Topology.Homology.Local.Neighborhood

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set
namespace DifferentialGeometry.Homology
universe u
variable (X : TopCat.{u}) [T1Space X] [ContractibleSpace X]
  (U : Set X) [ContractibleSpace U] (x : X) (hx : x ∈ U) (hU : IsOpen U)
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)

def reducedPuncturedNeighborhoodHomologyIso (n : ℕ) :
    reducedSingularHomology R (TopCat.of ({(⟨x,hx⟩ : U)}ᶜ : Set U)) n ≅
      reducedSingularHomology R (TopCat.of ({x}ᶜ : Set X)) n :=
  (relativeReducedConnectingIso (TopCat.of U) ({(⟨x,hx⟩ : U)}ᶜ : Set U) R n).symm ≪≫
    puncturedNeighborhoodHomologyIso X U x hx R hU (n + 1) ≪≫
      relativeReducedConnectingIso X ({x}ᶜ : Set X) R n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.reducedPuncturedNeighborhoodHomologyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.reducedPuncturedNeighborhoodHomologyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.reducedPuncturedNeighborhoodHomologyIso ``Submission.DifferentialGeometry.Homology.reducedPuncturedNeighborhoodHomologyIso


@[simp]
theorem reducedPuncturedNeighborhoodHomologyIso_hom (n : ℕ) :
    (reducedPuncturedNeighborhoodHomologyIso X U x hx hU R n).hom =
      reducedSingularHomologyMap R
        (relativeSubspaceMap (X := TopCat.of U) (Y := X)
          (TopCat.ofHom (⟨Subtype.val,continuous_subtype_val⟩ : C(U,X)))
          (puncturedNeighborhood_mapsTo X U x hx)) n := by
  change (relativeReducedConnectingIso (TopCat.of U) ({(⟨x,hx⟩ : U)}ᶜ : Set U) R n).inv ≫
    ((puncturedNeighborhoodHomologyIso X U x hx R hU (n + 1)).hom ≫
      (relativeReducedConnectingIso X ({x}ᶜ : Set X) R n).hom) = _
  apply (Iso.inv_comp_eq _).mpr
  exact (relativeReducedConnectingIso_naturality R
    (TopCat.ofHom (⟨Subtype.val,continuous_subtype_val⟩ : C(U,X)))
    (puncturedNeighborhood_mapsTo X U x hx) n).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.reducedPuncturedNeighborhoodHomologyIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.reducedPuncturedNeighborhoodHomologyIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.reducedPuncturedNeighborhoodHomologyIso_hom ``Submission.DifferentialGeometry.Homology.reducedPuncturedNeighborhoodHomologyIso_hom
end DifferentialGeometry.Homology
