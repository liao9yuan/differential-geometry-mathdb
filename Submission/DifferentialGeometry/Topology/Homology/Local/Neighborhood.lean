import Submission.DifferentialGeometry.Topology.Homology.Relative.Excision
import Submission.DifferentialGeometry.Topology.Homology.Algebra.FiniteTypeMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.Set
namespace DifferentialGeometry.Homology
universe u
variable (X : TopCat.{u}) (U : Set X) (x : X) (hx : x ∈ U)
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)

theorem puncturedNeighborhood_mapsTo :
    Set.MapsTo (Subtype.val : U → X) ({(⟨x, hx⟩ : U)}ᶜ : Set U) ({x}ᶜ : Set X) := by
  intro y hy
  change y ≠ ⟨x, hx⟩ at hy
  change y.val ≠ x
  exact fun he => hy (Subtype.ext he)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.puncturedNeighborhood_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.puncturedNeighborhood_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.puncturedNeighborhood_mapsTo ``Submission.DifferentialGeometry.Homology.puncturedNeighborhood_mapsTo


def puncturedNeighborhoodChainMap :
    relativeChainComplex (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) R ⟶
      relativeChainComplex X ({x}ᶜ : Set X) R :=
  relativeChainMap R (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))
    (puncturedNeighborhood_mapsTo X U x hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.puncturedNeighborhoodChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.puncturedNeighborhoodChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.puncturedNeighborhoodChainMap ``Submission.DifferentialGeometry.Homology.puncturedNeighborhoodChainMap

theorem quasiIso_puncturedNeighborhoodChainMap [T1Space X] (hU : IsOpen U) :
    QuasiIso (puncturedNeighborhoodChainMap X U x hx R) := by
  have hcover : U ∪ ({x}ᶜ : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      by_cases hy : y = x
      · exact Or.inl (hy.symm ▸ hx)
      · exact Or.inr hy
  have he : {y : U | (y : X) ∈ ({x}ᶜ : Set X)} = ({(⟨x, hx⟩ : U)}ᶜ : Set U) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff, Subtype.ext_iff]
  have hq := quasiIso_relativeChainMap_of_openCover X U ({x}ᶜ : Set X) R hU
    isClosed_singleton.isOpen_compl hcover
  let e := relativeChainIso (X := TopCat.of U) (Y := TopCat.of U) R (Homeomorph.refl (↥U))
    (s := ({(⟨x, hx⟩ : U)}ᶜ : Set U))
    (t := {y : U | (y : X) ∈ ({x}ᶜ : Set X)}) (fun y => by rw [he]; rfl)
  have hm : puncturedNeighborhoodChainMap X U x hx R = e.hom ≫
      relativeChainMap R (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))
        (show Set.MapsTo Subtype.val {y : U | (y : X) ∈ ({x}ᶜ : Set X)} ({x}ᶜ : Set X)
          from fun _ hy => hy) := by
    unfold puncturedNeighborhoodChainMap
    dsimp only [e, relativeChainIso]
    erw [← relativeChainMap_comp]
    apply relativeChainMap_congr
    rfl
  rw [hm]
  exact quasiIso_comp e.hom _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.quasiIso_puncturedNeighborhoodChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.quasiIso_puncturedNeighborhoodChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.quasiIso_puncturedNeighborhoodChainMap ``Submission.DifferentialGeometry.Homology.quasiIso_puncturedNeighborhoodChainMap

def puncturedNeighborhoodHomologyIso [T1Space X] (hU : IsOpen U) (n : ℕ) :
    relativeHomology (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) R n ≅
      relativeHomology X ({x}ᶜ : Set X) R n := by
  let := quasiIso_puncturedNeighborhoodChainMap X U x hx R hU
  exact isoOfQuasiIsoAt (puncturedNeighborhoodChainMap X U x hx R) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.puncturedNeighborhoodHomologyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.puncturedNeighborhoodHomologyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.puncturedNeighborhoodHomologyIso ``Submission.DifferentialGeometry.Homology.puncturedNeighborhoodHomologyIso

@[simp]
theorem puncturedNeighborhoodHomologyIso_hom [T1Space X] (hU : IsOpen U) (n : ℕ) :
    (puncturedNeighborhoodHomologyIso X U x hx R hU n).hom =
      relativeHomologyMap R (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))
        (puncturedNeighborhood_mapsTo X U x hx) n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.puncturedNeighborhoodHomologyIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.puncturedNeighborhoodHomologyIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.puncturedNeighborhoodHomologyIso_hom ``Submission.DifferentialGeometry.Homology.puncturedNeighborhoodHomologyIso_hom

section Field
variable (k : Type u) [Field k]

theorem finiteHomologyType_puncturedNeighborhood_iff [T1Space X] (hU : IsOpen U) :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType
        (relativeChainComplex (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) (ModuleCat.of k k)) ↔
      DifferentialGeometry.HomologicalComplex.finiteHomologyType
        (relativeChainComplex X ({x}ᶜ : Set X) (ModuleCat.of k k)) := by
  let :=  quasiIso_puncturedNeighborhoodChainMap X U x hx (ModuleCat.of k k) hU
  exact DifferentialGeometry.HomologicalComplex.finiteHomologyType_iff_of_quasiIso
    (puncturedNeighborhoodChainMap X U x hx (ModuleCat.of k k))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.finiteHomologyType_puncturedNeighborhood_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.finiteHomologyType_puncturedNeighborhood_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.finiteHomologyType_puncturedNeighborhood_iff ``Submission.DifferentialGeometry.Homology.finiteHomologyType_puncturedNeighborhood_iff

theorem relativeEulerChar_puncturedNeighborhood [T1Space X] (hU : IsOpen U) :
    relativeEulerChar (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) k =
      relativeEulerChar X ({x}ᶜ : Set X) k := by
  let :=  quasiIso_puncturedNeighborhoodChainMap X U x hx (ModuleCat.of k k) hU
  exact DifferentialGeometry.HomologicalComplex.homologyEulerChar_eq_of_quasiIso
    (puncturedNeighborhoodChainMap X U x hx (ModuleCat.of k k))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeEulerChar_puncturedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeEulerChar_puncturedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeEulerChar_puncturedNeighborhood ``Submission.DifferentialGeometry.Homology.relativeEulerChar_puncturedNeighborhood

end Field

end DifferentialGeometry.Homology
