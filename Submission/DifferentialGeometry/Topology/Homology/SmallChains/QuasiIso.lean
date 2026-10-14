import Submission.DifferentialGeometry.Topology.Homology.Algebra.EventualImage
import Submission.DifferentialGeometry.Topology.Homology.Subdivision.SingularSupport
import Submission.DifferentialGeometry.Topology.Homology.Subdivision.EventualSmallness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits
noncomputable section
universe u v
namespace DifferentialGeometry.Homology
variable (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)

theorem quasiIso_smallChainMap
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (smallChainMap X U R) := by
  let := mono_smallChainMap X U R
  apply DifferentialGeometry.HomologicalComplex.quasiIso_of_eventually_in_image (smallChainMap X U R)
    (smallSingularSubdivision X U R) (End.of (singularSubdivision R X))
    (smallSingularSubdivision_inclusion X U R).symm
    (singularSubdivisionHomotopy R X) (smallSingularSubdivisionHomotopyMap X U R)
  · intro n
    rw [singularSubdivisionHomotopy_hom]
    exact (smallSingularSubdivisionHomotopyMap_inclusion X U R n).symm
  · exact exists_small_subdivision_power R X U hopen hcover

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.quasiIso_smallChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.quasiIso_smallChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.quasiIso_smallChainMap ``Submission.DifferentialGeometry.Homology.quasiIso_smallChainMap


def smallChainHomologyIso
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    ((smallSingularSimplices X U : SSet).chainComplex R).homology n ≅
      ((TopCat.toSSet.obj X).chainComplex R).homology n := by
  letI := quasiIso_smallChainMap X U R hopen hcover
  exact isoOfQuasiIsoAt (smallChainMap X U R) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallChainHomologyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallChainHomologyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallChainHomologyIso ``Submission.DifferentialGeometry.Homology.smallChainHomologyIso


@[simp]
theorem smallChainHomologyIso_hom
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (smallChainHomologyIso X U R hopen hcover n).hom =
      _root_.HomologicalComplex.homologyMap (smallChainMap X U R) n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallChainHomologyIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallChainHomologyIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallChainHomologyIso_hom ``Submission.DifferentialGeometry.Homology.smallChainHomologyIso_hom

end DifferentialGeometry.Homology
