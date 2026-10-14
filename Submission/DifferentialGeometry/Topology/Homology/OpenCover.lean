import Submission.DifferentialGeometry.Topology.Homology.SmallChains.QuasiIso
import Submission.DifferentialGeometry.Topology.Homology.SmallChains.FiniteType
import Submission.DifferentialGeometry.Topology.Homology.Algebra.FiniteTypeMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits
noncomputable section
universe u
namespace DifferentialGeometry.Homology
variable (X : TopCat.{u}) (s t : Set X) (k : Type u) [Field k]

private theorem twoSet_cover_open (hs : IsOpen s) (ht : IsOpen t) (b : Bool) :
    IsOpen (twoSetFamily X s t b) := by
  cases b
  · exact ht
  · exact hs

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.twoSet_cover_open
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.twoSet_cover_open target :: scope.openDecls } }

private theorem twoSet_cover_all (hcover : s ∪ t = Set.univ) (x : X) :
    ∃ b, x ∈ twoSetFamily X s t b := by
  have hx : x ∈ s ∪ t := hcover.symm ▸ Set.mem_univ x
  rcases hx with hx | hx
  · exact ⟨true, hx⟩
  · exact ⟨false, hx⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.twoSet_cover_all
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.twoSet_cover_all target :: scope.openDecls } }

theorem finiteHomologyType_of_openCover
    (hs : IsOpen s) (ht : IsOpen t) (hcover : s ∪ t = Set.univ)
    (hfs : finiteHomologyType k (TopCat.of s)) (hft : finiteHomologyType k (TopCat.of t))
    (hfi : finiteHomologyType k (TopCat.of (s ∩ t : Set X))) : finiteHomologyType k X := by
  let φ := smallChainMap X (twoSetFamily X s t) (ModuleCat.of k k)
  let : QuasiIso φ := quasiIso_smallChainMap X _ _
    (twoSet_cover_open X s t hs ht) (twoSet_cover_all X s t hcover)
  exact (DifferentialGeometry.HomologicalComplex.finiteHomologyType_iff_of_quasiIso φ).mp
    (finiteHomologyType_twoSetSmall X s t k hfs hft hfi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.finiteHomologyType_of_openCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.finiteHomologyType_of_openCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.finiteHomologyType_of_openCover ``Submission.DifferentialGeometry.Homology.finiteHomologyType_of_openCover

theorem eulerChar_openCover
    (hs : IsOpen s) (ht : IsOpen t) (hcover : s ∪ t = Set.univ)
    (hfs : finiteHomologyType k (TopCat.of s)) (hft : finiteHomologyType k (TopCat.of t))
    (hfi : finiteHomologyType k (TopCat.of (s ∩ t : Set X))) :
    eulerChar k X = eulerChar k (TopCat.of s) + eulerChar k (TopCat.of t) -
      eulerChar k (TopCat.of (s ∩ t : Set X)) := by
  let φ := smallChainMap X (twoSetFamily X s t) (ModuleCat.of k k)
  let : QuasiIso φ := quasiIso_smallChainMap X _ _
    (twoSet_cover_open X s t hs ht) (twoSet_cover_all X s t hcover)
  have h := DifferentialGeometry.HomologicalComplex.homologyEulerChar_eq_of_quasiIso φ
  change ((smallSingularSimplices X (twoSetFamily X s t) : SSet).chainComplex
    (ModuleCat.of k k)).homologyEulerChar = eulerChar k X at h
  rw [← h]
  exact homologyEulerChar_twoSetSmall X s t k hfs hft hfi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.eulerChar_openCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.eulerChar_openCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.eulerChar_openCover ``Submission.DifferentialGeometry.Homology.eulerChar_openCover

end DifferentialGeometry.Homology
