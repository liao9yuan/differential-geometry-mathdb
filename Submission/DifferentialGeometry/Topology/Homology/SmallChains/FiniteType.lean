import Submission.DifferentialGeometry.Topology.Homology.SmallChains.Union
import Submission.DifferentialGeometry.Topology.Homology.EulerCharacteristic
import Submission.DifferentialGeometry.Topology.Homology.Algebra.Biproduct

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
noncomputable section
universe u
namespace DifferentialGeometry.Homology
variable (X : TopCat.{u}) (s t : Set X) (k : Type u) [Field k]

theorem finiteHomologyType_twoSetSmall
    (hs : finiteHomologyType k (TopCat.of s)) (ht : finiteHomologyType k (TopCat.of t))
    (hst : finiteHomologyType k (TopCat.of (s ∩ t : Set X))) :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType
      ((smallSingularSimplices X (twoSetFamily X s t) : SSet).chainComplex (ModuleCat.of k k)) := by
  let S := subspaceSmallShortComplex X s t (ModuleCat.of k k)
  exact DifferentialGeometry.HomologicalComplex.finiteHomologyType_last S
    (subspaceSmallShortExact X s t (ModuleCat.of k k)) hst
    (DifferentialGeometry.HomologicalComplex.finiteHomologyType_biprod _ _ hs ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.finiteHomologyType_twoSetSmall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.finiteHomologyType_twoSetSmall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.finiteHomologyType_twoSetSmall ``Submission.DifferentialGeometry.Homology.finiteHomologyType_twoSetSmall

theorem homologyEulerChar_twoSetSmall
    (hs : finiteHomologyType k (TopCat.of s)) (ht : finiteHomologyType k (TopCat.of t))
    (hst : finiteHomologyType k (TopCat.of (s ∩ t : Set X))) :
    ((smallSingularSimplices X (twoSetFamily X s t) : SSet).chainComplex
      (ModuleCat.of k k)).homologyEulerChar =
      eulerChar k (TopCat.of s) + eulerChar k (TopCat.of t) - eulerChar k (TopCat.of (s ∩ t : Set X)) := by
  let S := subspaceSmallShortComplex X s t (ModuleCat.of k k)
  have hm := DifferentialGeometry.HomologicalComplex.finiteHomologyType_biprod _ _ hs ht
  have hu := finiteHomologyType_twoSetSmall X s t k hs ht hst
  have : ∀ n, FiniteDimensional k (S.X₁.homology n) := hst.1
  have : ∀ n, FiniteDimensional k (S.X₂.homology n) := hm.1
  have : ∀ n, FiniteDimensional k (S.X₃.homology n) := hu.1
  have h := DifferentialGeometry.HomologicalComplex.homologyEulerChar_additive S
    (subspaceSmallShortExact X s t (ModuleCat.of k k)) hst.2 hm.2 hu.2
  have hb := DifferentialGeometry.HomologicalComplex.homologyEulerChar_biprod _ _ hs ht
  change S.X₂.homologyEulerChar = eulerChar k (TopCat.of s) + eulerChar k (TopCat.of t) at hb
  rw [hb] at h
  change eulerChar k (TopCat.of s) + eulerChar k (TopCat.of t) =
    eulerChar k (TopCat.of (s ∩ t : Set X)) + _ at h
  change S.X₃.homologyEulerChar = _
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.homologyEulerChar_twoSetSmall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.homologyEulerChar_twoSetSmall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.homologyEulerChar_twoSetSmall ``Submission.DifferentialGeometry.Homology.homologyEulerChar_twoSetSmall

end DifferentialGeometry.Homology
