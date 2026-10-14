import Submission.DifferentialGeometry.Topology.SimplicialComplex.GeometricRealizationHomeomorphism
import Submission.DifferentialGeometry.Topology.SimplicialComplex.OrderedRealizationEuler
import Mathlib.SetTheory.Cardinal.Order

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Topology.SimplicialComplex
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
  (k : Type u) [Field k]

theorem finiteHomologyType_geometricSpace :
    DifferentialGeometry.Homology.finiteHomologyType k (TopCat.of K.space) := by
  classical
  let := linearOrderOfSTO (WellOrderingRel : E → E → Prop)
  exact (DifferentialGeometry.Homology.finiteHomologyType_iff_of_homeomorph k
    (Y := TopCat.of K.space) (geometricRealizationHomeomorphism K)).mp
    (finiteHomologyType_orderedRealization K.toPreAbstractSimplicialComplex k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_geometricSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_geometricSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_geometricSpace ``Submission.DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_geometricSpace

theorem eulerChar_geometricSpace_eq_faceEulerChar :
    DifferentialGeometry.Homology.eulerChar k (TopCat.of K.space) =
      faceEulerChar K.toPreAbstractSimplicialComplex := by
  classical
  let := linearOrderOfSTO (WellOrderingRel : E → E → Prop)
  exact (DifferentialGeometry.Homology.eulerChar_eq_of_homeomorph k
    (Y := TopCat.of K.space) (geometricRealizationHomeomorphism K)).symm.trans
    (eulerChar_orderedRealization_eq_faceEulerChar K.toPreAbstractSimplicialComplex k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.eulerChar_geometricSpace_eq_faceEulerChar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.eulerChar_geometricSpace_eq_faceEulerChar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.eulerChar_geometricSpace_eq_faceEulerChar ``Submission.DifferentialGeometry.Topology.SimplicialComplex.eulerChar_geometricSpace_eq_faceEulerChar

theorem eulerChar_geometricSpace_eq_of_coefficients (l : Type u) [Field l] :
    DifferentialGeometry.Homology.eulerChar k (TopCat.of K.space) =
      DifferentialGeometry.Homology.eulerChar l (TopCat.of K.space) := by
  rw [eulerChar_geometricSpace_eq_faceEulerChar, eulerChar_geometricSpace_eq_faceEulerChar]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.eulerChar_geometricSpace_eq_of_coefficients then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.eulerChar_geometricSpace_eq_of_coefficients"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.eulerChar_geometricSpace_eq_of_coefficients ``Submission.DifferentialGeometry.Topology.SimplicialComplex.eulerChar_geometricSpace_eq_of_coefficients

end DifferentialGeometry.Topology.SimplicialComplex
