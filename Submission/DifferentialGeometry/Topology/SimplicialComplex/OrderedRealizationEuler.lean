import Submission.DifferentialGeometry.Topology.SimplicialComplex.OrderedSimplicialSet
import Submission.DifferentialGeometry.Topology.SimplicialComplex.EulerCharacteristic
import Submission.DifferentialGeometry.Topology.SimplicialSet.RealizationEulerCharacteristic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory
namespace DifferentialGeometry.Topology.SimplicialComplex
universe u
variable {ι : Type u} [LinearOrder ι] (K : PreAbstractSimplicialComplex ι) [Finite K.faces]


theorem card_orderedSimplicialSet_nonDegenerate (n : ℕ) :
    Nat.card ((orderedSimplicialSet K).nonDegenerate n) = (facesOfCard K (n + 1)).card := by
  let e : {s : Finset ι // s ∈ K ∧ s.card = n + 1} ≃ (facesOfCard K (n + 1)) :=
    Equiv.subtypeEquivRight (fun _ => (mem_facesOfCard K).symm)
  rw [Nat.card_congr ((orderedNondegenerateFaceEquiv K n).trans e), Nat.card_eq_fintype_card]
  exact Fintype.card_coe _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.card_orderedSimplicialSet_nonDegenerate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.card_orderedSimplicialSet_nonDegenerate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.card_orderedSimplicialSet_nonDegenerate ``Submission.DifferentialGeometry.Topology.SimplicialComplex.card_orderedSimplicialSet_nonDegenerate

theorem eulerChar_orderedRealization_eq_faceEulerChar (k : Type u) [Field k] :
    DifferentialGeometry.Homology.eulerChar k (SSet.toTop.obj (orderedSimplicialSet K)) = faceEulerChar K := by
  classical
  let d := (Set.toFinite K.faces).toFinset.sup Finset.card
  have hd : ∀ s ∈ K, s.card ≤ d := by
    intro s hs
    exact Finset.le_sup (f := Finset.card) ((Set.toFinite K.faces).mem_toFinset.mpr hs)
  have : (orderedSimplicialSet K).HasDimensionLT d := orderedSimplicialSet_hasDimensionLT K d hd
  rw [DifferentialGeometry.SSet.eulerChar_realization_eq_sum_card_nonDegenerate k _ d,
    faceEulerChar_eq_sum K d hd, Finset.sum_range_succ']
  simp only [pow_zero, facesOfCard_zero, Finset.card_empty, Nat.cast_zero, _root_.MulZeroClass.mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro n _
  rw [card_orderedSimplicialSet_nonDegenerate, pow_succ]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.eulerChar_orderedRealization_eq_faceEulerChar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.eulerChar_orderedRealization_eq_faceEulerChar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.eulerChar_orderedRealization_eq_faceEulerChar ``Submission.DifferentialGeometry.Topology.SimplicialComplex.eulerChar_orderedRealization_eq_faceEulerChar

theorem finiteHomologyType_orderedRealization (k : Type u) [Field k] :
    DifferentialGeometry.Homology.finiteHomologyType k (SSet.toTop.obj (orderedSimplicialSet K)) :=
  DifferentialGeometry.SSet.finiteHomologyType_realization k (orderedSimplicialSet K)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_orderedRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_orderedRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_orderedRealization ``Submission.DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_orderedRealization

end DifferentialGeometry.Topology.SimplicialComplex
