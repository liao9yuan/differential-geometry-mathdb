import Submission.DifferentialGeometry.Topology.SimplicialComplex.OrderedSimplicialSet
import Submission.DifferentialGeometry.Topology.SimplicialSet.FiniteCellInduction
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits
namespace DifferentialGeometry.Topology.SimplicialComplex
universe u
variable {ι : Type u} [LinearOrder ι]


theorem isEmpty_orderedRealization (K : PreAbstractSimplicialComplex ι) (hK : K.faces = ∅) :
    IsEmpty (SSet.toTop.obj (orderedSimplicialSet K)) := by
  let : IsEmpty (orderedSimplicialSet K).N := ⟨fun a => by
    have ha := a.simplex.prop
    change Finset.univ.image a.simplex.val.obj ∈ K.faces at ha
    rw [hK] at ha
    exact ha⟩
  have hI := (DifferentialGeometry.SSet.isInitial_of_isEmpty_nondegenerate (orderedSimplicialSet K)).isInitialObj
    SSet.toTop
  exact ⟨fun x => PEmpty.elim (hI.to (TopCat.of PEmpty.{u + 1}) x)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.isEmpty_orderedRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.isEmpty_orderedRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.isEmpty_orderedRealization ``Submission.DifferentialGeometry.Topology.SimplicialComplex.isEmpty_orderedRealization

end DifferentialGeometry.Topology.SimplicialComplex
