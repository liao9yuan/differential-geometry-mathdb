import Submission.DifferentialGeometry.Topology.LocalDegree.SphereHomology
import Mathlib.Analysis.Normed.Module.Connected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Metric
noncomputable section
namespace DifferentialGeometry.LocalDegree
open _root_.Submission.DifferentialGeometry.Homology
variable {k : Type} [Ring k] (R : ModuleCat k)

private theorem pathConnected_euclideanSphere (d : ℕ) :
    PathConnectedSpace (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 2))) 1) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_sphere
  · exact Module.one_lt_rank_of_one_lt_finrank (by simp)
  · norm_num

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.pathConnected_euclideanSphere
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.pathConnected_euclideanSphere target :: scope.openDecls } }

theorem isZero_euclideanSphere_reducedHomology (d n : ℕ) (h : n ≠ d) :
    _root_.CategoryTheory.Limits.IsZero (reducedSingularHomology R
      (TopCat.of (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1)) n) := by
  induction d generalizing n with
  | zero =>
    cases n with
    | zero => exact (h rfl).elim
    | succ n => exact isZero_euclideanZeroSphere_reducedHomology_succ R n
  | succ d ih =>
    cases n with
    | zero =>
      let := pathConnected_euclideanSphere d
      exact isZero_reducedSingularHomology_zero_of_pathConnected R _
    | succ n =>
      exact IsZero.of_iso (ih n (by omega))
        (euclideanSphereReducedHomologySuccIso R (d + 1) n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.isZero_euclideanSphere_reducedHomology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.isZero_euclideanSphere_reducedHomology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.isZero_euclideanSphere_reducedHomology ``Submission.DifferentialGeometry.LocalDegree.isZero_euclideanSphere_reducedHomology

end DifferentialGeometry.LocalDegree
