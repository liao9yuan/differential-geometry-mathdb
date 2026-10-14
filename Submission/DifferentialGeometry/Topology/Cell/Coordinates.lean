import Submission.DifferentialGeometry.Topology.Simplex.NormedBall
import Submission.DifferentialGeometry.Topology.Attachment.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Metric _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.Cell


def stdSimplexClosedCellHomeomorph (n : ℕ) : stdSimplex ℝ (Fin (n + 1)) ≃ₜ ClosedCell n :=
  (DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph (EuclideanSpace.equiv (Fin n) ℝ).symm).trans
    (Homeomorph.setCongr (by ext x; change _root_.Dist.dist x 0 ≤ 1 ↔ ‖x‖ ≤ 1; rw [dist_zero_right]))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Cell.stdSimplexClosedCellHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Cell.stdSimplexClosedCellHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Cell.stdSimplexClosedCellHomeomorph ``Submission.DifferentialGeometry.Cell.stdSimplexClosedCellHomeomorph


def stdSimplexCellBoundaryHomeomorph (n : ℕ) :
    DifferentialGeometry.Simplex.boundary (Fin (n + 1)) ≃ₜ CellBoundary n :=
  (DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph (EuclideanSpace.equiv (Fin n) ℝ).symm).trans
    (Homeomorph.setCongr (by ext x; change _root_.Dist.dist x 0 = 1 ↔ ‖x‖ = 1; rw [dist_zero_right]))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Cell.stdSimplexCellBoundaryHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Cell.stdSimplexCellBoundaryHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Cell.stdSimplexCellBoundaryHomeomorph ``Submission.DifferentialGeometry.Cell.stdSimplexCellBoundaryHomeomorph


@[simp]
theorem stdSimplexCellBoundaryHomeomorph_inclusion (n : ℕ)
    (x : DifferentialGeometry.Simplex.boundary (Fin (n + 1))) :
    cellBoundaryInclusion n (stdSimplexCellBoundaryHomeomorph n x) =
      stdSimplexClosedCellHomeomorph n x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Cell.stdSimplexCellBoundaryHomeomorph_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Cell.stdSimplexCellBoundaryHomeomorph_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Cell.stdSimplexCellBoundaryHomeomorph_inclusion ``Submission.DifferentialGeometry.Cell.stdSimplexCellBoundaryHomeomorph_inclusion

end DifferentialGeometry.Cell
