import Submission.DifferentialGeometry.Topology.Category.TopCat.Adjunction
import Submission.DifferentialGeometry.Topology.Cell.Coordinates
import Submission.DifferentialGeometry.Topology.Simplex.AttachmentEuler

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.Cell
variable {X : TopCat.{0}} (n : ℕ) (φ : C(CellBoundary n, X))


def boundaryInclusion : TopCat.of (CellBoundary n) ⟶ TopCat.of (ClosedCell n) :=
  TopCat.ofHom ⟨cellBoundaryInclusion n, continuous_cellBoundaryInclusion n⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Cell.boundaryInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Cell.boundaryInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Cell.boundaryInclusion ``Submission.DifferentialGeometry.Cell.boundaryInclusion


def simplexAttachingMap : TopCat.of (DifferentialGeometry.Simplex.boundary (Fin (n + 1))) ⟶ X :=
  (TopCat.isoOfHomeo (stdSimplexCellBoundaryHomeomorph n)).hom ≫ TopCat.ofHom φ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Cell.simplexAttachingMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Cell.simplexAttachingMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Cell.simplexAttachingMap ``Submission.DifferentialGeometry.Cell.simplexAttachingMap


def simplexCellMap : TopCat.of (stdSimplex ℝ (Fin (n + 1))) ⟶ TopCat.of (CellAdjunctionSpace n φ) :=
  (TopCat.isoOfHomeo (stdSimplexClosedCellHomeomorph n)).hom ≫
    DifferentialGeometry.TopCat.Adjunction.cellMap (boundaryInclusion n) (TopCat.ofHom φ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Cell.simplexCellMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Cell.simplexCellMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Cell.simplexCellMap ``Submission.DifferentialGeometry.Cell.simplexCellMap


theorem simplexAttachment_isPushout : _root_.CategoryTheory.IsPushout DifferentialGeometry.Simplex.Attachment.boundaryι
    (simplexAttachingMap n φ) (simplexCellMap n φ)
    (DifferentialGeometry.TopCat.Adjunction.lowerMap (boundaryInclusion n) (TopCat.ofHom φ)) := by
  apply (DifferentialGeometry.TopCat.Adjunction.isPushout (boundaryInclusion n) (TopCat.ofHom φ)).of_iso'
    (TopCat.isoOfHomeo (stdSimplexCellBoundaryHomeomorph n))
    (TopCat.isoOfHomeo (stdSimplexClosedCellHomeomorph n)) (Iso.refl _) (Iso.refl _)
  · ext x : 1
    exact stdSimplexCellBoundaryHomeomorph_inclusion n x
  · simp [simplexAttachingMap]
  · exact (Category.comp_id _).symm
  · simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Cell.simplexAttachment_isPushout then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Cell.simplexAttachment_isPushout"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Cell.simplexAttachment_isPushout ``Submission.DifferentialGeometry.Cell.simplexAttachment_isPushout


theorem finiteHomologyType_cellAdjunction (k : Type) [Field k]
    (hX : DifferentialGeometry.Homology.finiteHomologyType k X) :
    DifferentialGeometry.Homology.finiteHomologyType k (TopCat.of (CellAdjunctionSpace n φ)) :=
  DifferentialGeometry.Simplex.Attachment.finiteHomologyType_of_attachment k (simplexAttachment_isPushout n φ) hX

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Cell.finiteHomologyType_cellAdjunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Cell.finiteHomologyType_cellAdjunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Cell.finiteHomologyType_cellAdjunction ``Submission.DifferentialGeometry.Cell.finiteHomologyType_cellAdjunction


theorem eulerChar_cellAdjunction (k : Type) [Field k]
    (hX : DifferentialGeometry.Homology.finiteHomologyType k X) :
    DifferentialGeometry.Homology.eulerChar k (TopCat.of (CellAdjunctionSpace n φ)) =
      DifferentialGeometry.Homology.eulerChar k X + (-1 : ℤ)^n :=
  DifferentialGeometry.Simplex.Attachment.eulerChar_attachment k (simplexAttachment_isPushout n φ) hX

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Cell.eulerChar_cellAdjunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Cell.eulerChar_cellAdjunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Cell.eulerChar_cellAdjunction ``Submission.DifferentialGeometry.Cell.eulerChar_cellAdjunction

end DifferentialGeometry.Cell
