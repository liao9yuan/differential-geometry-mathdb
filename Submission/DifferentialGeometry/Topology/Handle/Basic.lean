import Submission.DifferentialGeometry.Topology.Attachment.Basic
import Submission.DifferentialGeometry.Topology.Handle.Defs
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Separation.Hausdorff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.Handle

open _root_.Function

theorem continuous_attachingInclusion (k l : ℕ) : Continuous (attachingInclusion k l) := by
  change Continuous (Prod.map (cellBoundaryInclusion k) (id : ClosedCell l → ClosedCell l))
  exact (continuous_cellBoundaryInclusion k).prodMap continuous_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.continuous_attachingInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.continuous_attachingInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.continuous_attachingInclusion ``Submission.DifferentialGeometry.Topology.Handle.continuous_attachingInclusion

theorem continuous_beltInclusion (k l : ℕ) : Continuous (beltInclusion k l) := by
  change Continuous (Prod.map (id : ClosedCell k → ClosedCell k) (cellBoundaryInclusion l))
  exact continuous_id.prodMap (continuous_cellBoundaryInclusion l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.continuous_beltInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.continuous_beltInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.continuous_beltInclusion ``Submission.DifferentialGeometry.Topology.Handle.continuous_beltInclusion

theorem continuous_cornerInclusion (k l : ℕ) : Continuous (cornerInclusion k l) := by
  change Continuous (Prod.map (cellBoundaryInclusion k) (cellBoundaryInclusion l))
  exact (continuous_cellBoundaryInclusion k).prodMap (continuous_cellBoundaryInclusion l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.continuous_cornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.continuous_cornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.continuous_cornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.continuous_cornerInclusion

theorem continuous_attachingCornerInclusion (k l : ℕ) : Continuous (attachingCornerInclusion k l) := by
  change Continuous (Prod.map (id : CellBoundary k → CellBoundary k) (cellBoundaryInclusion l))
  exact continuous_id.prodMap (continuous_cellBoundaryInclusion l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.continuous_attachingCornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.continuous_attachingCornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.continuous_attachingCornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.continuous_attachingCornerInclusion

theorem continuous_beltCornerInclusion (k l : ℕ) : Continuous (beltCornerInclusion k l) := by
  change Continuous (Prod.map (cellBoundaryInclusion k) (id : CellBoundary l → CellBoundary l))
  exact (continuous_cellBoundaryInclusion k).prodMap continuous_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.continuous_beltCornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.continuous_beltCornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.continuous_beltCornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.continuous_beltCornerInclusion

theorem continuous_coreDiskInclusion (k l : ℕ) : Continuous (coreDiskInclusion k l) := by
  change Continuous (fun x : ClosedCell k => (x, closedCellCenter l))
  exact continuous_id.prodMk continuous_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.continuous_coreDiskInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.continuous_coreDiskInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.continuous_coreDiskInclusion ``Submission.DifferentialGeometry.Topology.Handle.continuous_coreDiskInclusion

theorem continuous_cocoreDiskInclusion (k l : ℕ) : Continuous (cocoreDiskInclusion k l) := by
  change Continuous (fun y : ClosedCell l => (closedCellCenter k, y))
  exact continuous_const.prodMk continuous_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.continuous_cocoreDiskInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.continuous_cocoreDiskInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.continuous_cocoreDiskInclusion ``Submission.DifferentialGeometry.Topology.Handle.continuous_cocoreDiskInclusion

theorem continuous_attachingSphereInclusion (k l : ℕ) : Continuous (attachingSphereInclusion k l) := by
  change Continuous (fun x : CellBoundary k => (cellBoundaryInclusion k x, closedCellCenter l))
  exact (continuous_cellBoundaryInclusion k).prodMk continuous_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.continuous_attachingSphereInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.continuous_attachingSphereInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.continuous_attachingSphereInclusion ``Submission.DifferentialGeometry.Topology.Handle.continuous_attachingSphereInclusion

theorem continuous_beltSphereInclusion (k l : ℕ) : Continuous (beltSphereInclusion k l) := by
  change Continuous (fun y : CellBoundary l => (closedCellCenter k, cellBoundaryInclusion l y))
  exact continuous_const.prodMk (continuous_cellBoundaryInclusion l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.continuous_beltSphereInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.continuous_beltSphereInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.continuous_beltSphereInclusion ``Submission.DifferentialGeometry.Topology.Handle.continuous_beltSphereInclusion

theorem continuous_attachingSphereInclusionAttachingRegion (k l : ℕ) :
    Continuous (attachingSphereInclusionAttachingRegion k l) := by
  change Continuous (fun u : CellBoundary k => (u, closedCellCenter l))
  exact continuous_id.prodMk continuous_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.continuous_attachingSphereInclusionAttachingRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.continuous_attachingSphereInclusionAttachingRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.continuous_attachingSphereInclusionAttachingRegion ``Submission.DifferentialGeometry.Topology.Handle.continuous_attachingSphereInclusionAttachingRegion

theorem continuous_beltSphereInclusionBeltRegion (k l : ℕ) :
    Continuous (beltSphereInclusionBeltRegion k l) := by
  change Continuous (fun v : CellBoundary l => (closedCellCenter k, v))
  exact continuous_const.prodMk continuous_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.continuous_beltSphereInclusionBeltRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.continuous_beltSphereInclusionBeltRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.continuous_beltSphereInclusionBeltRegion ``Submission.DifferentialGeometry.Topology.Handle.continuous_beltSphereInclusionBeltRegion

theorem injective_attachingInclusion (k l : ℕ) : _root_.Function.Injective (attachingInclusion k l) := by
  change _root_.Function.Injective (Prod.map (cellBoundaryInclusion k) (id : ClosedCell l → ClosedCell l))
  exact Injective.prodMap (injective_cellBoundaryInclusion k)
    (_root_.Function.injective_id : _root_.Function.Injective (id : ClosedCell l → ClosedCell l))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.injective_attachingInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.injective_attachingInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.injective_attachingInclusion ``Submission.DifferentialGeometry.Topology.Handle.injective_attachingInclusion

theorem injective_beltInclusion (k l : ℕ) : _root_.Function.Injective (beltInclusion k l) := by
  change _root_.Function.Injective (Prod.map (id : ClosedCell k → ClosedCell k) (cellBoundaryInclusion l))
  exact Injective.prodMap (_root_.Function.injective_id : _root_.Function.Injective (id : ClosedCell k → ClosedCell k))
    (injective_cellBoundaryInclusion l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.injective_beltInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.injective_beltInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.injective_beltInclusion ``Submission.DifferentialGeometry.Topology.Handle.injective_beltInclusion

theorem injective_cornerInclusion (k l : ℕ) : _root_.Function.Injective (cornerInclusion k l) := by
  change _root_.Function.Injective (Prod.map (cellBoundaryInclusion k) (cellBoundaryInclusion l))
  exact Injective.prodMap (injective_cellBoundaryInclusion k) (injective_cellBoundaryInclusion l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.injective_cornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.injective_cornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.injective_cornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.injective_cornerInclusion

theorem injective_attachingCornerInclusion (k l : ℕ) : _root_.Function.Injective (attachingCornerInclusion k l) := by
  change _root_.Function.Injective (Prod.map (id : CellBoundary k → CellBoundary k) (cellBoundaryInclusion l))
  exact Injective.prodMap (_root_.Function.injective_id : _root_.Function.Injective (id : CellBoundary k → CellBoundary k))
    (injective_cellBoundaryInclusion l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.injective_attachingCornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.injective_attachingCornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.injective_attachingCornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.injective_attachingCornerInclusion

theorem injective_beltCornerInclusion (k l : ℕ) : _root_.Function.Injective (beltCornerInclusion k l) := by
  change _root_.Function.Injective (Prod.map (cellBoundaryInclusion k) (id : CellBoundary l → CellBoundary l))
  exact Injective.prodMap (injective_cellBoundaryInclusion k)
    (_root_.Function.injective_id : _root_.Function.Injective (id : CellBoundary l → CellBoundary l))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.injective_beltCornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.injective_beltCornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.injective_beltCornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.injective_beltCornerInclusion

theorem injective_coreDiskInclusion (k l : ℕ) : _root_.Function.Injective (coreDiskInclusion k l) := by
  intro x y h
  simpa [coreDiskInclusion] using congrArg Prod.fst h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.injective_coreDiskInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.injective_coreDiskInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.injective_coreDiskInclusion ``Submission.DifferentialGeometry.Topology.Handle.injective_coreDiskInclusion

theorem injective_cocoreDiskInclusion (k l : ℕ) : _root_.Function.Injective (cocoreDiskInclusion k l) := by
  intro x y h
  simpa [cocoreDiskInclusion] using congrArg Prod.snd h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.injective_cocoreDiskInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.injective_cocoreDiskInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.injective_cocoreDiskInclusion ``Submission.DifferentialGeometry.Topology.Handle.injective_cocoreDiskInclusion

theorem injective_attachingSphereInclusion (k l : ℕ) : _root_.Function.Injective (attachingSphereInclusion k l) := by
  intro x y h
  apply Subtype.ext
  have hfst := congrArg Prod.fst h
  simpa [attachingSphereInclusion, cellBoundaryInclusion] using
    congrArg (fun z : ClosedCell k => (z : EuclideanSpace ℝ (Fin k))) hfst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.injective_attachingSphereInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.injective_attachingSphereInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.injective_attachingSphereInclusion ``Submission.DifferentialGeometry.Topology.Handle.injective_attachingSphereInclusion

theorem injective_beltSphereInclusion (k l : ℕ) : _root_.Function.Injective (beltSphereInclusion k l) := by
  intro x y h
  apply Subtype.ext
  have hsnd := congrArg Prod.snd h
  simpa [beltSphereInclusion, cellBoundaryInclusion] using
    congrArg (fun z : ClosedCell l => (z : EuclideanSpace ℝ (Fin l))) hsnd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.injective_beltSphereInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.injective_beltSphereInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.injective_beltSphereInclusion ``Submission.DifferentialGeometry.Topology.Handle.injective_beltSphereInclusion

theorem injective_attachingSphereInclusionAttachingRegion (k l : ℕ) :
    Injective (attachingSphereInclusionAttachingRegion k l) := by
  intro x y h
  simpa [attachingSphereInclusionAttachingRegion] using congrArg Prod.fst h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.injective_attachingSphereInclusionAttachingRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.injective_attachingSphereInclusionAttachingRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.injective_attachingSphereInclusionAttachingRegion ``Submission.DifferentialGeometry.Topology.Handle.injective_attachingSphereInclusionAttachingRegion

theorem injective_beltSphereInclusionBeltRegion (k l : ℕ) :
    Injective (beltSphereInclusionBeltRegion k l) := by
  intro x y h
  simpa [beltSphereInclusionBeltRegion] using congrArg Prod.snd h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.injective_beltSphereInclusionBeltRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.injective_beltSphereInclusionBeltRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.injective_beltSphereInclusionBeltRegion ``Submission.DifferentialGeometry.Topology.Handle.injective_beltSphereInclusionBeltRegion

theorem isClosedEmbedding_attachingInclusion (k l : ℕ) : Topology.IsClosedEmbedding (attachingInclusion k l) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_attachingInclusion k l) (injective_attachingInclusion k l)
    ((continuous_attachingInclusion k l).isClosedMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isClosedEmbedding_attachingInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isClosedEmbedding_attachingInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isClosedEmbedding_attachingInclusion ``Submission.DifferentialGeometry.Topology.Handle.isClosedEmbedding_attachingInclusion

theorem isClosedEmbedding_beltInclusion (k l : ℕ) : Topology.IsClosedEmbedding (beltInclusion k l) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_beltInclusion k l) (injective_beltInclusion k l)
    ((continuous_beltInclusion k l).isClosedMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isClosedEmbedding_beltInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isClosedEmbedding_beltInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isClosedEmbedding_beltInclusion ``Submission.DifferentialGeometry.Topology.Handle.isClosedEmbedding_beltInclusion

theorem isClosedEmbedding_cornerInclusion (k l : ℕ) : Topology.IsClosedEmbedding (cornerInclusion k l) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_cornerInclusion k l) (injective_cornerInclusion k l)
    ((continuous_cornerInclusion k l).isClosedMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isClosedEmbedding_cornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isClosedEmbedding_cornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isClosedEmbedding_cornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.isClosedEmbedding_cornerInclusion

theorem isClosedEmbedding_attachingCornerInclusion (k l : ℕ) :
    Topology.IsClosedEmbedding (attachingCornerInclusion k l) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_attachingCornerInclusion k l) (injective_attachingCornerInclusion k l)
    ((continuous_attachingCornerInclusion k l).isClosedMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isClosedEmbedding_attachingCornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isClosedEmbedding_attachingCornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isClosedEmbedding_attachingCornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.isClosedEmbedding_attachingCornerInclusion

theorem isClosedEmbedding_beltCornerInclusion (k l : ℕ) :
    Topology.IsClosedEmbedding (beltCornerInclusion k l) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_beltCornerInclusion k l) (injective_beltCornerInclusion k l)
    ((continuous_beltCornerInclusion k l).isClosedMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isClosedEmbedding_beltCornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isClosedEmbedding_beltCornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isClosedEmbedding_beltCornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.isClosedEmbedding_beltCornerInclusion

theorem isClosedEmbedding_coreDiskInclusion (k l : ℕ) : Topology.IsClosedEmbedding (coreDiskInclusion k l) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_coreDiskInclusion k l) (injective_coreDiskInclusion k l)
    ((continuous_coreDiskInclusion k l).isClosedMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isClosedEmbedding_coreDiskInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isClosedEmbedding_coreDiskInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isClosedEmbedding_coreDiskInclusion ``Submission.DifferentialGeometry.Topology.Handle.isClosedEmbedding_coreDiskInclusion

theorem isClosedEmbedding_cocoreDiskInclusion (k l : ℕ) : Topology.IsClosedEmbedding (cocoreDiskInclusion k l) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_cocoreDiskInclusion k l) (injective_cocoreDiskInclusion k l)
    ((continuous_cocoreDiskInclusion k l).isClosedMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isClosedEmbedding_cocoreDiskInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isClosedEmbedding_cocoreDiskInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isClosedEmbedding_cocoreDiskInclusion ``Submission.DifferentialGeometry.Topology.Handle.isClosedEmbedding_cocoreDiskInclusion

theorem isClosedEmbedding_attachingSphereInclusion (k l : ℕ) :
    Topology.IsClosedEmbedding (attachingSphereInclusion k l) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_attachingSphereInclusion k l) (injective_attachingSphereInclusion k l)
    ((continuous_attachingSphereInclusion k l).isClosedMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isClosedEmbedding_attachingSphereInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isClosedEmbedding_attachingSphereInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isClosedEmbedding_attachingSphereInclusion ``Submission.DifferentialGeometry.Topology.Handle.isClosedEmbedding_attachingSphereInclusion

theorem isClosedEmbedding_beltSphereInclusion (k l : ℕ) :
    Topology.IsClosedEmbedding (beltSphereInclusion k l) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_beltSphereInclusion k l) (injective_beltSphereInclusion k l)
    ((continuous_beltSphereInclusion k l).isClosedMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isClosedEmbedding_beltSphereInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isClosedEmbedding_beltSphereInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isClosedEmbedding_beltSphereInclusion ``Submission.DifferentialGeometry.Topology.Handle.isClosedEmbedding_beltSphereInclusion

theorem isEmbedding_attachingInclusion (k l : ℕ) : Topology.IsEmbedding (attachingInclusion k l) :=
  (isClosedEmbedding_attachingInclusion k l).isEmbedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isEmbedding_attachingInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isEmbedding_attachingInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isEmbedding_attachingInclusion ``Submission.DifferentialGeometry.Topology.Handle.isEmbedding_attachingInclusion

theorem isEmbedding_beltInclusion (k l : ℕ) : Topology.IsEmbedding (beltInclusion k l) :=
  (isClosedEmbedding_beltInclusion k l).isEmbedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isEmbedding_beltInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isEmbedding_beltInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isEmbedding_beltInclusion ``Submission.DifferentialGeometry.Topology.Handle.isEmbedding_beltInclusion

theorem isEmbedding_cornerInclusion (k l : ℕ) : Topology.IsEmbedding (cornerInclusion k l) :=
  (isClosedEmbedding_cornerInclusion k l).isEmbedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isEmbedding_cornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isEmbedding_cornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isEmbedding_cornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.isEmbedding_cornerInclusion

theorem isEmbedding_attachingCornerInclusion (k l : ℕ) : Topology.IsEmbedding (attachingCornerInclusion k l) :=
  (isClosedEmbedding_attachingCornerInclusion k l).isEmbedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isEmbedding_attachingCornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isEmbedding_attachingCornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isEmbedding_attachingCornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.isEmbedding_attachingCornerInclusion

theorem isEmbedding_beltCornerInclusion (k l : ℕ) : Topology.IsEmbedding (beltCornerInclusion k l) :=
  (isClosedEmbedding_beltCornerInclusion k l).isEmbedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isEmbedding_beltCornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isEmbedding_beltCornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isEmbedding_beltCornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.isEmbedding_beltCornerInclusion

theorem isEmbedding_coreDiskInclusion (k l : ℕ) : Topology.IsEmbedding (coreDiskInclusion k l) :=
  (isClosedEmbedding_coreDiskInclusion k l).isEmbedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isEmbedding_coreDiskInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isEmbedding_coreDiskInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isEmbedding_coreDiskInclusion ``Submission.DifferentialGeometry.Topology.Handle.isEmbedding_coreDiskInclusion

theorem isEmbedding_cocoreDiskInclusion (k l : ℕ) : Topology.IsEmbedding (cocoreDiskInclusion k l) :=
  (isClosedEmbedding_cocoreDiskInclusion k l).isEmbedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isEmbedding_cocoreDiskInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isEmbedding_cocoreDiskInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isEmbedding_cocoreDiskInclusion ``Submission.DifferentialGeometry.Topology.Handle.isEmbedding_cocoreDiskInclusion

theorem isEmbedding_attachingSphereInclusion (k l : ℕ) : Topology.IsEmbedding (attachingSphereInclusion k l) :=
  (isClosedEmbedding_attachingSphereInclusion k l).isEmbedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isEmbedding_attachingSphereInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isEmbedding_attachingSphereInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isEmbedding_attachingSphereInclusion ``Submission.DifferentialGeometry.Topology.Handle.isEmbedding_attachingSphereInclusion

theorem isEmbedding_beltSphereInclusion (k l : ℕ) : Topology.IsEmbedding (beltSphereInclusion k l) :=
  (isClosedEmbedding_beltSphereInclusion k l).isEmbedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isEmbedding_beltSphereInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isEmbedding_beltSphereInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isEmbedding_beltSphereInclusion ``Submission.DifferentialGeometry.Topology.Handle.isEmbedding_beltSphereInclusion

theorem range_attachingInclusion (k l : ℕ) :
    Set.range (attachingInclusion k l) = attachingRegion k l := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simpa [attachingInclusion, attachingRegion, cellBoundaryInclusion] using q.1.2
  · intro hp
    refine ⟨(⟨(p.1 : EuclideanSpace ℝ (Fin k)), hp⟩, p.2), ?_⟩
    apply Prod.ext
    · simp [attachingInclusion, cellBoundaryInclusion]
    · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.range_attachingInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.range_attachingInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.range_attachingInclusion ``Submission.DifferentialGeometry.Topology.Handle.range_attachingInclusion

theorem range_beltInclusion (k l : ℕ) :
    Set.range (beltInclusion k l) = beltRegion k l := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simpa [beltInclusion, beltRegion, cellBoundaryInclusion] using q.2.2
  · intro hp
    refine ⟨(p.1, ⟨(p.2 : EuclideanSpace ℝ (Fin l)), hp⟩), ?_⟩
    apply Prod.ext
    · rfl
    · simp [beltInclusion, cellBoundaryInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.range_beltInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.range_beltInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.range_beltInclusion ``Submission.DifferentialGeometry.Topology.Handle.range_beltInclusion

theorem range_cornerInclusion (k l : ℕ) :
    Set.range (cornerInclusion k l) = corner k l := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simpa [cornerInclusion, corner, cellBoundaryInclusion] using ⟨q.1.2, q.2.2⟩
  · intro hp
    refine ⟨(⟨(p.1 : EuclideanSpace ℝ (Fin k)), hp.1⟩, ⟨(p.2 : EuclideanSpace ℝ (Fin l)), hp.2⟩), ?_⟩
    apply Prod.ext
    · simp [cornerInclusion, cellBoundaryInclusion]
    · simp [cornerInclusion, cellBoundaryInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.range_cornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.range_cornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.range_cornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.range_cornerInclusion

theorem range_attachingCornerInclusion (k l : ℕ) :
    Set.range (attachingCornerInclusion k l) =
      {p : AttachingRegion k l | ‖(p.2 : EuclideanSpace ℝ (Fin l))‖ = 1} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simpa [attachingCornerInclusion, cellBoundaryInclusion] using q.2.2
  · intro hp
    refine ⟨(p.1, ⟨(p.2 : EuclideanSpace ℝ (Fin l)), hp⟩), ?_⟩
    apply Prod.ext
    · rfl
    · simp [attachingCornerInclusion, cellBoundaryInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.range_attachingCornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.range_attachingCornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.range_attachingCornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.range_attachingCornerInclusion

theorem range_beltCornerInclusion (k l : ℕ) :
    Set.range (beltCornerInclusion k l) =
      {p : BeltRegion k l | ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simpa [beltCornerInclusion, cellBoundaryInclusion] using q.1.2
  · intro hp
    refine ⟨(⟨(p.1 : EuclideanSpace ℝ (Fin k)), hp⟩, p.2), ?_⟩
    apply Prod.ext
    · simp [beltCornerInclusion, cellBoundaryInclusion]
    · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.range_beltCornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.range_beltCornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.range_beltCornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.range_beltCornerInclusion

theorem range_coreDiskInclusion (k l : ℕ) :
    Set.range (coreDiskInclusion k l) = coreDisk k l := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    simp [coreDiskInclusion, coreDisk]
  · intro hp
    simp [coreDisk] at hp
    refine ⟨p.1, ?_⟩
    apply Prod.ext
    · rfl
    · simpa [coreDiskInclusion] using hp.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.range_coreDiskInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.range_coreDiskInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.range_coreDiskInclusion ``Submission.DifferentialGeometry.Topology.Handle.range_coreDiskInclusion

theorem range_cocoreDiskInclusion (k l : ℕ) :
    Set.range (cocoreDiskInclusion k l) = cocoreDisk k l := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    simp [cocoreDiskInclusion, cocoreDisk]
  · intro hp
    simp [cocoreDisk] at hp
    refine ⟨p.2, ?_⟩
    apply Prod.ext
    · simpa [cocoreDiskInclusion] using hp.symm
    · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.range_cocoreDiskInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.range_cocoreDiskInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.range_cocoreDiskInclusion ``Submission.DifferentialGeometry.Topology.Handle.range_cocoreDiskInclusion

theorem range_attachingSphereInclusion (k l : ℕ) :
    Set.range (attachingSphereInclusion k l) = attachingSphere k l := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    simpa [attachingSphereInclusion, attachingSphere, cellBoundaryInclusion] using
      And.intro x.2 (rfl : closedCellCenter l = closedCellCenter l)
  · intro hp
    refine ⟨⟨(p.1 : EuclideanSpace ℝ (Fin k)), hp.1⟩, ?_⟩
    apply Prod.ext
    · simp [attachingSphereInclusion, cellBoundaryInclusion]
    · simp [attachingSphereInclusion, hp.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.range_attachingSphereInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.range_attachingSphereInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.range_attachingSphereInclusion ``Submission.DifferentialGeometry.Topology.Handle.range_attachingSphereInclusion

theorem range_beltSphereInclusion (k l : ℕ) :
    Set.range (beltSphereInclusion k l) = beltSphere k l := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    simpa [beltSphereInclusion, beltSphere, cellBoundaryInclusion] using
      And.intro (rfl : closedCellCenter k = closedCellCenter k) x.2
  · intro hp
    refine ⟨⟨(p.2 : EuclideanSpace ℝ (Fin l)), hp.2⟩, ?_⟩
    apply Prod.ext
    · simp [beltSphereInclusion, hp.1]
    · simp [beltSphereInclusion, cellBoundaryInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.range_beltSphereInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.range_beltSphereInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.range_beltSphereInclusion ``Submission.DifferentialGeometry.Topology.Handle.range_beltSphereInclusion

theorem range_attachingSphereInclusionAttachingRegion (k l : ℕ) :
    Set.range (attachingSphereInclusionAttachingRegion k l) =
      {p : AttachingRegion k l | p.2 = closedCellCenter l} := by
  ext p
  constructor
  · rintro ⟨u, rfl⟩
    rfl
  · intro hp
    refine ⟨p.1, ?_⟩
    apply Prod.ext
    · rfl
    · exact hp.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.range_attachingSphereInclusionAttachingRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.range_attachingSphereInclusionAttachingRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.range_attachingSphereInclusionAttachingRegion ``Submission.DifferentialGeometry.Topology.Handle.range_attachingSphereInclusionAttachingRegion

theorem range_beltSphereInclusionBeltRegion (k l : ℕ) :
    Set.range (beltSphereInclusionBeltRegion k l) =
      {p : BeltRegion k l | p.1 = closedCellCenter k} := by
  ext p
  constructor
  · rintro ⟨v, rfl⟩
    rfl
  · intro hp
    refine ⟨p.2, ?_⟩
    apply Prod.ext
    · exact hp.symm
    · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.range_beltSphereInclusionBeltRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.range_beltSphereInclusionBeltRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.range_beltSphereInclusionBeltRegion ``Submission.DifferentialGeometry.Topology.Handle.range_beltSphereInclusionBeltRegion

@[simp]
theorem attachingInclusion_comp_attachingCornerInclusion {k l : ℕ} (a : Corner k l) :
    attachingInclusion k l (attachingCornerInclusion k l a) = cornerInclusion k l a := by
  rcases a with ⟨a₁, a₂⟩
  simp [attachingInclusion, attachingCornerInclusion, cornerInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.attachingInclusion_comp_attachingCornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.attachingInclusion_comp_attachingCornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.attachingInclusion_comp_attachingCornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.attachingInclusion_comp_attachingCornerInclusion

@[simp]
theorem beltInclusion_comp_beltCornerInclusion {k l : ℕ} (a : Corner k l) :
    beltInclusion k l (beltCornerInclusion k l a) = cornerInclusion k l a := by
  rcases a with ⟨a₁, a₂⟩
  simp [beltInclusion, beltCornerInclusion, cornerInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.beltInclusion_comp_beltCornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.beltInclusion_comp_beltCornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.beltInclusion_comp_beltCornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.beltInclusion_comp_beltCornerInclusion

@[simp]
theorem coreDiskInclusion_comp_cellBoundaryInclusion {k l : ℕ} (x : CellBoundary k) :
    coreDiskInclusion k l (cellBoundaryInclusion k x) = attachingSphereInclusion k l x := by
  simp [coreDiskInclusion, attachingSphereInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.coreDiskInclusion_comp_cellBoundaryInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.coreDiskInclusion_comp_cellBoundaryInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.coreDiskInclusion_comp_cellBoundaryInclusion ``Submission.DifferentialGeometry.Topology.Handle.coreDiskInclusion_comp_cellBoundaryInclusion

@[simp]
theorem cocoreDiskInclusion_comp_cellBoundaryInclusion {k l : ℕ} (y : CellBoundary l) :
    cocoreDiskInclusion k l (cellBoundaryInclusion l y) = beltSphereInclusion k l y := by
  simp [cocoreDiskInclusion, beltSphereInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.cocoreDiskInclusion_comp_cellBoundaryInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.cocoreDiskInclusion_comp_cellBoundaryInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.cocoreDiskInclusion_comp_cellBoundaryInclusion ``Submission.DifferentialGeometry.Topology.Handle.cocoreDiskInclusion_comp_cellBoundaryInclusion

@[simp]
theorem attachingInclusion_comp_attachingSphereInclusionAttachingRegion {k l : ℕ}
    (u : CellBoundary k) :
    attachingInclusion k l (attachingSphereInclusionAttachingRegion k l u) =
      attachingSphereInclusion k l u := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.attachingInclusion_comp_attachingSphereInclusionAttachingRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.attachingInclusion_comp_attachingSphereInclusionAttachingRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.attachingInclusion_comp_attachingSphereInclusionAttachingRegion ``Submission.DifferentialGeometry.Topology.Handle.attachingInclusion_comp_attachingSphereInclusionAttachingRegion

@[simp]
theorem beltInclusion_comp_beltSphereInclusionBeltRegion {k l : ℕ} (v : CellBoundary l) :
    beltInclusion k l (beltSphereInclusionBeltRegion k l v) = beltSphereInclusion k l v := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.beltInclusion_comp_beltSphereInclusionBeltRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.beltInclusion_comp_beltSphereInclusionBeltRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.beltInclusion_comp_beltSphereInclusionBeltRegion ``Submission.DifferentialGeometry.Topology.Handle.beltInclusion_comp_beltSphereInclusionBeltRegion

@[simp]
theorem mem_attachingRegion {k l : ℕ} {p : StandardHandle k l} :
    p ∈ attachingRegion k l ↔ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.mem_attachingRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.mem_attachingRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.mem_attachingRegion ``Submission.DifferentialGeometry.Topology.Handle.mem_attachingRegion

@[simp]
theorem mem_beltRegion {k l : ℕ} {p : StandardHandle k l} :
    p ∈ beltRegion k l ↔ ‖(p.2 : EuclideanSpace ℝ (Fin l))‖ = 1 := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.mem_beltRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.mem_beltRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.mem_beltRegion ``Submission.DifferentialGeometry.Topology.Handle.mem_beltRegion

@[simp]
theorem mem_corner {k l : ℕ} {p : StandardHandle k l} :
    p ∈ corner k l ↔ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 ∧ ‖(p.2 : EuclideanSpace ℝ (Fin l))‖ = 1 := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.mem_corner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.mem_corner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.mem_corner ``Submission.DifferentialGeometry.Topology.Handle.mem_corner

@[simp]
theorem mem_coreDisk {k l : ℕ} {p : StandardHandle k l} :
    p ∈ coreDisk k l ↔ p.2 = closedCellCenter l := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.mem_coreDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.mem_coreDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.mem_coreDisk ``Submission.DifferentialGeometry.Topology.Handle.mem_coreDisk

@[simp]
theorem mem_cocoreDisk {k l : ℕ} {p : StandardHandle k l} :
    p ∈ cocoreDisk k l ↔ p.1 = closedCellCenter k := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.mem_cocoreDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.mem_cocoreDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.mem_cocoreDisk ``Submission.DifferentialGeometry.Topology.Handle.mem_cocoreDisk

@[simp]
theorem mem_attachingSphere {k l : ℕ} {p : StandardHandle k l} :
    p ∈ attachingSphere k l ↔ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 ∧ p.2 = closedCellCenter l := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.mem_attachingSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.mem_attachingSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.mem_attachingSphere ``Submission.DifferentialGeometry.Topology.Handle.mem_attachingSphere

@[simp]
theorem mem_beltSphere {k l : ℕ} {p : StandardHandle k l} :
    p ∈ beltSphere k l ↔ p.1 = closedCellCenter k ∧ ‖(p.2 : EuclideanSpace ℝ (Fin l))‖ = 1 := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.mem_beltSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.mem_beltSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.mem_beltSphere ``Submission.DifferentialGeometry.Topology.Handle.mem_beltSphere

theorem attachingRegion_inter_beltRegion (k l : ℕ) :
    attachingRegion k l ∩ beltRegion k l = corner k l := by
  ext p
  simp [attachingRegion, beltRegion, corner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.attachingRegion_inter_beltRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.attachingRegion_inter_beltRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.attachingRegion_inter_beltRegion ``Submission.DifferentialGeometry.Topology.Handle.attachingRegion_inter_beltRegion

theorem coreDisk_inter_cocoreDisk (k l : ℕ) :
    coreDisk k l ∩ cocoreDisk k l = {(closedCellCenter k, closedCellCenter l)} := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hp1, hp2⟩
    simp [coreDisk, cocoreDisk] at hp1 hp2
    ext <;> simp [hp1, hp2]
  · intro hp
    simp at hp
    simp [coreDisk, cocoreDisk, hp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.coreDisk_inter_cocoreDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.coreDisk_inter_cocoreDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.coreDisk_inter_cocoreDisk ``Submission.DifferentialGeometry.Topology.Handle.coreDisk_inter_cocoreDisk

theorem attachingSphere_eq_inter (k l : ℕ) :
    attachingSphere k l = attachingRegion k l ∩ coreDisk k l := by
  ext p
  simp [attachingSphere, attachingRegion, coreDisk]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.attachingSphere_eq_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.attachingSphere_eq_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.attachingSphere_eq_inter ``Submission.DifferentialGeometry.Topology.Handle.attachingSphere_eq_inter

theorem beltSphere_eq_inter (k l : ℕ) :
    beltSphere k l = beltRegion k l ∩ cocoreDisk k l := by
  ext p
  simp [beltSphere, beltRegion, cocoreDisk, and_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.beltSphere_eq_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.beltSphere_eq_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.beltSphere_eq_inter ``Submission.DifferentialGeometry.Topology.Handle.beltSphere_eq_inter

theorem corner_subset_attachingRegion (k l : ℕ) : corner k l ⊆ attachingRegion k l := by
  intro p hp
  simpa [attachingRegion, corner] using hp.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.corner_subset_attachingRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.corner_subset_attachingRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.corner_subset_attachingRegion ``Submission.DifferentialGeometry.Topology.Handle.corner_subset_attachingRegion

theorem corner_subset_beltRegion (k l : ℕ) : corner k l ⊆ beltRegion k l := by
  intro p hp
  simpa [beltRegion, corner] using hp.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.corner_subset_beltRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.corner_subset_beltRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.corner_subset_beltRegion ``Submission.DifferentialGeometry.Topology.Handle.corner_subset_beltRegion

theorem attachingSphere_subset_attachingRegion (k l : ℕ) : attachingSphere k l ⊆ attachingRegion k l := by
  intro p hp
  simpa [attachingRegion, attachingSphere] using hp.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.attachingSphere_subset_attachingRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.attachingSphere_subset_attachingRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.attachingSphere_subset_attachingRegion ``Submission.DifferentialGeometry.Topology.Handle.attachingSphere_subset_attachingRegion

theorem beltSphere_subset_beltRegion (k l : ℕ) : beltSphere k l ⊆ beltRegion k l := by
  intro p hp
  simpa [beltRegion, beltSphere] using hp.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.beltSphere_subset_beltRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.beltSphere_subset_beltRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.beltSphere_subset_beltRegion ``Submission.DifferentialGeometry.Topology.Handle.beltSphere_subset_beltRegion

theorem attachingSphere_subset_coreDisk (k l : ℕ) : attachingSphere k l ⊆ coreDisk k l := by
  intro p hp
  simpa [coreDisk, attachingSphere] using hp.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.attachingSphere_subset_coreDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.attachingSphere_subset_coreDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.attachingSphere_subset_coreDisk ``Submission.DifferentialGeometry.Topology.Handle.attachingSphere_subset_coreDisk

theorem beltSphere_subset_cocoreDisk (k l : ℕ) : beltSphere k l ⊆ cocoreDisk k l := by
  intro p hp
  simpa [cocoreDisk, beltSphere] using hp.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.beltSphere_subset_cocoreDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.beltSphere_subset_cocoreDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.beltSphere_subset_cocoreDisk ``Submission.DifferentialGeometry.Topology.Handle.beltSphere_subset_cocoreDisk

end DifferentialGeometry.Topology.Handle
