import Submission.DifferentialGeometry.Topology.Attachment.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.Handle

universe u

abbrev StandardHandle (k l : ℕ) : Type := ClosedCell k × ClosedCell l

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.StandardHandle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.StandardHandle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.StandardHandle ``Submission.DifferentialGeometry.Topology.Handle.StandardHandle

abbrev AttachingRegion (k l : ℕ) : Type := CellBoundary k × ClosedCell l

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.AttachingRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.AttachingRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.AttachingRegion ``Submission.DifferentialGeometry.Topology.Handle.AttachingRegion

abbrev BeltRegion (k l : ℕ) : Type := ClosedCell k × CellBoundary l

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.BeltRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.BeltRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.BeltRegion ``Submission.DifferentialGeometry.Topology.Handle.BeltRegion

abbrev Corner (k l : ℕ) : Type := CellBoundary k × CellBoundary l

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.Corner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.Corner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.Corner ``Submission.DifferentialGeometry.Topology.Handle.Corner

def attachingInclusion (k l : ℕ) : AttachingRegion k l → StandardHandle k l :=
  Prod.map (cellBoundaryInclusion k) (id : ClosedCell l → ClosedCell l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.attachingInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.attachingInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.attachingInclusion ``Submission.DifferentialGeometry.Topology.Handle.attachingInclusion

def beltInclusion (k l : ℕ) : BeltRegion k l → StandardHandle k l :=
  Prod.map (id : ClosedCell k → ClosedCell k) (cellBoundaryInclusion l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.beltInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.beltInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.beltInclusion ``Submission.DifferentialGeometry.Topology.Handle.beltInclusion

def cornerInclusion (k l : ℕ) : Corner k l → StandardHandle k l :=
  Prod.map (cellBoundaryInclusion k) (cellBoundaryInclusion l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.cornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.cornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.cornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.cornerInclusion

def attachingCornerInclusion (k l : ℕ) : Corner k l → AttachingRegion k l :=
  Prod.map (id : CellBoundary k → CellBoundary k) (cellBoundaryInclusion l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.attachingCornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.attachingCornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.attachingCornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.attachingCornerInclusion

def beltCornerInclusion (k l : ℕ) : Corner k l → BeltRegion k l :=
  Prod.map (cellBoundaryInclusion k) (id : CellBoundary l → CellBoundary l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.beltCornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.beltCornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.beltCornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.beltCornerInclusion

def coreDiskInclusion (k l : ℕ) : ClosedCell k → StandardHandle k l :=
  fun x => (x, closedCellCenter l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.coreDiskInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.coreDiskInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.coreDiskInclusion ``Submission.DifferentialGeometry.Topology.Handle.coreDiskInclusion

def cocoreDiskInclusion (k l : ℕ) : ClosedCell l → StandardHandle k l :=
  fun y => (closedCellCenter k, y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.cocoreDiskInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.cocoreDiskInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.cocoreDiskInclusion ``Submission.DifferentialGeometry.Topology.Handle.cocoreDiskInclusion

def attachingSphereInclusion (k l : ℕ) : CellBoundary k → StandardHandle k l :=
  fun x => (cellBoundaryInclusion k x, closedCellCenter l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.attachingSphereInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.attachingSphereInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.attachingSphereInclusion ``Submission.DifferentialGeometry.Topology.Handle.attachingSphereInclusion

def beltSphereInclusion (k l : ℕ) : CellBoundary l → StandardHandle k l :=
  fun y => (closedCellCenter k, cellBoundaryInclusion l y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.beltSphereInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.beltSphereInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.beltSphereInclusion ``Submission.DifferentialGeometry.Topology.Handle.beltSphereInclusion

def attachingSphereInclusionAttachingRegion (k l : ℕ) : CellBoundary k → AttachingRegion k l :=
  fun u => (u, closedCellCenter l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.attachingSphereInclusionAttachingRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.attachingSphereInclusionAttachingRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.attachingSphereInclusionAttachingRegion ``Submission.DifferentialGeometry.Topology.Handle.attachingSphereInclusionAttachingRegion

def beltSphereInclusionBeltRegion (k l : ℕ) : CellBoundary l → BeltRegion k l :=
  fun v => (closedCellCenter k, v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.beltSphereInclusionBeltRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.beltSphereInclusionBeltRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.beltSphereInclusionBeltRegion ``Submission.DifferentialGeometry.Topology.Handle.beltSphereInclusionBeltRegion

def attachingRegion (k l : ℕ) : Set (StandardHandle k l) :=
  {p | ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.attachingRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.attachingRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.attachingRegion ``Submission.DifferentialGeometry.Topology.Handle.attachingRegion

def beltRegion (k l : ℕ) : Set (StandardHandle k l) :=
  {p | ‖(p.2 : EuclideanSpace ℝ (Fin l))‖ = 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.beltRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.beltRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.beltRegion ``Submission.DifferentialGeometry.Topology.Handle.beltRegion

def corner (k l : ℕ) : Set (StandardHandle k l) :=
  {p | ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 ∧ ‖(p.2 : EuclideanSpace ℝ (Fin l))‖ = 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.corner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.corner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.corner ``Submission.DifferentialGeometry.Topology.Handle.corner

def coreDisk (k l : ℕ) : Set (StandardHandle k l) :=
  {p | p.2 = closedCellCenter l}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.coreDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.coreDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.coreDisk ``Submission.DifferentialGeometry.Topology.Handle.coreDisk

def cocoreDisk (k l : ℕ) : Set (StandardHandle k l) :=
  {p | p.1 = closedCellCenter k}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.cocoreDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.cocoreDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.cocoreDisk ``Submission.DifferentialGeometry.Topology.Handle.cocoreDisk

def attachingSphere (k l : ℕ) : Set (StandardHandle k l) :=
  {p | ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 ∧ p.2 = closedCellCenter l}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.attachingSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.attachingSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.attachingSphere ``Submission.DifferentialGeometry.Topology.Handle.attachingSphere

def beltSphere (k l : ℕ) : Set (StandardHandle k l) :=
  {p | p.1 = closedCellCenter k ∧ ‖(p.2 : EuclideanSpace ℝ (Fin l))‖ = 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.beltSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.beltSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.beltSphere ``Submission.DifferentialGeometry.Topology.Handle.beltSphere

def handleSet (k l : ℕ) : Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ×ˢ
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin l)) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.handleSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.handleSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.handleSet ``Submission.DifferentialGeometry.Topology.Handle.handleSet

def attachingSet (k l : ℕ) : Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ×ˢ
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin l)) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.attachingSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.attachingSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.attachingSet ``Submission.DifferentialGeometry.Topology.Handle.attachingSet

def beltSet (k l : ℕ) : Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ×ˢ
    Metric.sphere (0 : EuclideanSpace ℝ (Fin l)) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.beltSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.beltSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.beltSet ``Submission.DifferentialGeometry.Topology.Handle.beltSet

def cornerSet (k l : ℕ) : Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ×ˢ
    Metric.sphere (0 : EuclideanSpace ℝ (Fin l)) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.cornerSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.cornerSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.cornerSet ``Submission.DifferentialGeometry.Topology.Handle.cornerSet

def toAmbient {k l : ℕ} (p : StandardHandle k l) :
    EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l) :=
  ((p.1 : EuclideanSpace ℝ (Fin k)), (p.2 : EuclideanSpace ℝ (Fin l)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.toAmbient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.toAmbient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.toAmbient ``Submission.DifferentialGeometry.Topology.Handle.toAmbient

abbrev AdjunctionSpace {X : Type u} (k l : ℕ) (φ : AttachingRegion k l → X) : Type u :=
  DifferentialGeometry.Topology.AdjunctionSpace (attachingInclusion k l) φ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.AdjunctionSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.AdjunctionSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.AdjunctionSpace ``Submission.DifferentialGeometry.Topology.Handle.AdjunctionSpace

def lower {X : Type u} {k l : ℕ} (φ : AttachingRegion k l → X) : X → AdjunctionSpace k l φ :=
  DifferentialGeometry.Topology.adjunctionLower (i := attachingInclusion k l) φ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.lower ``Submission.DifferentialGeometry.Topology.Handle.lower

def cell {X : Type u} {k l : ℕ} (φ : AttachingRegion k l → X) :
    StandardHandle k l → AdjunctionSpace k l φ :=
  DifferentialGeometry.Topology.adjunctionCell (attachingInclusion k l) φ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.cell ``Submission.DifferentialGeometry.Topology.Handle.cell

end DifferentialGeometry.Topology.Handle
