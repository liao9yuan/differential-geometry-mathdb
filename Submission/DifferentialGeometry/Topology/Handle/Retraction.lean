import Submission.DifferentialGeometry.Topology.Handle.Defs
import Submission.DifferentialGeometry.Topology.Handle.Duality
import Submission.DifferentialGeometry.Topology.Homotopy.ClosedCell

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.Handle

open _root_.Submission.DifferentialGeometry.Topology.Homotopy
open _root_.ContinuousMap
open _root_.unitInterval

def coreRetract (k l : ℕ) : StrongDeformationRetract (coreDisk k l) :=
  StrongDeformationRetract.congr (by
    ext p
    simp [coreDisk]) (StrongDeformationRetract.prod
      (StrongDeformationRetract.refl (ClosedCell k)) (closedCellRetract l))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.coreRetract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.coreRetract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.coreRetract ``Submission.DifferentialGeometry.Topology.Handle.coreRetract

def cocoreRetract (k l : ℕ) : StrongDeformationRetract (cocoreDisk k l) :=
  StrongDeformationRetract.congr (by
    ext p
    simp [cocoreDisk]) (StrongDeformationRetract.prod
      (closedCellRetract k) (StrongDeformationRetract.refl (ClosedCell l)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.cocoreRetract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.cocoreRetract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.cocoreRetract ``Submission.DifferentialGeometry.Topology.Handle.cocoreRetract

def attachingSphereRetract (k l : ℕ) :
    StrongDeformationRetract
      ({p : AttachingRegion k l | p.2 = closedCellCenter l} : Set (AttachingRegion k l)) :=
  StrongDeformationRetract.congr (by
    ext p
    simp) (StrongDeformationRetract.prod
      (StrongDeformationRetract.refl (CellBoundary k)) (closedCellRetract l))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.attachingSphereRetract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.attachingSphereRetract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.attachingSphereRetract ``Submission.DifferentialGeometry.Topology.Handle.attachingSphereRetract

def beltSphereRetract (k l : ℕ) :
    StrongDeformationRetract
      ({p : BeltRegion k l | p.1 = closedCellCenter k} : Set (BeltRegion k l)) :=
  StrongDeformationRetract.congr (by
    ext p
    simp) (StrongDeformationRetract.prod
      (closedCellRetract k) (StrongDeformationRetract.refl (CellBoundary l)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.beltSphereRetract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.beltSphereRetract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.beltSphereRetract ``Submission.DifferentialGeometry.Topology.Handle.beltSphereRetract

theorem coreRetract_apply (k l : ℕ) (x : ClosedCell k) (y : ClosedCell l) :
    ((coreRetract k l).retraction (x, y) : StandardHandle k l) = (x, closedCellCenter l) := by
  simp [coreRetract]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.coreRetract_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.coreRetract_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.coreRetract_apply ``Submission.DifferentialGeometry.Topology.Handle.coreRetract_apply

theorem cocoreRetract_apply (k l : ℕ) (x : ClosedCell k) (y : ClosedCell l) :
    ((cocoreRetract k l).retraction (x, y) : StandardHandle k l) = (closedCellCenter k, y) := by
  simp [cocoreRetract]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.cocoreRetract_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.cocoreRetract_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.cocoreRetract_apply ``Submission.DifferentialGeometry.Topology.Handle.cocoreRetract_apply

theorem coreRetract_retraction_attachingRegion (k l : ℕ) {p : StandardHandle k l}
    (hp : p ∈ attachingRegion k l) :
    ((coreRetract k l).retraction p : StandardHandle k l) =
      attachingInclusion k l
        (⟨p.1, by simpa [attachingRegion] using hp⟩, closedCellCenter l) := by
  rcases p with ⟨x, y⟩
  rw [coreRetract_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.coreRetract_retraction_attachingRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.coreRetract_retraction_attachingRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.coreRetract_retraction_attachingRegion ``Submission.DifferentialGeometry.Topology.Handle.coreRetract_retraction_attachingRegion

theorem cocoreRetract_retraction_beltRegion (k l : ℕ) {p : StandardHandle k l}
    (hp : p ∈ beltRegion k l) :
    ((cocoreRetract k l).retraction p : StandardHandle k l) =
      beltInclusion k l
        (closedCellCenter k, ⟨p.2, by simpa [beltRegion] using hp⟩) := by
  rcases p with ⟨x, y⟩
  rw [cocoreRetract_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.cocoreRetract_retraction_beltRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.cocoreRetract_retraction_beltRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.cocoreRetract_retraction_beltRegion ``Submission.DifferentialGeometry.Topology.Handle.cocoreRetract_retraction_beltRegion

theorem attachingSphereRetract_apply (k l : ℕ) (u : CellBoundary k) (y : ClosedCell l) :
    ((attachingSphereRetract k l).retraction (u, y) : AttachingRegion k l) = (u, closedCellCenter l) :=
  by
  rw [attachingSphereRetract]
  rw [StrongDeformationRetract.congr_retraction_apply]
  rw [StrongDeformationRetract.prod_retraction_apply]
  rw [StrongDeformationRetract.refl_retraction_apply]
  rw [closedCellRetract_retraction_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.attachingSphereRetract_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.attachingSphereRetract_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.attachingSphereRetract_apply ``Submission.DifferentialGeometry.Topology.Handle.attachingSphereRetract_apply

theorem beltSphereRetract_apply (k l : ℕ) (x : ClosedCell k) (v : CellBoundary l) :
    ((beltSphereRetract k l).retraction (x, v) : BeltRegion k l) = (closedCellCenter k, v) := by
  rw [beltSphereRetract]
  rw [StrongDeformationRetract.congr_retraction_apply]
  rw [StrongDeformationRetract.prod_retraction_apply]
  rw [StrongDeformationRetract.refl_retraction_apply]
  rw [closedCellRetract_retraction_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.beltSphereRetract_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.beltSphereRetract_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.beltSphereRetract_apply ``Submission.DifferentialGeometry.Topology.Handle.beltSphereRetract_apply

theorem coreRetract_homotopy_apply (k l : ℕ) (t : I) (x : ClosedCell k) (y : ClosedCell l) :
    ((coreRetract k l).homotopy (t, (x, y)) : StandardHandle k l) = (x, radialStep l t y) := by
  rw [coreRetract]
  rw [StrongDeformationRetract.congr_homotopy_apply]
  rw [StrongDeformationRetract.prod_homotopy_apply]
  rw [StrongDeformationRetract.refl_homotopy_apply]
  rw [closedCellRetract_homotopy_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.coreRetract_homotopy_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.coreRetract_homotopy_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.coreRetract_homotopy_apply ``Submission.DifferentialGeometry.Topology.Handle.coreRetract_homotopy_apply

theorem cocoreRetract_homotopy_apply (k l : ℕ) (t : I) (x : ClosedCell k) (y : ClosedCell l) :
    ((cocoreRetract k l).homotopy (t, (x, y)) : StandardHandle k l) = (radialStep k t x, y) := by
  rw [cocoreRetract]
  rw [StrongDeformationRetract.congr_homotopy_apply]
  rw [StrongDeformationRetract.prod_homotopy_apply]
  rw [StrongDeformationRetract.refl_homotopy_apply]
  rw [closedCellRetract_homotopy_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.cocoreRetract_homotopy_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.cocoreRetract_homotopy_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.cocoreRetract_homotopy_apply ``Submission.DifferentialGeometry.Topology.Handle.cocoreRetract_homotopy_apply

theorem attachingSphereRetract_homotopy_apply (k l : ℕ) (t : I) (u : CellBoundary k)
    (y : ClosedCell l) :
    ((attachingSphereRetract k l).homotopy (t, (u, y)) : AttachingRegion k l) =
      (u, radialStep l t y) := by
  rw [attachingSphereRetract]
  rw [StrongDeformationRetract.congr_homotopy_apply]
  rw [StrongDeformationRetract.prod_homotopy_apply]
  rw [StrongDeformationRetract.refl_homotopy_apply]
  rw [closedCellRetract_homotopy_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.attachingSphereRetract_homotopy_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.attachingSphereRetract_homotopy_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.attachingSphereRetract_homotopy_apply ``Submission.DifferentialGeometry.Topology.Handle.attachingSphereRetract_homotopy_apply

theorem beltSphereRetract_homotopy_apply (k l : ℕ) (t : I) (x : ClosedCell k)
    (v : CellBoundary l) :
    ((beltSphereRetract k l).homotopy (t, (x, v)) : BeltRegion k l) =
      (radialStep k t x, v) := by
  rw [beltSphereRetract]
  rw [StrongDeformationRetract.congr_homotopy_apply]
  rw [StrongDeformationRetract.prod_homotopy_apply]
  rw [StrongDeformationRetract.refl_homotopy_apply]
  rw [closedCellRetract_homotopy_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.beltSphereRetract_homotopy_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.beltSphereRetract_homotopy_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.beltSphereRetract_homotopy_apply ``Submission.DifferentialGeometry.Topology.Handle.beltSphereRetract_homotopy_apply

theorem coreRetract_preserves_attachingRegion (k l : ℕ) (t : I) {p : StandardHandle k l}
    (hp : p ∈ attachingRegion k l) :
    (coreRetract k l).homotopy (t, p) ∈ attachingRegion k l := by
  rcases p with ⟨x, y⟩
  rw [coreRetract_homotopy_apply]
  simpa [attachingRegion] using hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.coreRetract_preserves_attachingRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.coreRetract_preserves_attachingRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.coreRetract_preserves_attachingRegion ``Submission.DifferentialGeometry.Topology.Handle.coreRetract_preserves_attachingRegion

theorem cocoreRetract_preserves_beltRegion (k l : ℕ) (t : I) {p : StandardHandle k l}
    (hp : p ∈ beltRegion k l) :
    (cocoreRetract k l).homotopy (t, p) ∈ beltRegion k l := by
  rcases p with ⟨x, y⟩
  rw [cocoreRetract_homotopy_apply]
  simpa [beltRegion] using hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.cocoreRetract_preserves_beltRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.cocoreRetract_preserves_beltRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.cocoreRetract_preserves_beltRegion ``Submission.DifferentialGeometry.Topology.Handle.cocoreRetract_preserves_beltRegion

theorem coreRetract_swap (k l : ℕ) (t : I) (p : StandardHandle k l) :
    swap k l ((coreRetract k l).homotopy (t, p)) =
      (cocoreRetract l k).homotopy (t, swap k l p) := by
  rcases p with ⟨x, y⟩
  simp [coreRetract_homotopy_apply, cocoreRetract_homotopy_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.coreRetract_swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.coreRetract_swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.coreRetract_swap ``Submission.DifferentialGeometry.Topology.Handle.coreRetract_swap

theorem cocoreRetract_swap (k l : ℕ) (t : I) (p : StandardHandle k l) :
    swap k l ((cocoreRetract k l).homotopy (t, p)) =
      (coreRetract l k).homotopy (t, swap k l p) := by
  rcases p with ⟨x, y⟩
  simp [coreRetract_homotopy_apply, cocoreRetract_homotopy_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.cocoreRetract_swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.cocoreRetract_swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.cocoreRetract_swap ``Submission.DifferentialGeometry.Topology.Handle.cocoreRetract_swap

theorem attachingSphereRetract_swap (k l : ℕ) (t : I) (p : AttachingRegion k l) :
    swap k l (attachingInclusion k l ((attachingSphereRetract k l).homotopy (t, p))) =
      beltInclusion l k ((beltSphereRetract l k).homotopy (t, Prod.swap p)) := by
  rcases p with ⟨u, y⟩
  rw [attachingSphereRetract_homotopy_apply]
  rw [beltSphereRetract_homotopy_apply]
  simp [attachingInclusion, beltInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.attachingSphereRetract_swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.attachingSphereRetract_swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.attachingSphereRetract_swap ``Submission.DifferentialGeometry.Topology.Handle.attachingSphereRetract_swap

theorem beltSphereRetract_swap (k l : ℕ) (t : I) (p : BeltRegion k l) :
    swap k l (beltInclusion k l ((beltSphereRetract k l).homotopy (t, p))) =
      attachingInclusion l k ((attachingSphereRetract l k).homotopy (t, Prod.swap p)) := by
  rcases p with ⟨x, v⟩
  rw [beltSphereRetract_homotopy_apply]
  rw [attachingSphereRetract_homotopy_apply]
  simp [attachingInclusion, beltInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.beltSphereRetract_swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.beltSphereRetract_swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.beltSphereRetract_swap ``Submission.DifferentialGeometry.Topology.Handle.beltSphereRetract_swap

end DifferentialGeometry.Topology.Handle
