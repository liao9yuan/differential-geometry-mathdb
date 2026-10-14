/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.Attachment.Homeomorph
import Submission.DifferentialGeometry.Topology.Homeomorph.SphereExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Metric _root_.Set

namespace DifferentialGeometry.Topology

noncomputable def closedCellHomeomorphExtension {n m : ℕ}
    (f : CellBoundary n ≃ₜ CellBoundary m) : ClosedCell n ≃ₜ ClosedCell m := by
  let e₁ : CellBoundary n ≃ₜ _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    Homeomorph.setCongr (by ext x; exact mem_sphere_zero_iff_norm.symm)
  let e₂ : CellBoundary m ≃ₜ _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 :=
    Homeomorph.setCongr (by ext x; exact mem_sphere_zero_iff_norm.symm)
  exact (sphereRadialHomeomorph ((e₁.symm.trans f).trans e₂)).subtype fun x => by
    rw [norm_sphereRadialHomeomorph]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.closedCellHomeomorphExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.closedCellHomeomorphExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.closedCellHomeomorphExtension ``Submission.DifferentialGeometry.Topology.closedCellHomeomorphExtension

@[simp]
theorem norm_closedCellHomeomorphExtension {n m : ℕ}
    (f : CellBoundary n ≃ₜ CellBoundary m) (x : ClosedCell n) :
    ‖(closedCellHomeomorphExtension f x : EuclideanSpace ℝ (Fin m))‖ = ‖x.val‖ :=
  norm_sphereRadialHomeomorph _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.norm_closedCellHomeomorphExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.norm_closedCellHomeomorphExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.norm_closedCellHomeomorphExtension ``Submission.DifferentialGeometry.Topology.norm_closedCellHomeomorphExtension

@[simp]
theorem closedCellHomeomorphExtension_boundary {n m : ℕ}
    (f : CellBoundary n ≃ₜ CellBoundary m) (x : CellBoundary n) :
    closedCellHomeomorphExtension f (cellBoundaryInclusion n x) =
      cellBoundaryInclusion m (f x) := by
  apply Subtype.ext
  exact sphereRadialHomeomorph_apply_sphere _
    ⟨x.val, mem_sphere_zero_iff_norm.mpr x.property⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.closedCellHomeomorphExtension_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.closedCellHomeomorphExtension_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.closedCellHomeomorphExtension_boundary ``Submission.DifferentialGeometry.Topology.closedCellHomeomorphExtension_boundary

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def cellAdjunctionHomeomorph {n m : ℕ}
    (φ : CellBoundary n → X) (ψ : CellBoundary m → Y)
    (a : CellBoundary n ≃ₜ CellBoundary m) (f : X ≃ₜ Y)
    (hφ : ∀ x, f (φ x) = ψ (a x)) :
    CellAdjunctionSpace n φ ≃ₜ CellAdjunctionSpace m ψ :=
  adjunctionHomeomorph (cellBoundaryInclusion n) φ (cellBoundaryInclusion m) ψ
    a.toEquiv (closedCellHomeomorphExtension a) f
    (closedCellHomeomorphExtension_boundary a) hφ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cellAdjunctionHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cellAdjunctionHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cellAdjunctionHomeomorph ``Submission.DifferentialGeometry.Topology.cellAdjunctionHomeomorph

@[simp]
theorem cellAdjunctionHomeomorph_lower {n m : ℕ}
    (φ : CellBoundary n → X) (ψ : CellBoundary m → Y)
    (a : CellBoundary n ≃ₜ CellBoundary m) (f : X ≃ₜ Y)
    (hφ : ∀ x, f (φ x) = ψ (a x)) (x : X) :
    cellAdjunctionHomeomorph φ ψ a f hφ (adjunctionLower φ x) =
      adjunctionLower ψ (f x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cellAdjunctionHomeomorph_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cellAdjunctionHomeomorph_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cellAdjunctionHomeomorph_lower ``Submission.DifferentialGeometry.Topology.cellAdjunctionHomeomorph_lower

@[simp]
theorem cellAdjunctionHomeomorph_cell {n m : ℕ}
    (φ : CellBoundary n → X) (ψ : CellBoundary m → Y)
    (a : CellBoundary n ≃ₜ CellBoundary m) (f : X ≃ₜ Y)
    (hφ : ∀ x, f (φ x) = ψ (a x)) (x : ClosedCell n) :
    cellAdjunctionHomeomorph φ ψ a f hφ (adjunctionCell (cellBoundaryInclusion n) φ x) =
      adjunctionCell (cellBoundaryInclusion m) ψ (closedCellHomeomorphExtension a x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cellAdjunctionHomeomorph_cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cellAdjunctionHomeomorph_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cellAdjunctionHomeomorph_cell ``Submission.DifferentialGeometry.Topology.cellAdjunctionHomeomorph_cell

end DifferentialGeometry.Topology
