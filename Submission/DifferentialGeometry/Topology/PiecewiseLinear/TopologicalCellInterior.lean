/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.ClosedBallImage
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CanonicalConfiguration

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology _root_.Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsTopologicalCellWithInterior.interior_eq
    {n : ℕ} {C I : Set (EuclideanSpace ℝ (Fin n))}
    (h : IsTopologicalCellWithInterior n C I) : interior C = I := by
  rcases h with ⟨φ, hφ⟩
  rw [DifferentialGeometry.Topology.interior_eq_image_of_homeomorphClosedBall φ.symm, hφ,
    _root_.Set.image_image]
  congr 1
  ext q
  simp only [_root_.Set.mem_preimage, _root_.Metric.mem_ball, dist_zero_right, _root_.Set.mem_ofPred_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalCellWithInterior.interior_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalCellWithInterior.interior_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalCellWithInterior.interior_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalCellWithInterior.interior_eq

theorem IsTopologicalCellWithInterior.interior_mono
    {n : ℕ} {X : Type*} [TopologicalSpace X] {C I D J : Set X}
    (hC : IsTopologicalCellWithInterior n C I)
    (hD : IsTopologicalCellWithInterior n D J) (hCD : C ⊆ D) : I ⊆ J := by
  rcases hC with ⟨φC, hI⟩
  rcases hD with ⟨φD, hJ⟩
  let g : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 →
      EuclideanSpace ℝ (Fin n) := fun q => φD.symm (_root_.Set.inclusion hCD (φC q))
  have hgcont : Continuous g := continuous_subtype_val.comp
    (φD.symm.continuous.comp ((continuous_inclusion hCD).comp φC.continuous))
  have hginj : Function.Injective g :=
    Subtype.val_injective.comp
      (φD.symm.injective.comp ((_root_.Set.inclusion_injective hCD).comp φC.injective))
  have hrange : _root_.Set.range g ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rintro _ ⟨q, rfl⟩
    exact (φD.symm (_root_.Set.inclusion hCD (φC q))).property
  have hmain := DifferentialGeometry.Topology.interior_range_eq_image_preimage_interior
    (_root_.ProperSpace.isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) g hgcont hginj
  have hgball : ∀ q : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      ‖(q : EuclideanSpace ℝ (Fin n))‖ < 1 → ‖g q‖ < 1 := by
    intro q hq
    have hqint : g q ∈ interior (_root_.Set.range g) := by
      rw [hmain]
      refine ⟨q, ?_, rfl⟩
      simpa only [_root_.Set.mem_preimage, interior_closedBall _ one_ne_zero, _root_.Metric.mem_ball,
        dist_zero_right] using hq
    have hqball := _root_.interior_mono hrange hqint
    simpa only [interior_closedBall _ one_ne_zero, _root_.Metric.mem_ball, dist_zero_right] using hqball
  rw [hI, hJ]
  rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
  exact ⟨inclusion hCD (φC q),
    ⟨φD.symm (_root_.Set.inclusion hCD (φC q)), hgball q hq,
      φD.apply_symm_apply (_root_.Set.inclusion hCD (φC q))⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalCellWithInterior.interior_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalCellWithInterior.interior_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalCellWithInterior.interior_mono ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalCellWithInterior.interior_mono

end DifferentialGeometry.Topology.PiecewiseLinear
