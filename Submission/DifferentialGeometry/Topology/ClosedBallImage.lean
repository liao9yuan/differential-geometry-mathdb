/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.OpenEmbeddingFrontier
import Submission.DifferentialGeometry.Topology.BicollaredComplement
import Mathlib.Analysis.Normed.Module.Connected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def closedBallParam {C : Set E} (φ : C ≃ₜ _root_.Metric.closedBall (0 : E) 1) :
    closedBall (0 : E) 1 → E := fun b => (φ.symm b : E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.closedBallParam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.closedBallParam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.closedBallParam ``Submission.DifferentialGeometry.Topology.closedBallParam

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem continuous_closedBallParam {C : Set E} (φ : C ≃ₜ _root_.Metric.closedBall (0 : E) 1) :
    Continuous (closedBallParam φ) :=
  continuous_subtype_val.comp φ.symm.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_closedBallParam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_closedBallParam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_closedBallParam ``Submission.DifferentialGeometry.Topology.continuous_closedBallParam

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem injective_closedBallParam {C : Set E} (φ : C ≃ₜ _root_.Metric.closedBall (0 : E) 1) :
    Function.Injective (closedBallParam φ) := fun _ _ hab =>
  φ.symm.injective (Subtype.ext hab)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.injective_closedBallParam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.injective_closedBallParam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.injective_closedBallParam ``Submission.DifferentialGeometry.Topology.injective_closedBallParam

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem range_closedBallParam {C : Set E} (φ : C ≃ₜ _root_.Metric.closedBall (0 : E) 1) :
    range (closedBallParam φ) = C := by
  ext y
  constructor
  · rintro ⟨b, rfl⟩
    exact (φ.symm b).2
  · intro hy
    exact ⟨φ ⟨y, hy⟩, congrArg Subtype.val (φ.symm_apply_apply ⟨y, hy⟩)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.range_closedBallParam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.range_closedBallParam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.range_closedBallParam ``Submission.DifferentialGeometry.Topology.range_closedBallParam

theorem isCompact_of_homeomorphClosedBall {C : Set E} (φ : C ≃ₜ _root_.Metric.closedBall (0 : E) 1) :
    IsCompact C := by
  have hB : CompactSpace (_root_.Metric.closedBall (0 : E) 1) :=
    isCompact_iff_compactSpace.mp (_root_.ProperSpace.isCompact_closedBall 0 1)
  have _ : CompactSpace C := φ.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isCompact_of_homeomorphClosedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isCompact_of_homeomorphClosedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isCompact_of_homeomorphClosedBall ``Submission.DifferentialGeometry.Topology.isCompact_of_homeomorphClosedBall

theorem interior_eq_image_of_homeomorphClosedBall {C : Set E}
    (φ : C ≃ₜ _root_.Metric.closedBall (0 : E) 1) :
    interior C =
      closedBallParam φ '' ((Subtype.val : _root_.Metric.closedBall (0 : E) 1 → E) ⁻¹' _root_.Metric.ball 0 1) := by
  have h := interior_range_eq_image_preimage_interior (_root_.ProperSpace.isCompact_closedBall (0 : E) 1)
    (closedBallParam φ) (continuous_closedBallParam φ) (injective_closedBallParam φ)
  rw [range_closedBallParam φ, interior_closedBall (0 : E) one_ne_zero] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.interior_eq_image_of_homeomorphClosedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.interior_eq_image_of_homeomorphClosedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.interior_eq_image_of_homeomorphClosedBall ``Submission.DifferentialGeometry.Topology.interior_eq_image_of_homeomorphClosedBall

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem univ_sdiff_preimage_ball :
    (_root_.Set.univ : Set (_root_.Metric.closedBall (0 : E) 1)) \
        ((Subtype.val : _root_.Metric.closedBall (0 : E) 1 → E) ⁻¹' _root_.Metric.ball 0 1) =
      (Subtype.val : _root_.Metric.closedBall (0 : E) 1 → E) ⁻¹' _root_.Metric.sphere 0 1 := by
  ext b
  have hb : _root_.Dist.dist (b : E) 0 ≤ 1 := by simpa only [_root_.Metric.mem_closedBall] using b.2
  simp only [Set.mem_sdiff, _root_.Set.mem_univ, true_and, _root_.Set.mem_preimage, _root_.Metric.mem_ball, _root_.Metric.mem_sphere, not_lt]
  constructor
  · intro h
    exact le_antisymm hb h
  · intro h
    exact h.ge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.univ_sdiff_preimage_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.univ_sdiff_preimage_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.univ_sdiff_preimage_ball ``Submission.DifferentialGeometry.Topology.univ_sdiff_preimage_ball

theorem frontier_eq_image_sphere_of_homeomorphClosedBall {C : Set E}
    (φ : C ≃ₜ _root_.Metric.closedBall (0 : E) 1) :
    frontier C =
      closedBallParam φ '' ((Subtype.val : _root_.Metric.closedBall (0 : E) 1 → E) ⁻¹' _root_.Metric.sphere 0 1) := by
  have hC : IsCompact C := isCompact_of_homeomorphClosedBall φ
  rw [hC.isClosed.frontier_eq, interior_eq_image_of_homeomorphClosedBall φ,
    ← univ_sdiff_preimage_ball (E := E),
    Set.image_sdiff (injective_closedBallParam φ), _root_.Set.image_univ, range_closedBallParam φ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.frontier_eq_image_sphere_of_homeomorphClosedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.frontier_eq_image_sphere_of_homeomorphClosedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.frontier_eq_image_sphere_of_homeomorphClosedBall ``Submission.DifferentialGeometry.Topology.frontier_eq_image_sphere_of_homeomorphClosedBall

theorem isConnected_frontier_of_homeomorphClosedBall (hrank : 1 < Module.rank ℝ E)
    {C : Set E} (φ : C ≃ₜ _root_.Metric.closedBall (0 : E) 1) : IsConnected (frontier C) := by
  have hsp : IsConnected (_root_.Metric.sphere (0 : E) 1) := isConnected_sphere hrank 0 zero_le_one
  have _ : ConnectedSpace (_root_.Metric.sphere (0 : E) 1) := isConnected_iff_connectedSpace.mp hsp
  have hcont : Continuous
      (fun s : _root_.Metric.sphere (0 : E) 1 =>
        closedBallParam φ ⟨s.1, _root_.Metric.sphere_subset_closedBall s.2⟩) :=
    (continuous_closedBallParam φ).comp (continuous_subtype_val.subtype_mk _)
  have himg :
      closedBallParam φ '' ((Subtype.val : _root_.Metric.closedBall (0 : E) 1 → E) ⁻¹' _root_.Metric.sphere 0 1) =
        _root_.Set.range (fun s : _root_.Metric.sphere (0 : E) 1 =>
          closedBallParam φ ⟨s.1, _root_.Metric.sphere_subset_closedBall s.2⟩) := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b.1, hb⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨⟨s.1, _root_.Metric.sphere_subset_closedBall s.2⟩, s.2, rfl⟩
  rw [frontier_eq_image_sphere_of_homeomorphClosedBall φ, himg]
  exact isConnected_range hcont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isConnected_frontier_of_homeomorphClosedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isConnected_frontier_of_homeomorphClosedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isConnected_frontier_of_homeomorphClosedBall ``Submission.DifferentialGeometry.Topology.isConnected_frontier_of_homeomorphClosedBall

theorem interior_nonempty_of_homeomorphClosedBall {C : Set E}
    (φ : C ≃ₜ _root_.Metric.closedBall (0 : E) 1) : (interior C).Nonempty := by
  rw [interior_eq_image_of_homeomorphClosedBall φ]
  exact ⟨closedBallParam φ ⟨0, by simp⟩, ⟨0, by simp⟩, by simp, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.interior_nonempty_of_homeomorphClosedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.interior_nonempty_of_homeomorphClosedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.interior_nonempty_of_homeomorphClosedBall ``Submission.DifferentialGeometry.Topology.interior_nonempty_of_homeomorphClosedBall

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem compl_nonempty_of_isCompact [NoncompactSpace E] {C : Set E} (hC : IsCompact C) :
    Cᶜ.Nonempty := by
  refine Set.nonempty_compl.mpr ?_
  intro hCuniv
  rw [hCuniv] at hC
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace E))
    (isCompact_univ_iff.mp hC)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.compl_nonempty_of_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.compl_nonempty_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.compl_nonempty_of_isCompact ``Submission.DifferentialGeometry.Topology.compl_nonempty_of_isCompact

theorem isCompact_frontier_of_homeomorphClosedBall {C : Set E}
    (φ : C ≃ₜ _root_.Metric.closedBall (0 : E) 1) : IsCompact (frontier C) :=
  (isCompact_of_homeomorphClosedBall φ).of_isClosed_subset isClosed_frontier
    (isCompact_of_homeomorphClosedBall φ).isClosed.frontier_subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isCompact_frontier_of_homeomorphClosedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isCompact_frontier_of_homeomorphClosedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isCompact_frontier_of_homeomorphClosedBall ``Submission.DifferentialGeometry.Topology.isCompact_frontier_of_homeomorphClosedBall

theorem isConnected_compl_of_homeomorphClosedBall_of_isBicollared [NoncompactSpace E]
    (hrank : 1 < Module.rank ℝ E) {C : Set E} (φ : C ≃ₜ _root_.Metric.closedBall (0 : E) 1)
    (hbi : IsBicollared (frontier C)) : IsConnected Cᶜ :=
  isConnected_compl_of_isBicollared_frontier
    (isCompact_of_homeomorphClosedBall φ).isClosed
    (isCompact_frontier_of_homeomorphClosedBall φ)
    (isConnected_frontier_of_homeomorphClosedBall hrank φ)
    (interior_nonempty_of_homeomorphClosedBall φ)
    (compl_nonempty_of_isCompact (isCompact_of_homeomorphClosedBall φ)) hbi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isConnected_compl_of_homeomorphClosedBall_of_isBicollared then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isConnected_compl_of_homeomorphClosedBall_of_isBicollared"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isConnected_compl_of_homeomorphClosedBall_of_isBicollared ``Submission.DifferentialGeometry.Topology.isConnected_compl_of_homeomorphClosedBall_of_isBicollared

end DifferentialGeometry.Topology
