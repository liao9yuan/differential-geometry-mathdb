/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CircleAnnulusOrientation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Product

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology
open scoped _root_.ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem stdTriangleLoop_endpoints : stdTriangleLoop 0 = stdTriangleLoop 1 := by
  norm_num [stdTriangleLoop]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.stdTriangleLoop_endpoints
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.stdTriangleLoop_endpoints target :: scope.openDecls } }

private noncomputable def triangleCircleMap : loopCircle → (Fin 3 → ℝ) :=
  AddCircle.liftIco (1 : ℝ) 0 stdTriangleLoop

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangleCircleMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.triangleCircleMap target :: scope.openDecls } }

private theorem triangleCircleMap_coe {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) :
    triangleCircleMap (t : loopCircle) = stdTriangleLoop t := by
  by_cases ht1 : t = 1
  · subst t
    rw [show ((1 : ℝ) : loopCircle) = ((0 : ℝ) : loopCircle) by
      rw [AddCircle.coe_period, AddCircle.coe_zero]]
    exact (AddCircle.liftIco_coe_apply (by norm_num : (0 : ℝ) ∈ Ico 0 (0 + 1))).trans
      stdTriangleLoop_endpoints
  · exact AddCircle.liftIco_coe_apply ⟨ht.1, by simpa using lt_of_le_of_ne ht.2 ht1⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangleCircleMap_coe
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.triangleCircleMap_coe target :: scope.openDecls } }

private theorem triangleCircleMap_continuous : Continuous triangleCircleMap :=
  AddCircle.liftIco_continuous (by simpa using stdTriangleLoop_endpoints)
    (by simpa using continuous_stdTriangleLoop.continuousOn)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangleCircleMap_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.triangleCircleMap_continuous target :: scope.openDecls } }

private theorem triangleCircleMap_mem (x : loopCircle) :
    triangleCircleMap x ∈ stdSimplexBoundary 2 := by
  have hx := (AddCircle.equivIco (1 : ℝ) 0 x).2
  apply stdTriangleLoop_image.subset
  exact ⟨_, ⟨hx.1, by simpa using hx.2.le⟩, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangleCircleMap_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.triangleCircleMap_mem target :: scope.openDecls } }

private theorem triangleCircleMap_bijective :
    Function.Bijective (fun x : loopCircle =>
      (⟨triangleCircleMap x, triangleCircleMap_mem x⟩ : stdSimplexBoundary 2)) := by
  refine ⟨?_, ?_⟩
  · intro x y h
    apply (AddCircle.equivIco (1 : ℝ) 0).injective
    apply Subtype.ext
    exact injOn_stdTriangleLoop
      (by simpa using (AddCircle.equivIco (1 : ℝ) 0 x).2)
      (by simpa using (AddCircle.equivIco (1 : ℝ) 0 y).2) (congrArg Subtype.val h)
  · intro x
    obtain ⟨t, ht, htx⟩ := stdTriangleLoop_image.symm.subset x.2
    exact ⟨(t : loopCircle), Subtype.ext ((triangleCircleMap_coe ht).trans htx)⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangleCircleMap_bijective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.triangleCircleMap_bijective target :: scope.openDecls } }

noncomputable def stdTriangleCircleHomeomorph : loopCircle ≃ₜ stdSimplexBoundary 2 :=
  (triangleCircleMap_continuous.subtype_mk triangleCircleMap_mem).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ triangleCircleMap_bijective)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.stdTriangleCircleHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.stdTriangleCircleHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.stdTriangleCircleHomeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.stdTriangleCircleHomeomorph

theorem stdTriangleCircleHomeomorph_coe {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) :
    (stdTriangleCircleHomeomorph (t : loopCircle) : Fin 3 → ℝ) = stdTriangleLoop t :=
  triangleCircleMap_coe ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.stdTriangleCircleHomeomorph_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.stdTriangleCircleHomeomorph_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.stdTriangleCircleHomeomorph_coe ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.stdTriangleCircleHomeomorph_coe

private theorem triangleCircleMap_shift (k : ℤ) {t : ℝ}
    (ht : t ∈ _root_.Set.Icc (k : ℝ) ((k : ℝ) + 1)) :
    triangleCircleMap (t : loopCircle) = stdTriangleLoop (t - k) := by
  have hk : ((k : ℝ) : loopCircle) = 0 := by
    have h := @AddCircle.coe_zsmul ℝ _ (1 : ℝ) k 1
    simpa only [zsmul_eq_mul, mul_one, AddCircle.coe_period, smul_zero] using h
  have ht' : t - k ∈ _root_.Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have heq : ((t - k : ℝ) : loopCircle) = (t : loopCircle) := by
    rw [AddCircle.coe_sub, hk, sub_zero]
  rw [← heq]
  exact triangleCircleMap_coe ht'

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangleCircleMap_shift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.triangleCircleMap_shift target :: scope.openDecls } }

private theorem triangleCircleMap_piecewiseAffine_interval (k : ℤ) :
    IsPiecewiseAffineOn (fun t : ℝ => triangleCircleMap (t : loopCircle))
      (_root_.Set.Icc (k : ℝ) ((k : ℝ) + 1)) := by
  let A : ℝ →ᵃ[ℝ] ℝ := AffineMap.lineMap (-(k : ℝ)) (1 - k)
  have hA (t : ℝ) : A t = t - k := by
    dsimp [A]
    rw [AffineMap.lineMap_apply_module]
    simp only [smul_eq_mul]
    ring
  have ha : IsPiecewiseAffineOn A (_root_.Set.Icc (k : ℝ) ((k : ℝ) + 1)) :=
    isPiecewiseAffineOn_of_affine_of_isHPolytope A isHPolytope_Icc
  have hcomp := isPiecewiseAffineOn_stdTriangleLoop.comp ha
  have hmaps : _root_.Set.Icc (k : ℝ) ((k : ℝ) + 1) ⊆ A ⁻¹' _root_.Set.Icc (0 : ℝ) 1 := by
    intro t ht
    change A t ∈ _root_.Set.Icc (0 : ℝ) 1
    rw [hA]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [inter_eq_left.mpr hmaps] at hcomp
  exact hcomp.congr fun t ht => by
    rw [triangleCircleMap_shift k ht]
    exact congrArg stdTriangleLoop (hA t).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangleCircleMap_piecewiseAffine_interval
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.triangleCircleMap_piecewiseAffine_interval target :: scope.openDecls } }

theorem isPiecewiseAffineOn_stdTriangleCircleCover :
    IsPiecewiseAffineOn (fun t : ℝ =>
      (stdTriangleCircleHomeomorph (t : loopCircle) : Fin 3 → ℝ)) univ := by
  intro x hx
  let k : ℤ := ⌊x⌋
  have hleft := triangleCircleMap_piecewiseAffine_interval (k - 1)
  have hright := triangleCircleMap_piecewiseAffine_interval k
  have hcast : ((k - 1 : ℤ) : ℝ) = (k : ℝ) - 1 := by norm_cast
  rw [hcast, sub_add_cancel] at hleft
  have h := hleft.union_of_isClosed hright isClosed_Icc isClosed_Icc
  rw [_root_.Set.Icc_union_Icc_eq_Icc (by linarith) (by linarith)] at h
  have hk₀ : (k : ℝ) ≤ x := Int.floor_le x
  have hk₁ : x < (k : ℝ) + 1 := Int.lt_floor_add_one x
  have hmem : _root_.Set.Icc ((k : ℝ) - 1) ((k : ℝ) + 1) ∈ nhds x :=
    Icc_mem_nhds (by linarith) hk₁
  have hh := h x ⟨by linarith, hk₁.le⟩
  exact (show IsPiecewiseAffineWithinAt
    (fun t : ℝ => triangleCircleMap (t : loopCircle))
    (_root_.Set.univ ∩ _root_.Set.Icc ((k : ℝ) - 1) ((k : ℝ) + 1)) x by simpa using hh).of_inter_of_mem_nhds hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_stdTriangleCircleCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_stdTriangleCircleCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_stdTriangleCircleCover ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_stdTriangleCircleCover

end DifferentialGeometry.Topology.PiecewiseLinear
