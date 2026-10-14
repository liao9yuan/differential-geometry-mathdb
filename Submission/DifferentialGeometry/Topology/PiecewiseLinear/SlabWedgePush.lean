/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable section

def slabWedgeCore (c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  _root_.Min.min p.1 (c - p.1) - |p.2.1| - |p.2.2|

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeCore ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeCore

def slabWedgeHat (c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  _root_.Max.max 0 (slabWedgeCore c p) / 4

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat

def slabWedgeSupport (c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  _root_.Set.Icc 0 c ×ˢ (_root_.Set.Icc (-c) c ×ˢ _root_.Set.Icc (-c) c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeSupport ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeSupport

def wedgeSlab (c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ c}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.wedgeSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.wedgeSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.wedgeSlab ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.wedgeSlab

def wedgeSlabInterior (c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 < c}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.wedgeSlabInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.wedgeSlabInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.wedgeSlabInterior ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.wedgeSlabInterior

def wedgeSlabBoundary (c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 = 0 ∨ p.1 = c}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.wedgeSlabBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.wedgeSlabBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.wedgeSlabBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.wedgeSlabBoundary

def positiveSlabFold (c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p ∈ wedgeSlab c ∧
    ((p.2.2 = 0 ∧ 0 ≤ p.2.1) ∨ (p.2.1 = 0 ∧ 0 ≤ p.2.2))}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.positiveSlabFold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.positiveSlabFold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.positiveSlabFold ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.positiveSlabFold

def negativeSlabFold (c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p ∈ wedgeSlab c ∧
    ((p.2.2 = 0 ∧ p.2.1 ≤ 0) ∨ (p.2.1 = 0 ∧ p.2.2 ≤ 0))}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.negativeSlabFold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.negativeSlabFold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.negativeSlabFold ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.negativeSlabFold

def positiveWedgeDisplacement (c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (0, slabWedgeHat c p, slabWedgeHat c p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgeDisplacement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgeDisplacement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgeDisplacement ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgeDisplacement

def negativeWedgeDisplacement (c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (0, -slabWedgeHat c p, -slabWedgeHat c p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgeDisplacement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgeDisplacement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgeDisplacement ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgeDisplacement

def positiveWedgePush (c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  p + positiveWedgeDisplacement c p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgePush then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgePush"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgePush ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgePush

def negativeWedgePush (c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  p + negativeWedgeDisplacement c p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgePush then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgePush"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgePush ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgePush

theorem slabWedgeHat_nonneg (c : ℝ) (p : ℝ × ℝ × ℝ) : 0 ≤ slabWedgeHat c p := by
  rw [slabWedgeHat]
  exact div_nonneg (le_max_left _ _) (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_nonneg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_nonneg

theorem slabWedgeHat_eq_zero_of_left_face {c : ℝ} {p : ℝ × ℝ × ℝ} (hp : p.1 = 0) :
    slabWedgeHat c p = 0 := by
  have hcore : slabWedgeCore c p ≤ 0 := by
    rw [slabWedgeCore, hp]
    simp only [sub_zero]
    calc
      min 0 c - |p.2.1| - |p.2.2| ≤ _root_.Min.min 0 c := by
        nlinarith [abs_nonneg p.2.1, abs_nonneg p.2.2]
      _ ≤ 0 := min_le_left _ _
  rw [slabWedgeHat, max_eq_left hcore, zero_div]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_eq_zero_of_left_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_eq_zero_of_left_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_eq_zero_of_left_face ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_eq_zero_of_left_face

theorem slabWedgeHat_eq_zero_of_right_face {c : ℝ} {p : ℝ × ℝ × ℝ} (hp : p.1 = c) :
    slabWedgeHat c p = 0 := by
  have hcore : slabWedgeCore c p ≤ 0 := by
    rw [slabWedgeCore, hp]
    simp only [sub_self]
    calc
      min c 0 - |p.2.1| - |p.2.2| ≤ _root_.Min.min c 0 := by
        nlinarith [abs_nonneg p.2.1, abs_nonneg p.2.2]
      _ ≤ 0 := min_le_right _ _
  rw [slabWedgeHat, max_eq_left hcore, zero_div]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_eq_zero_of_right_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_eq_zero_of_right_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_eq_zero_of_right_face ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_eq_zero_of_right_face

theorem slabWedgeHat_axis (c x : ℝ) (hx : x ∈ _root_.Set.Icc (0 : ℝ) c) :
    slabWedgeHat c (x, 0, 0) = _root_.Min.min x (c - x) / 4 := by
  rw [slabWedgeHat, slabWedgeCore]
  simp only [abs_zero, sub_zero]
  rw [max_eq_right]
  exact le_min hx.1 (sub_nonneg.mpr hx.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_axis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_axis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_axis ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_axis

theorem slabWedgeHat_axis_eq_zero_iff {c x : ℝ} (hx : x ∈ _root_.Set.Icc (0 : ℝ) c) :
    slabWedgeHat c (x, 0, 0) = 0 ↔ x = 0 ∨ x = c := by
  rw [slabWedgeHat_axis c x hx]
  have hc : 0 ≤ c := hx.1.trans hx.2
  constructor
  · intro h
    have hmin : _root_.Min.min x (c - x) = 0 := by linarith
    rcases le_total x (c - x) with hle | hle
    · exact Or.inl (by rwa [min_eq_left hle] at hmin)
    · right
      have : c - x = 0 := by rwa [min_eq_right hle] at hmin
      linarith
  · rintro (rfl | rfl)
    · simp [hc]
    · simp [hc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_axis_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_axis_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_axis_eq_zero_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_axis_eq_zero_iff

theorem slabWedgeHat_pos_on_axis {c x : ℝ} (hx0 : 0 < x) (hxc : x < c) :
    0 < slabWedgeHat c (x, 0, 0) := by
  rw [slabWedgeHat_axis c x ⟨hx0.le, hxc.le⟩]
  exact div_pos (lt_min hx0 (sub_pos.mpr hxc)) (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_pos_on_axis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_pos_on_axis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_pos_on_axis ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_pos_on_axis

theorem isCompact_slabWedgeSupport (c : ℝ) : IsCompact (slabWedgeSupport c) :=
  isCompact_Icc.prod (isCompact_Icc.prod _root_.CompactIccSpace.isCompact_Icc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isCompact_slabWedgeSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isCompact_slabWedgeSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isCompact_slabWedgeSupport ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isCompact_slabWedgeSupport

theorem slabWedgeHat_eq_zero_of_notMem_support {c : ℝ} {p : ℝ × ℝ × ℝ}
    (hp : p ∉ slabWedgeSupport c) : slabWedgeHat c p = 0 := by
  have hcore : slabWedgeCore c p ≤ 0 := by
    by_contra h
    have hpos : 0 < slabWedgeCore c p := lt_of_not_ge h
    have hx0 : 0 ≤ p.1 := by
      by_contra hx
      have hmin := min_le_left p.1 (c - p.1)
      rw [slabWedgeCore] at hpos
      nlinarith [abs_nonneg p.2.1, abs_nonneg p.2.2]
    have hxc : p.1 ≤ c := by
      by_contra hx
      have hmin := min_le_right p.1 (c - p.1)
      rw [slabWedgeCore] at hpos
      nlinarith [abs_nonneg p.2.1, abs_nonneg p.2.2]
    have hy : |p.2.1| ≤ c := by
      have hmin := min_le_left p.1 (c - p.1)
      rw [slabWedgeCore] at hpos
      nlinarith [abs_nonneg p.2.2]
    have hz : |p.2.2| ≤ c := by
      have hmin := min_le_left p.1 (c - p.1)
      rw [slabWedgeCore] at hpos
      nlinarith [abs_nonneg p.2.1]
    exact hp ⟨⟨hx0, hxc⟩, abs_le.mp hy, abs_le.mp hz⟩
  rw [slabWedgeHat, max_eq_left hcore, zero_div]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_eq_zero_of_notMem_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_eq_zero_of_notMem_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_eq_zero_of_notMem_support ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_eq_zero_of_notMem_support

theorem slabWedgeHat_eqOn_zero_compl_support (c : ℝ) :
    EqOn (slabWedgeHat c) (fun _ => 0) (slabWedgeSupport c)ᶜ :=
  fun _ hp => slabWedgeHat_eq_zero_of_notMem_support hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_eqOn_zero_compl_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_eqOn_zero_compl_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_eqOn_zero_compl_support ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeHat_eqOn_zero_compl_support

theorem support_slabWedgeHat_subset (c : ℝ) :
    Function.support (slabWedgeHat c) ⊆ slabWedgeSupport c := by
  intro p hp
  by_contra hmem
  exact hp (slabWedgeHat_eq_zero_of_notMem_support hmem)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.support_slabWedgeHat_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.support_slabWedgeHat_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.support_slabWedgeHat_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.support_slabWedgeHat_subset

theorem hasCompactSupport_slabWedgeHat (c : ℝ) : HasCompactSupport (slabWedgeHat c) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_slabWedgeSupport c)
    (support_slabWedgeHat_subset c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.hasCompactSupport_slabWedgeHat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.hasCompactSupport_slabWedgeHat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.hasCompactSupport_slabWedgeHat ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.hasCompactSupport_slabWedgeHat

private noncomputable def quarterAffineMap : ℝ →ᵃ[ℝ] ℝ :=
  ((4 : ℝ)⁻¹ • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).toAffineMap

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.quarterAffineMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.quarterAffineMap target :: scope.openDecls } }

private theorem quarterAffineMap_apply (x : ℝ) : quarterAffineMap x = x / 4 := by
  change (4 : ℝ)⁻¹ • x = x / 4
  simp only [smul_eq_mul]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.quarterAffineMap_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.quarterAffineMap_apply target :: scope.openDecls } }

theorem isPiecewiseAffineOn_slabWedgeCore (c : ℝ) :
    IsPiecewiseAffineOn (slabWedgeCore c) univ := by
  have hid : IsPiecewiseAffineOn (id : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ) univ :=
    isPiecewiseAffineOn_id isOpen_univ
  have hx : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.1) univ :=
    hid.affine_comp (LinearMap.fst ℝ ℝ (ℝ × ℝ)).toAffineMap
  have hy : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.2.1) univ :=
    hid.affine_comp ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).toAffineMap
  have hz : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.2.2) univ :=
    hid.affine_comp ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).toAffineMap
  have hconst : ∀ r : ℝ, IsPiecewiseAffineOn (fun _ : ℝ × ℝ × ℝ => r) univ := fun r =>
    hid.affine_comp (AffineMap.const ℝ (ℝ × ℝ × ℝ) r)
  have hcx : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => c - p.1) univ := by
    have h := (hconst c).add (hx.affine_comp (-AffineMap.id ℝ ℝ))
    refine h.congr fun p _ => ?_
    change c - p.1 = c + -p.1
    rw [sub_eq_add_neg]
  have hcore := ((hx.min hcx).add (hy.abs.affine_comp (-AffineMap.id ℝ ℝ))).add
    (hz.abs.affine_comp (-AffineMap.id ℝ ℝ))
  refine hcore.congr fun p _ => ?_
  change slabWedgeCore c p = _root_.Min.min p.1 (c - p.1) + -|p.2.1| + -|p.2.2|
  simp only [slabWedgeCore, sub_eq_add_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_slabWedgeCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_slabWedgeCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_slabWedgeCore ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_slabWedgeCore

theorem isPiecewiseAffineOn_slabWedgeHat (c : ℝ) :
    IsPiecewiseAffineOn (slabWedgeHat c) univ := by
  have hconst : IsPiecewiseAffineOn (fun _ : ℝ × ℝ × ℝ => (0 : ℝ)) univ :=
    isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ × ℝ) 0) isOpen_univ
  have h := (hconst.max (isPiecewiseAffineOn_slabWedgeCore c)).affine_comp quarterAffineMap
  refine h.congr fun p _ => ?_
  change slabWedgeHat c p = quarterAffineMap (_root_.Max.max 0 (slabWedgeCore c p))
  rw [quarterAffineMap_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_slabWedgeHat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_slabWedgeHat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_slabWedgeHat ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_slabWedgeHat

theorem lipschitzWith_slabWedgeCore (c : ℝ) : LipschitzWith 3 (slabWedgeCore c) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hx : |p.1 - q.1| ≤ _root_.Dist.dist p q := by
    simp only [Prod.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have hy : |p.2.1 - q.2.1| ≤ _root_.Dist.dist p q := by
    simp only [Prod.dist_eq, Real.dist_eq]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hz : |p.2.2 - q.2.2| ≤ _root_.Dist.dist p q := by
    simp only [Prod.dist_eq, Real.dist_eq]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hmin : |_root_.Min.min p.1 (c - p.1) - _root_.Min.min q.1 (c - q.1)| ≤ _root_.Dist.dist p q := by
    calc
      |min p.1 (c - p.1) - _root_.Min.min q.1 (c - q.1)| ≤
          max |p.1 - q.1| |(c - p.1) - (c - q.1)| := abs_min_sub_min_le_max _ _ _ _
      _ = |p.1 - q.1| := by
        rw [show (c - p.1) - (c - q.1) = -(p.1 - q.1) by ring, abs_neg, max_self]
      _ ≤ _root_.Dist.dist p q := hx
  have habsy : abs (|p.2.1| - |q.2.1|) ≤ _root_.Dist.dist p q :=
    (abs_abs_sub_abs_le_abs_sub _ _).trans hy
  have habsz : abs (|p.2.2| - |q.2.2|) ≤ _root_.Dist.dist p q :=
    (abs_abs_sub_abs_le_abs_sub _ _).trans hz
  rw [Real.dist_eq]
  change |slabWedgeCore c p - slabWedgeCore c q| ≤ (3 : ℝ) * _root_.Dist.dist p q
  calc
    |slabWedgeCore c p - slabWedgeCore c q| ≤
        |min p.1 (c - p.1) - _root_.Min.min q.1 (c - q.1)| +
          abs (|p.2.1| - |q.2.1|) + abs (|p.2.2| - |q.2.2|) := by
      rw [slabWedgeCore, slabWedgeCore]
      have h₁ := abs_sub (_root_.Min.min p.1 (c - p.1) - _root_.Min.min q.1 (c - q.1))
        ((|p.2.1| - |q.2.1|) + (|p.2.2| - |q.2.2|))
      have h₂ := abs_add_le (|p.2.1| - |q.2.1|) (|p.2.2| - |q.2.2|)
      rw [show _root_.Min.min p.1 (c - p.1) - |p.2.1| - |p.2.2| -
          (_root_.Min.min q.1 (c - q.1) - |q.2.1| - |q.2.2|) =
            (_root_.Min.min p.1 (c - p.1) - _root_.Min.min q.1 (c - q.1)) -
              ((|p.2.1| - |q.2.1|) + (|p.2.2| - |q.2.2|)) by ring]
      linarith
    _ ≤ _root_.Dist.dist p q + _root_.Dist.dist p q + _root_.Dist.dist p q := by linarith
    _ = (3 : ℝ) * _root_.Dist.dist p q := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.lipschitzWith_slabWedgeCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.lipschitzWith_slabWedgeCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.lipschitzWith_slabWedgeCore ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.lipschitzWith_slabWedgeCore

theorem lipschitzWith_slabWedgeHat (c : ℝ) : LipschitzWith (3 / 4) (slabWedgeHat c) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hcore := (lipschitzWith_slabWedgeCore c).dist_le_mul p q
  have hmax : |_root_.Max.max 0 (slabWedgeCore c p) - _root_.Max.max 0 (slabWedgeCore c q)| ≤
      |slabWedgeCore c p - slabWedgeCore c q| := by
    calc
      |max 0 (slabWedgeCore c p) - _root_.Max.max 0 (slabWedgeCore c q)| ≤
          max |(0 : ℝ) - 0| |slabWedgeCore c p - slabWedgeCore c q| :=
        abs_max_sub_max_le_max _ _ _ _
      _ = |slabWedgeCore c p - slabWedgeCore c q| := by simp
  rw [Real.dist_eq]
  change |slabWedgeHat c p - slabWedgeHat c q| ≤ ((3 / 4 : NNReal) : ℝ) * _root_.Dist.dist p q
  rw [show slabWedgeHat c p - slabWedgeHat c q =
      (_root_.Max.max 0 (slabWedgeCore c p) - _root_.Max.max 0 (slabWedgeCore c q)) / 4 by
        rw [slabWedgeHat, slabWedgeHat]; ring, abs_div]
  rw [Real.dist_eq] at hcore
  norm_num at hcore ⊢
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.lipschitzWith_slabWedgeHat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.lipschitzWith_slabWedgeHat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.lipschitzWith_slabWedgeHat ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.lipschitzWith_slabWedgeHat

theorem isPiecewiseAffineOn_positiveWedgeDisplacement (c : ℝ) :
    IsPiecewiseAffineOn (positiveWedgeDisplacement c) univ := by
  have hzero : IsPiecewiseAffineOn (fun _ : ℝ × ℝ × ℝ => (0 : ℝ)) univ :=
    isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ × ℝ) 0) isOpen_univ
  exact (hzero.prod_mk ((isPiecewiseAffineOn_slabWedgeHat c).prod_mk
    (isPiecewiseAffineOn_slabWedgeHat c))).congr fun _ _ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_positiveWedgeDisplacement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_positiveWedgeDisplacement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_positiveWedgeDisplacement ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_positiveWedgeDisplacement

theorem isPiecewiseAffineOn_negativeWedgeDisplacement (c : ℝ) :
    IsPiecewiseAffineOn (negativeWedgeDisplacement c) univ := by
  have hhat := (isPiecewiseAffineOn_slabWedgeHat c).affine_comp (-AffineMap.id ℝ ℝ)
  have hzero : IsPiecewiseAffineOn (fun _ : ℝ × ℝ × ℝ => (0 : ℝ)) univ :=
    isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ × ℝ) 0) isOpen_univ
  exact (hzero.prod_mk (hhat.prod_mk hhat)).congr fun _ _ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_negativeWedgeDisplacement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_negativeWedgeDisplacement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_negativeWedgeDisplacement ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_negativeWedgeDisplacement

theorem lipschitzWith_positiveWedgeDisplacement (c : ℝ) :
    LipschitzWith (3 / 4) (positiveWedgeDisplacement c) := by
  change LipschitzWith (3 / 4) (fun p : ℝ × ℝ × ℝ =>
    (0, slabWedgeHat c p, slabWedgeHat c p))
  have hzero : LipschitzWith 0 (fun _ : ℝ × ℝ × ℝ => (0 : ℝ)) := LipschitzWith.const 0
  simpa only [max_self,
    max_eq_right (show (0 : NNReal) ≤ 3 / 4 by positivity)] using
    hzero.prodMk ((lipschitzWith_slabWedgeHat c).prodMk (lipschitzWith_slabWedgeHat c))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.lipschitzWith_positiveWedgeDisplacement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.lipschitzWith_positiveWedgeDisplacement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.lipschitzWith_positiveWedgeDisplacement ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.lipschitzWith_positiveWedgeDisplacement

theorem lipschitzWith_negativeWedgeDisplacement (c : ℝ) :
    LipschitzWith (3 / 4) (negativeWedgeDisplacement c) := by
  change LipschitzWith (3 / 4) (fun p : ℝ × ℝ × ℝ =>
    (0, -slabWedgeHat c p, -slabWedgeHat c p))
  have hneg : LipschitzWith (3 / 4) (fun p => -slabWedgeHat c p) :=
    (lipschitzWith_slabWedgeHat c).neg
  have hzero : LipschitzWith 0 (fun _ : ℝ × ℝ × ℝ => (0 : ℝ)) := LipschitzWith.const 0
  simpa only [negativeWedgeDisplacement, max_self,
    max_eq_right (show (0 : NNReal) ≤ 3 / 4 by positivity)] using hzero.prodMk (hneg.prodMk hneg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.lipschitzWith_negativeWedgeDisplacement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.lipschitzWith_negativeWedgeDisplacement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.lipschitzWith_negativeWedgeDisplacement ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.lipschitzWith_negativeWedgeDisplacement

theorem isPLHomeomorphOn_positiveWedgePush (c : ℝ) :
    IsPLHomeomorphOn (positiveWedgePush c) _root_.Set.univ univ := by
  change IsPLHomeomorphOn (fun p => p + positiveWedgeDisplacement c p) _root_.Set.univ _root_.Set.univ
  exact isPLHomeomorphOn_id_add_of_lipschitz
    (isPiecewiseAffineOn_positiveWedgeDisplacement c)
    (lipschitzWith_positiveWedgeDisplacement c) (by norm_num : (3 / 4 : NNReal) < 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_positiveWedgePush then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_positiveWedgePush"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_positiveWedgePush ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_positiveWedgePush

theorem isPLHomeomorphOn_negativeWedgePush (c : ℝ) :
    IsPLHomeomorphOn (negativeWedgePush c) _root_.Set.univ univ := by
  change IsPLHomeomorphOn (fun p => p + negativeWedgeDisplacement c p) _root_.Set.univ _root_.Set.univ
  exact isPLHomeomorphOn_id_add_of_lipschitz
    (isPiecewiseAffineOn_negativeWedgeDisplacement c)
    (lipschitzWith_negativeWedgeDisplacement c) (by norm_num : (3 / 4 : NNReal) < 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_negativeWedgePush then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_negativeWedgePush"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_negativeWedgePush ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_negativeWedgePush

noncomputable def positiveWedgePushHomeomorph (c : ℝ) :
    (ℝ × ℝ × ℝ) ≃ₜ (ℝ × ℝ × ℝ) :=
  (Homeomorph.Set.univ _).symm.trans
    ((isPLHomeomorphOn_positiveWedgePush c).homeomorph.trans (Homeomorph.Set.univ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgePushHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgePushHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgePushHomeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgePushHomeomorph

noncomputable def negativeWedgePushHomeomorph (c : ℝ) :
    (ℝ × ℝ × ℝ) ≃ₜ (ℝ × ℝ × ℝ) :=
  (Homeomorph.Set.univ _).symm.trans
    ((isPLHomeomorphOn_negativeWedgePush c).homeomorph.trans (Homeomorph.Set.univ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgePushHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgePushHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgePushHomeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgePushHomeomorph

@[simp]
theorem positiveWedgePushHomeomorph_apply (c : ℝ) (p : ℝ × ℝ × ℝ) :
    positiveWedgePushHomeomorph c p = positiveWedgePush c p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgePushHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgePushHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgePushHomeomorph_apply ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgePushHomeomorph_apply

@[simp]
theorem negativeWedgePushHomeomorph_apply (c : ℝ) (p : ℝ × ℝ × ℝ) :
    negativeWedgePushHomeomorph c p = negativeWedgePush c p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgePushHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgePushHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgePushHomeomorph_apply ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgePushHomeomorph_apply

theorem eqOn_positiveWedgePush_id_compl_support (c : ℝ) :
    EqOn (positiveWedgePush c) id (slabWedgeSupport c)ᶜ := by
  intro p hp
  rw [positiveWedgePush, positiveWedgeDisplacement,
    slabWedgeHat_eq_zero_of_notMem_support hp]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eqOn_positiveWedgePush_id_compl_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eqOn_positiveWedgePush_id_compl_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eqOn_positiveWedgePush_id_compl_support ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eqOn_positiveWedgePush_id_compl_support

theorem eqOn_negativeWedgePush_id_compl_support (c : ℝ) :
    EqOn (negativeWedgePush c) id (slabWedgeSupport c)ᶜ := by
  intro p hp
  rw [negativeWedgePush, negativeWedgeDisplacement,
    slabWedgeHat_eq_zero_of_notMem_support hp]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eqOn_negativeWedgePush_id_compl_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eqOn_negativeWedgePush_id_compl_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eqOn_negativeWedgePush_id_compl_support ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eqOn_negativeWedgePush_id_compl_support

theorem eqOn_positiveWedgePush_id_slabBoundary (c : ℝ) :
    EqOn (positiveWedgePush c) id (wedgeSlabBoundary c) := by
  intro p hp
  rcases hp with hp | hp
  · rw [positiveWedgePush, positiveWedgeDisplacement, slabWedgeHat_eq_zero_of_left_face hp]
    simp
  · rw [positiveWedgePush, positiveWedgeDisplacement, slabWedgeHat_eq_zero_of_right_face hp]
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eqOn_positiveWedgePush_id_slabBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eqOn_positiveWedgePush_id_slabBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eqOn_positiveWedgePush_id_slabBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eqOn_positiveWedgePush_id_slabBoundary

theorem eqOn_negativeWedgePush_id_slabBoundary (c : ℝ) :
    EqOn (negativeWedgePush c) id (wedgeSlabBoundary c) := by
  intro p hp
  rcases hp with hp | hp
  · rw [negativeWedgePush, negativeWedgeDisplacement, slabWedgeHat_eq_zero_of_left_face hp]
    simp
  · rw [negativeWedgePush, negativeWedgeDisplacement, slabWedgeHat_eq_zero_of_right_face hp]
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eqOn_negativeWedgePush_id_slabBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eqOn_negativeWedgePush_id_slabBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eqOn_negativeWedgePush_id_slabBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eqOn_negativeWedgePush_id_slabBoundary

@[simp]
theorem positiveWedgePush_fst (c : ℝ) (p : ℝ × ℝ × ℝ) :
    (positiveWedgePush c p).1 = p.1 := by
  simp [positiveWedgePush, positiveWedgeDisplacement]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgePush_fst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgePush_fst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgePush_fst ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.positiveWedgePush_fst

@[simp]
theorem negativeWedgePush_fst (c : ℝ) (p : ℝ × ℝ × ℝ) :
    (negativeWedgePush c p).1 = p.1 := by
  simp [negativeWedgePush, negativeWedgeDisplacement]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgePush_fst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgePush_fst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgePush_fst ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.negativeWedgePush_fst

theorem mapsTo_positiveWedgePush_wedgeSlab (c : ℝ) :
    MapsTo (positiveWedgePush c) (wedgeSlab c) (wedgeSlab c) :=
  fun _ hp => by
    change 0 ≤ _ ∧ _ ≤ c at hp ⊢
    simpa only [positiveWedgePush_fst] using hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_positiveWedgePush_wedgeSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_positiveWedgePush_wedgeSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_positiveWedgePush_wedgeSlab ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_positiveWedgePush_wedgeSlab

theorem mapsTo_negativeWedgePush_wedgeSlab (c : ℝ) :
    MapsTo (negativeWedgePush c) (wedgeSlab c) (wedgeSlab c) :=
  fun _ hp => by
    change 0 ≤ _ ∧ _ ≤ c at hp ⊢
    simpa only [negativeWedgePush_fst] using hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_negativeWedgePush_wedgeSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_negativeWedgePush_wedgeSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_negativeWedgePush_wedgeSlab ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_negativeWedgePush_wedgeSlab

theorem mapsTo_positiveWedgePush_wedgeSlabInterior (c : ℝ) :
    MapsTo (positiveWedgePush c) (wedgeSlabInterior c) (wedgeSlabInterior c) :=
  fun _ hp => by
    change 0 < _ ∧ _ < c at hp ⊢
    simpa only [positiveWedgePush_fst] using hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_positiveWedgePush_wedgeSlabInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_positiveWedgePush_wedgeSlabInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_positiveWedgePush_wedgeSlabInterior ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_positiveWedgePush_wedgeSlabInterior

theorem mapsTo_negativeWedgePush_wedgeSlabInterior (c : ℝ) :
    MapsTo (negativeWedgePush c) (wedgeSlabInterior c) (wedgeSlabInterior c) :=
  fun _ hp => by
    change 0 < _ ∧ _ < c at hp ⊢
    simpa only [negativeWedgePush_fst] using hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_negativeWedgePush_wedgeSlabInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_negativeWedgePush_wedgeSlabInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_negativeWedgePush_wedgeSlabInterior ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_negativeWedgePush_wedgeSlabInterior

theorem not_disjoint_image_positive_negative_slabFold_of_fix_left_endpoint {c : ℝ} (hc : 0 ≤ c)
    {f g : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ)}
    (hf : f (0, 0, 0) = (0, 0, 0)) (hg : g (0, 0, 0) = (0, 0, 0)) :
    ¬Disjoint (f '' positiveSlabFold c) (g '' negativeSlabFold c) := by
  rw [Set.not_disjoint_iff]
  refine ⟨(0, 0, 0), ⟨0, ?_, hf⟩, ⟨0, ?_, hg⟩⟩
  · exact ⟨⟨le_rfl, hc⟩, Or.inl ⟨rfl, le_rfl⟩⟩
  · exact ⟨⟨le_rfl, hc⟩, Or.inl ⟨rfl, le_rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.not_disjoint_image_positive_negative_slabFold_of_fix_left_endpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.not_disjoint_image_positive_negative_slabFold_of_fix_left_endpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.not_disjoint_image_positive_negative_slabFold_of_fix_left_endpoint ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.not_disjoint_image_positive_negative_slabFold_of_fix_left_endpoint

theorem image_positiveSlabFold_inter_image_negativeSlabFold {c : ℝ} (hc : 0 ≤ c) :
    positiveWedgePush c '' positiveSlabFold c ∩ negativeWedgePush c '' negativeSlabFold c =
      {(0, 0, 0), (c, 0, 0)} := by
  ext w
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, ⟨q, hq, hqp⟩⟩
    have hpnonneg : 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 := by
      rcases hp.2 with h | h
      · exact ⟨h.2, h.1.symm.le⟩
      · exact ⟨h.1.symm.le, h.2⟩
    have hqnonpos : q.2.1 ≤ 0 ∧ q.2.2 ≤ 0 := by
      rcases hq.2 with h | h
      · exact ⟨h.2, h.1.le⟩
      · exact ⟨h.1.le, h.2⟩
    rcases hpnonneg with ⟨hpy0, hpz0⟩
    rcases hqnonpos with ⟨hqy0, hqz0⟩
    have hpHat := slabWedgeHat_nonneg c p
    have hqHat := slabWedgeHat_nonneg c q
    have hy := congrArg (fun z : ℝ × ℝ × ℝ => z.2.1) hqp
    have hz := congrArg (fun z : ℝ × ℝ × ℝ => z.2.2) hqp
    change q.2.1 - slabWedgeHat c q = p.2.1 + slabWedgeHat c p at hy
    change q.2.2 - slabWedgeHat c q = p.2.2 + slabWedgeHat c p at hz
    have hpy : p.2.1 = 0 := by linarith
    have hpz : p.2.2 = 0 := by linarith
    have hpHat0 : slabWedgeHat c p = 0 := by linarith
    have haxis : slabWedgeHat c (p.1, 0, 0) = 0 := by
      rw [show (p.1, 0, 0) = p by
        exact Prod.ext rfl (Prod.ext hpy.symm hpz.symm)]
      exact hpHat0
    have hx : p.1 = 0 ∨ p.1 = c :=
      (slabWedgeHat_axis_eq_zero_iff hp.1).mp haxis
    rcases hx with hx | hx
    · left
      apply Prod.ext
      · simpa only [positiveWedgePush_fst] using hx
      · apply Prod.ext <;> simp [positiveWedgePush, positiveWedgeDisplacement, hpy, hpz, hpHat0]
    · right
      apply Prod.ext
      · simpa only [positiveWedgePush_fst] using hx
      · apply Prod.ext <;> simp [positiveWedgePush, positiveWedgeDisplacement, hpy, hpz, hpHat0]
  · intro hw
    rcases hw with rfl | hw
    · refine ⟨⟨(0, 0, 0), ?_, ?_⟩, ⟨(0, 0, 0), ?_, ?_⟩⟩
      · exact ⟨⟨le_rfl, hc⟩, Or.inl ⟨rfl, le_rfl⟩⟩
      · rw [eqOn_positiveWedgePush_id_slabBoundary c (Or.inl rfl)]
        rfl
      · exact ⟨⟨le_rfl, hc⟩, Or.inl ⟨rfl, le_rfl⟩⟩
      · rw [eqOn_negativeWedgePush_id_slabBoundary c (Or.inl rfl)]
        rfl
    · have hwc : w = (c, 0, 0) := by simpa using hw
      subst w
      refine ⟨⟨(c, 0, 0), ?_, ?_⟩, ⟨(c, 0, 0), ?_, ?_⟩⟩
      · exact ⟨⟨hc, le_rfl⟩, Or.inl ⟨rfl, le_rfl⟩⟩
      · rw [eqOn_positiveWedgePush_id_slabBoundary c (Or.inr rfl)]
        rfl
      · exact ⟨⟨hc, le_rfl⟩, Or.inl ⟨rfl, le_rfl⟩⟩
      · rw [eqOn_negativeWedgePush_id_slabBoundary c (Or.inr rfl)]
        rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_positiveSlabFold_inter_image_negativeSlabFold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_positiveSlabFold_inter_image_negativeSlabFold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_positiveSlabFold_inter_image_negativeSlabFold ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_positiveSlabFold_inter_image_negativeSlabFold

theorem disjoint_positive_negative_wedge_push_on_slabInterior {c : ℝ} :
    Disjoint (positiveWedgePush c '' (positiveSlabFold c ∩ wedgeSlabInterior c))
      (negativeWedgePush c '' (negativeSlabFold c ∩ wedgeSlabInterior c)) := by
  rw [Set.disjoint_left]
  rintro w ⟨p, ⟨hp, hpopen⟩, rfl⟩ ⟨q, ⟨hq, hqopen⟩, hqp⟩
  have hw : positiveWedgePush c p ∈
      positiveWedgePush c '' positiveSlabFold c ∩ negativeWedgePush c '' negativeSlabFold c :=
    ⟨⟨p, hp, rfl⟩, ⟨q, hq, hqp⟩⟩
  have hc : 0 ≤ c := le_trans hpopen.1.le hpopen.2.le
  rw [image_positiveSlabFold_inter_image_negativeSlabFold hc] at hw
  rcases hw with hw | hw
  · have := congrArg (fun z : ℝ × ℝ × ℝ => z.1) hw
    simp only [positiveWedgePush_fst] at this
    linarith [hpopen.1]
  · have hw' : positiveWedgePush c p = (c, 0, 0) := by simpa using hw
    have := congrArg (fun z : ℝ × ℝ × ℝ => z.1) hw'
    simp only [positiveWedgePush_fst] at this
    linarith [hpopen.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_positive_negative_wedge_push_on_slabInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.disjoint_positive_negative_wedge_push_on_slabInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_positive_negative_wedge_push_on_slabInterior ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.disjoint_positive_negative_wedge_push_on_slabInterior

end

end DifferentialGeometry.Topology.PiecewiseLinear
