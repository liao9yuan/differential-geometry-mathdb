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

variable {E : Type*}

noncomputable def collarInwardMap (g : E → ℝ) (a : ℝ) (x : E × ℝ) : E × ℝ :=
  (x.1, _root_.Max.max x.2 (_root_.Min.min (x.2 + g x.1) ((x.2 + a) / 2)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap

@[simp]
theorem collarInwardMap_fst (g : E → ℝ) (a : ℝ) (x : E × ℝ) :
    (collarInwardMap g a x).1 = x.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_fst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_fst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_fst ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_fst

theorem collarInwardMap_injective (g : E → ℝ) (a : ℝ) :
    Function.Injective (collarInwardMap g a) := by
  intro x y h
  have hxy : x.1 = y.1 := by
    simpa only [collarInwardMap] using congrArg Prod.fst h
  have hmono : StrictMono (fun t : ℝ => _root_.Max.max t (_root_.Min.min (t + g x.1) ((t + a) / 2))) := by
    intro s t hst
    exact max_lt_max hst (min_lt_min (by linarith) (by linarith))
  apply Prod.ext hxy
  apply hmono.injective
  simpa only [collarInwardMap, hxy] using congrArg Prod.snd h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_injective ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_injective

theorem collarInwardMap_eq_self_of_le (g : E → ℝ) {a : ℝ} {x : E × ℝ} (hx : a ≤ x.2) :
    collarInwardMap g a x = x := by
  refine Prod.ext ?_ ?_
  · rfl
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_eq_self_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_eq_self_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_eq_self_of_le ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_eq_self_of_le

theorem collarInwardMap_eq_self_of_eq_zero {g : E → ℝ} (a : ℝ) {x : E × ℝ}
    (hx : g x.1 = 0) : collarInwardMap g a x = x := by
  refine Prod.ext ?_ ?_
  · rfl
  change _root_.Max.max x.2 (_root_.Min.min (x.2 + g x.1) ((x.2 + a) / 2)) = x.2
  rw [hx, add_zero, max_eq_left (min_le_left _ _)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_eq_self_of_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_eq_self_of_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_eq_self_of_eq_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_eq_self_of_eq_zero

theorem le_collarInwardMap_snd (g : E → ℝ) (a : ℝ) (x : E × ℝ) :
    x.2 ≤ (collarInwardMap g a x).2 := le_max_left _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.le_collarInwardMap_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.le_collarInwardMap_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.le_collarInwardMap_snd ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.le_collarInwardMap_snd

theorem collarInwardMap_snd_lt_of_lt (g : E → ℝ) {a : ℝ} {x : E × ℝ} (hx : x.2 < a) :
    (collarInwardMap g a x).2 < a :=
  max_lt hx ((min_le_right _ _).trans_lt (by linarith))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_snd_lt_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_snd_lt_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_snd_lt_of_lt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_snd_lt_of_lt

theorem collarInwardMap_snd_eq_zero_iff {g : E → ℝ} {a : ℝ} (ha : 0 < a)
    {x : E × ℝ} (hg : 0 ≤ g x.1) (hx : 0 ≤ x.2) :
    (collarInwardMap g a x).2 = 0 ↔ x.2 = 0 ∧ g x.1 = 0 := by
  constructor
  · intro h
    have ht : x.2 = 0 := le_antisymm (h ▸ le_collarInwardMap_snd g a x) hx
    refine ⟨ht, ?_⟩
    have hmin : _root_.Min.min (g x.1) (a / 2) ≤ 0 := by
      have hm : _root_.Min.min (x.2 + g x.1) ((x.2 + a) / 2) ≤ (collarInwardMap g a x).2 :=
        le_max_right _ _
      rw [h] at hm
      simpa only [ht, zero_add] using hm
    rcases le_total (g x.1) (a / 2) with hle | hle
    · rw [min_eq_left hle] at hmin
      exact le_antisymm hmin hg
    · rw [min_eq_right hle] at hmin
      linarith
  · rintro ⟨ht, hg⟩
    rw [collarInwardMap_eq_self_of_eq_zero a hg, ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_snd_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_snd_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_snd_eq_zero_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_snd_eq_zero_iff

theorem collarInwardMap_mapsTo_prod_Icc (g : E → ℝ) {a b : ℝ} (hab : a ≤ b) (B : Set E) :
    MapsTo (collarInwardMap g a) (B ×ˢ _root_.Set.Icc 0 b) (B ×ˢ _root_.Set.Icc 0 b) := by
  intro x hx
  refine ⟨hx.1, hx.2.1.trans (le_collarInwardMap_snd g a x), ?_⟩
  by_cases ha : a ≤ x.2
  · rw [collarInwardMap_eq_self_of_le g ha]
    exact hx.2.2
  · exact (collarInwardMap_snd_lt_of_lt g (lt_of_not_ge ha)).le.trans hab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_mapsTo_prod_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_mapsTo_prod_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_mapsTo_prod_Icc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.collarInwardMap_mapsTo_prod_Icc

theorem isPiecewiseAffineOn_collarInwardMap [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {g : E → ℝ} (hg : IsPiecewiseAffineOn g _root_.Set.univ) (a : ℝ) :
    IsPiecewiseAffineOn (collarInwardMap g a) univ := by
  have hfst : IsPiecewiseAffineOn (Prod.fst : E × ℝ → E) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.fst ℝ E ℝ).toAffineMap isOpen_univ
  have hsnd : IsPiecewiseAffineOn (Prod.snd : E × ℝ → ℝ) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.snd ℝ E ℝ).toAffineMap isOpen_univ
  have hgfst : IsPiecewiseAffineOn (fun x : E × ℝ => g x.1) univ := by
    simpa only [_root_.Set.preimage_univ, _root_.Set.inter_univ, Function.comp_def] using hg.comp hfst
  let A : (E × ℝ) →ᵃ[ℝ] ℝ :=
    (1 / 2 : ℝ) • ((LinearMap.snd ℝ E ℝ).toAffineMap + AffineMap.const ℝ (E × ℝ) a)
  have hA : IsPiecewiseAffineOn (fun x : E × ℝ => (x.2 + a) / 2) univ := by
    convert isPiecewiseAffineOn_of_affine A isOpen_univ using 1
    ext x
    change (x.2 + a) / 2 = (1 / 2 : ℝ) * (x.2 + a)
    ring
  exact hfst.prod_mk (hsnd.max ((hsnd.add hgfst).min hA))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_collarInwardMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_collarInwardMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_collarInwardMap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_collarInwardMap

end DifferentialGeometry.Topology.PiecewiseLinear
