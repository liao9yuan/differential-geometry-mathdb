/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ConcaveCornerMap
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.InnerProductSpace.Calculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Complex
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def toHalfSpace (v : EuclideanSpace ℝ (Fin 3)) : EuclideanHalfSpace 3 :=
  if h : 0 ≤ v 0 then ⟨v, h⟩ else ⟨0, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.toHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.toHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.toHalfSpace ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.toHalfSpace

theorem toHalfSpace_val {v : EuclideanSpace ℝ (Fin 3)} (h : 0 ≤ v 0) :
    (toHalfSpace v).val = v := by
  simp only [toHalfSpace, dif_pos h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.toHalfSpace_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.toHalfSpace_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.toHalfSpace_val ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.toHalfSpace_val

theorem contMDiffWithinAt_toHalfSpace_comp {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {g : Y → EuclideanSpace ℝ (Fin 3)} {s : Set Y} {p : Y}
    (hg : ContDiffWithinAt ℝ ∞ g s p) (hs : ∀ q ∈ s, 0 ≤ g q 0) (hp : p ∈ s) :
    ContMDiffWithinAt 𝓘(ℝ, Y) (𝓡∂ 3) ∞ (fun q => toHalfSpace (g q)) s p := by
  have heq : ∀ q ∈ s, (toHalfSpace (g q)).val = g q := fun q hq =>
    toHalfSpace_val (hs q hq)
  rw [contMDiffWithinAt_iff]
  refine ⟨?_, ?_⟩
  · refine (Topology.IsInducing.subtypeVal
      (t := {x : EuclideanSpace ℝ (Fin 3) | 0 ≤ x 0})).continuousWithinAt_iff.mpr ?_
    exact hg.continuousWithinAt.congr heq (heq p hp)
  · simp only [extChartAt_self_eq, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, Function.comp_id, modelWithCornersSelf_coe, _root_.Set.range_id, id_eq,
      _root_.Set.preimage_id, _root_.Set.inter_univ]
    exact hg.congr heq (heq p hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.contMDiffWithinAt_toHalfSpace_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.contMDiffWithinAt_toHalfSpace_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.contMDiffWithinAt_toHalfSpace_comp ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.contMDiffWithinAt_toHalfSpace_comp

theorem contMDiffAt_comp_val_of_contDiffWithinAt {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] {G : EuclideanSpace ℝ (Fin 3) → Y} {y : EuclideanHalfSpace 3}
    (hG : ContDiffWithinAt ℝ ∞ G {v | 0 ≤ v 0} y.val) :
    ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, Y) ∞ (fun z : EuclideanHalfSpace 3 => G z.val) y := by
  have hrange : _root_.Set.range (𝓡∂ 3) = {v : EuclideanSpace ℝ (Fin 3) | 0 ≤ v 0} :=
    range_modelWithCornersEuclideanHalfSpace 3
  rw [contMDiffAt_iff]
  refine ⟨?_, ?_⟩
  · have hc : ContinuousWithinAt G {v : EuclideanSpace ℝ (Fin 3) | 0 ≤ v 0} y.val :=
      hG.continuousWithinAt
    have hv : ContinuousWithinAt (fun z : EuclideanHalfSpace 3 => z.val) _root_.Set.univ y :=
      continuous_subtype_val.continuousWithinAt
    exact (continuousWithinAt_univ _ _).mp (hc.comp hv fun z _ => z.2)
  · simp only [extChartAt_self_eq, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp]
    rw [hrange]
    have heq : ∀ v ∈ {v : EuclideanSpace ℝ (Fin 3) | 0 ≤ v 0},
        ((fun z : EuclideanHalfSpace 3 => G z.val) ∘ (𝓡∂ 3).symm) v = G v := by
      intro v hv
      simp only [Function.comp_apply]
      congr 1
      exact (𝓡∂ 3).right_inv (by rw [hrange]; exact hv)
    exact hG.congr heq (heq _ y.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.contMDiffAt_comp_val_of_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.contMDiffAt_comp_val_of_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.contMDiffAt_comp_val_of_contDiffWithinAt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.contMDiffAt_comp_val_of_contDiffWithinAt

noncomputable def cornerChartVec (a b : ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(concaveCornerMap (a + b * _root_.Complex.I)).re,
    (2 + (concaveCornerMap (a + b * _root_.Complex.I)).im) * u 0,
    (2 + (concaveCornerMap (a + b * _root_.Complex.I)).im) * u 1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec

noncomputable def cornerChartPlane (y : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![y 1, y 2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartPlane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.cornerChartPlane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartPlane ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.cornerChartPlane

noncomputable def cornerChartInvZ (y : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  concaveCornerInv (y 0 + (‖cornerChartPlane y‖ - 2) * _root_.Complex.I)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartInvZ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.cornerChartInvZ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartInvZ ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.cornerChartInvZ

theorem cornerChartVec_zero_coord (a b : ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    cornerChartVec a b u 0 = (concaveCornerMap (a + b * _root_.Complex.I)).re := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_zero_coord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_zero_coord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_zero_coord ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_zero_coord

theorem cornerChartVec_plane (a b : ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    cornerChartPlane (cornerChartVec a b u) = (2 + (concaveCornerMap (a + b * _root_.Complex.I)).im) • u := by
  ext i
  fin_cases i <;> simp [cornerChartPlane, cornerChartVec]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_plane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_plane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_plane ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_plane

theorem cornerChartVec_nonneg {a b : ℝ} (hab : a + b * _root_.Complex.I ∈ concaveQuadrant)
    (u : EuclideanSpace ℝ (Fin 2)) : 0 ≤ cornerChartVec a b u 0 :=
  concaveCornerMap_re_nonneg hab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_nonneg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_nonneg

theorem abs_im_concaveCornerMap_lt {z : ℂ} (hz : z ∈ concaveQuadrant) (hz1 : ‖z‖ < 1) :
    |(concaveCornerMap z).im| < 1 := by
  calc |(concaveCornerMap z).im| ≤ ‖concaveCornerMap z‖ := _root_.Complex.abs_im_le_norm _
    _ = ‖z‖ ^ (2 / 3 : ℝ) := norm_concaveCornerMap hz
    _ < 1 := Real.rpow_lt_one (norm_nonneg z) hz1 (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.abs_im_concaveCornerMap_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.abs_im_concaveCornerMap_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.abs_im_concaveCornerMap_lt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.abs_im_concaveCornerMap_lt

theorem norm_cornerChartPlane_cornerChartVec {a b : ℝ} (hab : a + b * _root_.Complex.I ∈ concaveQuadrant)
    (hab1 : ‖a + b * I‖ < 1) {u : EuclideanSpace ℝ (Fin 2)} (hu : ‖u‖ = 1) :
    ‖cornerChartPlane (cornerChartVec a b u)‖ = 2 + (concaveCornerMap (a + b * _root_.Complex.I)).im := by
  have h := abs_im_concaveCornerMap_lt hab hab1
  rw [cornerChartVec_plane, norm_smul, hu, mul_one, Real.norm_of_nonneg]
  linarith [(abs_lt.mp h).1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.norm_cornerChartPlane_cornerChartVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.norm_cornerChartPlane_cornerChartVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.norm_cornerChartPlane_cornerChartVec ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.norm_cornerChartPlane_cornerChartVec

theorem cornerChartInvZ_cornerChartVec {a b : ℝ} (hab : a + b * _root_.Complex.I ∈ concaveQuadrant)
    (hab1 : ‖a + b * I‖ < 1) {u : EuclideanSpace ℝ (Fin 2)} (hu : ‖u‖ = 1) :
    cornerChartInvZ (cornerChartVec a b u) = a + b * I := by
  unfold cornerChartInvZ
  rw [norm_cornerChartPlane_cornerChartVec hab hab1 hu, cornerChartVec_zero_coord]
  have : ((concaveCornerMap (a + b * _root_.Complex.I)).re : ℂ) +
      ((2 + (concaveCornerMap (a + b * _root_.Complex.I)).im - 2 : ℝ) : ℂ) * _root_.Complex.I =
      concaveCornerMap (a + b * _root_.Complex.I) := by
    apply Complex.ext <;> simp
  push_cast at this ⊢
  rw [this, concaveCornerInv_map hab]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartInvZ_cornerChartVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.cornerChartInvZ_cornerChartVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartInvZ_cornerChartVec ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.cornerChartInvZ_cornerChartVec

theorem cornerChartPlane_normalize {a b : ℝ} (hab : a + b * _root_.Complex.I ∈ concaveQuadrant)
    (hab1 : ‖a + b * I‖ < 1) {u : EuclideanSpace ℝ (Fin 2)} (hu : ‖u‖ = 1) :
    ‖cornerChartPlane (cornerChartVec a b u)‖⁻¹ • cornerChartPlane (cornerChartVec a b u) = u := by
  have h := abs_im_concaveCornerMap_lt hab hab1
  have hpos : 0 < 2 + (concaveCornerMap (a + b * _root_.Complex.I)).im := by linarith [(abs_lt.mp h).1]
  rw [norm_cornerChartPlane_cornerChartVec hab hab1 hu, cornerChartVec_plane, smul_smul,
    inv_mul_cancel₀ hpos.ne', one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartPlane_normalize then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.cornerChartPlane_normalize"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartPlane_normalize ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.cornerChartPlane_normalize

theorem cornerChartInvZ_mem {y : EuclideanSpace ℝ (Fin 3)} (hy : 0 ≤ y 0) :
    cornerChartInvZ y ∈ concaveQuadrant :=
  concaveCornerInv_mem (by simpa using hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartInvZ_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.cornerChartInvZ_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartInvZ_mem ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.cornerChartInvZ_mem

theorem cornerChartVec_inv {y : EuclideanSpace ℝ (Fin 3)} (hy : 0 ≤ y 0)
    (hv : cornerChartPlane y ≠ 0) :
    cornerChartVec (cornerChartInvZ y).re (cornerChartInvZ y).im
      (‖cornerChartPlane y‖⁻¹ • cornerChartPlane y) = y := by
  have hK : concaveCornerMap (cornerChartInvZ y) = y 0 + (‖cornerChartPlane y‖ - 2) * I :=
    concaveCornerMap_inv (by simpa using hy)
  have hn : ‖cornerChartPlane y‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have h1 : (cornerChartPlane y) 0 = y 1 := rfl
  have h2 : (cornerChartPlane y) 1 = y 2 := rfl
  ext i
  fin_cases i
  · simp only [cornerChartVec, Complex.re_add_im, hK]
    simp
  · simp only [cornerChartVec, Complex.re_add_im, hK]
    simp [h1]
    field_simp
  · simp only [cornerChartVec, Complex.re_add_im, hK]
    simp [h2]
    field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_inv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_inv

theorem cornerChartVec_zero_coord_eq_zero_iff {a b : ℝ} (hab : a + b * _root_.Complex.I ∈ concaveQuadrant)
    (u : EuclideanSpace ℝ (Fin 2)) :
    cornerChartVec a b u 0 = 0 ↔ (a = 0 ∧ b ≤ 0) ∨ (b = 0 ∧ a ≤ 0) := by
  rw [cornerChartVec_zero_coord, concaveCornerMap_re_eq_zero_iff hab]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_zero_coord_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_zero_coord_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_zero_coord_eq_zero_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.cornerChartVec_zero_coord_eq_zero_iff

theorem contDiffAt_cornerChartVec {a b : ℝ} (hab : a + b * _root_.Complex.I ∈ concaveQuadrant)
    (hab0 : a + b * _root_.Complex.I ≠ 0) (u : EuclideanSpace ℝ (Fin 2)) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × EuclideanSpace ℝ (Fin 2) => cornerChartVec q.1 q.2.1 q.2.2)
      (a, b, u) := by
  have hz : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × EuclideanSpace ℝ (Fin 2) =>
      concaveCornerMap ((q.1 : ℂ) + (q.2.1 : ℂ) * _root_.Complex.I)) (a, b, u) := by
    have hl : ContDiff ℝ ∞ (fun q : ℝ × ℝ × EuclideanSpace ℝ (Fin 2) =>
        (q.1 : ℂ) + (q.2.1 : ℂ) * _root_.Complex.I) :=
      (ofRealCLM.contDiff.comp contDiff_fst).add
        ((ofRealCLM.contDiff.comp (contDiff_fst.comp contDiff_snd)).mul contDiff_const)
    exact (contDiffAt_concaveCornerMap hab hab0).comp (a, b, u) hl.contDiffAt
  have hre := reCLM.contDiff.contDiffAt.comp (a, b, u) hz
  have him := imCLM.contDiff.contDiffAt.comp (a, b, u) hz
  have hu0 : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × EuclideanSpace ℝ (Fin 2) => q.2.2 0) (a, b, u) :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff.comp
      (contDiff_snd.comp contDiff_snd)).contDiffAt
  have hu1 : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × EuclideanSpace ℝ (Fin 2) => q.2.2 1) (a, b, u) :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).contDiff.comp
      (contDiff_snd.comp contDiff_snd)).contDiffAt
  apply (contDiffAt_piLp 2).2
  intro i
  fin_cases i
  · exact hre
  · exact (contDiffAt_const.add him).mul hu0
  · exact (contDiffAt_const.add him).mul hu1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.contDiffAt_cornerChartVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.contDiffAt_cornerChartVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.contDiffAt_cornerChartVec ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.contDiffAt_cornerChartVec

theorem contDiffAt_cornerChartInv {y : EuclideanSpace ℝ (Fin 3)} (hy : 0 ≤ y 0)
    (hv : cornerChartPlane y ≠ 0) (hz : cornerChartInvZ y ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 3) =>
      ((cornerChartInvZ y).re, (cornerChartInvZ y).im,
        ‖cornerChartPlane y‖⁻¹ • cornerChartPlane y)) y := by
  have hP : ContDiff ℝ ∞ cornerChartPlane := by
    apply (contDiff_piLp 2).2
    intro i
    fin_cases i
    · exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 1).contDiff
    · exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).contDiff
  have hN : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 3) => ‖cornerChartPlane y‖) y :=
    (contDiffAt_norm ℝ hv).comp y hP.contDiffAt
  have harg : (y 0 : ℂ) + ((‖cornerChartPlane y‖ - 2 : ℝ) : ℂ) * _root_.Complex.I ≠ 0 := by
    intro h
    apply hz
    unfold cornerChartInvZ
    push_cast at h
    rw [h, concaveCornerInv_zero]
  have hre : 0 ≤ ((y 0 : ℂ) + ((‖cornerChartPlane y‖ - 2 : ℝ) : ℂ) * _root_.Complex.I).re := by simpa using hy
  have hw : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 3) =>
      (y 0 : ℂ) + ((‖cornerChartPlane y‖ - 2 : ℝ) : ℂ) * _root_.Complex.I) y := by
    have h0 : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 3) => y 0) y :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0).contDiff.contDiffAt
    exact (ofRealCLM.contDiff.contDiffAt.comp y h0).add
      ((ofRealCLM.contDiff.contDiffAt.comp y (hN.sub contDiffAt_const)).mul contDiffAt_const)
  have hZ : ContDiffAt ℝ ∞ cornerChartInvZ y := by
    have h := (contDiffAt_concaveCornerInv hre harg).comp y hw
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y' => ?_)
    simp only [Function.comp_apply, cornerChartInvZ]
    push_cast
    rfl
  refine (reCLM.contDiff.contDiffAt.comp y hZ).prodMk
    ((imCLM.contDiff.contDiffAt.comp y hZ).prodMk ?_)
  exact (hN.inv (norm_ne_zero_iff.mpr hv)).smul hP.contDiffAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.contDiffAt_cornerChartInv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.contDiffAt_cornerChartInv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.contDiffAt_cornerChartInv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.contDiffAt_cornerChartInv

theorem continuousOn_cornerChartVec :
    ContinuousOn (fun q : ℝ × ℝ × EuclideanSpace ℝ (Fin 2) => cornerChartVec q.1 q.2.1 q.2.2)
      {q | (q.1 : ℂ) + q.2.1 * _root_.Complex.I ∈ concaveQuadrant} := by
  have hl : Continuous (fun q : ℝ × ℝ × EuclideanSpace ℝ (Fin 2) =>
      (q.1 : ℂ) + (q.2.1 : ℂ) * _root_.Complex.I) := by fun_prop
  have hz : ContinuousOn (fun q : ℝ × ℝ × EuclideanSpace ℝ (Fin 2) =>
      concaveCornerMap ((q.1 : ℂ) + (q.2.1 : ℂ) * _root_.Complex.I))
      {q | (q.1 : ℂ) + q.2.1 * _root_.Complex.I ∈ concaveQuadrant} :=
    continuousOn_concaveCornerMap.comp hl.continuousOn fun q hq => hq
  have hre := continuous_re.comp_continuousOn hz
  have him := continuous_im.comp_continuousOn hz
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  apply continuousOn_pi.2
  intro i
  fin_cases i
  · exact hre
  · exact (continuousOn_const.add him).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp
        (continuous_snd.comp continuous_snd)).continuousOn
  · exact (continuousOn_const.add him).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
        (continuous_snd.comp continuous_snd)).continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_cornerChartVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_cornerChartVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_cornerChartVec ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_cornerChartVec

theorem continuousOn_cornerChartInv :
    ContinuousOn (fun y : EuclideanSpace ℝ (Fin 3) =>
      ((cornerChartInvZ y).re, (cornerChartInvZ y).im,
        ‖cornerChartPlane y‖⁻¹ • cornerChartPlane y))
      {y | 0 ≤ y 0 ∧ cornerChartPlane y ≠ 0} := by
  have hP : Continuous cornerChartPlane := by
    unfold cornerChartPlane
    fun_prop
  have hw : Continuous (fun y : EuclideanSpace ℝ (Fin 3) =>
      (y 0 : ℂ) + ((‖cornerChartPlane y‖ - 2 : ℝ) : ℂ) * _root_.Complex.I) := by fun_prop
  have hZ : ContinuousOn cornerChartInvZ {y | 0 ≤ y 0 ∧ cornerChartPlane y ≠ 0} := by
    have h := continuousOn_concaveCornerInv.comp hw.continuousOn
      (fun y (hy : y ∈ {y : EuclideanSpace ℝ (Fin 3) | 0 ≤ y 0 ∧ cornerChartPlane y ≠ 0}) => by
        change 0 ≤ ((y 0 : ℂ) + ((‖cornerChartPlane y‖ - 2 : ℝ) : ℂ) * _root_.Complex.I).re
        simpa using hy.1)
    refine h.congr fun y _ => ?_
    simp only [Function.comp_apply, cornerChartInvZ]
    push_cast
    rfl
  refine (continuous_re.comp_continuousOn hZ).prodMk
    ((continuous_im.comp_continuousOn hZ).prodMk ?_)
  intro y hy
  exact ((continuous_norm.comp hP).continuousAt.inv₀ (norm_ne_zero_iff.mpr hy.2)).smul
    hP.continuousAt |>.continuousWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_cornerChartInv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_cornerChartInv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_cornerChartInv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_cornerChartInv

end DifferentialGeometry.Topology.PiecewiseLinear
