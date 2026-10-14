/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CircleOrientationParity
import Mathlib.Topology.OpenPartialHomeomorph.Composition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M E F : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem circleOrientationParity_chart_eq
    (b : OpenPartialHomeomorph M E) (c : OpenPartialHomeomorph M F)
    {J : Set M} (hJb : J ⊆ b.source) (hJc : J ⊆ c.source)
    {N : M → M} (hNJ : _root_.Set.MapsTo N J J) :
    circleOrientationParity (b '' J) (b ∘ N ∘ b.symm) =
      circleOrientationParity (c '' J) (c ∘ N ∘ c.symm) := by
  classical
  let u := b ∘ N ∘ b.symm
  let h := c ∘ b.symm
  let i := b ∘ c.symm
  have hBt : b '' J ⊆ b.target := image_subset_iff.mpr fun _ hx => b.map_source (hJb hx)
  have hCt : c '' J ⊆ c.target := image_subset_iff.mpr fun _ hx => c.map_source (hJc hx)
  have hbback := b.symm_image_image_of_subset_source hJb
  have hcback := c.symm_image_image_of_subset_source hJc
  have hbm : _root_.Set.MapsTo b.symm (b '' J) J :=
    fun _ hx => hbback ▸ _root_.Set.mem_image_of_mem b.symm hx
  have hcm : _root_.Set.MapsTo c.symm (c '' J) J :=
    fun _ hx => hcback ▸ _root_.Set.mem_image_of_mem c.symm hx
  have hub : _root_.Set.MapsTo u (b '' J) (b '' J) :=
    fun x hx => ⟨N (b.symm x), hNJ (hbm hx), rfl⟩
  have hbc : ContinuousOn h (b '' J) :=
    c.continuousOn.comp (b.continuousOn_symm.mono hBt) (fun _ hx => hJc (hbm hx))
  have hic : ContinuousOn i (c '' J) :=
    b.continuousOn.comp (c.continuousOn_symm.mono hCt) (fun _ hx => hJb (hcm hx))
  have hbbi : _root_.Set.BijOn b.symm (b '' J) J := ⟨hbm, b.symm.injOn.mono hBt, hbback.ge⟩
  have hbij : _root_.Set.BijOn h (b '' J) (c '' J) :=
    (c.injOn.mono hJc).bijOn_image.comp hbbi
  have hleft : _root_.Set.LeftInvOn i h (b '' J) := by
    rintro _ ⟨x, hx, rfl⟩
    change b (c.symm (c (b.symm (b x)))) = b x
    rw [b.left_inv (hJb hx), c.left_inv (hJc hx)]
  have hpos := isPLCirclePositive_conj_iff_of_leftInvOn hub hbc hic hbij hleft
  have hpar : circleOrientationParity (c '' J) (h ∘ u ∘ i) =
      circleOrientationParity (b '' J) u := by
    unfold circleOrientationParity
    rw [hpos]
  have heq : _root_.Set.EqOn (c ∘ N ∘ c.symm) (h ∘ u ∘ i) (c '' J) := by
    rintro _ ⟨x, hx, rfl⟩
    change c (N (c.symm (c x))) =
      c (b.symm (b (N (b.symm (b (c.symm (c x)))))))
    rw [c.left_inv (hJc hx), b.left_inv (hJb hx), b.left_inv (hJb (hNJ hx))]
  exact ((circleOrientationParity_congr heq).trans hpar).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.circleOrientationParity_chart_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.circleOrientationParity_chart_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.circleOrientationParity_chart_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.circleOrientationParity_chart_eq

omit [TopologicalSpace M] in
theorem IsPLHomeomorphOn.circleOrientationParity_conj
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {C S : Set E} {D : Set F} {h : E → F} (hh : IsPLHomeomorphOn h C D)
    (hSC : S ⊆ C) {u : E → E} (hmu : _root_.Set.MapsTo u S S) :
    circleOrientationParity (h '' S) (h ∘ u ∘ Function.invFunOn h C) =
      circleOrientationParity S u := by
  classical
  unfold circleOrientationParity
  rw [hh.isPLCirclePositive_conj_iff hSC hmu]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.circleOrientationParity_conj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.circleOrientationParity_conj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.circleOrientationParity_conj ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.circleOrientationParity_conj

end DifferentialGeometry.Topology.PiecewiseLinear
