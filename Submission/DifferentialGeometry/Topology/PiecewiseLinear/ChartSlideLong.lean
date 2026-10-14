/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ModelSlideLong
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ChartConjugate

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]

theorem isPiecewiseAffineOn_chartSlideLong {d R : ℝ} (hd : 0 ≤ d)
    (e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ))
    (he : IsPiecewiseAffineOn e e.source) (hei : IsPiecewiseAffineOn e.symm e.target)
    (hsub : slideSupportLong R ⊆ e.target) :
    IsPiecewiseAffineOn (e.conjugateMap (slideMapLong d R)) univ :=
  isPiecewiseAffineOn_conjugateMap e he hei
    (isPiecewiseAffineOn_slideMapLong.mono e.open_target (_root_.Set.subset_univ _))
    (mapsTo_slideMapLong_of_subset hd hsub) (isCompact_slideSupportLong R) hsub
    (eqOn_slideMapLong_id_compl hd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_chartSlideLong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_chartSlideLong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_chartSlideLong ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_chartSlideLong

omit [NormedSpace ℝ M] [FiniteDimensional ℝ M] in
theorem injective_chartSlideLong {d R : ℝ} (hd : 0 ≤ d)
    (e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)) (hsub : slideSupportLong R ⊆ e.target) :
    Function.Injective (e.conjugateMap (slideMapLong d R)) := by
  have hmaps := mapsTo_slideMapLong_of_subset (d := d) hd hsub
  intro x y hxy
  by_cases hx : x ∈ e.source
  · by_cases hy : y ∈ e.source
    · rw [e.conjugateMap_of_mem _ hx, e.conjugateMap_of_mem _ hy] at hxy
      have h1 : slideMapLong d R (e x) ∈ e.target := hmaps (e.map_source hx)
      have h2 : slideMapLong d R (e y) ∈ e.target := hmaps (e.map_source hy)
      have hslide : slideMapLong d R (e x) = slideMapLong d R (e y) := by
        have := congrArg e hxy
        rwa [e.right_inv h1, e.right_inv h2] at this
      have hex : e x = e y := injective_slideMapLong hslide
      have := congrArg e.symm hex
      rwa [e.left_inv hx, e.left_inv hy] at this
    · rw [e.conjugateMap_of_mem _ hx, e.conjugateMap_of_notMem _ hy] at hxy
      exact absurd (hxy ▸ e.map_target (hmaps (e.map_source hx))) hy
  · by_cases hy : y ∈ e.source
    · rw [e.conjugateMap_of_notMem _ hx, e.conjugateMap_of_mem _ hy] at hxy
      exact absurd (hxy.symm ▸ e.map_target (hmaps (e.map_source hy))) hx
    · rwa [e.conjugateMap_of_notMem _ hx, e.conjugateMap_of_notMem _ hy] at hxy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.injective_chartSlideLong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.injective_chartSlideLong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.injective_chartSlideLong ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.injective_chartSlideLong

omit [NormedSpace ℝ M] [FiniteDimensional ℝ M] in
theorem disjoint_chartSlideLong_image {d R a b c : ℝ} (hd : 0 ≤ d) (hR : c + 2 * d ≤ R)
    (hca : c - d < a) (e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ))
    (hsub : slideSupportLong R ⊆ e.target) (hA : slideBandA c ⊆ e.target)
    (hQ : slideBandQ a b ⊆ e.target) :
    Disjoint (e.conjugateMap (slideMapLong d R) '' (e.symm '' slideBandA c))
      (e.symm '' slideBandQ a b) := by
  have hmaps := mapsTo_slideMapLong_of_subset (d := d) hd hsub
  rw [Set.disjoint_left]
  rintro w ⟨u, ⟨p, hp, rfl⟩, rfl⟩ ⟨q, hq, hqe⟩
  have hps : e.symm p ∈ e.source := e.map_target (hA hp)
  have hval : e.conjugateMap (slideMapLong d R) (e.symm p) = e.symm (slideMapLong d R p) := by
    rw [e.conjugateMap_of_mem _ hps, e.right_inv (hA hp)]
  rw [hval] at hqe
  have h1 : slideMapLong d R p ∈ e.target := hmaps (hA hp)
  have hpq : slideMapLong d R p = q := by
    have hcong := congrArg e hqe
    rw [e.right_inv h1, e.right_inv (hQ hq)] at hcong
    exact hcong.symm
  exact Set.disjoint_left.mp (disjoint_slideMapLong_image_slideBandA (b := b) hd hR hca)
    ⟨p, hp, rfl⟩ (hpq ▸ hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_chartSlideLong_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.disjoint_chartSlideLong_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_chartSlideLong_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.disjoint_chartSlideLong_image

end DifferentialGeometry.Topology.PiecewiseLinear
