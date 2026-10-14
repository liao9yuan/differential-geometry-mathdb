/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.HoledSphereExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem IsPLCirclePositive.conj_of_leftInvOn
    {S : Set E} {T : Set F} {u : E → E} {h : E → F} {i : F → E}
    (hu : IsPLCirclePositive S u) (hmu : _root_.Set.MapsTo u S S)
    (hh : ContinuousOn h S) (hbij : _root_.Set.BijOn h S T) (hi : _root_.Set.LeftInvOn i h S) :
    IsPLCirclePositive T (h ∘ u ∘ i) := by
  have hpos := hu.conj hmu hh hbij
  apply hpos.of_eqOn
  intro y hy
  have hiy : i y = Function.invFunOn h S y := by
    calc
      i y = i (h (Function.invFunOn h S y)) := congrArg i (hbij.invOn_invFunOn.2 hy).symm
      _ = Function.invFunOn h S y := hi (hbij.surjOn.mapsTo_invFunOn hy)
  simp only [Function.comp_apply, hiy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCirclePositive.conj_of_leftInvOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCirclePositive.conj_of_leftInvOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCirclePositive.conj_of_leftInvOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCirclePositive.conj_of_leftInvOn

theorem isPLCirclePositive_conj_iff_of_leftInvOn
    {S : Set E} {T : Set F} {u : E → E} {h : E → F} {i : F → E}
    (hmu : _root_.Set.MapsTo u S S) (hh : ContinuousOn h S) (hic : ContinuousOn i T)
    (hbij : _root_.Set.BijOn h S T) (hi : _root_.Set.LeftInvOn i h S) :
    IsPLCirclePositive T (h ∘ u ∘ i) ↔ IsPLCirclePositive S u := by
  have him : _root_.Set.MapsTo i T S := by
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := hbij.surjOn hy
    rwa [hi hx]
  have hri : _root_.Set.LeftInvOn h i T := by
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := hbij.surjOn hy
    rw [hi hx]
  have hbi : _root_.Set.BijOn i T S := (show _root_.Set.InvOn i h S T from ⟨hi, hri⟩).symm.bijOn him hbij.mapsTo
  have hcm : _root_.Set.MapsTo (h ∘ u ∘ i) T T := fun _ hy => hbij.mapsTo (hmu (him hy))
  constructor
  · intro hpos
    have hp := hpos.conj_of_leftInvOn hcm hic hbi hri
    apply hp.of_eqOn
    intro x hx
    simp only [Function.comp_apply, hi hx, hi (hmu hx)]
  · exact fun hp => hp.conj_of_leftInvOn hmu hh hbij hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_conj_iff_of_leftInvOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_conj_iff_of_leftInvOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_conj_iff_of_leftInvOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_conj_iff_of_leftInvOn

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem IsPLHomeomorphOn.isPLCirclePositive_conj_iff
    {C S : Set E} {D : Set F} {h : E → F} (hh : IsPLHomeomorphOn h C D)
    (hSC : S ⊆ C) {u : E → E} (hmu : _root_.Set.MapsTo u S S) :
    IsPLCirclePositive (h '' S) (h ∘ u ∘ Function.invFunOn h C) ↔ IsPLCirclePositive S u := by
  have hTD : h '' S ⊆ D := image_subset_iff.mpr (hh.bijOn.mapsTo.mono_left hSC)
  exact isPLCirclePositive_conj_iff_of_leftInvOn hmu
    (hh.isPiecewiseAffineOn.continuousOn.mono hSC)
    (hh.symm.isPiecewiseAffineOn.continuousOn.mono hTD)
    (hh.bijOn.injOn.mono hSC).bijOn_image (hh.bijOn.invOn_invFunOn.1.mono hSC)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isPLCirclePositive_conj_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isPLCirclePositive_conj_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isPLCirclePositive_conj_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isPLCirclePositive_conj_iff

end DifferentialGeometry.Topology.PiecewiseLinear
