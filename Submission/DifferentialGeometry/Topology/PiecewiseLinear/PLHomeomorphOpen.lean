/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def IsPLHomeomorphOn.toOpenPartialHomeomorph [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F]
    {f : E → F} {P : Set E} {Q : Set F} (hf : IsPLHomeomorphOn f P Q) (hP : IsOpen P) (hQ : IsOpen
        Q) :
    OpenPartialHomeomorph E F where
  toFun := f
  invFun := Function.invFunOn f P
  source := P
  target := Q
  map_source' := hf.bijOn.mapsTo
  map_target' := hf.bijOn.surjOn.mapsTo_invFunOn
  left_inv' := hf.bijOn.invOn_invFunOn.1
  right_inv' := hf.bijOn.invOn_invFunOn.2
  open_source := hP
  open_target := hQ
  continuousOn_toFun := hf.isPiecewiseAffineOn.continuousOn
  continuousOn_invFun := hf.isPiecewiseAffineOn_invFunOn.continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.toOpenPartialHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.toOpenPartialHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.toOpenPartialHomeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.toOpenPartialHomeomorph

theorem isPLHomeomorphOn_openPartialHomeomorph [FiniteDimensional ℝ E]
    (e : OpenPartialHomeomorph E E) (he : IsPiecewiseAffineOn e e.source) :
    IsPLHomeomorphOn e e.source e.target := by
  refine ⟨e.bijOn, he, he.symm.congr ?_⟩
  intro y hy
  exact e.injOn (e.bijOn.surjOn.mapsTo_invFunOn hy) (e.map_target hy)
    ((e.bijOn.invOn_invFunOn.2 hy).trans (e.right_inv hy).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_openPartialHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_openPartialHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_openPartialHomeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_openPartialHomeomorph

theorem IsPLHomeomorphOn.postcomp_openPartialHomeomorph [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {f : E → F} {P : Set E} {Q : Set F} (hf : IsPLHomeomorphOn f P Q)
    (e : OpenPartialHomeomorph F F) (he : IsPiecewiseAffineOn e e.source) (hQ : Q ⊆ e.source) :
    IsPLHomeomorphOn (e ∘ f) P (e '' Q) := by
  have hbij : _root_.Set.BijOn (e ∘ f) P (e '' Q) := ((e.injOn.mono hQ).bijOn_image).comp hf.bijOn
  have hdom : P ∩ f ⁻¹' e.source = P := inter_eq_left.mpr fun x hx => hQ (hf.bijOn.mapsTo hx)
  have himage : e.target ∩ e.symm ⁻¹' Q = e '' Q := by
    rw [← e.image_source_inter_eq', inter_eq_right.mpr hQ]
  refine ⟨hbij, ?_, ?_⟩
  · have hpl := he.comp hf.isPiecewiseAffineOn
    rwa [hdom] at hpl
  · have hpl := hf.isPiecewiseAffineOn_invFunOn.comp he.symm
    rw [himage] at hpl
    refine hpl.congr fun y hy => ?_
    have hy' : y ∈ e.target ∩ e.symm ⁻¹' Q := himage.symm ▸ hy
    have hcomp : (e ∘ f) (Function.invFunOn f P (e.symm y)) = y := by
      dsimp only [Function.comp_apply]
      rw [hf.bijOn.invOn_invFunOn.2 hy'.2, e.right_inv hy'.1]
    exact hbij.injOn (hbij.surjOn.mapsTo_invFunOn hy) (hf.bijOn.surjOn.mapsTo_invFunOn hy'.2)
      ((hbij.invOn_invFunOn.2 hy).trans hcomp.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.postcomp_openPartialHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.postcomp_openPartialHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.postcomp_openPartialHomeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.postcomp_openPartialHomeomorph

end DifferentialGeometry.Topology.PiecewiseLinear
