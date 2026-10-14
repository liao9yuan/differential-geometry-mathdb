/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.MapApproximation
import Mathlib.Topology.MetricSpace.Thickening

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPiecewiseAffineOn_mapsTo_eqOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P Q : Set E} (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) (hQP : Q ⊆ P)
    {U : Set F} (hU : IsOpen U) {f : E → F} (hf : ContinuousOn f P)
    (hfQ : IsPiecewiseAffineOn f Q) (hmap : _root_.Set.MapsTo f P U) :
    ∃ g : E → F, IsPiecewiseAffineOn g P ∧ _root_.Set.EqOn g f Q ∧ _root_.Set.MapsTo g P U := by
  obtain ⟨ε, hε, hεU⟩ :=
    (hP.isCompact.image_of_continuousOn hf).exists_thickening_subset_open hU hmap.image_subset
  obtain ⟨g, hg, heq, hdist⟩ :=
    exists_isPiecewiseAffineOn_dist_lt_eqOn hP hQ hQP hP.isCompact hf hfQ hε
  refine ⟨g, hg, heq, fun x hx => hεU ?_⟩
  exact Metric.mem_thickening_iff.mpr ⟨f x, _root_.Set.mem_image_of_mem f hx, hdist x hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPiecewiseAffineOn_mapsTo_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPiecewiseAffineOn_mapsTo_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPiecewiseAffineOn_mapsTo_eqOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPiecewiseAffineOn_mapsTo_eqOn

end DifferentialGeometry.Topology.PiecewiseLinear
