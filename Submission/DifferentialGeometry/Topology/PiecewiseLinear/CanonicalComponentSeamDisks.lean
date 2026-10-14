/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceState
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerNullSeamDisks
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SurfaceTraceMonotonicity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable [DecidableEq E3] {X : ℤ → Geometry.SimplicialComplex ℝ E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}

theorem IsCanonicalSurface.lower_component_boundsDiskIn_iff
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (i : ℤ) (c : ConnectedComponents (X i).space) {G : Set E3}
    (hG : G ∈ traceCircles (connectedComponentComplex (X i) c).space (T'' (2 * i))) :
    boundsDiskIn G (T'' (2 * i)) ↔ boundsDiskIn G (T'' (2 * i + 1)) := by
  have hsub : (connectedComponentComplex (X i) c).space ⊆ (X i).space :=
    (_root_.Set.subset_iUnion (fun d => (connectedComponentComplex (X i) d).space) c).trans
      (iUnion_connectedComponentComplex_space (X i)).subset
  have hrow : G ∈ traceCircles (X i).space (T'' (2 * i)) :=
    traceCircles_subset_of_inter_subset (hX.lowerTrace i).traceCover
      (fun _ hx => ⟨hsub hx.1, hx.2⟩) hG
  have horiginal : G ∈ traceCircles (T'' (2 * i)) (T'' (2 * i + 1)) := by
    simpa only [traceCircles, _root_.Set.inter_comm] using hX.lowerOrigin i hrow
  exact htw.boundsDiskIn_iff h314 (2 * i) horiginal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.lower_component_boundsDiskIn_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.lower_component_boundsDiskIn_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.lower_component_boundsDiskIn_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.lower_component_boundsDiskIn_iff

theorem IsCanonicalSurface.upper_component_boundsDiskIn_iff
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (i : ℤ) (c : ConnectedComponents (X i).space) {G : Set E3}
    (hG : G ∈ traceCircles (connectedComponentComplex (X i) c).space (T'' (2 * (i + 1)))) :
    boundsDiskIn G (T'' (2 * (i + 1))) ↔ boundsDiskIn G (T'' (2 * i + 1)) := by
  have hsub : (connectedComponentComplex (X i) c).space ⊆ (X i).space :=
    (_root_.Set.subset_iUnion (fun d => (connectedComponentComplex (X i) d).space) c).trans
      (iUnion_connectedComponentComplex_space (X i)).subset
  have hrow : G ∈ traceCircles (X i).space (T'' (2 * (i + 1))) :=
    traceCircles_subset_of_inter_subset (hX.upperTrace i).traceCover
      (fun _ hx => ⟨hsub hx.1, hx.2⟩) hG
  have horiginal : G ∈ traceCircles (T'' (2 * i + 1)) (T'' ((2 * i + 1) + 1)) := by
    simpa only [show (2 * i + 1) + 1 = 2 * (i + 1) by omega] using hX.upperOrigin i hrow
  simpa only [show (2 * i + 1) + 1 = 2 * (i + 1) by omega] using
    (htw.boundsDiskIn_iff h314 (2 * i + 1) horiginal).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.upper_component_boundsDiskIn_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.upper_component_boundsDiskIn_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.upper_component_boundsDiskIn_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.upper_component_boundsDiskIn_iff

end DifferentialGeometry.Topology.PiecewiseLinear
