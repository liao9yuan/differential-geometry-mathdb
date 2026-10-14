/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SphereDiskMarked
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallPair

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked
    {p : E} {Lc : Geometry.SimplicialComplex ℝ E} [Finite Lc.faces] (hLc : IsConeBase p Lc)
    {X : Set E} (hXLc : X ⊆ Lc.space) (hSph : IsPLSphere 2 Lc.space)
    {q : F} {Lc' : Geometry.SimplicialComplex ℝ F} [Finite Lc'.faces] (hLc' : IsConeBase q Lc')
    {X' : Set F} (hSph' : IsPLSphere 2 Lc'.space)
    {D : Set E} {D' : Set F} (hD : IsPLBall 2 D) (hDS : D ⊆ Lc.space) (hD'S' : D' ⊆ Lc'.space)
    {g : E → F} (hg : IsPLHomeomorphOn g D D')
    {y : E} (hy : y ∈ closure (Lc.space \ D) \ D)
    {y' : F} (hy' : y' ∈ closure (Lc'.space \ D') \ D')
    (hJsplit : X = X ∩ D ∪ {y}) (hJ'split : X' = X' ∩ D' ∪ {y'})
    (hgJ : g '' (X ∩ D) = X' ∩ D') :
    ∃ G : E → F, IsPLHomeomorphOn G (coneSet p Lc.space) (coneSet q Lc'.space) ∧
      _root_.Set.EqOn G g D ∧ G p = q ∧ G '' coneSet p X = coneSet q X' ∧
      G '' Lc.space = Lc'.space ∧ G y = y' := by
  classical
  obtain ⟨Gs, hGs, hGseq, hGsy⟩ :=
    exists_isPLHomeomorphOn_eqOn_disk_of_isPLSphere_two_marked hSph hSph' hD hDS hg hD'S' hy hy'
  have hGsJ : Gs '' X = X' := by
    rw [hJsplit, _root_.Set.image_union, _root_.Set.image_singleton, hGsy,
      (hGseq.mono _root_.Set.inter_subset_right).image_eq, hgJ, ← hJ'split]
  obtain ⟨G, hG, hGeq, hGp, hGJ⟩ :=
    exists_isPLHomeomorphOn_coneSet_pair hLc hXLc hLc' hGs hGsJ
  have hyLc : y ∈ Lc.space :=
    closure_minimal _root_.Set.sdiff_subset hSph.isPolyhedron.isClosed hy.1
  exact ⟨G, hG, (hGeq.mono hDS).trans hGseq, hGp, hGJ,
    hGeq.image_eq.trans hGs.image_eq, (hGeq hyLc).trans hGsy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked

end DifferentialGeometry.Topology.PiecewiseLinear
