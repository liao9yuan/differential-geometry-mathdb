/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceTraceLocality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCanonicalSurface.windowNullRank_pos_iff [DecidableEq E3]
    {X : ℤ → Geometry.SimplicialComplex ℝ E3} {S' T : ℤ → Set E3}
    {I : Set E3} {P' a b : E3} (h : IsCanonicalSurface X S' T I P' a b) (window : Finset ℤ) :
    0 < windowNullRank X T window ↔
      ∃ i ∈ window, ∃ G ∈ traceCircles ((X (i - 1)).space ∪ (X i).space) (T (2 * i)),
        boundsDiskIn G (T (2 * i)) := by
  classical
  simp only [Nat.pos_iff_ne_zero, ne_eq, h.windowNullRank_eq_zero_iff window,
    _root_.Classical.not_forall, _root_.Classical.not_not, exists_prop]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.windowNullRank_pos_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.windowNullRank_pos_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.windowNullRank_pos_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.windowNullRank_pos_iff

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.windowNullRank_lt_of_local_replacement
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} {i : ℤ} {window : Finset ℤ}
    (hi : i ∈ window)
    (hout : ∀ j, (Y j).space \ interior (φ '' S (2 * i)) =
      (X j).space \ interior (φ '' S (2 * i)))
    (hlt : nullTraceCount ((Y (i - 1)).space ∪ (Y i).space) (T'' (2 * i)) <
      nullTraceCount ((X (i - 1)).space ∪ (X i).space) (T'' (2 * i))) :
    windowNullRank Y T'' window < windowNullRank X T'' window := by
  have hother (k : ℤ) (hki : k ≠ i) :
      nullTraceCount ((Y (k - 1)).space ∪ (Y k).space) (T'' (2 * k)) =
        nullTraceCount ((X (k - 1)).space ∪ (X k).space) (T'' (2 * k)) := by
    apply nullTraceCount_eq_of_inter_eq
    apply htw.inter_even_of_sdiff_eq hki
    rw [_root_.Set.union_sdiff_distrib, _root_.Set.union_sdiff_distrib, hout (k - 1), hout k]
  unfold windowNullRank
  apply Finset.sum_lt_sum ?_ ⟨i, hi, hlt⟩
  intro k _
  by_cases hki : k = i
  · exact hki ▸ hlt.le
  · exact (hother k hki).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.windowNullRank_lt_of_local_replacement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.windowNullRank_lt_of_local_replacement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.windowNullRank_lt_of_local_replacement ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.windowNullRank_lt_of_local_replacement

end DifferentialGeometry.Topology.PiecewiseLinear
