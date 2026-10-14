/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerInnermostSeam

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.traceCircles_generators_of_nullTraceCount_eq_zero
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (i : ℤ) {L : Set E3}
    (hfin : (traceCircles L (T'' (2 * i))).Finite)
    (hseams : traceCircles L (T'' (2 * i)) ⊆ evenTorusSeams T'' i)
    (hzero : nullTraceCount L (T'' (2 * i)) = 0) :
    ∀ G ∈ traceCircles L (T'' (2 * i)), ∀ hsub : G ⊆ S'' (2 * i), ∀ x : G,
      Function.Surjective (FundamentalGroup.map
        (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(G, S'' (2 * i))) x) := by
  have hnull := (nullTraceCount_eq_zero_iff hfin).mp hzero
  intro G hG hsub x
  rcases hseams hG with hleft | hright
  · rcases htw.seam_generator_or_bounds_disks h314 (2 * i - 1) (G := G)
        (by simpa only [sub_add_cancel] using hleft) with hgen | hdisks
    · exact hgen (2 * i) (by
        simp only [_root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff]
        right
        omega) hsub x
    · exact (hnull G hG (by simpa only [sub_add_cancel] using hdisks.2)).elim
  · rcases htw.seam_generator_or_bounds_disks h314 (2 * i) hright with hgen | hdisks
    · exact hgen (2 * i) (Or.inl rfl) hsub x
    · exact (hnull G hG hdisks.1).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.traceCircles_generators_of_nullTraceCount_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.traceCircles_generators_of_nullTraceCount_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.traceCircles_generators_of_nullTraceCount_eq_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.traceCircles_generators_of_nullTraceCount_eq_zero

end DifferentialGeometry.Topology.PiecewiseLinear
