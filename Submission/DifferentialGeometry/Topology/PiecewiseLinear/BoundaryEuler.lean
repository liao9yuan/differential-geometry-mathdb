/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.EulerPolyhedra
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Orientation
import Submission.DifferentialGeometry.Topology.SimplicialComplex.BoundaryCounting

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]

open _root_.Classical in
theorem eulerChar_geometricLink_of_isCombinatorialManifoldWithBoundary {n k : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {s : Finset E}
    (hs : s ∈ K.faces) (hc : s.card = k + 1) (hk : k ≤ n) :
    eulerChar (SimplicialComplex.geometricLink K s) =
      if s ∈ (boundaryComplex (n + 1) K).faces then 1 else 1 + (-1 : ℤ) ^ (n - k) := by
  by_cases hb : s ∈ (boundaryComplex (n + 1) K).faces
  · rw [if_pos hb]
    exact eulerChar_of_isPLBall _ ((hK.mem_boundaryComplex_faces_iff K).mp hb).2.2
  · rw [if_neg hb]
    rcases hK.isPLSphere_or_isPLBall_geometricLink K hs hc hk with hS | hB
    · exact eulerChar_of_isPLSphere _ hS
    · exfalso
      apply hb
      apply (hK.mem_boundaryComplex_faces_iff K).mpr
      refine ⟨hs, by omega, ?_⟩
      simpa only [hc, Nat.add_sub_add_right] using hB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_geometricLink_of_isCombinatorialManifoldWithBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_geometricLink_of_isCombinatorialManifoldWithBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_geometricLink_of_isCombinatorialManifoldWithBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_geometricLink_of_isCombinatorialManifoldWithBoundary

open _root_.Classical in
theorem eulerChar_boundaryComplex_eq_two_mul
    (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    eulerChar (boundaryComplex 3 K) = 2 * eulerChar K := by
  apply SimplicialComplex.faceEulerChar_eq_two_mul_of_link_counts
    K.toPreAbstractSimplicialComplex (boundaryComplex 3 K).toPreAbstractSimplicialComplex
  · exact boundaryComplex_faces_subset 3 K
  · exact fun _ hs => hK.card_le K hs
  · exact fun _ hs => ((hK.mem_boundaryComplex_faces_iff K).mp hs).2.1
  · intro s hs
    obtain ⟨hsK, hc⟩ := (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hs
    change (faceCofaces K s 4).card = if s ∈ (boundaryComplex 3 K).faces then 1 else 2
    by_cases hb : s ∈ (boundaryComplex 3 K).faces
    · rw [if_pos hb]
      exact (hK.mem_boundaryComplex_iff_card_cofaces_eq_one K hsK hc).mp hb
    · rw [if_neg hb]
      exact (hK.card_faceCofaces_eq_one_or_two K hsK hc).resolve_left fun h =>
        hb ((hK.mem_boundaryComplex_iff_card_cofaces_eq_one K hsK hc).mpr h)
  · intro s hs
    obtain ⟨hsK, hc⟩ := (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hs
    have h := eulerChar_geometricLink_of_isCombinatorialManifoldWithBoundary K hK hsK hc (by decide)
    change SimplicialComplex.faceEulerChar (SimplicialComplex.link K.toPreAbstractSimplicialComplex
        s) = _ at h
    norm_num at h
    exact h
  · intro s hs
    obtain ⟨hsK, hc⟩ := (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hs
    have h := eulerChar_geometricLink_of_isCombinatorialManifoldWithBoundary K hK hsK hc (by decide)
    change SimplicialComplex.faceEulerChar (SimplicialComplex.link K.toPreAbstractSimplicialComplex
        s) = _ at h
    norm_num at h
    exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_boundaryComplex_eq_two_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_boundaryComplex_eq_two_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_boundaryComplex_eq_two_mul ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_boundaryComplex_eq_two_mul

end DifferentialGeometry.Topology.PiecewiseLinear
