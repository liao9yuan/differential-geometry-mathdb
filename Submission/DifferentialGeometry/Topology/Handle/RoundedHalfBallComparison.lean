import Submission.DifferentialGeometry.Topology.Handle.RoundedHalfBallDisk
import Submission.DifferentialGeometry.Topology.Handle.BallPairComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace PartialDiffeomorph
open _root_.PartialDiffeomorph

variable (m : ℕ)

open _root_.PartialDiffeomorph in
private local instance _root_.Submission.PartialDiffeomorph.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat_differentialGeometry : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.PartialDiffeomorph.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `PartialDiffeomorph.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat_differentialGeometry target :: scope.openDecls } }

open _root_.PartialDiffeomorph in
theorem exists_diffeomorph_roundedHalfBall_comparison
    (c : PartialDiffeomorph (𝓡 ((m + 1) + 1)) (𝓡 ((m + 1) + 1))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))) (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ∞)
    (D : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin ((m + 1) + 1))))
    (v : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {B : Set (EuclideanSpace ℝ (Fin ((m + 1) + 1)))} {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 2)
    (hD : D '' _root_.Metric.closedBall 0 1 = B)
    (hc : c.toOpenPartialHomeomorph.IsImage
      {z | DifferentialGeometry.Topology.Handle.roundedHalfBallFunction (m + 1) ε 0 z ≤ 0} B)
    (hK : (EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1)).symm ''
      (_root_.Metric.closedBall 0 1 ×ˢ {(0 : ℝ)}) ⊆ c.source)
    (hstrip : {p : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × (ℝ × ℝ) |
      0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      ((c.symm.toOpenPartialHomeomorph.trans
        (EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1)).toHomeomorph.toOpenPartialHomeomorph).trans
          (OpenPartialHomeomorph.halfBallCorner 1 v)).target) :
    ∃ Q : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin ((m + 1) + 1))),
      Q '' {z | DifferentialGeometry.Topology.Handle.roundedHalfBallFunction (m + 1) ε 0 z ≤ 0} = B ∧
      ∃ V, IsOpen V ∧
        (fun x : EuclideanSpace ℝ (Fin (m + 1)) => (EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1)).symm
          (DifferentialGeometry.Topology.Handle.halfBallRounding 1 ε (x, 0))) '' _root_.Metric.closedBall 0 1 ⊆ V ∧
        V ⊆ c.source ∧ _root_.Set.EqOn Q c V := by
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1)
  let e := OpenPartialHomeomorph.halfBallCorner 1 v
  let d := (c.symm.toOpenPartialHomeomorph.trans L.toHomeomorph.toOpenPartialHomeomorph).trans e
  have hsource (x : EuclideanSpace ℝ (Fin (m + 1))) (hx : x ∈ _root_.Metric.closedBall 0 1) :
      L.symm (DifferentialGeometry.Topology.Handle.halfBallRounding 1 ε (x, 0)) ∈ c.source := by
    have hraw : L.symm (x, 0) ∈ c.source := hK ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩
    by_cases hx0 : x = 0
    · subst x
      simpa only [DifferentialGeometry.Topology.Handle.halfBallRounding_zero_fst] using hraw
    · have hxs : (x, (0 : ℝ)) ∈ e.source := hx0
      have hdt : e (x, 0) ∈ d.target := by
        refine ⟨e.map_source hxs, ?_⟩
        change (True ∧ L.symm (e.symm (e (x, 0))) ∈ c.source)
        rwa [e.left_inv hxs, true_and]
      have hq : 0 ≤ (e (x, 0)).2.1 ∧ 0 ≤ (e (x, 0)).2.2 := by
        have hn := mem_closedBall_zero_iff.mp hx
        change 0 ≤ 1 ^ 2 - ‖x‖ ^ 2 - 0 ^ 2 ∧ 0 ≤ (0 : ℝ)
        exact ⟨by nlinarith [norm_nonneg x], le_rfl⟩
      have hnew := d.smoothAbsQuadrantMap_coordinate_mem_target hε hstrip hdt hq
      have hnewsource : L.symm (e.symm ((e (x, 0)).1,
          Real.smoothAbs.quadrantMap ε (e (x, 0)).2)) ∈ c.source := hnew.2.2
      have heq := DifferentialGeometry.Topology.Handle.halfBallRounding_halfBallCorner_symm
        1 ε v (e.map_source hxs)
      change DifferentialGeometry.Topology.Handle.halfBallRounding 1 ε (e.symm (e (x, 0))) =
        e.symm ((e (x, 0)).1, Real.smoothAbs.quadrantMap ε (e (x, 0)).2) at heq
      rw [e.left_inv hxs] at heq
      rwa [← heq] at hnewsource
  obtain ⟨D₀, ψ, hD₀, _, hψs, hψ⟩ :=
    DifferentialGeometry.Topology.Handle.exists_partialDiffeomorph_roundedHalfBall_disk (m + 1) hε hsmall
  obtain ⟨Q, hQ, V, hV, hKV, hVc, hQV⟩ :=
    c.exists_diffeomorph_eqOn_neighborhood_of_boundary_disk m D₀ D hD₀ hD hc ψ hψs (by
      intro x hx
      rw [hψ x (hψs hx)]
      exact hsource x hx)
  refine ⟨Q, hQ, V, hV, ?_, hVc, hQV⟩
  rintro z ⟨x, hx, rfl⟩
  apply hKV
  refine ⟨(ψ x).val, ⟨ψ x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
  exact hψ x (hψs hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.exists_diffeomorph_roundedHalfBall_comparison then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.exists_diffeomorph_roundedHalfBall_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.exists_diffeomorph_roundedHalfBall_comparison ``Submission.PartialDiffeomorph.exists_diffeomorph_roundedHalfBall_comparison

end PartialDiffeomorph
