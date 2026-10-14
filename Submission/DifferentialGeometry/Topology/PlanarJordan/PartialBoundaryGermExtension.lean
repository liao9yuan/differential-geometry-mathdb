/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PlanarJordan.BoundaryGermExtension
import Submission.DifferentialGeometry.Topology.PlanarJordan.CompactRegion
import Submission.DifferentialGeometry.Topology.Homeomorph.SubsetImage
import Submission.DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import Submission.DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.PlanarJordan

open _root_.Submission.Schoenflies (Plane)

theorem exists_diffeomorph_eqOn_neighborhood_of_localDiffeomorphOn
    (e : OpenPartialHomeomorph Plane Plane)
    {γ : AddCircle (1 : ℝ) → Plane}
    (hγ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) ∞ γ)
    (hsource : closure (Schoenflies.inside (_root_.Set.range γ)) ⊆ e.source)
    {U : Set Plane} (hU : IsOpen U) (hcurve : _root_.Set.range γ ⊆ U) (hUs : U ⊆ e.source)
    (hlocal : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ e U) :
    ∃ Q : Plane ≃ₘ[ℝ] Plane,
      Q '' closure (Schoenflies.inside (_root_.Set.range γ)) =
        e '' closure (Schoenflies.inside (_root_.Set.range γ)) ∧
      ∃ V : Set Plane, IsOpen V ∧ _root_.Set.range γ ⊆ V ∧ V ⊆ U ∧ _root_.Set.EqOn Q e V := by
  obtain ⟨c, hcs, -, hceq⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn
      hU hlocal (e.injOn.mono hUs)
  have hγc : _root_.Set.range γ ⊆ c.source := by rw [hcs]; exact hcurve
  let δ : AddCircle (1 : ℝ) → Plane := c ∘ γ
  have hδ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) ∞ δ :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph c hγ hγc
  let C := closure (Schoenflies.inside (_root_.Set.range γ))
  obtain ⟨D, hDsphere, -, hDball⟩ := smooth_schoenflies hγ
  have hC : IsCompact C := by
    rw [show C = D '' _root_.Metric.closedBall (0 : Plane) 1 from hDball.symm]
    exact (_root_.ProperSpace.isCompact_closedBall (0 : Plane) 1).image D.continuous
  have hfr : frontier C = _root_.Set.range γ := by
    rw [show C = D '' _root_.Metric.closedBall (0 : Plane) 1 from hDball.symm]
    change frontier (D.toHomeomorph '' _root_.Metric.closedBall (0 : Plane) 1) = _root_.Set.range γ
    rw [← D.toHomeomorph.image_frontier, frontier_closedBall _ one_ne_zero]
    exact hDsphere
  have hne : (interior C).Nonempty := by
    rw [show C = D '' _root_.Metric.closedBall (0 : Plane) 1 from hDball.symm]
    change (interior (D.toHomeomorph '' _root_.Metric.closedBall (0 : Plane) 1)).Nonempty
    rw [← D.toHomeomorph.image_interior, interior_closedBall _ one_ne_zero]
    exact (nonempty_ball.mpr one_pos).image D
  have hδrange : _root_.Set.range δ = e '' _root_.Set.range γ := by
    rw [show δ = (c : Plane → Plane) ∘ γ from rfl, _root_.Set.range_comp]
    exact _root_.Set.image_congr (fun x _ => congrFun hceq x)
  have htargetfr : frontier (e '' C) = _root_.Set.range δ := by
    rw [← e.image_frontier_of_isCompact hC hsource, hfr, hδrange]
  have htargetC : IsCompact (e '' C) :=
    hC.image_of_continuousOn (e.continuousOn.mono hsource)
  have htargetne : (interior (e '' C)).Nonempty := by
    rw [← e.image_interior_of_subset_source hsource]
    exact hne.image e
  have htargetJ : Schoenflies.IsJordanCurve (frontier (e '' C)) := by
    rw [htargetfr]
    exact isJordanCurve_range_of_isEmbedding_addCircle one_ne_zero hδ.isEmbedding
  have htarget : closure (Schoenflies.inside (_root_.Set.range δ)) = e '' C := by
    rw [← htargetfr]
    exact closure_inside_frontier_eq_of_isCompact htargetC htargetJ htargetne
  have hc : c.toOpenPartialHomeomorph.IsImage C
      (closure (Schoenflies.inside (_root_.Set.range δ))) := by
    intro x hx
    change c x ∈ closure (Schoenflies.inside (_root_.Set.range δ)) ↔ x ∈ C
    rw [htarget, congrFun hceq x]
    exact e.isImage_image_of_subset_source hsource (hUs (hcs ▸ hx))
  obtain ⟨Q, -, hQ, V, hV, hγV, hVc, hQV⟩ :=
    exists_diffeomorph_eqOn_neighborhood_of_jordan_curve hγ hδ c hc hγc
  exact ⟨Q, hQ.trans htarget, V, hV, hγV,
    fun x hx => hcs ▸ hVc hx, fun x hx => (hQV hx).trans (congrFun hceq x)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_diffeomorph_eqOn_neighborhood_of_localDiffeomorphOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_diffeomorph_eqOn_neighborhood_of_localDiffeomorphOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_diffeomorph_eqOn_neighborhood_of_localDiffeomorphOn ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_diffeomorph_eqOn_neighborhood_of_localDiffeomorphOn

end DifferentialGeometry.Topology.PlanarJordan
