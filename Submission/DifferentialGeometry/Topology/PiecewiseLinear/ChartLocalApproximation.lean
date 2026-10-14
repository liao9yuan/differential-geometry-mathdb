/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology _root_.Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem Moise341.exists_isPLHomeomorphInto_dist_lt_of_mapsTo_chart (h341 : Moise341)
    {M : Type*} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [HasGroupoid M (plGroupoid 3)] {C : Set (EuclideanSpace ℝ (Fin 3))} (hC : IsPLBall 3 C)
    {h : EuclideanSpace ℝ (Fin 3) → M} (hcont : ContinuousOn h C) (hinj : _root_.Set.InjOn h C)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (he : e ∈ (plGroupoid 3).maximalAtlas M) (hmap : _root_.Set.MapsTo h C e.source)
    {τ : EuclideanSpace ℝ (Fin 3) → ℝ} (hτ : ContinuousOn τ C) (hτpos : ∀ x ∈ C, 0 < τ x) :
    ∃ f : EuclideanSpace ℝ (Fin 3) → M, IsPLHomeomorphInto 3 f C ∧ _root_.Set.MapsTo f C e.source ∧
      ∀ x ∈ C, _root_.Dist.dist (f x) (h x) < τ x := by
  classical
  have hCcompact : IsCompact C := hC.isPolyhedron.isCompact
  obtain ⟨ε, hε, hεle⟩ := exists_pos_forall_le_of_continuousOn hCcompact hτ hτpos
  have hφc : ContinuousOn (e ∘ h) C := e.continuousOn.comp hcont hmap
  have himg : IsCompact ((e ∘ h) '' C) := hCcompact.image_of_continuousOn hφc
  have hsub : (e ∘ h) '' C ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hmap hx)
  obtain ⟨r, hr, hrsub⟩ := himg.exists_thickening_subset_open e.open_target hsub
  set D := _root_.Metric.cthickening (r / 2) ((e ∘ h) '' C) with hD
  have hDsub : D ⊆ e.target :=
    (_root_.Metric.cthickening_subset_thickening' hr (by linarith) _).trans hrsub
  have hDcompact : IsCompact D := himg.cthickening
  have hsymmc : ContinuousOn e.symm D := e.symm.continuousOn.mono hDsub
  obtain ⟨δ, hδ, hδclose⟩ :=
    Metric.uniformContinuousOn_iff.mp
      (hDcompact.uniformContinuousOn_of_continuous hsymmc) ε hε
  obtain ⟨g, hg, hgdist⟩ :=
    h341 C hC (e ∘ h) hφc (e.injOn.comp hinj hmap) (_root_.Min.min δ (r / 2)) (lt_min hδ (by linarith))
  have hgmem : ∀ x ∈ C, g x ∈ D := by
    intro x hx
    refine _root_.Metric.mem_cthickening_of_dist_le _ _ (r / 2) _ ⟨x, hx, rfl⟩ ?_
    exact le_of_lt ((hgdist x hx).trans_le (min_le_right _ _))
  have hφmem : ∀ x ∈ C, (e ∘ h) x ∈ D := fun x hx =>
    _root_.Metric.self_subset_cthickening _ ⟨x, hx, rfl⟩
  have hgtarget : _root_.Set.MapsTo g C e.target := fun x hx => hDsub (hgmem x hx)
  have hmapsTo : _root_.Set.MapsTo (fun y => e.symm (g y)) C e.source := fun x hx =>
    e.map_target (hgtarget hx)
  have hPL : IsPLOn 3 3 (fun y => e.symm (g y)) C := by
    rw [isPLOn_iff_isPiecewiseAffineOn_comp_chart e he hmapsTo]
    refine hg.isPiecewiseAffineOn.congr fun x hx => ?_
    exact e.right_inv (hgtarget hx)
  have hfinj : _root_.Set.InjOn (fun y => e.symm (g y)) C := by
    intro x hx y hy hxy
    refine hg.bijOn.injOn hx hy ?_
    rw [← e.right_inv (hgtarget hx), ← e.right_inv (hgtarget hy)]
    exact congrArg e hxy
  refine ⟨fun y => e.symm (g y), hPL.isPLHomeomorphInto hCcompact hfinj, hmapsTo, ?_⟩
  intro x hx
  have hd := hδclose (g x) (hgmem x hx) ((e ∘ h) x) (hφmem x hx)
    ((hgdist x hx).trans_le (min_le_left _ _))
  simp only [Function.comp_apply, e.left_inv (hmap hx)] at hd
  exact hd.trans_le (hεle x hx)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.Moise341
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Moise341.exists_isPLHomeomorphInto_dist_lt_of_mapsTo_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Moise341.exists_isPLHomeomorphInto_dist_lt_of_mapsTo_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Moise341.exists_isPLHomeomorphInto_dist_lt_of_mapsTo_chart ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Moise341.exists_isPLHomeomorphInto_dist_lt_of_mapsTo_chart

end DifferentialGeometry.Topology.PiecewiseLinear
