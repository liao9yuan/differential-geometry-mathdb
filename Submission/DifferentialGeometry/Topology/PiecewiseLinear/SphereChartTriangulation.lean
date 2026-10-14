/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Manifold.SphereCompactReduction
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PartialChartSubdivision
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PlanarRectTriangulation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric _root_.Submission.Metric
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace Homeomorph
open _root_.Homeomorph

open _root_.Submission.Schoenflies (Plane)
open _root_.Submission.DifferentialGeometry.Topology.PiecewiseLinear
open _root_.Submission.DifferentialGeometry.Topology.PlanarJordan

variable {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
  [IsManifold (𝓡 2) ∞ S]

open _root_.Homeomorph in
theorem exists_finite_chart_triangulation_sphere
    (h : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ S)
    (p : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ g : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ S, g p = h p ∧
      ∃ a : PartialDiffeomorph (𝓡 2) (𝓡 2)
        (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) Plane ∞,
        a.source = {p}ᶜ ∧ a.target = _root_.Set.univ ∧ ∃ R > 0,
          IsLocalDiffeomorphOn (𝓡 2) (𝓡 2) ∞ g
            (a.symm '' planeOpenRect (-R) R (-R) R)ᶜ ∧
          ∃ K : Geometry.SimplicialComplex ℝ Plane,
            K.faces.Finite ∧ K.space = planeRect (-R) R (-R) R ∧
            ∀ s ∈ K.faces, ∃ y : S,
              g '' (a.symm '' (⋃ v ∈ s, closedStar K v)) ⊆
                (extChartAtPartialDiffeomorph (𝓡 2) ∞ y).source := by
  obtain ⟨g, hgp, a, has, hat, R, hR, hlocal⟩ :=
    h.exists_smooth_outside_rectangle_sphere p
  obtain ⟨K, hfinite, hspace⟩ := exists_simplicialComplex_planeRect (-R) R (-R) R
  let _ : Finite K.faces := hfinite.to_subtype
  let e := a.symm.toOpenPartialHomeomorph.trans g.toOpenPartialHomeomorph
  have hKe : K.space ⊆ e.source := by
    intro v _
    exact ⟨by change v ∈ a.target; rw [hat]; trivial, trivial⟩
  obtain ⟨L, hL, hLfinite, hstars⟩ :=
    exists_isSubdivision_closedStars_subset_chart_preimages K e hKe
  refine ⟨g, hgp, a, has, hat, R, hR, hlocal, L, hLfinite, hL.space_eq.trans hspace, ?_⟩
  intro s hs
  obtain ⟨y, -, hy⟩ := hstars s hs
  refine ⟨y, ?_⟩
  rintro z ⟨x, ⟨v, hv, rfl⟩, rfl⟩
  exact hy ⟨v, hv, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.exists_finite_chart_triangulation_sphere then
    throwError "Refusing to shadow existing declaration Homeomorph.exists_finite_chart_triangulation_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.exists_finite_chart_triangulation_sphere ``Submission.Homeomorph.exists_finite_chart_triangulation_sphere

end Homeomorph
