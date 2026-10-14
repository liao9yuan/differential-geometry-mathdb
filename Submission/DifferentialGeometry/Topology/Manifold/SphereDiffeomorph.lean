/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Manifold.SurfaceTriangulationSmoothing
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SphereChartTriangulation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace Homeomorph
open _root_.Homeomorph

open _root_.Submission.Schoenflies (Plane)
open _root_.Submission.DifferentialGeometry.Topology.PiecewiseLinear
open _root_.Submission.DifferentialGeometry.Topology.PlanarJordan

variable {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
  [IsManifold (𝓡 2) ∞ S]

open _root_.Homeomorph in
theorem exists_diffeomorph_sphere_eq_at
    (h : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ S)
    (p : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ D : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S, D p = h p := by
  classical
  obtain ⟨g, hgp, a, has, hat, R, hR, hlocal, K, hfinite, hspace, hstars⟩ :=
    h.exists_finite_chart_triangulation_sphere p
  let _ : Finite K.faces := hfinite.to_subtype
  choose y hy using fun s : K.faces => hstars s.val s.property
  let b (s : K.faces) := extChartAtPartialDiffeomorph (𝓡 2) ∞ (y s)
  have hb (s : K.faces) : g '' (a.symm '' convexHull ℝ (s.val : Set Plane)) ⊆ (b s).source := by
    apply Subset.trans (_root_.Set.image_mono (_root_.Set.image_mono ?_)) (hy s)
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces s.property
    intro x hx
    exact mem_iUnion₂.mpr ⟨v, hv, mem_iUnion₂.mpr
      ⟨s.val, ⟨s.property, subset_convexHull ℝ _ hv⟩, hx⟩⟩
  have hconv : Convex ℝ K.space := by
    rw [hspace]
    exact (isHPolytope_planeRect (-R) R (-R) R).convex
  have hKa : K.space ⊆ a.target := by rw [hat]; exact _root_.Set.subset_univ _
  have hinterior : interior K.space = planeOpenRect (-R) R (-R) R := by
    rw [hspace, interior_planeRect (by linarith) (by linarith)]
  obtain ⟨D, hD⟩ := g.exists_diffeomorph_of_planar_triangulation a K hconv hKa b hb
    (by simpa only [hinterior] using hlocal)
  refine ⟨D, (hD ?_).trans hgp⟩
  rintro ⟨v, hv, hvp⟩
  have hp : p ∈ a.source := hvp ▸ a.map_target (hKa (interior_subset hv))
  simp only [has, _root_.Set.mem_compl_iff, _root_.Set.mem_singleton_iff, not_true_eq_false] at hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.exists_diffeomorph_sphere_eq_at then
    throwError "Refusing to shadow existing declaration Homeomorph.exists_diffeomorph_sphere_eq_at"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.exists_diffeomorph_sphere_eq_at ``Submission.Homeomorph.exists_diffeomorph_sphere_eq_at

open _root_.Homeomorph in
theorem nonempty_diffeomorph_sphere
    (h : S ≃ₜ _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Nonempty (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S) := by
  let p : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨D, -⟩ := h.symm.exists_diffeomorph_sphere_eq_at p
  exact ⟨D⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.nonempty_diffeomorph_sphere then
    throwError "Refusing to shadow existing declaration Homeomorph.nonempty_diffeomorph_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.nonempty_diffeomorph_sphere ``Submission.Homeomorph.nonempty_diffeomorph_sphere

end Homeomorph
