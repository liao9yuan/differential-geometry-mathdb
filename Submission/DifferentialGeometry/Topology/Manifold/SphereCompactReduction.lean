/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Manifold.SurfacePointSmoothing
import Submission.DifferentialGeometry.Topology.Manifold.PuncturedSphereChart
import Submission.DifferentialGeometry.Topology.PlanarJordan.PlanarArcSmoothing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric _root_.Submission.Metric
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace Homeomorph

open _root_.Submission.Schoenflies (Plane)

variable {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
  [IsManifold 𝓘(ℝ, Plane) ∞ S]

theorem exists_smooth_outside_rectangle_sphere
    (h : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ S)
    (p : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ g : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ S, g p = h p ∧
      ∃ a : PartialDiffeomorph (𝓡 2) (𝓡 2)
        (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) Plane ∞,
        a.source = {p}ᶜ ∧ a.target = _root_.Set.univ ∧ ∃ R > 0,
          IsLocalDiffeomorphOn (𝓡 2) (𝓡 2) ∞ g
            (a.symm ''
              DifferentialGeometry.Topology.PlanarJordan.planeOpenRect (-R) R (-R) R)ᶜ := by
  obtain ⟨_, -, -, g, -, hgp, hglocal, -⟩ :=
    h.exists_smooth_at isOpen_univ (_root_.Set.mem_univ p)
  obtain ⟨φ, hpφ, hφ⟩ := hglocal
  obtain ⟨a, has, hat⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_smooth_punctured_sphere_chart 2 p
  let C := φ.sourceᶜ
  have hC : IsCompact C := φ.open_source.isClosed_compl.isCompact
  have hCa : C ⊆ a.source := by
    intro x hx
    rw [has]
    intro hxp
    have hxp' : x = p := hxp
    exact hx (hxp'.symm ▸ hpφ)
  have hD : IsCompact (a '' C) :=
    hC.image_of_continuousOn (a.toOpenPartialHomeomorph.continuousOn.mono hCa)
  obtain ⟨R, hR, hDR⟩ := hD.isBounded.subset_ball_lt 0 (0 : Plane)
  have hball : _root_.Metric.ball (0 : Plane) R ⊆
      DifferentialGeometry.Topology.PlanarJordan.planeOpenRect (-R) R (-R) R := by
    intro v hv
    have h0 := (DifferentialGeometry.Topology.PlanarJordan.planeAbsSub_le_dist v 0 0).trans_lt
      (mem_ball.mp hv)
    have h1 := (DifferentialGeometry.Topology.PlanarJordan.planeAbsSub_le_dist v 0 1).trans_lt
      (mem_ball.mp hv)
    simp only [PiLp.zero_apply, sub_zero, abs_lt] at h0 h1
    exact ⟨h0.1, h0.2, h1.1, h1.2⟩
  refine ⟨g, hgp, a, has, hat, R, hR, ?_⟩
  intro x
  have hxφ : (x : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∈ φ.source := by
    by_contra hx
    exact x.property ⟨a x, hball (hDR ⟨x, hx, rfl⟩), a.left_inv (hCa hx)⟩
  exact ⟨φ, hxφ, hφ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.exists_smooth_outside_rectangle_sphere then
    throwError "Refusing to shadow existing declaration Homeomorph.exists_smooth_outside_rectangle_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.exists_smooth_outside_rectangle_sphere ``Submission.Homeomorph.exists_smooth_outside_rectangle_sphere

end Homeomorph
