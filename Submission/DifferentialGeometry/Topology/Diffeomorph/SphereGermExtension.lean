import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Sphere
import Submission.DifferentialGeometry.Topology.Diffeomorph.SphereExtension
import Submission.DifferentialGeometry.Topology.Diffeomorph.SphereGerm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph
    (A : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hsource : _root_.Metric.sphere (0 : E3) 1 ⊆ A.source)
    (himage : A '' _root_.Metric.sphere (0 : E3) 1 = _root_.Metric.sphere (0 : E3) 1)
    (hmap : _root_.Set.MapsTo A (_root_.Metric.closedBall (0 : E3) 1 ∩ A.source) (_root_.Metric.closedBall (0 : E3) 1)) :
    ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      D '' _root_.Metric.closedBall (0 : E3) 1 = _root_.Metric.closedBall (0 : E3) 1 ∧
      ∃ V : Set E3, IsOpen V ∧ _root_.Metric.sphere (0 : E3) 1 ⊆ V ∧ V ⊆ A.source ∧ _root_.Set.EqOn D A V := by
  obtain ⟨f, hf, _hfi⟩ := exists_sphere_diffeomorph_of_partialDiffeomorph A hsource himage
  obtain ⟨D, hnorm, hD⟩ := exists_norm_preserving_diffeomorph_extension_sphere f
  let B := A.trans D.symm.toPartialDiffeomorph
  have hBsource : B.source = A.source := by
    ext x
    change (x ∈ A.source ∧ A x ∈ (_root_.Set.univ : Set E3)) ↔ x ∈ A.source
    exact ⟨And.left, fun hx => ⟨hx, _root_.Set.mem_univ _⟩⟩
  have hBfixed : _root_.Set.EqOn B id (_root_.Metric.sphere (0 : E3) 1) := by
    intro x hx
    change D.symm (A x) = x
    rw [← hf ⟨x, hx⟩, ← hD ⟨x, hx⟩]
    exact D.symm_apply_apply x
  have hDinvnorm (x : E3) : ‖D.symm x‖ = ‖x‖ := by
    rw [← hnorm (D.symm x), D.apply_symm_apply]
  have hBmap : _root_.Set.MapsTo B (_root_.Metric.closedBall (0 : E3) 1 ∩ B.source) (_root_.Metric.closedBall (0 : E3) 1) := by
    intro x hx
    change D.symm (A x) ∈ _root_.Metric.closedBall (0 : E3) 1
    rw [mem_closedBall_zero_iff, hDinvnorm]
    have hh := hmap ⟨hx.1, hx.2.1⟩
    exact mem_closedBall_zero_iff.mp hh
  obtain ⟨V, hVo, hSV, hVB, H, _hH, _hHi, _hH0, hH, _hfixed, hball, _hsupport⟩ :=
    B.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood zero_lt_one
      (by rw [hBsource]; exact hsource) hBfixed hBmap isOpen_univ (_root_.Set.subset_univ _)
  have hDball : D '' _root_.Metric.closedBall (0 : E3) 1 = _root_.Metric.closedBall (0 : E3) 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [mem_closedBall_zero_iff, hnorm] using hx
    · intro hy
      exact ⟨D.symm y, by simpa only [mem_closedBall_zero_iff, hDinvnorm] using hy, D.apply_symm_apply y⟩
  refine ⟨(H 1).trans D, ?_, V, hVo, hSV, hVB.trans hBsource.le, ?_⟩
  · change (D ∘ H 1) '' _root_.Metric.closedBall (0 : E3) 1 = _
    rw [_root_.Set.image_comp, hball 1 ⟨zero_le_one, le_rfl⟩, hDball]
  · intro x hx
    change D (H 1 x) = A x
    rw [hH hx]
    exact D.apply_symm_apply (A x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph

theorem exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph_of_compl_ball
    (A : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hsource : _root_.Metric.sphere (0 : E3) 1 ⊆ A.source)
    (himage : A '' _root_.Metric.sphere (0 : E3) 1 = _root_.Metric.sphere (0 : E3) 1)
    (hmap : _root_.Set.MapsTo A ((_root_.Metric.ball (0 : E3) 1)ᶜ ∩ A.source) (_root_.Metric.ball (0 : E3) 1)ᶜ) :
    ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      D '' _root_.Metric.closedBall (0 : E3) 1 = _root_.Metric.closedBall (0 : E3) 1 ∧
      ∃ V : Set E3, IsOpen V ∧ _root_.Metric.sphere (0 : E3) 1 ⊆ V ∧ V ⊆ A.source ∧ _root_.Set.EqOn D A V := by
  obtain ⟨f, hf, _hfi⟩ := exists_sphere_diffeomorph_of_partialDiffeomorph A hsource himage
  obtain ⟨D, hnorm, hD⟩ := exists_norm_preserving_diffeomorph_extension_sphere f
  let B := A.trans D.symm.toPartialDiffeomorph
  have hBsource : B.source = A.source := by
    ext x
    change (x ∈ A.source ∧ A x ∈ (_root_.Set.univ : Set E3)) ↔ x ∈ A.source
    exact ⟨And.left, fun hx => ⟨hx, _root_.Set.mem_univ _⟩⟩
  have hBfixed : _root_.Set.EqOn B id (_root_.Metric.sphere (0 : E3) 1) := by
    intro x hx
    change D.symm (A x) = x
    rw [← hf ⟨x, hx⟩, ← hD ⟨x, hx⟩]
    exact D.symm_apply_apply x
  have hDinvnorm (x : E3) : ‖D.symm x‖ = ‖x‖ := by
    rw [← hnorm (D.symm x), D.apply_symm_apply]
  have hBmap : _root_.Set.MapsTo B ((_root_.Metric.ball (0 : E3) 1)ᶜ ∩ B.source) (_root_.Metric.ball (0 : E3) 1)ᶜ := by
    intro x hx
    change D.symm (A x) ∉ _root_.Metric.ball (0 : E3) 1
    rw [mem_ball_zero_iff, hDinvnorm]
    have hh := hmap ⟨hx.1, hx.2.1⟩
    intro hlt
    exact hh (mem_ball_zero_iff.mpr hlt)
  obtain ⟨V, hVo, hSV, hVB, H, _hH, _hHi, _hH0, hH, _hfixed, hball, _hsupport⟩ :=
    B.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood_of_mapsTo_compl_ball zero_lt_one
      (by rw [hBsource]; exact hsource) hBfixed hBmap isOpen_univ (_root_.Set.subset_univ _)
  have hDball : D '' _root_.Metric.closedBall (0 : E3) 1 = _root_.Metric.closedBall (0 : E3) 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [mem_closedBall_zero_iff, hnorm] using hx
    · intro hy
      exact ⟨D.symm y, by simpa only [mem_closedBall_zero_iff, hDinvnorm] using hy, D.apply_symm_apply y⟩
  refine ⟨(H 1).trans D, ?_, V, hVo, hSV, hVB.trans hBsource.le, ?_⟩
  · change (D ∘ H 1) '' _root_.Metric.closedBall (0 : E3) 1 = _
    rw [_root_.Set.image_comp, hball 1 ⟨zero_le_one, le_rfl⟩, hDball]
  · intro x hx
    change D (H 1 x) = A x
    rw [hH hx]
    exact D.apply_symm_apply (A x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph_of_compl_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph_of_compl_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph_of_compl_ball ``Submission.DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph_of_compl_ball

end DifferentialGeometry.Topology.Manifold

end

end
