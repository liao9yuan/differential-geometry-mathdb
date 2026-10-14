import Submission.DifferentialGeometry.Topology.Circle.GermExtension
import Submission.DifferentialGeometry.Topology.PlanarJordan.SmoothSchoenflies

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.PlanarJordan

theorem exists_diffeomorph_eqOn_neighborhood_of_jordan_curve
    {γ₀ γ₁ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ₀ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ₀)
    (hγ₁ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ₁)
    (c : PartialDiffeomorph 𝓘(ℝ, Schoenflies.Plane) 𝓘(ℝ, Schoenflies.Plane)
      Schoenflies.Plane Schoenflies.Plane ∞)
    (hc : c.toOpenPartialHomeomorph.IsImage
      (closure (Schoenflies.inside (_root_.Set.range γ₀))) (closure (Schoenflies.inside (_root_.Set.range γ₁))))
    (hsource : _root_.Set.range γ₀ ⊆ c.source) :
    ∃ Q : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane,
      Q '' _root_.Set.range γ₀ = _root_.Set.range γ₁ ∧
      Q '' closure (Schoenflies.inside (_root_.Set.range γ₀)) = closure (Schoenflies.inside (_root_.Set.range γ₁)) ∧
      ∃ V : Set Schoenflies.Plane, IsOpen V ∧
        range γ₀ ⊆ V ∧ V ⊆ c.source ∧ _root_.Set.EqOn Q c V := by
  let _ : Fact (Module.finrank ℝ Schoenflies.Plane = 1 + 1) := ⟨by simp [Schoenflies.Plane]⟩
  obtain ⟨D₀, hD₀sphere, _, hD₀ball⟩ := smooth_schoenflies hγ₀
  obtain ⟨D₁, hD₁sphere, _, hD₁ball⟩ := smooth_schoenflies hγ₁
  let F := (D₀.toPartialDiffeomorph.trans c).trans D₁.symm.toPartialDiffeomorph
  have hFs : F.source = D₀ ⁻¹' c.source := by
    ext x
    change ((x ∈ (_root_.Set.univ : Set Schoenflies.Plane) ∧ D₀ x ∈ c.source) ∧
      c (D₀ x) ∈ (_root_.Set.univ : Set Schoenflies.Plane)) ↔ _
    simp only [_root_.Set.mem_univ, true_and, and_true, _root_.Set.mem_preimage]
  have hF (x : Schoenflies.Plane) : F x = D₁.symm (c (D₀ x)) := rfl
  have h₀ (x : Schoenflies.Plane) :
      D₀ x ∈ closure (Schoenflies.inside (_root_.Set.range γ₀)) ↔ x ∈ _root_.Metric.closedBall 0 1 := by
    rw [← hD₀ball]
    exact D₀.injective.mem_set_image
  have h₁ (x : Schoenflies.Plane) :
      D₁.symm x ∈ _root_.Metric.closedBall 0 1 ↔ x ∈ closure (Schoenflies.inside (_root_.Set.range γ₁)) := by
    rw [← hD₁ball]
    exact (Set.mem_image_iff_of_inverse D₁.symm_apply_apply D₁.apply_symm_apply).symm
  have hFi : F.toOpenPartialHomeomorph.IsImage (_root_.Metric.closedBall 0 1) (_root_.Metric.closedBall 0 1) := by
    intro x hx
    change F x ∈ _root_.Metric.closedBall 0 1 ↔ x ∈ _root_.Metric.closedBall 0 1
    rw [hF, h₁]
    have hx' : D₀ x ∈ c.source := by
      have hs : x ∈ F.source := hx
      rwa [hFs] at hs
    exact (hc hx').trans (h₀ x)
  have hFsource : _root_.Metric.sphere (0 : Schoenflies.Plane) 1 ⊆ F.source := by
    intro x hx
    rw [hFs]
    exact hsource (hD₀sphere.subset (_root_.Set.mem_image_of_mem D₀ hx))
  have hFboundary : _root_.Set.MapsTo F (_root_.Metric.sphere (0 : Schoenflies.Plane) 1) (_root_.Metric.sphere 0 1) := by
    intro x hx
    have h := hFi.frontier (hFsource hx)
    rw [frontier_closedBall _ one_ne_zero] at h
    exact h.mpr hx
  have hFside : _root_.Set.MapsTo F (_root_.Metric.closedBall (0 : Schoenflies.Plane) 1 ∩ F.source) (_root_.Metric.closedBall 0 1) :=
    fun _ hx => (hFi hx.2).mpr hx.1
  obtain ⟨q, hqball, U, hU, hSU, hUF, heq⟩ :=
    F.exists_diffeomorph_eqOn_circle_neighborhood hFsource hFboundary hFside
  let Q := (D₀.symm.trans q).trans D₁
  have hQball : Q '' closure (Schoenflies.inside (_root_.Set.range γ₀)) =
      closure (Schoenflies.inside (_root_.Set.range γ₁)) := by
    rw [← hD₀ball, ← hD₁ball]
    change (D₁ ∘ q ∘ D₀.symm) '' (D₀ '' _root_.Metric.closedBall 0 1) = D₁ '' _root_.Metric.closedBall 0 1
    rw [_root_.Set.image_comp, _root_.Set.image_comp, _root_.Set.image_image D₀.symm D₀]
    simp only [D₀.symm_apply_apply, _root_.Set.image_id']
    rw [hqball]
  refine ⟨Q, ?_, hQball, D₀ '' U, D₀.toHomeomorph.isOpenMap U hU, ?_, ?_, ?_⟩
  · have hfr₀ : frontier (closure (Schoenflies.inside (_root_.Set.range γ₀))) = _root_.Set.range γ₀ := by
      rw [← hD₀ball]
      change frontier (D₀.toHomeomorph '' _root_.Metric.closedBall 0 1) = _
      rw [← D₀.toHomeomorph.image_frontier, frontier_closedBall _ one_ne_zero]
      exact hD₀sphere
    have hfr₁ : frontier (closure (Schoenflies.inside (_root_.Set.range γ₁))) = _root_.Set.range γ₁ := by
      rw [← hD₁ball]
      change frontier (D₁.toHomeomorph '' _root_.Metric.closedBall 0 1) = _
      rw [← D₁.toHomeomorph.image_frontier, frontier_closedBall _ one_ne_zero]
      exact hD₁sphere
    change Q.toHomeomorph '' _root_.Set.range γ₀ = _root_.Set.range γ₁
    rw [← hfr₀, Q.toHomeomorph.image_frontier]
    exact (congrArg frontier hQball).trans hfr₁
  · rw [← hD₀sphere]
    exact _root_.Set.image_mono hSU
  · rintro x ⟨y, hy, rfl⟩
    have h := hUF hy
    rwa [hFs] at h
  · rintro x ⟨y, hy, rfl⟩
    change D₁ (q (D₀.symm (D₀ y))) = c (D₀ y)
    rw [D₀.symm_apply_apply, heq hy, hF, D₁.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_diffeomorph_eqOn_neighborhood_of_jordan_curve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_diffeomorph_eqOn_neighborhood_of_jordan_curve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_diffeomorph_eqOn_neighborhood_of_jordan_curve ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_diffeomorph_eqOn_neighborhood_of_jordan_curve

end DifferentialGeometry.Topology.PlanarJordan
