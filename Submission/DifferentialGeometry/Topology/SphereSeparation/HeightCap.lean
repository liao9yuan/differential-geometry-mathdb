import Submission.DifferentialGeometry.Topology.SphereSeparation.HeightExtremum
import Submission.DifferentialGeometry.Topology.Morse.ExtremumIndex
import Submission.DifferentialGeometry.Topology.Morse.QuadraticSublevel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_global_height_preserving_minimum_cap {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) ∞ e)
    {p : SphereTwo}
    (hnd : IsNondegenerateCriticalPointAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (fun x => e x 2) p)
    (hmin : ∀ x, x ≠ p → e p 2 < e x 2) :
    ∃ R : ℝ, 0 < R ∧
      ∃ χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) SphereTwo ∞,
        ∃ Φ : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
          _root_.Metric.closedBall 0 R ⊆ χ.source ∧ χ 0 = p ∧ (∀ z, Φ z 2 = z 2) ∧
          (∀ y ∈ χ.source,
            e (χ y) 2 = e p 2 + 1 / 2 * ‖y‖ ^ 2 ∧
            Φ ((EuclideanSpace.equivProdLast 2).symm (y, e p 2 + 1 / 2 * ‖y‖ ^ 2)) = e (χ y)) ∧
          ∀ r : ℝ, 0 ≤ r → r ≤ R →
            χ '' _root_.Metric.closedBall 0 r = {x | e x 2 ≤ e p 2 + 1 / 2 * r ^ 2} ∧
            χ '' _root_.Metric.sphere 0 r = {x | e x 2 = e p 2 + 1 / 2 * r ^ 2} := by
  have hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) ∞ (fun x => e x 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  have hle (x : SphereTwo) : e p 2 ≤ e x 2 := by
    by_cases hx : x = p
    · exact hx ▸ le_rfl
    · exact (hmin x hx).le
  have hindex := minimum_morse_index_eq_zero hf hnd (Filter.Eventually.of_forall hle)
  obtain ⟨α, hα, r₀, hr₀, χ, Φ, hsource, hχ0, hheight, hnormal⟩ :=
    exists_global_height_preserving_extremum_normal_form he hnd (Or.inl hindex)
  have hαone : α = 1 := by
    rcases hα with h | h
    · exact h
    · let y : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 (r₀ / 2)
      have hyn : ‖y‖ = r₀ / 2 := by
        simp [y, EuclideanSpace.single, PiLp.norm_single, abs_of_pos hr₀]
      have hys : y ∈ χ.source := by
        rw [hsource, _root_.Metric.mem_ball, dist_zero_right, hyn]
        exact half_lt_self hr₀
      have hn := (hnormal y hys).1
      rw [h, hyn] at hn
      have hm := hle (χ y)
      nlinarith [sq_pos_of_pos (half_pos hr₀)]
  have hzero : (0 : EuclideanSpace ℝ (Fin 2)) ∈ χ.source := hsource ▸ _root_.Metric.mem_ball_self hr₀
  have hχ0' : χ.toOpenPartialHomeomorph 0 = p := hχ0
  obtain ⟨R, hR, hRs, hlevels⟩ :=
    χ.toOpenPartialHomeomorph.exists_closedBall_image_sublevel_of_unique_minimum
    hzero hf.continuous (by norm_num : (0 : ℝ) < 1)
    (fun y hy => by
      change e (χ y) 2 = e (χ 0) 2 + 1 / 2 * ‖y‖ ^ 2
      simpa only [hχ0, hαone] using (hnormal y hy).1)
    (by simpa only [hχ0'] using hmin)
  refine ⟨R, hR, χ, Φ, hRs, hχ0, hheight, ?_, ?_⟩
  · simpa only [hαone] using hnormal
  · intro r hr hrR
    have h := hlevels r hr hrR
    simp only [hχ0'] at h
    exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_minimum_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_minimum_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_minimum_cap ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_minimum_cap

theorem exists_global_height_preserving_maximum_cap {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) ∞ e)
    {p : SphereTwo}
    (hnd : IsNondegenerateCriticalPointAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (fun x => e x 2) p)
    (hmax : ∀ x, x ≠ p → e x 2 < e p 2) :
    ∃ R : ℝ, 0 < R ∧
      ∃ χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) SphereTwo ∞,
        ∃ Φ : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
          _root_.Metric.closedBall 0 R ⊆ χ.source ∧ χ 0 = p ∧ (∀ z, Φ z 2 = z 2) ∧
          (∀ y ∈ χ.source,
            e (χ y) 2 = e p 2 + (-1) / 2 * ‖y‖ ^ 2 ∧
            Φ ((EuclideanSpace.equivProdLast 2).symm (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) = e (χ y)) ∧
          ∀ r : ℝ, 0 ≤ r → r ≤ R →
            χ '' _root_.Metric.closedBall 0 r = {x | e p 2 + (-1) / 2 * r ^ 2 ≤ e x 2} ∧
            χ '' _root_.Metric.sphere 0 r = {x | e x 2 = e p 2 + (-1) / 2 * r ^ 2} := by
  have hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) ∞ (fun x => e x 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  have hle (x : SphereTwo) : e x 2 ≤ e p 2 := by
    by_cases hx : x = p
    · exact hx ▸ le_rfl
    · exact (hmax x hx).le
  have hindex : sigNeg (chartHessianAt
      (fun y => e ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p).symm y) 2)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p p)) = 2 := by
    simpa using maximum_morse_index_eq_finrank hf hnd (Filter.Eventually.of_forall hle)
  obtain ⟨α, hα, r₀, hr₀, χ, Φ, hsource, hχ0, hheight, hnormal⟩ :=
    exists_global_height_preserving_extremum_normal_form he hnd (Or.inr hindex)
  have hαneg : α = -1 := by
    rcases hα with h | h
    · let y : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 (r₀ / 2)
      have hyn : ‖y‖ = r₀ / 2 := by
        simp [y, EuclideanSpace.single, PiLp.norm_single, abs_of_pos hr₀]
      have hys : y ∈ χ.source := by
        rw [hsource, _root_.Metric.mem_ball, dist_zero_right, hyn]
        exact half_lt_self hr₀
      have hn := (hnormal y hys).1
      rw [h, hyn] at hn
      have hm := hle (χ y)
      nlinarith [sq_pos_of_pos (half_pos hr₀)]
    · exact h
  have hzero : (0 : EuclideanSpace ℝ (Fin 2)) ∈ χ.source := hsource ▸ _root_.Metric.mem_ball_self hr₀
  have hχ0' : χ.toOpenPartialHomeomorph 0 = p := hχ0
  obtain ⟨R, hR, hRs, hlevels⟩ :=
    χ.toOpenPartialHomeomorph.exists_closedBall_image_superlevel_of_unique_maximum
    hzero hf.continuous (by norm_num : (-1 : ℝ) < 0)
    (fun y hy => by
      change e (χ y) 2 = e (χ 0) 2 + (-1) / 2 * ‖y‖ ^ 2
      simpa only [hχ0, hαneg] using (hnormal y hy).1)
    (by simpa only [hχ0'] using hmax)
  refine ⟨R, hR, χ, Φ, hRs, hχ0, hheight, ?_, ?_⟩
  · simpa only [hαneg] using hnormal
  · intro r hr hrR
    have h := hlevels r hr hrR
    simp only [hχ0'] at h
    exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_maximum_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_maximum_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_maximum_cap ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_maximum_cap

end DifferentialGeometry.Topology.SphereSeparation
