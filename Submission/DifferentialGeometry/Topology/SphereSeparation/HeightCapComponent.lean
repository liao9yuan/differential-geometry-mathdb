import Submission.DifferentialGeometry.Topology.SphereSeparation.HeightNormalForm
import Submission.DifferentialGeometry.Topology.Morse.ExtremumIndex
import Submission.DifferentialGeometry.Topology.Morse.QuadraticComponent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric
open _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Topology.Morse
open _root_.Submission.DifferentialGeometry.Topology.Morse.CellAttachment

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_global_height_preserving_local_maximum_cap {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) ∞ e)
    {p : SphereTwo}
    (hnd : IsNondegenerateCriticalPointAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (fun x => e x 2) p)
    (hmax : IsLocalMax (fun x => e x 2) p) :
    ∃ R : ℝ, 0 < R ∧ ∃ t : ℝ, 0 < t ∧
      ∃ χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) SphereTwo ∞,
        ∃ Φ : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
          _root_.Metric.closedBall 0 R ⊆ χ.source ∧ χ 0 = p ∧ (∀ z, Φ z 2 = z 2) ∧
          (∀ y ∈ χ.source,
            e (χ y) 2 = e p 2 + (-1) / 2 * ‖y‖ ^ 2 ∧
            Φ ((EuclideanSpace.equivProdLast 2).symm
              (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) = e (χ y)) ∧
          ((_root_.Metric.closedBall 0 R ×ˢ _root_.Metric.closedBall (e p 2) t) ∩
              _root_.Set.range (fun x => EuclideanSpace.equivProdLast 2 (Φ.symm (e x))) =
            (fun y => (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) '' _root_.Metric.closedBall 0 R) ∧
          ∀ r : ℝ, 0 ≤ r → r ≤ R →
            χ '' _root_.Metric.closedBall 0 r =
              connectedComponentIn {x | e p 2 + (-1) / 2 * r ^ 2 ≤ e x 2} p ∧
            χ '' _root_.Metric.sphere 0 r =
              connectedComponentIn {x | e p 2 + (-1) / 2 * r ^ 2 ≤ e x 2} p ∩
                {x | e x 2 = e p 2 + (-1) / 2 * r ^ 2} := by
  have hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) ∞ (fun x => e x 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  have hindex : sigNeg (chartHessianAt
      (fun y => e ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p).symm y) 2)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p p)) = 2 := by
    simpa using maximum_morse_index_eq_finrank hf hnd hmax
  obtain ⟨R, hR, t, ht, χ, Φ, hsource, hχ0, hheight, hnormal, _, hgraph⟩ :=
    exists_global_height_preserving_normal_neighborhood he 2 le_rfl hnd hindex
  have hquad (y : EuclideanSpace ℝ (Fin 2)) : morseNormalForm (le_refl 2) (e p 2)
      (EuclideanSpace.equiv (Fin 2) ℝ y) = e p 2 + (-1) / 2 * ‖y‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [morseNormalForm, posIdx, negIdx, Fin.sum_univ_two]
    ring
  simp_rw [hquad] at hnormal hgraph
  let χ' := DifferentialGeometry.Topology.PartialDiffeomorph.restrict χ (_root_.Metric.ball 0 R) _root_.Metric.isOpen_ball
  have hsource' : χ'.source = _root_.Metric.ball 0 R :=
    inter_eq_right.mpr (ball_subset_closedBall.trans hsource)
  have hRs : _root_.Metric.closedBall 0 (R / 2) ⊆ χ'.source := by
    rw [hsource']
    exact _root_.Metric.closedBall_subset_ball (half_lt_self hR)
  have hnormal' (y) (hy : y ∈ χ'.source) :
      e (χ' y) 2 = e p 2 + (-1) / 2 * ‖y‖ ^ 2 ∧
      Φ ((EuclideanSpace.equivProdLast 2).symm
        (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) = e (χ' y) := by
    have hn := hnormal y (_root_.Metric.ball_subset_closedBall (hsource' ▸ hy))
    refine ⟨?_, hn⟩
    change e (χ y) 2 = _
    rw [← hn, hheight]
    exact EuclideanSpace.equivProdLast_symm_last (n := 2) _
  have hsmall : _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (R / 2) ⊆ _root_.Metric.closedBall 0 R :=
    _root_.Metric.closedBall_subset_closedBall (half_le_self hR.le)
  have hgraph' : (_root_.Metric.closedBall 0 (R / 2) ×ˢ _root_.Metric.closedBall (e p 2) t) ∩
      _root_.Set.range (fun x => EuclideanSpace.equivProdLast 2 (Φ.symm (e x))) =
        (fun y => (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) '' _root_.Metric.closedBall 0 (R / 2) := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨y, hy, hyz⟩ := hgraph.subset ⟨⟨hsmall hz.1.1, hz.1.2⟩, hz.2⟩
      refine ⟨y, ?_, hyz⟩
      simpa only [← hyz] using hz.1.1
    · rintro z ⟨y, hy, rfl⟩
      have hz := hgraph.symm.subset (_root_.Set.mem_image_of_mem _ (hsmall hy))
      exact ⟨⟨hy, hz.1.2⟩, hz.2⟩
  refine ⟨R / 2, half_pos hR, t, ht, χ', Φ, hRs, hχ0, hheight, hnormal', hgraph', ?_⟩
  intro r hr hrR
  have hrs : _root_.Metric.closedBall 0 r ⊆ χ'.source :=
    (_root_.Metric.closedBall_subset_closedBall hrR).trans hRs
  have hχ0' : χ'.toOpenPartialHomeomorph 0 = p := hχ0
  have hcomponent := χ'.toOpenPartialHomeomorph.closedBall_image_eq_connectedComponentIn_superlevel
    hr (_root_.ProperSpace.isCompact_closedBall 0 r) hrs (by norm_num : (-1 : ℝ) < 0)
    (f := fun x => e x 2) (fun y hy => by
      change e (χ' y) 2 = e (χ' 0) 2 + (-1) / 2 * ‖y‖ ^ 2
      simpa only [show χ' 0 = p from hχ0] using (hnormal' y hy).1)
  change χ' '' _root_.Metric.closedBall 0 r = _ at hcomponent
  simp only [hχ0'] at hcomponent
  change χ' '' _root_.Metric.closedBall 0 r =
    connectedComponentIn {x | e p 2 + (-1) / 2 * r ^ 2 ≤ e x 2} p at hcomponent
  refine ⟨hcomponent, ?_⟩
  rw [← hcomponent]
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨mem_image_of_mem χ' (_root_.Metric.sphere_subset_closedBall hy), ?_⟩
    change e (χ' y) 2 = _
    rw [(hnormal' y (hrs (_root_.Metric.sphere_subset_closedBall hy))).1,
      mem_sphere_zero_iff_norm.mp hy]
  · rintro x ⟨⟨y, hy, rfl⟩, hlevel⟩
    refine ⟨y, ?_, rfl⟩
    rw [mem_sphere_zero_iff_norm]
    apply (sq_eq_sq₀ (norm_nonneg y) hr).mp
    have hn := (hnormal' y (hrs hy)).1
    change e (χ' y) 2 = _ at hlevel
    nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_local_maximum_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_local_maximum_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_local_maximum_cap ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_local_maximum_cap

end DifferentialGeometry.Topology.SphereSeparation
