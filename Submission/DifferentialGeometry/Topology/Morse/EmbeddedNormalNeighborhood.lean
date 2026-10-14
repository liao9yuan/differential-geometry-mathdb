import Submission.DifferentialGeometry.Topology.Morse.EmbeddedNormalFormGlobal
import Submission.DifferentialGeometry.Topology.Embedding.GraphNeighborhood
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Mathlib.Geometry.Manifold.SmoothEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Manifold _root_.Submission.Manifold _root_.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Topology.Morse.CellAttachment

namespace DifferentialGeometry.Topology.Morse

variable {n : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (MorseModel n) H}
  [I.Boundaryless] [IsManifold I ∞ M]

theorem exists_global_height_preserving_morse_normal_neighborhood
    {e : M → EuclideanSpace ℝ (Fin n) × ℝ}
    (he : _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) ∞ e)
    {p : M} (k : ℕ) (hk : k ≤ n)
    (hnd : IsNondegenerateCriticalPointAt I (fun x => (e x).2) p)
    (hindex : sigNeg (chartHessianAt (fun y => (e ((extChartAt I p).symm y)).2)
      (extChartAt I p p)) = k) :
    let q := fun y => morseNormalForm hk (e p).2 (EuclideanSpace.equiv (Fin n) ℝ y)
    ∃ r : ℝ, 0 < r ∧ ∃ t : ℝ, 0 < t ∧
      ∃ χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I
          (EuclideanSpace ℝ (Fin n)) M ∞,
        ∃ Φ : (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ),
          _root_.Metric.closedBall 0 r ⊆ χ.source ∧ χ 0 = p ∧ (∀ z, (Φ z).2 = z.2) ∧
          (∀ y ∈ _root_.Metric.closedBall 0 r, Φ (y, q y) = e (χ y)) ∧
          (∀ y ∈ _root_.Metric.closedBall 0 r, q y ∈ _root_.Metric.ball (e p).2 t) ∧
          (_root_.Metric.closedBall 0 r ×ˢ _root_.Metric.closedBall (e p).2 t) ∩ _root_.Set.range (Φ.symm ∘ e) =
            (fun y => (y, q y)) '' _root_.Metric.closedBall 0 r := by
  dsimp only
  let L := EuclideanSpace.equiv (Fin n) ℝ
  let q := fun y => morseNormalForm hk (e p).2 (L y)
  have hq0 : q 0 = (e p).2 := by simp [q, morseNormalForm]
  obtain ⟨R, hR, χ, Φ, hRs, hχ0, hheight, hnormal⟩ :=
    exists_global_height_preserving_morse_normal_form he.contMDiff
      ((he.isImmersion.isImmersionAt p).injective_mfderiv (by simp)) k hk hnd hindex
  have hgraph : ∀ y ∈ _root_.Metric.ball 0 R, (Φ.symm ∘ e) (χ.toOpenPartialHomeomorph y) = (y, q y) := by
    intro y hy
    change Φ.symm (e (χ y)) = (y, q y)
    rw [← hnormal y (_root_.Metric.ball_subset_closedBall hy), Φ.symm_apply_apply]
  have hq : Continuous q := by
    dsimp [q, morseNormalForm]
    fun_prop
  have he' := (Φ.symm.toHomeomorph.isEmbedding.comp he.isEmbedding).isInducing
  obtain ⟨r, hr, t, ht, hrs, hqt, hset⟩ :=
    he'.exists_prod_closedBall_inter_range_eq_graph χ.toOpenPartialHomeomorph
        _root_.Metric.isOpen_ball (ball_subset_closedBall.trans hRs) hgraph (_root_.Metric.mem_ball_self hR) hq.continuousAt
  refine ⟨r, hr, t, ht, χ, Φ, hrs.trans (ball_subset_closedBall.trans hRs), hχ0,
    hheight, fun y hy => hnormal y (_root_.Metric.ball_subset_closedBall (hrs hy)), ?_, ?_⟩
  · simpa only [hq0] using hqt
  · simpa only [hq0, Diffeomorph.coe_toHomeomorph] using hset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.exists_global_height_preserving_morse_normal_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.exists_global_height_preserving_morse_normal_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.exists_global_height_preserving_morse_normal_neighborhood ``Submission.DifferentialGeometry.Topology.Morse.exists_global_height_preserving_morse_normal_neighborhood

end DifferentialGeometry.Topology.Morse
