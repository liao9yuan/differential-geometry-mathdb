import Submission.DifferentialGeometry.Topology.SphereSeparation.HeightTangent
import Submission.DifferentialGeometry.Topology.Morse.EmbeddedNormalFormGlobal
import Submission.DifferentialGeometry.Topology.Morse.ModelTransport
import Submission.DifferentialGeometry.Topology.Manifold.ModelWithCorners
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import Submission.DifferentialGeometry.Analysis.InnerProductSpace.EuclideanSplit
import Submission.DifferentialGeometry.Topology.Embedding.GraphNeighborhood
import Submission.DifferentialGeometry.Topology.Embedding.LinearEquiv
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Topology.Morse
open _root_.Submission.DifferentialGeometry.Topology.Morse.CellAttachment

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_global_height_preserving_normal_form {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) ∞ e)
    {p : SphereTwo} (k : ℕ) (hk : k ≤ 2)
    (hnd : IsNondegenerateCriticalPointAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (fun x => e x 2) p)
    (hindex : sigNeg (chartHessianAt
      (fun y => e ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p).symm y) 2)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p p)) = k) :
    ∃ r : ℝ, 0 < r ∧
      ∃ χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) SphereTwo ∞,
        ∃ Φ : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
          _root_.Metric.closedBall 0 r ⊆ χ.source ∧ χ 0 = p ∧ (∀ z, Φ z 2 = z 2) ∧
          ∀ y ∈ _root_.Metric.closedBall 0 r,
            Φ ((EuclideanSpace.equivProdLast 2).symm
              (y, morseNormalForm hk (e p 2) (EuclideanSpace.equiv (Fin 2) ℝ y))) = e (χ y) := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
  let L := EuclideanSpace.equiv (Fin 2) ℝ
  let J := I.transContinuousLinearEquiv L
  let A := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  let D : SphereTwo ≃ₘ⟮I, J⟯ SphereTwo :=
    ContinuousLinearEquiv.toTransContinuousLinearEquiv I SphereTwo L
  have hD :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
    D.symm.isLocalDiffeomorph D.symm.injective
  have he' : _root_.Manifold.IsSmoothEmbedding J 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ (A ∘ e) :=
    (he.continuousLinearEquiv_comp A).comp hD (by simp)
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => e x 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  have hnd' : IsNondegenerateCriticalPointAt J (fun x => (A (e x)).2) p :=
    (DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_transContinuousLinearEquiv_iff
      I L hf BoundarylessManifold.isInteriorPoint).mpr hnd
  have hindex' : sigNeg (chartHessianAt
      (fun y => (A (e ((extChartAt J p).symm y))).2) (extChartAt J p p)) = k :=
    (DifferentialGeometry.Morse.sigNeg_chartHessianAt_transContinuousLinearEquiv
      I L hf BoundarylessManifold.isInteriorPoint hnd.1).trans hindex
  obtain ⟨r, hr, χ, Ψ, hrs, hχ0, hheight, hnormal⟩ :=
    exists_global_height_preserving_morse_normal_form he'.contMDiff
      ((he'.isImmersion.isImmersionAt p).injective_mfderiv (by simp)) k hk hnd' hindex'
  let χ' : PartialDiffeomorph I I (EuclideanSpace ℝ (Fin 2)) SphereTwo ∞ :=
    { toPartialEquiv := χ.toPartialEquiv
      open_source := χ.open_source
      open_target := χ.open_target
      contMDiffOn_toFun := by simpa only [J,
        ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_right] using χ.contMDiffOn
      contMDiffOn_invFun := by
        have h := χ.symm.contMDiffOn
        change ContMDiffOn J I ∞ χ.symm χ.target at h
        exact (ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_left L).mp h }
  let Φ := (A.toDiffeomorph.trans Ψ).trans A.symm.toDiffeomorph
  refine ⟨r, hr, χ', Φ, hrs, hχ0, ?_, ?_⟩
  · intro z
    change ((EuclideanSpace.equivProdLast 2).symm (Ψ (A z))) (Fin.last 2) = z 2
    rw [EuclideanSpace.equivProdLast_symm_last, hheight]
    rfl
  · intro y hy
    change A.symm (Ψ (A (A.symm (y, morseNormalForm hk (e p 2) (L y))))) = e (χ y)
    rw [A.apply_symm_apply]
    have hn : Ψ (y, morseNormalForm hk (e p 2) (L y)) = A (e (χ y)) := hnormal y hy
    rw [hn, A.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_normal_form then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_normal_form"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_normal_form ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_normal_form

theorem exists_global_height_preserving_normal_neighborhood {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) ∞ e)
    {p : SphereTwo} (k : ℕ) (hk : k ≤ 2)
    (hnd : IsNondegenerateCriticalPointAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (fun x => e x 2) p)
    (hindex : sigNeg (chartHessianAt
      (fun y => e ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p).symm y) 2)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p p)) = k) :
    let q := fun y => morseNormalForm hk (e p 2) (EuclideanSpace.equiv (Fin 2) ℝ y)
    ∃ r : ℝ, 0 < r ∧ ∃ t : ℝ, 0 < t ∧
      ∃ χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) SphereTwo ∞,
        ∃ Φ : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
          _root_.Metric.closedBall 0 r ⊆ χ.source ∧ χ 0 = p ∧ (∀ z, Φ z 2 = z 2) ∧
          (∀ y ∈ _root_.Metric.closedBall 0 r, Φ ((EuclideanSpace.equivProdLast 2).symm (y, q y)) = e (χ y)) ∧
          (∀ y ∈ _root_.Metric.closedBall 0 r, q y ∈ _root_.Metric.ball (e p 2) t) ∧
          (_root_.Metric.closedBall 0 r ×ˢ _root_.Metric.closedBall (e p 2) t) ∩
              _root_.Set.range (fun x => EuclideanSpace.equivProdLast 2 (Φ.symm (e x))) =
            (fun y => (y, q y)) '' _root_.Metric.closedBall 0 r := by
  dsimp only
  let L := EuclideanSpace.equiv (Fin 2) ℝ
  let A := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  let q := fun y => morseNormalForm hk (e p 2) (L y)
  have hq0 : q 0 = e p 2 := by simp [q, morseNormalForm]
  obtain ⟨R, hR, χ, Φ, hRs, hχ0, hheight, hnormal⟩ :=
    exists_global_height_preserving_normal_form he k hk hnd hindex
  have hgraph : ∀ y ∈ _root_.Metric.ball 0 R,
      (A ∘ Φ.symm ∘ e) (χ.toOpenPartialHomeomorph y) = (y, q y) := by
    intro y hy
    change A (Φ.symm (e (χ y))) = (y, q y)
    rw [← hnormal y (_root_.Metric.ball_subset_closedBall hy), Φ.symm_apply_apply]
    exact A.apply_symm_apply (y, q y)
  have hq : Continuous q := by
    dsimp [q, morseNormalForm]
    fun_prop
  have he' := (A.toHomeomorph.isEmbedding.comp
    (Φ.symm.toHomeomorph.isEmbedding.comp he.isEmbedding)).isInducing
  obtain ⟨r, hr, t, ht, hrs, hqt, hset⟩ :=
    he'.exists_prod_closedBall_inter_range_eq_graph χ.toOpenPartialHomeomorph
      _root_.Metric.isOpen_ball (ball_subset_closedBall.trans hRs) hgraph (_root_.Metric.mem_ball_self hR) hq.continuousAt
  refine ⟨r, hr, t, ht, χ, Φ, hrs.trans (ball_subset_closedBall.trans hRs), hχ0,
    hheight, fun y hy => hnormal y (_root_.Metric.ball_subset_closedBall (hrs hy)), ?_, ?_⟩
  · simpa only [hq0] using hqt
  · simpa only [hq0, Diffeomorph.coe_toHomeomorph, ContinuousLinearEquiv.coe_toHomeomorph,
      Function.comp_def, q, L, A] using hset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_normal_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_normal_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_normal_neighborhood ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_global_height_preserving_normal_neighborhood

end DifferentialGeometry.Topology.SphereSeparation
