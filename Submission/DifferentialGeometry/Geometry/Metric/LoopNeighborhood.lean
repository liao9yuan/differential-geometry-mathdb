import Submission.DifferentialGeometry.Topology.Manifold.Embedding.CompactRetraction
import Submission.DifferentialGeometry.Geometry.Metric.LoopEmbedding
import Submission.DifferentialGeometry.Topology.LoopSpace.InverseLipschitz
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothTraceLift
import Submission.DifferentialGeometry.Geometry.Metric.SmoothLipschitz
import Submission.DifferentialGeometry.Analysis.Calculus.Periodic.Affine
import Submission.DifferentialGeometry.Topology.LoopSpace.Regular
import Submission.DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_loop_neighborhood_embedding_retraction
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) :
    ∃ (N : TopologicalSpace.Opens M) (n : ℕ)
      (e : M → EuclideanSpace ℝ (Fin n)) (r : EuclideanSpace ℝ (Fin n) → M)
      (U : Set (EuclideanSpace ℝ (Fin n))) (Ce Cγ J : ℝ≥0),
      _root_.Set.range γ ⊆ N ∧ ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e ∧
      HasCompactSupport e ∧ IsOpen U ∧ e '' (N : Set M) ⊆ U ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ r U ∧
      (∀ x ∈ N, r (e x) = x) ∧
      (∀ x y, _root_.EDist.edist (e x) (e y) ≤ (Ce : ℝ≥0∞) * riemannianEDistOf g x y) ∧
      LipschitzWith Cγ (fun t : ℝ => e (γ (t : loopCircle))) ∧
      AntilipschitzWith J (fun θ : loopCircle => e (γ θ)) := by
  obtain ⟨N, n, e, r, U, hN, he, hesupp, hemb, hi, hU, heU, hr, hleft⟩ :=
    exists_contMDiff_embedding_retraction_near_isCompact (I := 𝓘(ℝ, E))
      (isCompact_range γ.continuous) (_root_.Set.range_nonempty γ)
  obtain ⟨Ce, _, hCe⟩ := exists_riemannian_lipschitz_of_contMDiff_of_hasCompactSupport g
    (he.of_le (by simp)) hesupp
  let Γ : loopCircle → EuclideanSpace ℝ (Fin n) := fun θ => e (γ θ)
  let G : ℝ → EuclideanSpace ℝ (Fin n) := fun t => Γ (t : loopCircle)
  have hGs : ContDiff ℝ ∞ G := (he.comp hγ.smooth).contDiff
  have hΓs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ Γ :=
    AddCircle.isLocalDiffeomorph_coe.contMDiff_of_comp_of_surjective
      QuotientAddGroup.mk_surjective hGs.contMDiff
  have hGi (t : ℝ) : _root_.Function.Injective (fderiv ℝ G t) := by
    have hder : fderiv ℝ G t =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e (γ (t : loopCircle))).comp
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) t) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp t (he.mdifferentiableAt (by simp)) (hγ.smooth.mdifferentiableAt (by simp))
    rw [hder]
    exact (hi _ (hN (_root_.Set.mem_range_self _))).comp
      (realContinuousLinearMap_injective_of_one_ne_zero _ (hγ.immersed t))
  have hΓi (θ : loopCircle) : _root_.Function.Injective
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Γ θ) := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    let A : ℝ →L[ℝ] ℝ := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun s : ℝ => (s : loopCircle)) t
    let D : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Γ (t : loopCircle)
    change _root_.Function.Injective D
    have hA : _root_.Function.Surjective A := (AddCircle.bijective_mfderiv_coe t).2
    have hd : fderiv ℝ G t = D.comp A := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp t (hΓs.mdifferentiableAt (by simp))
        (AddCircle.contMDiff_coe.mdifferentiableAt (by simp))
    intro x y hxy
    obtain ⟨a, ha⟩ := hA x
    obtain ⟨b, hb⟩ := hA y
    have heqab : fderiv ℝ G t a = fderiv ℝ G t b := by
      rw [hd]
      change D (A a) = D (A b)
      rw [ha, hb]
      exact hxy
    exact ha.symm.trans ((congrArg A (hGi t heqab)).trans hb)
  have hΓinj : _root_.Function.Injective Γ := by
    intro x y hxy
    apply hγ.embedding.injective
    exact congrArg Subtype.val (hemb.injective (show
      e (⟨γ x, hN (_root_.Set.mem_range_self x)⟩ : N) = e (⟨γ y, hN (_root_.Set.mem_range_self y)⟩ : N) from hxy))
  have hΓemb : _root_.Topology.IsEmbedding Γ :=
    (hΓs.continuous.isClosedEmbedding hΓinj).isEmbedding
  obtain ⟨J, hJ⟩ := exists_antilipschitzWith_of_smooth_loop_embedding hΓs hΓemb hΓi
  have hper : _root_.Function.Periodic G 1 := by
    intro t
    simp only [G, AddCircle.coe_add, AddCircle.coe_period, add_zero]
  have hdper : _root_.Function.Periodic (deriv G) 1 := by
    simpa only [iteratedDeriv_one] using periodic_iteratedDeriv hper 1
  obtain ⟨B, hB, hbound⟩ := exists_bound_of_continuous_unit_periodic
    (hGs.continuous_deriv (by simp)) hdper
  let Cγ : ℝ≥0 := ⟨B, hB.le⟩
  have hCγ : LipschitzWith Cγ G :=
    lipschitzWith_of_nnnorm_deriv_le (hGs.differentiable (by simp))
      (fun t => by exact_mod_cast hbound t)
  exact ⟨N, n, e, r, U, Ce, Cγ, J, hN, he, hesupp, hU, heU, hr, hleft, hCe, hCγ, hJ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_loop_neighborhood_embedding_retraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_loop_neighborhood_embedding_retraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_loop_neighborhood_embedding_retraction ``Submission.DifferentialGeometry.Geometry.exists_loop_neighborhood_embedding_retraction

end DifferentialGeometry.Geometry

end

end
