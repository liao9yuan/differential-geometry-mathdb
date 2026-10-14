import Submission.DifferentialGeometry.Topology.Manifold.ManifoldIsotopyExtension
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.Manifold

open _root_.Set _root_.Metric _root_.Submission.Metric

theorem exists_isotopy_eqOn_closedBall_of_partialDiffeomorph {n : ℕ}
    (φ : PartialDiffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ∞)
    {r : ℝ} (hr : 0 < r) (hs : _root_.Metric.closedBall 0 r ⊆ φ.source)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
    (hV₀ : _root_.Metric.closedBall 0 r ⊆ V) (hV₁ : φ '' _root_.Metric.closedBall 0 r ⊆ V)
    (hseg : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, t • φ 0 ∈ V) :
    ∃ (Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
      (J : ℝ → Diffeomorph (𝓡 n) (𝓡 n)
        (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ∞),
      ContDiff ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin n) => J q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin n) => (J q.1).symm q.2) ∧
      J 0 = Diffeomorph.refl (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞ ∧
      (∀ x ∈ _root_.Metric.closedBall 0 r, J 1 (Q x) = φ x) ∧
      ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧ K ⊆ V ∧
        ∀ t y, y ∉ K → J t y = y ∧ (J t).symm y = y := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  have h0s : (0 : E) ∈ φ.source := hs (_root_.Metric.mem_closedBall_self hr.le)
  have hloc := PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ φ h0s
  let A : E ≃L[ℝ] E :=
    hloc.mfderivToContinuousLinearEquiv (by simp)
  have hA : (A : E →L[ℝ] E) = fderiv ℝ φ 0 := by
    change mfderiv (𝓡 n) (𝓡 n) φ 0 = fderiv ℝ φ 0
    exact mfderiv_eq_fderiv
  have hdet : (fderiv ℝ φ 0).det ≠ 0 := by
    rw [← hA]
    exact A.toLinearEquiv.isUnit_det'.ne_zero
  have hQ : ∃ Q : E ≃ₗᵢ[ℝ] E,
      0 < LinearMap.det Q.toLinearMap * (fderiv ℝ φ 0).det := by
    by_cases hpos : 0 < (fderiv ℝ φ 0).det
    · exact ⟨LinearIsometryEquiv.refl ℝ E, by simpa using hpos⟩
    · have hneg : (fderiv ℝ φ 0).det < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hdet
      have hn : n ≠ 0 := by
        intro hn
        subst n
        have hz : Module.finrank ℝ E = 0 := by simp [E]
        have hone := LinearMap.det_eq_one_of_finrank_eq_zero
          (f := (fderiv ℝ φ 0).toLinearMap) hz
        change (fderiv ℝ φ 0).det = 1 at hone
        linarith
      obtain ⟨v, hv⟩ : ∃ v : E, v ≠ 0 := by
        let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
        exact ⟨(EuclideanSpace.basisFun (Fin n) ℝ) i,
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ne_zero i⟩
      refine ⟨(ℝ ∙ v)ᗮ.reflection, ?_⟩
      rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal,
        finrank_span_singleton hv]
      simpa using neg_pos.mpr hneg
  obtain ⟨Q, hQ⟩ := hQ
  let ψ := Q.toContinuousLinearEquiv.toDiffeomorph.toPartialDiffeomorph
  have hψ : (ψ : E → E) = Q := rfl
  have hψball : ψ '' _root_.Metric.closedBall 0 r = _root_.Metric.closedBall 0 r := by
    rw [hψ]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_closedBall_zero_iff, Q.norm_map] using hy
    · intro hx
      refine ⟨Q.symm x, ?_, Q.apply_symm_apply x⟩
      simpa only [mem_closedBall_zero_iff, Q.symm.norm_map] using hx
  have hderiv : fderiv ℝ ψ 0 = Q.toContinuousLinearEquiv.toContinuousLinearMap := by
    exact Q.toContinuousLinearEquiv.toContinuousLinearMap.fderiv
  obtain ⟨J, hJ, hJi, hJ0, hJ1, K, hK, hKV, hfix⟩ :=
    exists_isotopy_eqOn_closedBall_of_partialDiffeomorphs_of_subset_of_radius ψ φ hr
      (_root_.Set.subset_univ _) hs hV (by rw [hψball]; exact hV₀) hV₁
      (by simpa only [hψ, map_zero, smul_zero, zero_add] using hseg)
      (by rw [hderiv]; exact hQ)
  exact ⟨Q, J, hJ, hJi, hJ0, hJ1, K, hK, hKV, hfix⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_isotopy_eqOn_closedBall_of_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_isotopy_eqOn_closedBall_of_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_isotopy_eqOn_closedBall_of_partialDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.exists_isotopy_eqOn_closedBall_of_partialDiffeomorph

theorem exists_isotopy_image_closedBall_of_partialDiffeomorph {n : ℕ}
    (φ : PartialDiffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ∞)
    {r : ℝ} (hr : 0 < r) (hs : _root_.Metric.closedBall 0 r ⊆ φ.source)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
    (hV₀ : _root_.Metric.closedBall 0 r ⊆ V) (hV₁ : φ '' _root_.Metric.closedBall 0 r ⊆ V)
    (hseg : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, t • φ 0 ∈ V) :
    ∃ J : ℝ → Diffeomorph (𝓡 n) (𝓡 n)
        (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ∞,
      ContDiff ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin n) => J q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin n) => (J q.1).symm q.2) ∧
      J 0 = Diffeomorph.refl (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞ ∧
      J 1 '' _root_.Metric.closedBall 0 r = φ '' _root_.Metric.closedBall 0 r ∧
      ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧ K ⊆ V ∧
        ∀ t y, y ∉ K → J t y = y ∧ (J t).symm y = y := by
  obtain ⟨Q, J, hJ, hJi, hJ0, hJ1, K, hK, hKV, hfix⟩ :=
    exists_isotopy_eqOn_closedBall_of_partialDiffeomorph φ hr hs hV hV₀ hV₁ hseg
  have hQball : Q '' _root_.Metric.closedBall 0 r = _root_.Metric.closedBall 0 r := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_closedBall_zero_iff, Q.norm_map] using hy
    · intro hx
      refine ⟨Q.symm x, ?_, Q.apply_symm_apply x⟩
      simpa only [mem_closedBall_zero_iff, Q.symm.norm_map] using hx
  refine ⟨J, hJ, hJi, hJ0, ?_, K, hK, hKV, hfix⟩
  calc
    J 1 '' _root_.Metric.closedBall 0 r = J 1 '' (Q '' _root_.Metric.closedBall 0 r) := by rw [hQball]
    _ = φ '' _root_.Metric.closedBall 0 r := by rw [Set.image_image]; exact Set.image_congr hJ1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_isotopy_image_closedBall_of_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_isotopy_image_closedBall_of_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_isotopy_image_closedBall_of_partialDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.exists_isotopy_image_closedBall_of_partialDiffeomorph

end DifferentialGeometry.Topology.Manifold
