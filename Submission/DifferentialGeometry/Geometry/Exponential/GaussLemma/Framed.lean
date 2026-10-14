import Submission.DifferentialGeometry.Geometry.Exponential.GaussLemma.Pullback
import Submission.DifferentialGeometry.Geometry.Exponential.Smoothness.Framed
import Submission.DifferentialGeometry.Geometry.Comparison.RadialLength
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)]

theorem gauss_lemma_framedExpMap
    (g : SmoothRiemannianMetric I M) (p : M) {z : E} (v : E)
    (hz : normalFrame g p z ∈ expDomain g p) :
    g.inner (framedExpMap g p z)
      (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z z)
      (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v) = _root_.Inner.inner ℝ z v := by
  rw [mfderiv_framedExpMap g p hz]
  change g.inner (expMap g p (normalFrame g p z))
      (mfderiv 𝓘(ℝ, E) I (fun u : E => expMap g p (show TangentSpace I p from u))
        (normalFrame g p z) (normalFrame g p z))
      (mfderiv 𝓘(ℝ, E) I (fun u : E => expMap g p (show TangentSpace I p from u))
        (normalFrame g p z) (normalFrame g p v)) = _root_.Inner.inner ℝ z v
  exact (gauss_lemma g p hz).trans (normalFrame_inner g p z v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.gauss_lemma_framedExpMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.gauss_lemma_framedExpMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.gauss_lemma_framedExpMap ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.gauss_lemma_framedExpMap

theorem framedExpMap_radial_lower_bound
    (g : SmoothRiemannianMetric I M) (p : M) {z : E} (v : E)
    (hz : normalFrame g p z ∈ expDomain g p) :
    |inner ℝ z v| ≤ ‖z‖ * Real.sqrt (g.inner (framedExpMap g p z)
      (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v)
      (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v)) := by
  have h := DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
    g (framedExpMap g p z) (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z z)
      (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v)
  rw [gauss_lemma_framedExpMap g p v hz, gauss_lemma_framedExpMap g p z hz,
    real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg z)] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExpMap_radial_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExpMap_radial_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExpMap_radial_lower_bound ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExpMap_radial_lower_bound

theorem norm_sub_le_pathELength_framedExpMap
    [(x : M) → ENorm (TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {η : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hη : ContDiffOn ℝ 1 η (_root_.Set.Icc a b))
    (hdom : ∀ x ∈ _root_.Set.Icc a b, normalFrame g p (η x) ∈ expDomain g p) :
    ENNReal.ofReal (‖η b‖ - ‖η a‖) ≤ Manifold.pathELength I (framedExpMap g p ∘ η) a b := by
  exact Manifold.norm_sub_le_pathELength_comp_of_radial_bound
    g.toContinuousRiemannianMetric hEnorm (framedExpMap g p) hab hη
    (fun x hx => (contMDiffAt_framedExpMap g p (hdom x hx)).of_le (by simp))
    (fun x hx v => (le_abs_self _).trans
      (framedExpMap_radial_lower_bound g p v (hdom x (_root_.Set.Ioo_subset_Icc_self hx))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.norm_sub_le_pathELength_framedExpMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.norm_sub_le_pathELength_framedExpMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.norm_sub_le_pathELength_framedExpMap ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.norm_sub_le_pathELength_framedExpMap

theorem norm_le_pathELength_framedExpMap
    [(x : M) → ENorm (TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {η : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hηa : η a = 0) (hη : ContDiffOn ℝ 1 η (_root_.Set.Icc a b))
    (hdom : ∀ x ∈ _root_.Set.Icc a b, normalFrame g p (η x) ∈ expDomain g p) :
    ENNReal.ofReal ‖η b‖ ≤ Manifold.pathELength I (framedExpMap g p ∘ η) a b := by
  simpa only [hηa, norm_zero, sub_zero] using
    norm_sub_le_pathELength_framedExpMap g hEnorm p hab hη hdom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.norm_le_pathELength_framedExpMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.norm_le_pathELength_framedExpMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.norm_le_pathELength_framedExpMap ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.norm_le_pathELength_framedExpMap

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
