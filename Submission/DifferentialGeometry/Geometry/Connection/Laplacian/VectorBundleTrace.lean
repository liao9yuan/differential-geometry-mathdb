import Submission.DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundle
import Submission.DifferentialGeometry.Geometry.Metric.BilinearTrace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.CovariantDerivative _root_.Submission.CovariantDerivative
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

theorem rawBundleConnLap_eq_sum_hessian_of_orthonormal
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    {σ : ∀ x, V x} {x : M}
    (hDσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] F))
      (fun y => (⟨y, cov σ y⟩ : _root_.Bundle.TotalSpace (E →L[ℝ] F)
        (fun y => TangentSpace I y →L[ℝ] V y))) x)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0) :
    rawBundleConnLap g cov σ x =
      ∑ i, cov.hessian (LeviCivita g) σ x (e i) (e i) := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : IsEmpty (Fin (Module.finrank ℝ E)) := by
      simpa [hdim] using (Fin.isEmpty : IsEmpty (Fin 0))
    simp [rawBundleConnLap]
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  rw [rawBundleConnLap_eq_sum_hessian g cov hDσ]
  let A := cov.hessian (LeviCivita g) σ x
  let B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] V x :=
    { toFun := fun v => (A v).toLinearMap
      map_add' := by intro v w; ext z; simp
      map_smul' := by intro c v; ext z; simp }
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by rw [Fintype.card_fin]; rfl
  change (∑ i, B (smoothOrthoFrame g x i x) (smoothOrthoFrame g x i x)) =
    ∑ i, B (e i) (e i)
  let D := (tangentMetricData (I := I) g x).metric
  let : InnerProductSpace.Core ℝ (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I x) _ _ _ D.toCore
  let : InnerProductSpace ℝ (TangentSpace I x) :=
    @InnerProductSpace.ofCore ℝ (TangentSpace I x) _ _ _ D.toCore.toCore
  have hg (v w : TangentSpace I x) : g.inner x v w = _root_.Inner.inner ℝ v w := by
    rw [← TangentMetricData.inner_eq (tangentMetricData (I := I) g x) v w]
    exact (MetricFiberData.toCore_inner D v w).symm
  let f := fun i => smoothOrthoFrame g x i x
  have hf : Orthonormal ℝ f := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [← hg]
    exact smoothOrthoFrame_orthonormal_at_center g x i j
  have he' : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [← hg]
    exact he i j
  let b := OrthonormalBasis.mk hf
    (ge_of_eq (hf.linearIndependent.span_eq_top_of_card_eq_finrank hcard))
  let c := OrthonormalBasis.mk he'
    (ge_of_eq (he'.linearIndependent.span_eq_top_of_card_eq_finrank hcard))
  simpa only [b, c, OrthonormalBasis.coe_mk] using b.sum_bilinear_diag_eq c B

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.rawBundleConnLap_eq_sum_hessian_of_orthonormal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.rawBundleConnLap_eq_sum_hessian_of_orthonormal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.rawBundleConnLap_eq_sum_hessian_of_orthonormal ``Submission.DifferentialGeometry.Geometry.Connection.rawBundleConnLap_eq_sum_hessian_of_orthonormal

theorem rawBundleConnLap_eq_sum_covariantDerivative_of_orthonormal
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    {σ : ∀ x, V x} {x : M}
    (hDσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] F))
      (fun y => (⟨y, cov σ y⟩ : _root_.Bundle.TotalSpace (E →L[ℝ] F)
        (fun y => TangentSpace I y →L[ℝ] V y))) x)
    (e : Fin (Module.finrank ℝ E) → ∀ y, TangentSpace I y)
    (he : ∀ i j, g.inner x (e i x) (e j x) = if i = j then 1 else 0)
    (heDiff : ∀ i, MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (e i)) x) :
    rawBundleConnLap g cov σ x =
      ∑ i, (cov (fun y => cov σ y (e i y)) x (e i x) -
        cov σ x (LeviCivita g (e i) x (e i x))) := by
  rw [rawBundleConnLap_eq_sum_hessian_of_orthonormal g cov hDσ (fun i => e i x) he]
  apply Finset.sum_congr rfl
  intro i _
  exact cov.hessian_apply (LeviCivita g) hDσ (heDiff i) (e i x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.rawBundleConnLap_eq_sum_covariantDerivative_of_orthonormal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.rawBundleConnLap_eq_sum_covariantDerivative_of_orthonormal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.rawBundleConnLap_eq_sum_covariantDerivative_of_orthonormal ``Submission.DifferentialGeometry.Geometry.Connection.rawBundleConnLap_eq_sum_covariantDerivative_of_orthonormal

variable [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]

theorem rawBundleConnLap_eq_sum_hessian_of_orthonormal_of_contMDiffAt
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    (hcov : _root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    {σ : ∀ x, V x} {x : M}
    (hσ : ContMDiffAt I (I.prod 𝓘(ℝ, F)) 2 (T% σ) x)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0) :
    rawBundleConnLap g cov σ x =
      ∑ i, cov.hessian (LeviCivita g) σ x (e i) (e i) :=
  rawBundleConnLap_eq_sum_hessian_of_orthonormal g cov
    ((hcov.contMDiffAt (m := 1) hσ (by norm_num)).mdifferentiableAt (by simp)) e he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.rawBundleConnLap_eq_sum_hessian_of_orthonormal_of_contMDiffAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.rawBundleConnLap_eq_sum_hessian_of_orthonormal_of_contMDiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.rawBundleConnLap_eq_sum_hessian_of_orthonormal_of_contMDiffAt ``Submission.DifferentialGeometry.Geometry.Connection.rawBundleConnLap_eq_sum_hessian_of_orthonormal_of_contMDiffAt

theorem rawBundleConnLap_eq_sum_covariantDerivative_of_orthonormal_of_contMDiffAt
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    (hcov : _root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    {σ : ∀ x, V x} {x : M}
    (hσ : ContMDiffAt I (I.prod 𝓘(ℝ, F)) 2 (T% σ) x)
    (e : Fin (Module.finrank ℝ E) → ∀ y, TangentSpace I y)
    (he : ∀ i j, g.inner x (e i x) (e j x) = if i = j then 1 else 0)
    (heDiff : ∀ i, MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (e i)) x) :
    rawBundleConnLap g cov σ x =
      ∑ i, (cov (fun y => cov σ y (e i y)) x (e i x) -
        cov σ x (LeviCivita g (e i) x (e i x))) :=
  rawBundleConnLap_eq_sum_covariantDerivative_of_orthonormal g cov
    ((hcov.contMDiffAt (m := 1) hσ (by norm_num)).mdifferentiableAt (by simp)) e he heDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.rawBundleConnLap_eq_sum_covariantDerivative_of_orthonormal_of_contMDiffAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.rawBundleConnLap_eq_sum_covariantDerivative_of_orthonormal_of_contMDiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.rawBundleConnLap_eq_sum_covariantDerivative_of_orthonormal_of_contMDiffAt ``Submission.DifferentialGeometry.Geometry.Connection.rawBundleConnLap_eq_sum_covariantDerivative_of_orthonormal_of_contMDiffAt

end DifferentialGeometry.Geometry.Connection
