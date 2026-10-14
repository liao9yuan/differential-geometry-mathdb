import Submission.DifferentialGeometry.Analysis.Calculus.Compactness.BilinearForm
import Submission.DifferentialGeometry.Analysis.Calculus.MapConvergence.SmoothInverseOn


import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.Bounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open _root_.Filter _root_.Topology

section HCGNormalCoord

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_normal_coord_metric_limit_subsequence
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : NormalCoordMetricBounds (I := I) X)
    (c : ∀ k : ℕ, (X.obj k).M)
    {U : Set E} (hU : IsOpen U)
    (hdom : ∀ k, U ⊆ Metric.ball (0 : E) (input.radius k (c k)))
    (hsub : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      U ⊆ Metric.ball (0 : E) (expMapC2Radius (I := I) (X.obj k).metric (c k))) :
    ∃ (φ : ℕ → ℕ) (gInf : E → (E →L[ℝ] E →L[ℝ] ℝ)),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) gInf U ∧
        MapCInfConvergenceOnCompacts U
          (fun k => normalCoordMetric (I := I) (X.obj (φ k)) (c (φ k))) gInf ∧
        ∀ z ∈ U, ∀ v : E,
          (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ gInf z v v ∧ gInf z v v ≤ 2 * ‖v‖ ^ 2 :=
  exists_smooth_bilinear_form_limit_subsequence_on hU
    (fun k => normalCoordMetric (I := I) (X.obj k) (c k))
    (normal_coord_metric_cont_diff_on_of_subset_exp_ball (I := I) c hsub)
    (fun r _K _hKcpt hKU =>
      ⟨input.metricC r, fun k z hz => input.metric_deriv k r (c k) z (hdom k (hKU hz))⟩)
    (1 / 2) 2
    (fun k z hz v => input.metric_equiv k (c k) z (hdom k hz) v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_normal_coord_metric_limit_subsequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_normal_coord_metric_limit_subsequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_normal_coord_metric_limit_subsequence ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_normal_coord_metric_limit_subsequence

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_finite_normal_coord_metric_limit_subsequence
    {ι : Type*} [Fintype ι]
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : NormalCoordMetricBounds (I := I) X)
    (c : ι → ∀ k : Nat, (X.obj k).M)
    {U : Set E} (hU : IsOpen U)
    (hdom : ∀ k i, U ⊆ Metric.ball (0 : E) (input.radius k (c i k)))
    (hsub : ∀ k i,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      U ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric (c i k))) :
    ∃ (phi : Nat → Nat)
        (gInf : E → (ι → (E →L[Real] E →L[Real] Real))),
      StrictMono phi ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) gInf U ∧
      MapCInfConvergenceOnCompacts U
        (fun k z i ↦ normalCoordMetric (I := I) (X.obj (phi k))
          (c i (phi k)) z) gInf ∧
      ∀ z ∈ U, ∀ i v,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z i v v ∧
          gInf z i v v ≤ 2 * ‖v‖ ^ 2 := by
  classical
  let gLocal : Nat → E → (ι → (E →L[Real] E →L[Real] Real)) :=
    fun k z i ↦ normalCoordMetric (I := I) (X.obj k) (c i k) z
  have hsmooth_comp : ∀ k i, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z ↦ gLocal k z i) U := by
    intro k i
    exact normal_coord_metric_cont_diff_on_of_subset_exp_ball
      (I := I) (fun n ↦ c i n) (fun n ↦ hsub n i) k
  have hsmooth : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (gLocal k) U :=
    fun k ↦ contDiffOn_pi.mpr (hsmooth_comp k)
  have hbdd_comp : ∀ i,
      iteratedFDerivBoundsOnCompactsWithin U (fun k z ↦ gLocal k z i) := by
    intro i r K hK hKU
    exact ⟨input.metricC r, fun k z hz ↦
      input.metric_deriv k r (c i k) z (hdom k i (hKU hz))⟩
  have hbdd : iteratedFDerivBoundsOnCompactsWithin U gLocal :=
    iteratedFDerivBoundsOnCompactsWithin.pi hU hsmooth_comp hbdd_comp
  obtain ⟨phi, gInf, hphi, hginf, hconv⟩ :=
    exists_cInf_subseq_on hU gLocal hsmooth hbdd
  refine ⟨phi, gInf, hphi, hginf, hconv, ?_⟩
  intro z hz i v
  have htendAll : _root_.Filter.Tendsto (fun k ↦ gLocal (phi k) z) _root_.Filter.atTop (nhds (gInf z)) :=
    tendsto_of_cInf hconv hz
  have htend : _root_.Filter.Tendsto (fun k ↦ gLocal (phi k) z i) _root_.Filter.atTop
      (nhds (gInf z i)) := (tendsto_pi_nhds.mp htendAll) i
  have heval : Continuous
      (fun A : E →L[Real] E →L[Real] Real ↦ A v v) := by
    fun_prop
  have htendv : _root_.Filter.Tendsto (fun k ↦ gLocal (phi k) z i v v) _root_.Filter.atTop
      (nhds (gInf z i v v)) := (heval.tendsto _).comp htend
  exact ⟨
    ge_of_tendsto htendv (Filter.Eventually.of_forall fun k ↦
      (input.metric_equiv (phi k) (c i (phi k)) z
        (hdom (phi k) i hz) v).1),
    le_of_tendsto htendv (Filter.Eventually.of_forall fun k ↦
      (input.metric_equiv (phi k) (c i (phi k)) z
        (hdom (phi k) i hz) v).2)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_finite_normal_coord_metric_limit_subsequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_finite_normal_coord_metric_limit_subsequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_finite_normal_coord_metric_limit_subsequence ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_finite_normal_coord_metric_limit_subsequence

end HCGNormalCoord

end CheegerGromovCompactness
end DifferentialGeometry
