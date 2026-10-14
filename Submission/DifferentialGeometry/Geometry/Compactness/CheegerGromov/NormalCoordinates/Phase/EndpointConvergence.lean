import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.Bounds
import Submission.DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative
import Submission.DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Convergence
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Phase.Endpoint

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

open _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry
namespace CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace NormalRadiusProfile

theorem diag_end_convergence
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) (R : Real)
    (c : ∀ n : Nat, (X.obj n).M)
    (hc : ∀ n, hd.dist n (c n) (X.obj n).basepoint ≤ R)
    {Q : Set (E × E)} (hQ : IsOpen Q)
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hgInf_cd : ContDiffOn Real ∞ gInf
      (Metric.ball 0 (h.phaseRadius R)))
    (hgInf_lo : ∀ z ∈ Metric.ball (0 : E) (h.phaseRadius R), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z v v)
    (hg_convergence : MapCInfConvergenceOnCompacts
      (Metric.ball 0 (h.phaseRadius R))
      (fun n ↦ normalCoordMetric (I := I) (X.obj n) (c n)) gInf)
    {Φ : Nat → (E × E) → Real → E × E}
    {ΦInf : (E × E) → Real → E × E}
    {e : Nat → OpenPartialHomeomorph (E × E) (E × E)}
    (hΦ : ∀ n z, z ∈ Q →
      Φ n z 0 = z ∧
      IsIntegralCurveOn (Φ n z)
        (fun _ ↦ MetricKoszul.metricSpray
          (normalCoordMetric (I := I) (X.obj n) (c n)))
        (_root_.Set.Icc 0 1))
    (hΦInf : ∀ z, z ∈ Q →
      ΦInf z 0 = z ∧
      IsIntegralCurveOn (ΦInf z)
        (fun _ ↦ MetricKoszul.metricSpray gInf) (_root_.Set.Icc 0 1))
    (hstay : ∀ n z, z ∈ Q → ∀ t ∈ _root_.Set.Icc (0 : Real) 1,
      (Φ n z t).1 ∈ Metric.ball 0 (h.phaseRadius R))
    (hstayInf : ∀ z, z ∈ Q → ∀ t ∈ _root_.Set.Icc (0 : Real) 1,
      (ΦInf z t).1 ∈ Metric.ball 0 (h.phaseRadius R))
    (he : ∀ n, (e n : E × E → E × E) =
      fun z ↦ (z.1, (Φ n z 1).1)) :
    MapCInfConvergenceOnCompacts Q
      (fun n ↦ (e n : E × E → E × E))
      (fun z ↦ (z.1, (ΦInf z 1).1)) := by
  have hg_cd : ∀ n, ContDiffOn Real ∞
      (normalCoordMetric (I := I) (X.obj n) (c n))
      (Metric.ball 0 (h.phaseRadius R)) := by
    intro n
    let : TopologicalSpace (X.obj n).M := (X.obj n).topology
    let : ChartedSpace H (X.obj n).M := (X.obj n).charted
    let : IsManifold I ∞ (X.obj n).M := (X.obj n).smooth
    let : T2Space (TangentBundle I (X.obj n).M) :=
      (X.obj n).t2TangentBundle
    apply (normal_coord_metric_cont_diff_on_exp_ball (I := I) (X.obj n) (c n)).mono
    exact (h.phaseRadius_exp (hc n)).trans (Metric.ball_subset_ball (by
      nlinarith [Geometry.Riemannian.expMapC2Radius_pos
        (I := I) (X.obj n).metric (c n)]))
  have hg_co : ∀ n z, z ∈ Metric.ball (0 : E) (h.phaseRadius R) →
      IsCoercive (normalCoordMetric (I := I) (X.obj n) (c n) z) := by
    intro n z hz
    exact (hb.metric_equiv n (c n)).coercive (h.phaseRadius_metric (hc n) hz)
  have hgInf_co : ∀ z, z ∈ Metric.ball (0 : E) (h.phaseRadius R) →
      IsCoercive (gInf z) := by
    intro z hz
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro v
    simpa only [pow_two, mul_assoc] using hgInf_lo z hz v
  have hconv := normalDiag_end_convergence
    (Metric.isOpen_ball : IsOpen (Metric.ball (0 : E) (h.phaseRadius R)))
    hQ hg_cd hgInf_cd hg_co hgInf_co hg_convergence hΦ hΦInf hstay hstayInf
  exact hconv.congr hQ
    (fun n z _hz ↦ congrFun (he n) z)
    (fun _z _hz ↦ rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.NormalRadiusProfile.diag_end_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.NormalRadiusProfile.diag_end_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.NormalRadiusProfile.diag_end_convergence ``Submission.DifferentialGeometry.CheegerGromovCompactness.NormalRadiusProfile.diag_end_convergence

end NormalRadiusProfile
end CheegerGromovCompactness
end DifferentialGeometry
