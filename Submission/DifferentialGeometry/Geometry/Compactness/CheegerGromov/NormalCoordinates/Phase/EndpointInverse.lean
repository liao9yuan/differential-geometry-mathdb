import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.Bounds
import Submission.DifferentialGeometry.Analysis.ODE.PhaseFlow.EndpointInverse
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Phase.Smallness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

universe u uE uH

open _root_.Filter _root_.Set _root_.Topology _root_.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal _root_.Topology

namespace DifferentialGeometry
namespace CheegerGromovCompactness

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

theorem exists_normal_q
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X) {r : Real} (hr : 0 < r) :
    ∃ q : NNReal, 0 < q ∧
      4 * (q : Real) < r ∧
      3 * h.metricC 1 * (2 * (q : Real)) ^ 2 ≤ (q : Real) ∧
      PhaseFlow.phaseErr (normalPhaseK h (2 * q)) <
        ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊⁻¹ := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  let threshold : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊⁻¹
  have hthreshold : 0 < threshold := PhaseFlow.freeDiagInv_pos (E := E)
  have htwo : _root_.Filter.Tendsto (fun q : NNReal ↦ 2 * q) (nhds 0) (nhds 0) := by
    have hcont : Continuous (fun q : NNReal ↦ 2 * q) :=
      continuous_const.mul continuous_id
    have hAt : _root_.Filter.Tendsto (fun q : NNReal ↦ 2 * q) (nhds (0 : NNReal))
        (nhds ((fun q : NNReal ↦ 2 * q) 0)) := hcont.continuousAt
    simpa using hAt
  have herrEv : ∀ᶠ q : NNReal in nhds 0,
      PhaseFlow.phaseErr (normalPhaseK h (2 * q)) < threshold :=
    htwo (normalPhaseErr_lt_ev (I := I) h hthreshold)
  obtain ⟨eps, heps, herr⟩ := Metric.eventually_nhds_iff_ball.mp herrEv
  let C : Real := h.metricC 1
  have hC : 0 ≤ C := h.metricC_nonneg 1
  let accelBound : Real := 1 / (24 * (C + 1))
  have hden : 0 < 24 * (C + 1) := mul_pos (by norm_num) (by linarith)
  have haccelBound : 0 < accelBound := one_div_pos.mpr hden
  let qReal : Real := _root_.Min.min (eps / 4) (_root_.Min.min (r / 8) accelBound)
  have hqReal : 0 < qReal := by
    dsimp only [qReal]
    exact lt_min (div_pos heps (by norm_num))
      (lt_min (div_pos hr (by norm_num)) haccelBound)
  let q : NNReal := ⟨qReal, hqReal.le⟩
  have hqEps : qReal ≤ eps / 4 := by
    exact min_le_left _ _
  have hqRadius : qReal ≤ r / 8 := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hqAccel : qReal ≤ accelBound := by
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hqBall : q ∈ Metric.ball (0 : NNReal) eps := by
    rw [Metric.mem_ball, NNReal.dist_eq]
    change |qReal - 0| < eps
    rw [sub_zero, abs_of_pos hqReal]
    exact hqEps.trans_lt (div_lt_self heps (by norm_num))
  have herrQ : PhaseFlow.phaseErr (normalPhaseK h (2 * q)) < threshold :=
    herr q hqBall
  have hqRadius' : 4 * qReal < r := by
    nlinarith
  have hqProd : qReal * (24 * (C + 1)) ≤ 1 := by
    apply (le_div_iff₀ hden).mp
    simpa only [accelBound, one_div] using hqAccel
  have hlinear : 12 * C * qReal ≤ 1 := by
    nlinarith
  have hmul : 0 ≤ qReal * (1 - 12 * C * qReal) :=
    mul_nonneg hqReal.le (sub_nonneg.mpr hlinear)
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hqReal
  · change 4 * qReal < r
    exact hqRadius'
  · change 3 * C * (2 * qReal) ^ 2 ≤ qReal
    nlinarith
  · simpa only [threshold] using herrQ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_normal_q then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_normal_q"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_normal_q ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_normal_q

theorem exists_normal_inv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X)
    (k : Nat) (x : (X.obj k).M) {r : Real} (hr : 0 < r)
    (hrMetric : Metric.ball (0 : E) r ⊆
      Metric.ball (0 : E) (h.radius k x))
    (hrQuarter :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E)
        (Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x / 4)) :
    ∃ (q : NNReal) (Φ : (E × E) → Real → E × E)
        (e : OpenPartialHomeomorph (E × E) (E × E)) (δ : Real),
      0 < q ∧
      4 * (q : Real) < r ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, Φ z 0 = z) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        ContinuousOn (Φ z) (_root_.Set.Icc 0 1)) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ _root_.Set.Ico 0 1,
        HasDerivWithinAt (Φ z)
          (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t))
          (_root_.Set.Ici t) t) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ _root_.Set.Icc 0 1,
        Φ z t ∈ normalPhaseBox r (2 * q)) ∧
      0 < δ ∧
      e.source = Metric.ball (0 : E × E) q ∧
      (e : E × E → E × E) = (fun z ↦ (z.1, (Φ z 1).1)) ∧
      Metric.closedBall ((fun z ↦ (z.1, (Φ z 1).1)) 0) δ ⊆ e.target := by
  obtain ⟨q, hq, hqRadius, hqAccel, herr⟩ :=
    exists_normal_q (I := I) h hr
  obtain ⟨Φ, hΦ0, hΦcont, hΦderiv, hΦbox, happrox⟩ :=
    exists_normalFlow (I := I) h k x hrMetric hrQuarter q hq hqRadius hqAccel
  obtain ⟨e, δ, hδ, hsource, hcoe, htarget, _⟩ :=
    PhaseFlow.exists_quant_inv hq happrox herr
  exact ⟨q, Φ, e, δ, hq, hqRadius, hΦ0, hΦcont, hΦderiv, hΦbox,
    hδ, hsource, hcoe, htarget⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_normal_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_normal_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_normal_inv ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_normal_inv

end CheegerGromovCompactness
end DifferentialGeometry
