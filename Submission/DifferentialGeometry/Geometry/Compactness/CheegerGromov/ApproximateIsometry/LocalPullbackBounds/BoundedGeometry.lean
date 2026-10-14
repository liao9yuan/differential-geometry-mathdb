import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricConvergence.BoundedGeometry
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.DistanceComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open _root_.Set _root_.Filter _root_.Topology _root_.Submission.Topology
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

omit [CompleteSpace E] in
theorem BoundedGeometryNormalChartData.source_stay
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSupportedCenterMapConvergenceOn (I := I) inp P L r hr phi hphi d.chart
      U C0 C1 aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r) {R S eta : Real}
    (hRS : R < S) (heta : 0 < eta)
    (kn : Nat → Nat) (z : Nat → E) (zInf : E)
    (hzconv : _root_.Filter.Tendsto z _root_.Filter.atTop (𝓝 zInf))
    (hbuffer : ∀ n, Metric.closedBall (z n) eta ⊆ interior (C0 alpha))
    (hsource : ∀ n,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ (kn n))
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
      (d.chart (Lphi.φ (kn n))
        (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).hom (z n) ∈
          Lphi.hatSourceBall inp.decay P R (kn n)) :
    ∃ q : Real, 0 < q ∧
      let V := Metric.ball zInf q
      let W := Metric.ball zInf (2 * q)
      IsOpen V ∧ IsCompact (closure V) ∧ closure V ⊆ W ∧
        W ⊆ interior (C0 alpha) ∧
        ∀ᶠ n in _root_.Filter.atTop,
          let Lphi := L.subseq hphi
          let Yk := X.obj (Lphi.φ (kn n))
          letI : TopologicalSpace Yk.M := Yk.topology
          letI : ChartedSpace H Yk.M := Yk.charted
          letI : IsManifold I ∞ Yk.M := Yk.smooth
          letI : T2Space Yk.M := Yk.t2
          letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
          letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
          Set.MapsTo
            (d.chart (Lphi.φ (kn n))
              (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).hom
            W (Lphi.hatSourceBall inp.decay P S (kn n)) := by
  classical
  obtain ⟨_hU, _hC0, _hC1, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf alpha
  have hIntU : interior (C0 alpha) ⊆ U alpha :=
    interior_subset.trans (hC01.trans (interior_subset.trans hC1U))
  let q : Real := _root_.Min.min (eta / 8) ((S - R) / 8)
  have hq : 0 < q := by
    dsimp only [q]
    exact lt_min (by positivity) (by linarith)
  have hqEta : q ≤ eta / 8 := min_le_left _ _
  have hqGap : q ≤ (S - R) / 8 := min_le_right _ _
  have hzclose : ∀ᶠ n in _root_.Filter.atTop, _root_.Dist.dist (z n) zInf < q := by
    rw [_root_.Filter.eventually_atTop]
    exact (Metric.tendsto_atTop.1 hzconv) q hq
  obtain ⟨Nclose, hNclose⟩ := eventually_atTop.mp hzclose
  have hclose0 : _root_.Dist.dist (z Nclose) zInf < q := hNclose Nclose le_rfl
  refine ⟨q, hq, Metric.isOpen_ball, ?_, ?_, ?_, ?_⟩
  · rw [closure_ball zInf hq.ne']
    exact _root_.ProperSpace.isCompact_closedBall zInf q
  · rw [closure_ball zInf hq.ne']
    exact Metric.closedBall_subset_ball (by linarith)
  · intro w hw
    have hwz : _root_.Dist.dist w (z Nclose) < eta := by
      calc
        dist w (z Nclose) ≤ _root_.Dist.dist w zInf + _root_.Dist.dist zInf (z Nclose) :=
          dist_triangle _ _ _
        _ < 2 * q + q := by
          have hw' : _root_.Dist.dist w zInf < 2 * q := Metric.mem_ball.mp hw
          rw [dist_comm zInf (z Nclose)]
          exact add_lt_add hw' hclose0
        _ < eta := by linarith
    exact hbuffer Nclose (Metric.mem_closedBall.mpr hwz.le)
  · filter_upwards [hzclose] with n hn
    dsimp only
    let Lphi := L.subseq hphi
    let Yk := X.obj (Lphi.φ (kn n))
    let : TopologicalSpace Yk.M := Yk.topology
    let : ChartedSpace H Yk.M := Yk.charted
    let : IsManifold I ∞ Yk.M := Yk.smooth
    let : T2Space Yk.M := Yk.t2
    let : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    let : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
    let ck := seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat)
    let chiK := d.chart (Lphi.φ (kn n)) ck
    intro w hw
    have hwzq : _root_.Dist.dist w (z n) < 3 * q := by
      calc
        dist w (z n) ≤ _root_.Dist.dist w zInf + _root_.Dist.dist zInf (z n) := dist_triangle _ _ _
        _ < 2 * q + q := by
          have hw' : _root_.Dist.dist w zInf < 2 * q := Metric.mem_ball.mp hw
          rw [dist_comm zInf (z n)]
          exact add_lt_add hw' hn
        _ = 3 * q := by ring
    have hwz : _root_.Dist.dist w (z n) < eta := by linarith
    have hsegInt : segment Real w (z n) ⊆ interior (C0 alpha) := by
      refine (segment_subset_closedBall_right w (z n)).trans ?_
      exact (Metric.closedBall_subset_closedBall hwz.le).trans (hbuffer n)
    obtain ⟨hRad, _hMaps⟩ :=
      hdata.geom_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf
        (kn n) alpha
    have hEquiv : chiK.MetricEquivOn Yk.metric (U alpha) := by
      intro v hv xi
      exact d.metric_equiv (Lphi.φ (kn n)) ck v (hRad hv) xi
    have hUsrc : U alpha ⊆ chiK.hom.source := by
      intro v hv
      exact chiK.ball_subset (hRad hv)
    have hman := NormalBallChart.MetricEquivOn.hom_dist_le
      (J := I) Yk (P (Lphi.φ (kn n))) chiK hEquiv hUsrc
        (hsegInt.trans hIntU)
    have hsqrt : Real.sqrt 2 ≤ 2 := by
      linarith [Real.sqrt_two_lt_three_halves]
    have hlocal : _root_.Dist.dist (chiK.hom w) (chiK.hom (z n)) < S - R := by
      calc
        _root_.Dist.dist (chiK.hom w) (chiK.hom (z n)) ≤
            Real.sqrt 2 * _root_.Dist.dist w (z n) := hman
        _ ≤ 2 * _root_.Dist.dist w (z n) :=
          mul_le_mul_of_nonneg_right hsqrt dist_nonneg
        _ < S - R := by linarith
    have hzSource : _root_.Dist.dist (chiK.hom (z n)) Yk.basepoint ≤ R := by
      simpa only [NetLimitData.hatSourceBall, Metric.mem_closedBall,
        chiK, ck, Yk, Lphi] using hsource n
    have hdist : _root_.Dist.dist (chiK.hom w) Yk.basepoint < S := by
      calc
        _root_.Dist.dist (chiK.hom w) Yk.basepoint ≤
            _root_.Dist.dist (chiK.hom w) (chiK.hom (z n)) +
              dist (chiK.hom (z n)) Yk.basepoint := dist_triangle _ _ _
        _ < (S - R) + R := add_lt_add_of_lt_of_le hlocal hzSource
        _ = S := by ring
    change _root_.Dist.dist (chiK.hom w) Yk.basepoint ≤ S
    exact hdist.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.BoundedGeometryNormalChartData.source_stay then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.BoundedGeometryNormalChartData.source_stay"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.BoundedGeometryNormalChartData.source_stay ``Submission.DifferentialGeometry.CheegerGromovCompactness.BoundedGeometryNormalChartData.source_stay

end CheegerGromovCompactness
end DifferentialGeometry
