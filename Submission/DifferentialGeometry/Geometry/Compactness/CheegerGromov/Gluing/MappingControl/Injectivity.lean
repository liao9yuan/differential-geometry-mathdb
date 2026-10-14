import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.Source.Buffer
import Submission.DifferentialGeometry.Analysis.Calculus.Inverse.DerivativePerturbation


import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.MappingControl.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open _root_.Set _root_.Filter _root_.Topology _root_.Submission.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

theorem HasStageJetConvergence.inj_tail
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {s : Real} (hs : 0 ≤ s)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hcomplete : ∀ j, MetricComplete (I := I) (X.obj j))
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack s → Set E)
    (aInf : (alpha : LiveSlot L inp.pack s) →
      Fin (inp.pack.A s) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack s) →
      InterSlot L inp.pack s alpha → E → E)
    (gInf : LiveSlot L inp.pack s →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetConvergence (I := I) inp P L hs phi hphi
      U C0 C1 aInf Jinf Jbarinf gInf)
    (R0 R1 : Real)
    (hroom : R0 + (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 < R1)
    (hR1s : R1 < s) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ k)
      letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
      Set.InjOn (stageComparisonMap inp P Lphi s hs k l)
        (Lphi.hatSourceBall inp.decay P R0 k) := by
  classical
  have hstage0 := hstage
  rcases hstage with ⟨hdata, _hmetric, hjets, _hbase⟩
  have hlam0 : 0 < inp.decay.lambda inp.D 0 :=
    inp.decay.lambda_pos inp.divisor_pos 0
  have hcoef : 0 <
      (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 := by positivity
  have hR0R1 : R0 < R1 := by linarith
  have hR0s : R0 < s := hR0R1.trans hR1s
  obtain ⟨rho0, hrho0, hbuffer⟩ :=
    hdata.metric_buffer inp P L s hs U C0 C1 aInf Jinf Jbarinf
      hcomplete hconn
  let rho : Real := _root_.Min.min rho0 (R1 - R0)
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact lt_min hrho0 (sub_pos.mpr hR0R1)
  have hrho_le : rho ≤ rho0 := min_le_left _ _
  have hrho_room : rho ≤ R1 - R0 := min_le_right _ _
  obtain ⟨Nret, hret⟩ := hstage0.return_tail inp P L hs phi hphi
    U C0 C1 aInf Jinf Jbarinf gInf R0 R1 hroom hR1s
      (rho / 4) (div_pos hrho (by norm_num))
  obtain ⟨Njet, hjet⟩ := hjets R1 hR1s 1 (1 / 2 : Real) (by norm_num)
  refine ⟨max Nret Njet, ?_⟩
  intro k hk l hl
  have hkRet : Nret ≤ k := (le_max_left _ _).trans hk
  have hlRet : Nret ≤ l := (le_max_left _ _).trans hl
  have hkJet : Njet ≤ k := (le_max_right _ _).trans hk
  have hlJet : Njet ≤ l := (le_max_right _ _).trans hl
  dsimp only
  let Lphi := L.subseq hphi
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
  let : TopologicalSpace Yk.M := Yk.topology
  let : ChartedSpace H Yk.M := Yk.charted
  let : IsManifold I ∞ Yk.M := Yk.smooth
  let : T2Space Yk.M := Yk.t2
  let : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  let : TopologicalSpace Yl.M := Yl.topology
  let : ChartedSpace H Yl.M := Yl.charted
  let : IsManifold I ∞ Yl.M := Yl.smooth
  let : T2Space Yl.M := Yl.t2
  let : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  let : MetricSpace Yk.M := (P (Lphi.φ k)).ms
  let : MetricSpace Yl.M := (P (Lphi.φ l)).ms
  let F := stageComparisonMap inp P Lphi s hs k l
  let Hret := stageComparisonMap inp P Lphi s hs l k
  intro x hx y hy hFxy
  have hFxy' : F x = F y := by
    simpa only [F] using hFxy
  have hretx := hret k l hkRet hlRet x hx
  have hrety := hret k l hkRet hlRet y hy
  have hxyHalf : _root_.Dist.dist y x < rho / 2 := by
    calc
      dist y x ≤ _root_.Dist.dist y (Hret (F y)) + _root_.Dist.dist (Hret (F y)) x :=
        dist_triangle _ _ _
      _ = _root_.Dist.dist (Hret (F y)) y + _root_.Dist.dist (Hret (F x)) x := by
        rw [dist_comm y (Hret (F y)), hFxy']
      _ < rho / 4 + rho / 4 := by
        simpa only [F, Hret] using add_lt_add hrety hretx
      _ = rho / 2 := by ring
  have hxy : _root_.Dist.dist y x < rho0 :=
    hxyHalf.trans_le (by linarith [hrho, hrho_le])
  have hxLarge : x ∈ Lphi.hatSourceBall inp.decay P s k :=
    cball_subset_of_le hR0s.le hx
  obtain ⟨alpha, z, hzx, hball, hcoord⟩ := hbuffer k x hxLarge
  let ck := seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
  let cl := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric ck
  let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric cl
  have hxBall : x ∈ Metric.ball x rho0 := Metric.mem_ball_self hrho0
  have hyBall : y ∈ Metric.ball x rho0 := by
    simpa only [Metric.mem_ball] using hxy
  obtain ⟨zx, hzxInt, hzxEq⟩ := hball hxBall
  obtain ⟨zy, hzyInt, hzyEq⟩ := hball hyBall
  obtain ⟨_hUopen, _hC0compact, _hC1compact, hC01, hC1U⟩ :=
    hdata.core_on inp P L s hs U C0 C1 aInf Jinf Jbarinf alpha
  obtain ⟨hconv, _hzero⟩ :=
    hdata.core_shape inp P L s hs U C0 C1 aInf Jinf Jbarinf alpha
  obtain ⟨hUmetric, hUexp, _hUmap⟩ :=
    hdata.geom_on inp P L s hs U C0 C1 aInf Jinf Jbarinf k alpha
  have hIntU : interior (C0 alpha) ⊆ U alpha :=
    interior_subset.trans (hC01.trans interior_subset |>.trans hC1U)
  have hUtgt : U alpha ⊆ chiK.target := by
    intro w hw
    have hwBall := hUexp hw
    rw [Metric.mem_ball, dist_zero_right] at hwBall
    change w ∈ (NormalCoordinates.expMapDiffeo
      (I := I) Yk.metric ck).source
    apply mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Yk.metric ck
    exact hwBall
  have hchiX : chiK x = zx := by
    rw [← hzxEq]
    exact chiK.right_inv (hUtgt (hIntU hzxInt))
  have hchiY : chiK y = zy := by
    rw [← hzyEq]
    exact chiK.right_inv (hUtgt (hIntU hzyInt))
  have hcoordX0 := hcoord x hxBall
  rw [← ProperMetricOn.dist_eq inp.decay inp.realizes P (Lphi.φ k) x x,
      dist_self, _root_.MulZeroClass.mul_zero] at hcoordX0
  have hcoordX0' : _root_.Dist.dist (chiK x) z ≤ 0 := by
    simpa only [chiK, ck, Yk, Lphi] using hcoordX0
  have hzxCoord : zx = z := by
    apply dist_le_zero.mp
    simpa only [hchiX] using hcoordX0'
  have hcoordY0 := hcoord y hyBall
  rw [← ProperMetricOn.dist_eq inp.decay inp.realizes P (Lphi.φ k) y x]
      at hcoordY0
  have hcoordYX : _root_.Dist.dist zy zx ≤ Real.sqrt 2 * _root_.Dist.dist y x := by
    rw [hzxCoord]
    simpa only [chiK, ck, Yk, Lphi, hchiY] using hcoordY0
  have hequiv : NormalCoordMetricEquivOn (I := I) Yk ck (U alpha) := by
    intro w hw v
    exact inp.normalBounds.metric_equiv (Lphi.φ k) ck w (hUmetric hw) v
  let G : E → E := fun w ↦ chiL (F (chiK.symm w))
  have hsegInt : segment Real zx zy ⊆ interior (C0 alpha) :=
    hconv.interior.segment_subset hzxInt hzyInt
  have hsegR1 : ∀ w ∈ segment Real zx zy, chiK.symm w ∈
      Lphi.hatSourceBall inp.decay P R1 k := by
    intro w hw
    have hwInt := hsegInt hw
    have hwClosed : w ∈ Metric.closedBall zx (_root_.Dist.dist zx zy) :=
      segment_subset_closedBall_left zx zy hw
    have hwCoord : _root_.Dist.dist w zx ≤ _root_.Dist.dist zx zy := Metric.mem_closedBall.mp hwClosed
    have hsegU : segment Real w zx ⊆ U alpha := by
      intro q hq
      exact hIntU (hconv.interior.segment_subset hwInt hzxInt hq)
    have hsymm := NormalCoordMetricEquivOn.symm_dist_le
      (I := I) Yk (P (Lphi.φ k)) hequiv hUtgt hsegU
    have hlocal : _root_.Dist.dist (chiK.symm w) x < rho := by
      rw [← hzxEq]
      calc
        _root_.Dist.dist (chiK.symm w) (chiK.symm zx) ≤
            Real.sqrt 2 * _root_.Dist.dist w zx := by
          simpa only [chiK] using hsymm
        _ ≤ Real.sqrt 2 * _root_.Dist.dist zx zy := by gcongr
        _ ≤ Real.sqrt 2 * (Real.sqrt 2 * _root_.Dist.dist y x) := by
          gcongr
          simpa only [dist_comm] using hcoordYX
        _ = 2 * _root_.Dist.dist y x := by
          rw [← mul_assoc, Real.mul_self_sqrt (by norm_num : (0 : Real) ≤ 2)]
        _ < rho := by linarith
    rw [NetLimitData.hatSourceBall, Metric.mem_closedBall]
    have hxR0 : _root_.Dist.dist x Yk.basepoint ≤ R0 := by
      change _root_.Dist.dist x Yk.basepoint ≤ R0 at hx
      exact hx
    have hlt : _root_.Dist.dist (chiK.symm w) Yk.basepoint < R1 := by
      calc
        _root_.Dist.dist (chiK.symm w) Yk.basepoint ≤
            dist (chiK.symm w) x + _root_.Dist.dist x Yk.basepoint := dist_triangle _ _ _
        _ < rho + R0 := add_lt_add_of_lt_of_le hlocal hxR0
        _ ≤ R1 := by linarith
    exact hlt.le
  have hsegDiff : ∀ w ∈ segment Real zx zy, DifferentiableAt Real G w := by
    intro w hw
    have hwInt := hsegInt hw
    have hwR1 := hsegR1 w hw
    have hout := hjet k hkJet l hlJet alpha w
      (interior_subset hwInt) hwInt hwR1
    with_unfolding_all
      exact hout.2.1.differentiableAt (by simp)
  have hsegBd : ∀ w ∈ segment Real zx zy,
      ‖ContinuousLinearMap.id Real E - fderiv Real G w‖ ≤ (1 / 2 : Real) := by
    intro w hw
    have hwInt := hsegInt hw
    have hwR1 := hsegR1 w hw
    have hout := hjet k hkJet l hlJet alpha w
      (interior_subset hwInt) hwInt hwR1
    have hdiff : DifferentiableAt Real G w := hsegDiff w hw
    have hraw : mapDerivNorm 1 G id w ≤ (1 / 2 : Real) := by
      with_unfolding_all
        exact hout.2.2 1 le_rfl
    exact neumannOfDerivNorm hdiff hraw
  have hGinj : Set.InjOn G (segment Real zx zy) :=
    Coordinates.injOn_of_fderiv_near_id (convex_segment zx zy)
      (by norm_num) hsegDiff hsegBd
  have hGxy : G zx = G zy := by
    dsimp only [G]
    rw [hzxEq, hzyEq, hFxy']
  have hzyeq : zx = zy :=
    hGinj (left_mem_segment Real zx zy) (right_mem_segment Real zx zy) hGxy
  calc
    x = chiK.symm zx := hzxEq.symm
    _ = chiK.symm zy := congrArg chiK.symm hzyeq
    _ = y := hzyEq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HasStageJetConvergence.inj_tail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HasStageJetConvergence.inj_tail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HasStageJetConvergence.inj_tail ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasStageJetConvergence.inj_tail

end CheegerGromovCompactness
end DifferentialGeometry
