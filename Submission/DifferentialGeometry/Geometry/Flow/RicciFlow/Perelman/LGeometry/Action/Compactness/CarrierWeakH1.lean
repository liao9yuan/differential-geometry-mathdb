import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.KineticEnergy
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Coercivity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.Scalar
import Submission.DifferentialGeometry.Geometry.Operator.Family.Gram.CarrierCompactness
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Chart.H1
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Curve.Partition
import Submission.DifferentialGeometry.Topology.Manifold.CurveChart.Subdivision
import Submission.DifferentialGeometry.Topology.UniformConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.Interval

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [UniformSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {D : RealTimeInterval}

theorem exists_chartH1_weakly_convergent_subsequence_of_compact_range_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) {m : ℕ} (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a) (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (alpha : ℕ → Real → M)
    (Q : Set M) (hQ : IsCompact Q)
    (hval : ∀ n s, s ∈ _root_.Set.Icc a b → alpha n s ∈ Q)
    (hLag : ∀ n, IntervalIntegrable (lRegularizedLagrangian S T (alpha n)) _root_.MeasureTheory.MeasureSpace.volume a b)
    (u : (i : Fin m) → ℕ → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i n, _root_.Set.MapsTo (alpha n) (_root_.Set.Icc (t i.castSucc) (t i.succ))
      (chartAt H (p i)).source)
    (hrep : ∀ i n, _root_.Set.EqOn (u i n).toFun
      (fun r ↦ extChartAt I (p i) (alpha n (t i.castSucc + r)))
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i)))
    (K : Fin m → Set E) (hKc : ∀ i, IsCompact (K i))
    (hKchart : ∀ i, K i ⊆ (extChartAt I (p i)).target)
    (huK : ∀ i n (r : _root_.Set.Icc (0 : Real) (partitionIntervalLength t i)),
      (u i n).toFun r.1 ∈ K i)
    {A : Real} (hact : ∀ n, lRegularizedAction S T (alpha n) a b ≤ A)
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.carrier) :
    ∃ (phi : ℕ → ℕ)
      (uLim : (i : Fin m) → timeH1 E (partitionIntervalLength t i)),
      StrictMono phi ∧
        (∀ i (z : timeL2 E (partitionIntervalLength t i)),
          _root_.Filter.Tendsto (fun n ↦ _root_.Inner.inner Real (u i (phi n)).deriv z) _root_.Filter.atTop
            (nhds (_root_.Inner.inner Real (uLim i).deriv z))) ∧
        (∀ i, TendstoUniformly
          (fun n (r : _root_.Set.Icc (0 : Real) (partitionIntervalLength t i)) ↦
            (u i (phi n)).toFun r.1)
          (fun r ↦ (uLim i).toFun r.1) _root_.Filter.atTop) := by
  classical
  have hab : a ≤ b := by
    rw [← ht0, ← htlast]
    exact htmono (Fin.zero_le _)
  let kin : ℕ → Real := fun n ↦ ∫ s in a..b, (1 / 2 : Real) *
    (S.base.metric (T - s ^ 2)).inner (alpha n s)
      (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s)
  let pot : ℕ → Real := fun n ↦
    ∫ s in a..b, 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s)
  have hcarrier : ∀ s ∈ _root_.Set.uIcc a b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    exact hreg s (by simpa only [_root_.Set.uIcc_of_le hab] using hs)
  have hcont (n : ℕ) : ContinuousOn (alpha n) (_root_.Set.Icc a b) := by
    have hpiece (i : Fin m) :
        ContinuousOn (alpha n) (_root_.Set.Icc (t i.castSucc) (t i.succ)) :=
      curve_cont_local I (p i) (alpha n) (u i n)
        (htmono Fin.castSucc_lt_succ.le) (hsrc i n) (hrep i n)
    have hprefix (i : Fin (m + 1)) :
        ContinuousOn (alpha n) (_root_.Set.Icc (t 0) (t i)) := by
      induction i using Fin.induction with
      | zero => simpa only [_root_.Set.Icc_self] using continuousOn_singleton (alpha n) (t 0)
      | succ i ih =>
        have hunion := ih.union_of_isClosed (hpiece i) isClosed_Icc isClosed_Icc
        rwa [_root_.Set.Icc_union_Icc_eq_Icc (htmono (Fin.zero_le _))
          (htmono Fin.castSucc_lt_succ.le)] at hunion
    simpa only [ht0, htlast] using hprefix (Fin.last m)
  have hpotInt (n : ℕ) : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s)) _root_.MeasureTheory.MeasureSpace.volume a b :=
    lScalar_int (I := I) S hSc T a b (alpha n) hcarrier (by
      simpa only [_root_.Set.uIcc_of_le hab] using hcont n)
  have hkinInt (n : ℕ) : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha n s)
          (lVelocity (I := I) (alpha n) s)
          (lVelocity (I := I) (alpha n) s)) _root_.MeasureTheory.MeasureSpace.volume a b := by
    simpa only [lRegularizedLagrangian, add_sub_cancel_right] using (hLag n).sub (hpotInt n)
  have hsplit (n : ℕ) : lRegularizedAction S T (alpha n) a b = kin n + pot n := by
    simpa only [lRegularizedAction, lRegularizedLagrangian, kin, pot] using
      intervalIntegral.integral_add (hkinInt n) (hpotInt n)
  obtain ⟨C, hC⟩ := lScalar_lower_compact (I := I) S hSc T a b hcarrier Q hQ
  have hpotLower (n : ℕ) : C * (b - a) ≤ pot n := by
    have hmono := intervalIntegral.integral_mono_on hab
      intervalIntegrable_const (hpotInt n) (fun s hs ↦
        hC s (by simpa only [_root_.Set.uIcc_of_le hab] using hs) (alpha n s) (hval n s hs))
    rw [intervalIntegral.integral_const] at hmono
    simpa only [pot, smul_eq_mul, mul_comm] using hmono
  let B : Real := A - C * (b - a)
  have hkinBound (n : ℕ) : kin n ≤ B := by
    have ha := hact n
    rw [hsplit n] at ha
    dsimp only [B]
    linarith [ha, hpotLower n]
  have hkinNonneg (n : ℕ) :
      ∀ᵐ s ∂volume.restrict (_root_.Set.Ioc a b), 0 ≤ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha n s)
          (lVelocity (I := I) (alpha n) s)
          (lVelocity (I := I) (alpha n) s) := by
    apply Eventually.of_forall
    intro s
    apply mul_nonneg (by norm_num)
    let v := lVelocity (I := I) (alpha n) s
    by_cases hv : v = 0
    · change 0 ≤ (S.base.metric (T - s ^ 2)).inner (alpha n s) v v
      rw [hv]
      simp
    · exact ((S.base.metric (T - s ^ 2)).pos (alpha n s) v hv).le
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ :=
    htmono Fin.castSucc_lt_succ.le
  have hleft (i : Fin m) : a ≤ t i.castSucc := by
    rw [← ht0]
    exact htmono (Fin.zero_le _)
  have hright (i : Fin m) : t i.succ ≤ b := by
    rw [← htlast]
    exact htmono (Fin.le_last _)
  have hpiece (i : Fin m) (n : ℕ) :
      (∫ s in t i.castSucc..t i.succ, (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha n s)
          (lVelocity (I := I) (alpha n) s)
          (lVelocity (I := I) (alpha n) s)) ≤ B := by
    have hmono :
        (∫ s in t i.castSucc..t i.succ, (1 / 2 : Real) *
          (S.base.metric (T - s ^ 2)).inner (alpha n s)
            (lVelocity (I := I) (alpha n) s)
            (lVelocity (I := I) (alpha n) s)) ≤ kin n := by
      exact intervalIntegral.integral_mono_interval (hleft i) (hseg i) (hright i)
        (hkinNonneg n) (hkinInt n)
    exact hmono.trans (hkinBound n)
  have hchart (i : Fin m) (n : ℕ) :
      (∫ r in (0 : Real)..partitionIntervalLength t i, (1 / 2 : Real) * _root_.Inner.inner Real
        (chartGramOp (I := I) S.family (p i)
          (T - (t i.castSucc + r) ^ 2, (u i n).toFun r) ((u i n).deriv r))
        ((u i n).deriv r)) ≤ B := by
    have heq :
        (∫ r in (0 : Real)..partitionIntervalLength t i,
          (1 / 2 : Real) * _root_.Inner.inner Real
            (chartGramOp (I := I) S.family (p i)
              (T - (t i.castSucc + r) ^ 2, (u i n).toFun r) ((u i n).deriv r))
            ((u i n).deriv r)) =
          ∫ s in t i.castSucc..t i.succ, (1 / 2 : Real) *
            (S.base.metric (T - s ^ 2)).inner (alpha n s)
              (lVelocity (I := I) (alpha n) s)
              (lVelocity (I := I) (alpha n) s) := by
      simpa only [partitionIntervalLength, smul_apply, real_inner_smul_left] using
        (lKinetic_eq_chart_integral S T (alpha n) (p i) (t i.castSucc) (t i.succ)
          (hseg i) (u i n) (hsrc i n) (hrep i n)).symm
    rw [heq]
    exact hpiece i n
  have hτc (i : Fin m) : ContinuousOn
      (fun r : Real ↦ T - (t i.castSucc + r) ^ 2)
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i)) :=
    (continuous_const.sub ((continuous_const.add continuous_id).pow 2)).continuousOn
  have hτregularity (i : Fin m) : _root_.Set.MapsTo
      (fun r : Real ↦ T - (t i.castSucc + r) ^ 2)
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i)) D.carrier := by
    intro r hr
    change r ∈ _root_.Set.Icc (0 : Real) (t i.succ - t i.castSucc) at hr
    apply hreg (t i.castSucc + r)
    exact ⟨by linarith [hleft i, hr.1], by linarith [hr.2, hright i]⟩
  exact chartH1_fin_of_carrier (I := I) hMet p
    (fun i ↦ partitionIntervalLength t i) (fun i ↦ by
      change 0 ≤ t i.succ - t i.castSucc
      exact sub_nonneg.mpr (hseg i))
    (fun i r ↦ T - (t i.castSucc + r) ^ 2) hτc hτregularity K hKc hKchart
    u (fun _ ↦ B) huK hchart

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_chartH1_weakly_convergent_subsequence_of_compact_range_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_chartH1_weakly_convergent_subsequence_of_compact_range_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_chartH1_weakly_convergent_subsequence_of_compact_range_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_chartH1_weakly_convergent_subsequence_of_compact_range_carrier

end DifferentialGeometry.PDE.RicciFlow.Perelman
