import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.CarrierKineticEnergy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Function _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology _root_.Interval
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {N : Type u} [UniformSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N]
variable {D : RealTimeInterval}

theorem lRegularizedAction_chart_of_carrier
    (S : SolutionOn (I := I) (M := N) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := N) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := N) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b)
    (p : Fin m → N) (gamma : Real → N)
    (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i, _root_.Set.MapsTo gamma
      (_root_.Set.Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i, _root_.Set.EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i)))
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.carrier) :
    lRegularizedAction S T gamma a b =
      ∑ i : Fin m, (
        (∫ r in (0 : Real)..partitionIntervalLength t i, (1 / 2 : Real) * _root_.Inner.inner Real
          (chartGramOp (I := I) S.family (p i)
            (T - (t i.castSucc + r) ^ 2, (u i).toFun r) ((u i).deriv r))
          ((u i).deriv r)) +
        (∫ s in (t i.castSucc)..(t i.succ),
          2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s))) := by
  classical
  have hab : a ≤ b := by
    rw [← ht0, ← htlast]
    exact htmono (Fin.zero_le _)
  have hleft (i : Fin m) : a ≤ t i.castSucc := by
    rw [← ht0]
    exact htmono (Fin.zero_le _)
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ :=
    htmono Fin.castSucc_lt_succ.le
  have hright (i : Fin m) : t i.succ ≤ b := by
    rw [← htlast]
    exact htmono (Fin.le_last _)
  have hreg_i (i : Fin m) (s : Real) (hs : s ∈ _root_.Set.Icc (t i.castSucc) (t i.succ)) :
      T - s ^ 2 ∈ D.carrier :=
    hreg s ⟨(hleft i).trans hs.1, hs.2.trans (hright i)⟩
  have hcarrier_i (i : Fin m) :
      ∀ s ∈ _root_.Set.uIcc (t i.castSucc) (t i.succ), T - s ^ 2 ∈ D.carrier := by
    intro s hs
    apply hreg_i i s
    simpa only [_root_.Set.uIcc_of_le (hseg i)] using hs
  have hcont (i : Fin m) :
      ContinuousOn gamma (_root_.Set.Icc (t i.castSucc) (t i.succ)) :=
    curve_cont_local I (p i) gamma (u i) (hseg i) (hsrc i) (hrep i)
  have hkinInt (i : Fin m) : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (gamma s)
          (lVelocity (I := I) gamma s) (lVelocity (I := I) gamma s))
      volume (t i.castSucc) (t i.succ) :=
    intervalIntegrable_lKinetic_of_chartH1_of_carrier S hMet T gamma (p i) (t i.castSucc) (t i.succ)
      (hseg i) (u i) (hsrc i) (hrep i) (hreg_i i)
  have hpotInt (i : Fin m) : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s))
      volume (t i.castSucc) (t i.succ) :=
    lScalar_int (I := I) S hSc T (t i.castSucc) (t i.succ) gamma
      (hcarrier_i i) (by
        simpa only [_root_.Set.uIcc_of_le (hseg i)] using hcont i)
  let kin : Fin m → Real := fun i ↦
    ∫ s in t i.castSucc..t i.succ, (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (gamma s)
        (lVelocity (I := I) gamma s) (lVelocity (I := I) gamma s)
  let pot : Fin m → Real := fun i ↦
    ∫ s in t i.castSucc..t i.succ,
      2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s)
  have hsplit (i : Fin m) :
      lRegularizedAction S T gamma (t i.castSucc) (t i.succ) = kin i + pot i := by
    simpa only [lRegularizedAction, lRegularizedLagrangian, kin, pot] using
      intervalIntegral.integral_add (hkinInt i) (hpotInt i)
  have hkinChart (i : Fin m) : kin i =
      ∫ r in (0 : Real)..partitionIntervalLength t i, (1 / 2 : Real) * _root_.Inner.inner Real
        (chartGramOp (I := I) S.family (p i)
          (T - (t i.castSucc + r) ^ 2, (u i).toFun r) ((u i).deriv r))
        ((u i).deriv r) := by
    simpa only [kin, partitionIntervalLength, smul_apply, real_inner_smul_left] using
      lKinetic_eq_chart_integral S T gamma (p i) (t i.castSucc) (t i.succ)
        (hseg i) (u i) (hsrc i) (hrep i)
  have hLag (i : Fin m) : IntervalIntegrable (lRegularizedLagrangian S T gamma) _root_.MeasureTheory.MeasureSpace.volume
      (t i.castSucc) (t i.succ) := by
    with_unfolding_all exact (hkinInt i).add (hpotInt i)
  let tNat : Nat → Real := fun k ↦
    if hk : k < m + 1 then t ⟨k, hk⟩ else b
  have hsum : (∑ i : Fin m,
      lRegularizedAction S T gamma (t i.castSucc) (t i.succ)) =
      lRegularizedAction S T gamma a b := by
    calc
      (∑ i : Fin m, lRegularizedAction S T gamma (t i.castSucc) (t i.succ)) =
          ∑ k ∈ Finset.range m,
            lRegularizedAction S T gamma (tNat k) (tNat (k + 1)) := by
        rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k < m := Finset.mem_range.mp hk
        have hk0 : k ≤ m := Nat.le_of_lt hk'
        have hk1 : k + 1 ≤ m := Nat.succ_le_of_lt hk'
        rw [dif_pos hk']
        simp only [tNat, Nat.lt_succ_iff, dif_pos hk0, dif_pos hk1]
        congr 2
      _ = lRegularizedAction S T gamma (tNat 0) (tNat m) :=
        lRegularizedAction_sum S T gamma (fun k hk ↦ by
          have hk' : k < m := hk
          simp only [tNat, dif_pos (Nat.lt_trans hk' (Nat.lt_succ_self m)),
            dif_pos (Nat.succ_lt_succ hk')]
          with_unfolding_all exact hLag ⟨k, hk'⟩)
      _ = lRegularizedAction S T gamma a b := by
        simp only [tNat, dif_pos (Nat.succ_pos m),
          dif_pos (Nat.lt_succ_self m)]
        change lRegularizedAction S T gamma (t 0) (t (Fin.last m)) =
          lRegularizedAction S T gamma a b
        rw [ht0, htlast]
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsplit i, hkinChart i]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_chart_of_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_chart_of_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_chart_of_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_chart_of_carrier


end DifferentialGeometry.PDE.RicciFlow.Perelman
