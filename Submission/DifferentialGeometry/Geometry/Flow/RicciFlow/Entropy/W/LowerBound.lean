import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.LogSobolev
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Gradient
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Estimate

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

open _root_.Submission.DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open _root_.MeasureTheory _root_.Set

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal

private local instance instMeasurableSpaceM
    {M : Type*} [TopologicalSpace M] : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instMeasurableSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Entropy.instMeasurableSpaceM target :: scope.openDecls } }
private local instance instBorelSpaceM
    {M : Type*} [TopologicalSpace M] : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instBorelSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Entropy.instBorelSpaceM target :: scope.openDecls } }

theorem w_fixed_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 3)
    (tauMax : Real) :
    ∃ B : Real, ∀ {tau : Real}, tau ∈ _root_.Set.Ioc 0 tauMax ->
      ∀ {v : M -> Real}, ContMDiff I 𝓘(Real, Real) ∞ v ->
        (∀ x : M, 0 < v x) ->
        (∫ x, v x ^ 2 ∂(riemannianVolumeMeasure I M g)) = 1 ->
        B ≤
          wFunctional (riemannianVolumeMeasure I M g) 3 tau
            (fun x => metricScalarAt (I := I) (M := M) g x)
            (fun x =>
              g.inner x
                (gradientFun (I := I) g
                  (perelmanPotential 3 tau (fun y => v y * v y)) x)
                (gradientFun (I := I) g
                  (perelmanPotential 3 tau (fun y => v y * v y)) x))
            (perelmanPotential 3 tau (fun y => v y * v y)) := by
  classical
  let μ := riemannianVolumeMeasure I M g
  let : _root_.MeasureTheory.IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let R : M -> Real := fun x => metricScalarAt (I := I) (M := M) g x
  have hRcont : Continuous R := by
    simpa only [R] using (metricScalar_smooth (I := I) (M := M) g).continuous
  obtain ⟨K, hK⟩ := (isCompact_range hRcont.abs).bddAbove
  let K0 := _root_.Max.max 0 K
  have hK0 : 0 ≤ K0 := le_max_left 0 K
  have hRlower (x : M) : -K0 ≤ R x := by
    have habs : |R x| ≤ K := hK ⟨x, rfl⟩
    have habs0 : |R x| ≤ K0 := habs.trans (le_max_right 0 K)
    exact (abs_le.mp habs0).1
  obtain ⟨L, hLog⟩ := logSobolev_closed (I := I) (M := M) g hdim tauMax
  refine ⟨-tauMax * K0 - L - ((3 : Real) / 2) *
      Real.log (4 * Real.pi) - 3, ?_⟩
  intro tau htau v hv hpos hmass
  have htau0 : 0 < tau := htau.1
  have htau_le : tau ≤ tauMax := htau.2
  have hmass' : (∫ x, v x ^ 2 ∂μ) = 1 := by
    simpa only [μ] using hmass
  let energy : M -> Real := fun x =>
    g.inner x
      (gradFun (I := I) g v x)
      (gradFun (I := I) g v x)
  let entropy : M -> Real := fun x => v x ^ 2 * Real.log (v x ^ 2)
  let A : Real := ∫ x, energy x ∂μ
  let S : Real := ∫ x, R x * v x ^ 2 ∂μ
  let Ent : Real := ∫ x, entropy x ∂μ
  have henergy0 (x : M) : 0 ≤ energy x := by
    by_cases hzero : gradFun (I := I) g v x = 0
    · change 0 ≤ g.inner x
        (gradFun (I := I) g v x) (gradFun (I := I) g v x)
      rw [hzero]
      simpa only [map_zero] using (le_refl (0 : Real))
    · exact (g.pos x (gradFun (I := I) g v x) hzero).le
  have hA0 : 0 ≤ A := _root_.MeasureTheory.integral_nonneg henergy0
  have henergy_cont : Continuous energy := by
    have hinner := TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I) (M := M) g
      (gradG (I := I) g ⟨_, hv⟩) (gradG (I := I) g ⟨_, hv⟩)
    exact hinner.congr (fun _ => rfl)
  have hv2cont : Continuous (fun x => v x ^ 2) := hv.continuous.pow 2
  have hR2cont : Continuous (fun x => R x * v x ^ 2) := hRcont.mul hv2cont
  have hentcont : Continuous entropy := by
    have hlogv2 : Continuous (fun x => Real.log (v x ^ 2)) :=
      hv2cont.log fun x => pow_ne_zero 2 (hpos x).ne'
    exact hv2cont.mul hlogv2
  have henergy_int : _root_.MeasureTheory.Integrable energy μ :=
    henergy_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hv2int : _root_.MeasureTheory.Integrable (fun x => v x ^ 2) μ :=
    hv2cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hR2int : _root_.MeasureTheory.Integrable (fun x => R x * v x ^ 2) μ :=
    hR2cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hentint : _root_.MeasureTheory.Integrable entropy μ :=
    hentcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hS0 : -K0 ≤ S := by
    have hnegint : _root_.MeasureTheory.Integrable (fun x => (-K0) * v x ^ 2) μ := hv2int.const_mul _
    have hmono :
        (∫ x, (-K0) * v x ^ 2 ∂μ) ≤ ∫ x, R x * v x ^ 2 ∂μ := by
      exact _root_.MeasureTheory.integral_mono hnegint hR2int fun x =>
        mul_le_mul_of_nonneg_right (hRlower x) (sq_nonneg (v x))
    change -K0 ≤ ∫ x, R x * v x ^ 2 ∂μ
    calc
      -K0 = ∫ x, (-K0) * v x ^ 2 ∂μ := by
        rw [_root_.MeasureTheory.integral_const_mul, hmass']
        ring
      _ ≤ ∫ x, R x * v x ^ 2 ∂μ := hmono
  have hscaledS : -tauMax * K0 ≤ tau * S := by
    calc
      -tauMax * K0 ≤ -tau * K0 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr htau_le) hK0]
      _ ≤ tau * S := by
        simpa only [mul_neg, mul_one, neg_mul] using
          mul_le_mul_of_nonneg_left hS0 htau0.le
  have hLog' := hLog htau hv hpos hmass
  change Ent ≤ 2 * tau * A - ((3 : Real) / 2) * Real.log tau + L at hLog'
  have hW :
      wFunctional μ 3 tau R
          (fun x =>
            g.inner x
              (gradientFun (I := I) g
                (perelmanPotential 3 tau (fun y => v y * v y)) x)
              (gradientFun (I := I) g
                (perelmanPotential 3 tau (fun y => v y * v y)) x))
          (perelmanPotential 3 tau (fun y => v y * v y)) =
        4 * tau * A + tau * S - Ent +
          (Real.log (perelmanDensityPrefactor 3 tau) - 3) := by
    rw [w_square_form μ g 3 htau0 R hv hpos]
    calc
      (∫ x,
          4 * tau * g.inner x
              (gradientFun (I := I) g v x)
              (gradientFun (I := I) g v x) +
            tau * R x * (v x * v x) -
            (v x * v x) * Real.log (v x * v x) +
            (Real.log (perelmanDensityPrefactor 3 tau) - (3 : Real)) *
              (v x * v x) ∂μ) =
          ∫ x,
            (4 * tau) * energy x + tau * (R x * v x ^ 2) - entropy x +
              (Real.log (perelmanDensityPrefactor 3 tau) - 3) * v x ^ 2 ∂μ := by
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp only [energy, entropy, gradient_eq_gradFun, pow_two]
        ring
      _ = 4 * tau * A + tau * S - Ent +
          (Real.log (perelmanDensityPrefactor 3 tau) - 3) := by
        let c := Real.log (perelmanDensityPrefactor 3 tau) - 3
        have hdir : _root_.MeasureTheory.Integrable (fun x => (4 * tau) * energy x) μ :=
          henergy_int.const_mul _
        have hscal : _root_.MeasureTheory.Integrable (fun x => tau * (R x * v x ^ 2)) μ :=
          hR2int.const_mul _
        have hnorm : _root_.MeasureTheory.Integrable (fun x => c * v x ^ 2) μ :=
          hv2int.const_mul _
        calc
          (∫ x, (4 * tau) * energy x + tau * (R x * v x ^ 2) - entropy x +
              c * v x ^ 2 ∂μ) =
              (∫ x, (4 * tau) * energy x + tau * (R x * v x ^ 2) - entropy x ∂μ) +
                ∫ x, c * v x ^ 2 ∂μ := by
            exact _root_.MeasureTheory.integral_add ((hdir.add hscal).sub hentint) hnorm
          _ = ((∫ x, (4 * tau) * energy x + tau * (R x * v x ^ 2) ∂μ) -
                ∫ x, entropy x ∂μ) + ∫ x, c * v x ^ 2 ∂μ := by
            congr 1
            simpa only [Pi.add_apply] using
              (_root_.MeasureTheory.integral_sub (hdir.add hscal) hentint)
          _ = (((∫ x, (4 * tau) * energy x ∂μ) +
                  ∫ x, tau * (R x * v x ^ 2) ∂μ) -
                ∫ x, entropy x ∂μ) + ∫ x, c * v x ^ 2 ∂μ := by
            rw [_root_.MeasureTheory.integral_add hdir hscal]
          _ = 4 * tau * A + tau * S - Ent +
              (Real.log (perelmanDensityPrefactor 3 tau) - 3) := by
            dsimp only [A, S, Ent, c]
            rw [_root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul, hmass']
            ring
  have hpref := log_prefactor 3 htau0
  have hbase : (4 * Real.pi : Real) ≠ 0 :=
    (mul_pos (by norm_num) Real.pi_pos).ne'
  rw [show 4 * Real.pi * tau = (4 * Real.pi) * tau by ring,
    Real.log_mul hbase htau0.ne'] at hpref
  norm_num at hpref
  change -tauMax * K0 - L - ((3 : Real) / 2) * Real.log (4 * Real.pi) - 3 ≤
    wFunctional μ 3 tau R
      (fun x =>
        g.inner x
          (gradientFun (I := I) g
            (perelmanPotential 3 tau (fun y => v y * v y)) x)
          (gradientFun (I := I) g
            (perelmanPotential 3 tau (fun y => v y * v y)) x))
      (perelmanPotential 3 tau (fun y => v y * v y))
  rw [hW, hpref]
  nlinarith [mul_nonneg htau0.le hA0]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.w_fixed_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.w_fixed_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.w_fixed_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.w_fixed_lower

theorem w_density_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 3)
    (tauMax : Real) :
    ∃ B : Real, ∀ {tau : Real}, tau ∈ _root_.Set.Ioc 0 tauMax ->
      ∀ {u : M -> Real}, ContMDiff I 𝓘(Real, Real) ∞ u ->
        (∀ x : M, 0 < u x) ->
        (∫ x, u x ∂(riemannianVolumeMeasure I M g)) = 1 ->
        B ≤
          wFunctional (riemannianVolumeMeasure I M g) 3 tau
            (fun x => metricScalarAt (I := I) (M := M) g x)
            (fun x =>
              g.inner x
                (gradientFun (I := I) g (perelmanPotential 3 tau u) x)
                (gradientFun (I := I) g (perelmanPotential 3 tau u) x))
            (perelmanPotential 3 tau u) := by
  obtain ⟨B, hB⟩ := w_fixed_lower (I := I) (M := M) g hdim tauMax
  refine ⟨B, ?_⟩
  intro tau htau u hu hpos hmass
  let v : M -> Real := fun x => Real.sqrt (u x)
  have hv : ContMDiff I 𝓘(Real, Real) ∞ v := by
    intro x
    have hsqrt : ContMDiffAt 𝓘(Real, Real) 𝓘(Real, Real) ∞ Real.sqrt (u x) :=
      (Real.contDiffAt_sqrt (hpos x).ne').contMDiffAt
    exact hsqrt.comp x (hu x)
  have hvpos (x : M) : 0 < v x := Real.sqrt_pos.2 (hpos x)
  have hv_sq (x : M) : v x * v x = u x := by
    change Real.sqrt (u x) * Real.sqrt (u x) = u x
    exact Real.mul_self_sqrt (hpos x).le
  have hmassv :
      (∫ x, v x ^ 2 ∂(riemannianVolumeMeasure I M g)) = 1 := by
    calc
      (∫ x, v x ^ 2 ∂(riemannianVolumeMeasure I M g)) =
          ∫ x, u x ∂(riemannianVolumeMeasure I M g) := by
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards with x
        simpa only [pow_two] using hv_sq x
      _ = 1 := hmass
  have hbound := hB htau hv hvpos hmassv
  have huv : (fun x => v x * v x) = u := funext hv_sq
  simpa only [huv] using hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.w_density_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.w_density_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.w_density_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.w_density_lower

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
