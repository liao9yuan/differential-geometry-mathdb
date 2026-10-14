import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLaplacianDifference.Pairing
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLaplacianDifference.L2Bound
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

theorem lapDiffA2_cont
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) {S : Set Real}
    (hreg : ∀ s ∈ S, (T : Real) - s ∈ D.regular)
    (hsmall : ∀ s ∈ S,
      (Module.finrank Real E : Real) *
          CheegerGromovCompactness.metricDerivNormSupOn (I := I) Set.univ 1
            (g_fam ((T : Real) - s))
            (g_fam (T : Real)) (g_fam (T : Real)) ≤
        (1 / 2 : Real)) :
    ContinuousOn
      (fun s : Real => lapDiffA2 (I := I) (M := M) g_fam T s) S := by
  let : SeminormedAddCommGroup
      (TensorHs (I := I) (M := M) (g_fam (T : Real)) 0 0 2 →L[Real]
        TensorL2 0 0 (g_fam (T : Real))) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  intro s0 hs0
  let q : SmoothRiemannianMetric I M := g_fam (T : Real)
  let K : D.RegularTime := ⟨(T : Real) - s0, hreg s0 hs0⟩
  let k : SmoothRiemannianMetric I M := g_fam (K : Real)
  let rhoK : Real → Real := fun s =>
    CheegerGromovCompactness.metricDerivNormSupOn (I := I) Set.univ 1
      (g_fam ((T : Real) - s)) k k
  have hshiftK :
      _root_.Filter.Tendsto (fun s : Real => (T : Real) - s)
        (nhds s0) (nhds (K : Real)) := by
    dsimp only [K]
    simpa only [id_eq] using
      (tendsto_const_nhds.sub
        (_root_.Filter.tendsto_id : _root_.Filter.Tendsto (fun s : Real => s) (nhds s0) (nhds s0)))
  have hrhoK : _root_.Filter.Tendsto rhoK (nhds s0) (nhds 0) := by
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun _ => rfl) ?_
    exact (CheegerGromovCompactness.metric_c1_tendsto (I := I) g_fam hG K).comp hshiftK
  obtain ⟨C, hC, hpair⟩ :=
    lapDiff_pair_norm (I := I) (M := M) q k
  change _root_.Filter.Tendsto
    (fun s : Real => lapDiffA2 (I := I) (M := M) g_fam T s)
    (nhdsWithin s0 S)
    (nhds (lapDiffA2 (I := I) (M := M) g_fam T s0))
  rw [Metric.tendsto_nhds]
  intro eta heta
  have hKsmall :
      ∀ᶠ s in nhds s0,
        (Module.finrank Real E : Real) * rhoK s < (1 / 2 : Real) :=
    (hrhoK.const_mul (Module.finrank Real E : Real)).eventually_lt_const
      (by norm_num)
  have hupperLim :
      _root_.Filter.Tendsto (fun s => Real.sqrt C * |rhoK s|)
        (nhds s0) (nhds 0) := by
    simpa only [abs_zero, _root_.MulZeroClass.mul_zero] using
      hrhoK.abs.const_mul (Real.sqrt C)
  have hupper :
      ∀ᶠ s in nhds s0, Real.sqrt C * |rhoK s| < eta :=
    hupperLim.eventually_lt_const heta
  filter_upwards [hKsmall.filter_mono inf_le_left,
    hupper.filter_mono inf_le_left, self_mem_nhdsWithin]
      with s hks hu hs
  have hqh := hsmall s hs
  have hqk := hsmall s0 hs0
  have hkh :
      (Module.finrank Real E : Real) *
          CheegerGromovCompactness.metricDerivNormSupOn (I := I) Set.univ 1
            (g_fam ((T : Real) - s)) k k ≤
        (1 / 2 : Real) := by
    simpa only [rhoK] using hks.le
  rw [dist_eq_norm]
  simpa only [lapDiffA2, q, k, K, rhoK] using
    lt_of_le_of_lt
      (hpair (g_fam ((T : Real) - s)) hqh hqk hkh) hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffA2_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffA2_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffA2_cont ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffA2_cont

theorem lapDiffA20_short
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ tau : Real, 0 < tau ∧ tau ≤ 1 ∧
      ContinuousOn
        (fun s : Real => lapDiffA20 (I := I) (M := M) g_fam T s)
        (Set.Icc 0 tau) ∧
      _root_.MeasureTheory.AEStronglyMeasurable
        (fun s : Real => lapDiffA20 (I := I) (M := M) g_fam T s)
        (timeMeasure tau) ∧
      (∀ s ∈ Set.Icc 0 tau,
        ‖lapDiffA20 (I := I) (M := M) g_fam T s‖ ≤ epsilon) ∧
      ∀ᵐ s ∂timeMeasure tau,
        ‖lapDiffA20 (I := I) (M := M) g_fam T s‖ ≤ epsilon := by
  let : SeminormedAddCommGroup
      (TensorHs (I := I) (M := M) (g_fam (T : Real)) 0 0 2 →L[Real]
        TensorHs (I := I) (M := M) (g_fam (T : Real)) 0 0 0) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  let q : SmoothRiemannianMetric I M := g_fam (T : Real)
  let rhoQ : Real → Real := fun s =>
    CheegerGromovCompactness.metricDerivNormSupOn (I := I) Set.univ 1
      (g_fam ((T : Real) - s)) q q
  have hshift :
      _root_.Filter.Tendsto (fun s : Real => (T : Real) - s)
        (nhds 0) (nhds (T : Real)) := by
    simpa only [id_eq, sub_zero] using
      (tendsto_const_nhds.sub
        (_root_.Filter.tendsto_id : _root_.Filter.Tendsto (fun s : Real => s) (nhds 0) (nhds 0)))
  have hrhoQ : _root_.Filter.Tendsto rhoQ (nhds 0) (nhds 0) := by
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun _ => rfl) ?_
    exact (CheegerGromovCompactness.metric_c1_tendsto (I := I) g_fam hG T).comp hshift
  have hreg :
      ∀ᶠ s in nhds (0 : Real), (T : Real) - s ∈ D.regular :=
    hshift.eventually (D.regular_isOpen.mem_nhds T.2)
  have hqsmall :
      ∀ᶠ s in nhds (0 : Real),
        (Module.finrank Real E : Real) * rhoQ s < (1 / 2 : Real) :=
    (hrhoQ.const_mul (Module.finrank Real E : Real)).eventually_lt_const
      (by norm_num)
  have heps :
      ∀ᶠ s in nhds (0 : Real),
        ‖lapDiffA2 (I := I) (M := M) g_fam T s‖ < epsilon :=
    (lapDiffA2_zero (I := I) (M := M) g_fam hG T).eventually_lt_const
      hepsilon
  let U : Set Real := {s |
    (T : Real) - s ∈ D.regular ∧
      (Module.finrank Real E : Real) * rhoQ s ≤ (1 / 2 : Real) ∧
      ‖lapDiffA2 (I := I) (M := M) g_fam T s‖ ≤ epsilon}
  have hU : U ∈ nhds (0 : Real) := by
    change ∀ᶠ s in nhds (0 : Real),
      (T : Real) - s ∈ D.regular ∧
        (Module.finrank Real E : Real) * rhoQ s ≤ (1 / 2 : Real) ∧
        ‖lapDiffA2 (I := I) (M := M) g_fam T s‖ ≤ epsilon
    filter_upwards [hreg, hqsmall, heps] with s hs hr he
    exact ⟨hs, hr.le, he.le⟩
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hU
  let tau : Real := _root_.Min.min 1 (delta / 2)
  have htaupos : 0 < tau := by
    dsimp only [tau]
    exact lt_min zero_lt_one (half_pos hdelta)
  have htauone : tau ≤ 1 := by
    exact min_le_left _ _
  have htaudelta : tau < delta := by
    exact (min_le_right (1 : Real) (delta / 2)).trans_lt
      (half_lt_self hdelta)
  have hIccU : Set.Icc (0 : Real) tau ⊆ U := by
    intro s hs
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    exact hs.2.trans_lt htaudelta
  have hgood (s : Real) (hs : s ∈ Set.Icc (0 : Real) tau) :
      (T : Real) - s ∈ D.regular ∧
        (Module.finrank Real E : Real) * rhoQ s ≤ (1 / 2 : Real) ∧
        ‖lapDiffA2 (I := I) (M := M) g_fam T s‖ ≤ epsilon := by
    change s ∈ U
    exact hIccU hs
  have hA2cont :
      ContinuousOn
        (fun s : Real => lapDiffA2 (I := I) (M := M) g_fam T s)
        (Set.Icc 0 tau) := by
    apply lapDiffA2_cont (I := I) (M := M) g_fam hG T
    · intro s hs
      exact (hgood s hs).1
    · intro s hs
      simpa only [rhoQ, q] using (hgood s hs).2.1
  have hA20cont :
      ContinuousOn
        (fun s : Real => lapDiffA20 (I := I) (M := M) g_fam T s)
        (Set.Icc 0 tau) :=
    lapDiffA20_cont_of (I := I) (M := M) g_fam T hA2cont
  have hA20meas :
      _root_.MeasureTheory.AEStronglyMeasurable
        (fun s : Real => lapDiffA20 (I := I) (M := M) g_fam T s)
        (timeMeasure tau) := by
    unfold timeMeasure
    exact hA20cont.aestronglyMeasurable measurableSet_Icc
  have hboundOn :
      ∀ s ∈ Set.Icc (0 : Real) tau,
        ‖lapDiffA20 (I := I) (M := M) g_fam T s‖ ≤ epsilon := by
    intro s hs
    rw [lapDiffA20_norm]
    exact (hgood s hs).2.2
  have hboundAE :
      ∀ᵐ s ∂timeMeasure tau,
        ‖lapDiffA20 (I := I) (M := M) g_fam T s‖ ≤ epsilon := by
    unfold timeMeasure
    exact (_root_.MeasureTheory.ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall hboundOn)
  exact ⟨tau, htaupos, htauone, hA20cont, hA20meas, hboundOn,
    hboundAE⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffA20_short then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffA20_short"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffA20_short ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffA20_short

end Spectral
end Analysis
end DifferentialGeometry

end
