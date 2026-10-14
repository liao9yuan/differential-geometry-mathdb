import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.ForwardTransfer
import Submission.DifferentialGeometry.Geometry.Measure.MetricComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem riemannianVolumeMeasure_le_exp_mul_of_rmNormSq_le
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {a b ρ : ℝ} (hρ : 0 < ρ) (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    {U : Set M} (hU : MeasurableSet U)
    (hcurv : ∀ u ∈ _root_.Set.Icc a b, ∀ y ∈ U, ρ ^ 4 * FlowMetricBall.rmNormSq S u y ≤ 1)
    {A : Set M} (hAU : A ⊆ U) {s t : ℝ} (hs : s ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc a b) :
    riemannianVolumeMeasure I M (S.base.metric s) A ≤
      ENNReal.ofReal (Real.exp ((Module.finrank ℝ E : ℝ) ^ 3 / ρ ^ 2 * |s - t|)) *
        riemannianVolumeMeasure I M (S.base.metric t) A := by
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn
  set c : ℝ := n ^ 2 / ρ ^ 2 * |s - t| with hc
  have hcomp : ∀ y ∈ U, ∀ v : TangentSpace I y,
      (S.base.metric s).inner y v v ≤ Real.exp (2 * c) * (S.base.metric t).inner y v v :=
    fun y hy v => inner_le_exp_mul_inner_of_rmNormSq_le hS hρ hslab hreg
      (fun u hu => hcurv u hu y hy) hs ht v
  have hroot : Real.sqrt (Real.exp (2 * c) ^ Module.finrank ℝ E) =
      Real.exp (n ^ 3 / ρ ^ 2 * |s - t|) := by
    rw [← Real.exp_nat_mul, show (Module.finrank ℝ E : ℝ) * (2 * c) =
      n ^ 3 / ρ ^ 2 * |s - t| + n ^ 3 / ρ ^ 2 * |s - t| by rw [hc, ← hn]; ring,
      Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  set T : Set M := _root_.MeasureTheory.toMeasurable (riemannianVolumeMeasure I M (S.base.metric t)) A with hT
  have hTU : MeasurableSet (T ∩ U) := (_root_.MeasureTheory.measurableSet_toMeasurable _ A).inter hU
  have hvol := Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le
    (I := I) (M := M) (S.base.metric t) (S.base.metric s) (Real.exp_pos (2 * c)) hTU
    (fun y hy v => hcomp y hy.2 v)
  rw [hroot] at hvol
  calc
    riemannianVolumeMeasure I M (S.base.metric s) A ≤
        riemannianVolumeMeasure I M (S.base.metric s) (T ∩ U) :=
      _root_.MeasureTheory.measure_mono (_root_.Set.subset_inter (_root_.MeasureTheory.subset_toMeasurable _ A) hAU)
    _ ≤ _ := hvol
    _ ≤ ENNReal.ofReal (Real.exp (n ^ 3 / ρ ^ 2 * |s - t|)) *
        riemannianVolumeMeasure I M (S.base.metric t) T :=
      mul_le_mul' le_rfl (_root_.MeasureTheory.measure_mono _root_.Set.inter_subset_left)
    _ = _ := by rw [hT, _root_.MeasureTheory.measure_toMeasurable]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.riemannianVolumeMeasure_le_exp_mul_of_rmNormSq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.riemannianVolumeMeasure_le_exp_mul_of_rmNormSq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.riemannianVolumeMeasure_le_exp_mul_of_rmNormSq_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.riemannianVolumeMeasure_le_exp_mul_of_rmNormSq_le

theorem riemannianVolumeMeasure_le_exp_cube_mul_of_parabolic_rmNormSq_le
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {T ρ : ℝ} (hρ : 0 < ρ) (hslab : _root_.Set.Icc (T - ρ ^ 2) T ⊆ D.carrier)
    (hreg : _root_.Set.Ioo (T - ρ ^ 2) T ⊆ D.regular) {U : Set M} (hU : MeasurableSet U)
    (hcurv : ∀ u ∈ _root_.Set.Icc (T - ρ ^ 2) T, ∀ y ∈ U,
      ρ ^ 4 * FlowMetricBall.rmNormSq S u y ≤ 1)
    {A : Set M} (hAU : A ⊆ U) {s t : ℝ} (hs : s ∈ _root_.Set.Icc (T - ρ ^ 2) T)
    (ht : t ∈ _root_.Set.Icc (T - ρ ^ 2) T) :
    riemannianVolumeMeasure I M (S.base.metric s) A ≤
      ENNReal.ofReal (Real.exp ((Module.finrank ℝ E : ℝ) ^ 3)) *
        riemannianVolumeMeasure I M (S.base.metric t) A := by
  refine (riemannianVolumeMeasure_le_exp_mul_of_rmNormSq_le hS hρ hslab hreg hU hcurv hAU
    hs ht).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) le_rfl)
  have hst : |s - t| ≤ ρ ^ 2 := abs_sub_le_iff.mpr ⟨by linarith [hs.2, ht.1], by
    linarith [hs.1, ht.2]⟩
  have hρ2 : 0 < ρ ^ 2 := by positivity
  calc
    (Module.finrank ℝ E : ℝ) ^ 3 / ρ ^ 2 * |s - t| ≤
        (Module.finrank ℝ E : ℝ) ^ 3 / ρ ^ 2 * ρ ^ 2 :=
      mul_le_mul_of_nonneg_left hst (by positivity)
    _ = (Module.finrank ℝ E : ℝ) ^ 3 := by field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.riemannianVolumeMeasure_le_exp_cube_mul_of_parabolic_rmNormSq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.riemannianVolumeMeasure_le_exp_cube_mul_of_parabolic_rmNormSq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.riemannianVolumeMeasure_le_exp_cube_mul_of_parabolic_rmNormSq_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.riemannianVolumeMeasure_le_exp_cube_mul_of_parabolic_rmNormSq_le

end DifferentialGeometry.PDE.RicciFlow.Perelman
