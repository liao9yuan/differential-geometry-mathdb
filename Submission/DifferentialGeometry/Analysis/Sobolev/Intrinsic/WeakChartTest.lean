import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakProduct
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.ChartPullbackSmooth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }


def weightedChartTest (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (φ : M → ℝ)
    (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) (hsupp : tsupport φ ⊆ (chartAt H α).source) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := by
  let T := _root_.FiberBundle.trivializationAt E (TangentSpace I) α
  have hsupport : tsupport φ ⊆ T.baseSet := by
    simpa only [T, TangentBundle.trivializationAt_baseSet] using hsupp
  have hlocal : ContMDiffOn I I.tangent ∞
      (T% fun x => (chartDensity g α x)⁻¹ • chartBasisVecFiber (I := I) α i x)
      T.baseSet :=
    ((chartDensity_contMDiffOn g α).inv₀ (fun x hx => (chartDensity_pos g α hx).ne')).smul_section
      (chartBasisVec_contMDiffOn α i)
  exact ⟨fun x => φ x • ((chartDensity g α x)⁻¹ • chartBasisVecFiber (I := I) α i x),
    hφ.contMDiffOn.smul_section_of_tsupport T.open_baseSet hsupport hlocal⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.weightedChartTest then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.weightedChartTest"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.weightedChartTest ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.weightedChartTest

@[simp] theorem weightedChartTest_apply (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (φ : M → ℝ)
    (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) (hsupp : tsupport φ ⊆ (chartAt H α).source) (x : M) :
    weightedChartTest g α i φ hφ hsupp x =
      (φ x / chartDensity g α x) • chartBasisVecFiber (I := I) α i x := by
  change φ x • ((chartDensity g α x)⁻¹ • chartBasisVecFiber (I := I) α i x) = _
  rw [smul_smul, div_eq_mul_inv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.weightedChartTest_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.weightedChartTest_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.weightedChartTest_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.weightedChartTest_apply

theorem tsupport_weightedChartTest_subset (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (φ : M → ℝ)
    (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) (hsupp : tsupport φ ⊆ (chartAt H α).source) :
    tsupport (weightedChartTest g α i φ hφ hsupp) ⊆ tsupport φ := by
  apply closure_mono
  intro x hx
  contrapose! hx
  apply Function.notMem_support.mpr
  rw [weightedChartTest_apply, Function.notMem_support.mp hx, zero_div, zero_smul]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.tsupport_weightedChartTest_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.tsupport_weightedChartTest_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.tsupport_weightedChartTest_subset ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.tsupport_weightedChartTest_subset

theorem chartCoeff_weightedChartTest (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (φ : M → ℝ)
    (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) (hsupp : tsupport φ ⊆ (chartAt H α).source)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    chartCoeff α (weightedChartTest g α i φ hφ hsupp) j x =
      if j = i then φ x / chartDensity g α x else 0 := by
  classical
  have hxT : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  have htriv : (_root_.FiberBundle.trivializationAt E (TangentSpace I) α
      ⟨x, weightedChartTest g α i φ hφ hsupp x⟩).2 =
        (φ x / chartDensity g α x) • chartModelBasis E i := by
    rw [weightedChartTest_apply]
    rw [((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).linear ℝ hxT).map_smul,
      trivializationAt_chartBasisVec_snd α i hxT]
  rw [chartCoeff_def, htriv]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self,
    Finsupp.single_apply]
  by_cases hji : j = i
  · subst j
    simp
  · simp only [hji, Ne.symm hji, if_false, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.chartCoeff_weightedChartTest then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.chartCoeff_weightedChartTest"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.chartCoeff_weightedChartTest ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.chartCoeff_weightedChartTest


theorem divergence_weightedChartTest [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (φ : M → ℝ)
    (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) (hsupp : tsupport φ ⊆ (chartAt H α).source)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    divergenceG g (weightedChartTest g α i φ hφ hsupp) x =
      partialDeriv i (scalarOnE (I := I) α φ) (extChartAt I α x) / chartDensity g α x := by
  classical
  rw [voss_weyl_divergence_formula g α _ hx, localDivergence_def]
  congr 1
  have hxT : extChartAt I α x ∈ (extChartAt I α).target := by
    apply (extChartAt I α).map_source
    simpa only [extChartAt_source_eq_chartAt_source] using hx
  have hcoeff (j : Fin (Module.finrank ℝ E)) :
      (fun y => chartCoeffOnE α (weightedChartTest g α i φ hφ hsupp) j y *
        chartDensityOnE g α y) =ᶠ[𝓝 (extChartAt I α x)]
          (fun y => if j = i then scalarOnE (I := I) α φ y else 0) := by
    filter_upwards [(isOpen_extChartAt_target (I := I) α).mem_nhds hxT] with y hy
    have hyM : (extChartAt I α).symm y ∈ (chartAt H α).source := by
      simpa only [extChartAt_source_eq_chartAt_source] using (extChartAt I α).map_target hy
    have hyB : (extChartAt I α).symm y ∈
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet] using hyM
    dsimp only [chartCoeffOnE, chartDensityOnE, scalarOnE]
    rw [chartCoeff_weightedChartTest g α i j φ hφ hsupp hyM]
    split_ifs
    · exact div_mul_cancel₀ _ (chartDensity_pos g α hyB).ne'
    · exact _root_.MulZeroClass.zero_mul _
  have hpartial (j : Fin (Module.finrank ℝ E)) :
      partialDeriv j (fun y =>
          chartCoeffOnE α (weightedChartTest g α i φ hφ hsupp) j y *
            chartDensityOnE g α y) (extChartAt I α x) =
        if j = i then partialDeriv i (scalarOnE (I := I) α φ) (extChartAt I α x) else 0 := by
    unfold partialDeriv
    rw [(hcoeff j).fderiv_eq]
    by_cases hji : j = i
    · subst j
      simp only [ite_true]
    · simp only [hji, if_false, fderiv_const_apply, zero_apply]
  simp_rw [hpartial]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.divergence_weightedChartTest then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.divergence_weightedChartTest"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.divergence_weightedChartTest ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.divergence_weightedChartTest

private lemma integral_eq_chart_of_support [CompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (α : M) {f : M → ℝ}
    (hf : _root_.MeasureTheory.Integrable f (riemannianVolumeMeasure I M g))
    (hsupp : ∀ x, x ∉ (chartAt H α).source → f x = 0) :
    (∫ x, f x ∂riemannianVolumeMeasure I M g) =
      ∫ y in (extChartAt I α).target,
        chartDensityOnE g α y * f ((extChartAt I α).symm y) ∂modelHaar (E := E) := by
  have hfchart : _root_.MeasureTheory.Integrable f (chartLocalMeasure g α) := by
    have hlocal : _root_.MeasureTheory.IntegrableOn f (chartAt H α).source (chartLocalMeasure g α) := by
      change _root_.MeasureTheory.Integrable f ((chartLocalMeasure g α).restrict (chartAt H α).source)
      rw [← Chart.volume_restrict_eq g α]
      exact hf.integrableOn
    exact hlocal.integrable_of_forall_notMem_eq_zero hsupp
  rw [(Chart.chart_int_eq_global g α hfchart hsupp).2]
  exact integral_chart_ae g α f hfchart.aestronglyMeasurable

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.integral_eq_chart_of_support
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.integral_eq_chart_of_support target :: scope.openDecls } }


theorem HasWeakRiemannianGradLp.chart_pairing [CompactSpace M] [T2Space M] [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {u : M → ℝ} {G : ∀ x : M, TangentSpace I x}
    (hG : HasWeakRiemannianGradLp g u G)
    (hu : _root_.MeasureTheory.Integrable u (riemannianVolumeMeasure I M g))
    (hGn : _root_.MeasureTheory.Integrable (fun x => Real.sqrt (g.inner x (G x) (G x)))
      (riemannianVolumeMeasure I M g))
    (α : M) (i : Fin (Module.finrank ℝ E)) {φ : M → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) (hsupp : tsupport φ ⊆ (chartAt H α).source) :
    (∫ y in (extChartAt I α).target,
      g.inner ((extChartAt I α).symm y) (G ((extChartAt I α).symm y))
        (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y)) * scalarOnE (I := I) α φ y
      ∂modelHaar (E := E)) =
      -∫ y in (extChartAt I α).target,
        scalarOnE (I := I) α u y * partialDeriv i (scalarOnE (I := I) α φ) y ∂modelHaar (E := E) := by
  let X := weightedChartTest g α i φ hφ hsupp
  have hXsupport : tsupport X ⊆ (chartAt H α).source :=
    (tsupport_weightedChartTest_subset g α i φ hφ hsupp).trans hsupp
  have hleft := hG.pairing_integrable hGn X
  have hright : _root_.MeasureTheory.Integrable (fun x => u x * divergenceG g X x)
      (riemannianVolumeMeasure I M g) := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      (divergence_g_contMDiff g X).continuous.continuousOn
    exact hu.mul_bdd (divergence_g_contMDiff g X).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => hC x (_root_.Set.mem_univ x))
  have hleftsupp : ∀ x, x ∉ (chartAt H α).source → g.inner x (G x) (X x) = 0 := by
    intro x hx
    have hXx : X x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hXsupport h))
    rw [hXx, map_zero]
  have hrightsupp : ∀ x, x ∉ (chartAt H α).source → u x * divergenceG g X x = 0 := by
    intro x hx
    have hdivx : divergenceG g X x = 0 := by
      apply Function.notMem_support.mp
      exact fun h => hx (hXsupport (support_divergence_g_subset g X h))
    rw [hdivx, _root_.MulZeroClass.mul_zero]
  have hweak := hG.pairing_eq X ((isClosed_tsupport _).isCompact)
  rw [integral_eq_chart_of_support g α hleft hleftsupp,
    integral_eq_chart_of_support g α hright hrightsupp] at hweak
  have hleft_eq : (∫ y in (extChartAt I α).target,
      chartDensityOnE g α y * g.inner ((extChartAt I α).symm y)
        (G ((extChartAt I α).symm y)) (X ((extChartAt I α).symm y)) ∂modelHaar (E := E)) =
      ∫ y in (extChartAt I α).target,
        g.inner ((extChartAt I α).symm y) (G ((extChartAt I α).symm y))
          (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y)) * scalarOnE (I := I) α φ y
        ∂modelHaar (E := E) := by
    apply _root_.MeasureTheory.setIntegral_congr_fun (measurableSet_extChartAt_target (I := I) α)
    intro y hy
    have hyB : (extChartAt I α).symm y ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source_eq_chartAt_source]
        using (extChartAt I α).map_target hy
    simp only [X, weightedChartTest_apply, map_smul, smul_eq_mul, chartDensityOnE, scalarOnE]
    rw [← mul_assoc, mul_div_cancel₀ _ (chartDensity_pos g α hyB).ne', mul_comm]
  have hright_eq : (∫ y in (extChartAt I α).target,
      chartDensityOnE g α y * (u ((extChartAt I α).symm y) *
        divergenceG g X ((extChartAt I α).symm y)) ∂modelHaar (E := E)) =
      ∫ y in (extChartAt I α).target,
        scalarOnE (I := I) α u y * partialDeriv i (scalarOnE (I := I) α φ) y ∂modelHaar (E := E) := by
    apply _root_.MeasureTheory.setIntegral_congr_fun (measurableSet_extChartAt_target (I := I) α)
    intro y hy
    have hyM : (extChartAt I α).symm y ∈ (chartAt H α).source := by
      simpa only [extChartAt_source_eq_chartAt_source] using (extChartAt I α).map_target hy
    have hyB : (extChartAt I α).symm y ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet] using hyM
    dsimp only
    rw [show divergenceG g X ((extChartAt I α).symm y) = _ from
      divergence_weightedChartTest g α i φ hφ hsupp hyM,
      (extChartAt I α).right_inv hy]
    dsimp only [chartDensityOnE, scalarOnE]
    rw [mul_left_comm, mul_div_cancel₀ _ (chartDensity_pos g α hyB).ne']
  rw [hleft_eq, hright_eq] at hweak
  exact hweak

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.chart_pairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.chart_pairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.chart_pairing ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.chart_pairing

end DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
