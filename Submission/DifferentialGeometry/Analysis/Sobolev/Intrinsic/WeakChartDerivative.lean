import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakChartTest

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

local notation "Eucl" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [IsManifold I ∞ M] in
private lemma tsupport_chartPullback_subset [T2Space M]
    (α : M) {ψ : Eucl → ℝ} (hψ : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ Chart.chartTargetEuclid (I := I) α) :
    tsupport (Chart.chartPullback I α ψ) ⊆ (chartAt H α).source := by
  have htarget : (toEuclidean (E := E)).symm '' tsupport ψ ⊆ (extChartAt I α).target := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwz⟩ := hsupp hz
    rw [← hwz, ContinuousLinearEquiv.symm_apply_apply]
    exact hw
  let K := (extChartAt I α).symm '' ((toEuclidean (E := E)).symm '' tsupport ψ)
  have hK : IsCompact K :=
    (hψ.image (toEuclidean (E := E)).symm.continuous).image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := I) α).mono htarget)
  have hKsource : K ⊆ (chartAt H α).source := by
    rintro x ⟨y, hy, rfl⟩
    simpa only [extChartAt_source_eq_chartAt_source] using
      (extChartAt I α).map_target (htarget hy)
  apply subset_trans (closure_minimal (t := K) ?_ hK.isClosed) hKsource
  intro x hx
  have hxsource := Chart.support_chartPullback_subset_chartAt_source α ψ hx
  have hxext : x ∈ (extChartAt I α).source := by
    simpa only [extChartAt_source_eq_chartAt_source] using hxsource
  have hψx : toEuclidean (extChartAt I α x) ∈ tsupport ψ := by
    apply subset_tsupport ψ
    simpa only [Function.mem_support, Chart.chartPullback_apply_of_mem α ψ hxsource] using hx
  exact ⟨extChartAt I α x,
    ⟨toEuclidean (extChartAt I α x), hψx, ContinuousLinearEquiv.symm_apply_apply _ _⟩,
    (extChartAt I α).left_inv hxext⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.tsupport_chartPullback_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.tsupport_chartPullback_subset target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private lemma scalarOnE_chartPullback
    (α : M) (ψ : Eucl → ℝ) {y : E} (hy : y ∈ (extChartAt I α).target) :
    scalarOnE (I := I) α (Chart.chartPullback I α ψ) y = ψ (toEuclidean y) := by
  have hyM : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    simpa only [extChartAt_source_eq_chartAt_source] using (extChartAt I α).map_target hy
  rw [scalarOnE, Chart.chartPullback_apply_of_mem α ψ hyM, (extChartAt I α).right_inv hy]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.scalarOnE_chartPullback
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.scalarOnE_chartPullback target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private lemma partialDeriv_scalarOnE_chartPullback [I.Boundaryless]
    (α : M) {ψ : Eucl → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (i : Fin (Module.finrank ℝ E)) {y : E} (hy : y ∈ (extChartAt I α).target) :
    partialDeriv i (scalarOnE (I := I) α (Chart.chartPullback I α ψ)) y =
      fderiv ℝ ψ (toEuclidean y) (EuclideanSpace.single i 1) := by
  have heq : scalarOnE (I := I) α (Chart.chartPullback I α ψ) =ᶠ[𝓝 y]
      (fun z => ψ (toEuclidean z)) := by
    filter_upwards [(isOpen_extChartAt_target (I := I) α).mem_nhds hy] with z hz
    exact scalarOnE_chartPullback α ψ hz
  have hd := (hψ.differentiable (by simp) (toEuclidean y)).hasFDerivAt.comp y
    (toEuclidean (E := E)).hasFDerivAt
  rw [partialDeriv, heq.fderiv_eq]
  change fderiv ℝ (ψ ∘ toEuclidean (E := E)) y (chartModelBasis E i) = _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    chartModelBasis_apply, ContinuousLinearEquiv.apply_symm_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.partialDeriv_scalarOnE_chartPullback
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.partialDeriv_scalarOnE_chartPullback target :: scope.openDecls } }


theorem HasWeakRiemannianGradLp.hasWeakPartialDeriv_chartPushedRaw
    [CompactSpace M] [T2Space M] [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {u : M → ℝ} {G : ∀ x : M, TangentSpace I x}
    (hG : HasWeakRiemannianGradLp g u G)
    (hu : _root_.MeasureTheory.Integrable u (riemannianVolumeMeasure I M g))
    (hGn : _root_.MeasureTheory.Integrable (fun x => Real.sqrt (g.inner x (G x) (G x)))
      (riemannianVolumeMeasure I M g))
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv i
      (Chart.chartPushedRaw I α (fun x => g.inner x (G x) (chartBasisVecFiber (I := I) α i x)))
      (Chart.chartPushedRaw I α u) (Chart.chartTargetEuclid (I := I) α) := by
  intro ψ hψ hψc hψs
  have hφ := Chart.chartPullback_contMDiff α hψ hψc hψs
  have hφs := tsupport_chartPullback_subset α hψc hψs
  have hpair := hG.chart_pairing hu hGn α i hφ hφs
  have hmeas : MeasurableEmbedding (toEuclidean (E := E)) :=
    (toEuclidean (E := E)).toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hpres : _root_.MeasureTheory.MeasurePreserving (toEuclidean (E := E)) (modelHaar (E := E)) volume :=
    ⟨hmeas.measurable, map_toEuclidean_modelHaar_eq_volume⟩
  have htransport (F : Eucl → ℝ) :
      (∫ z in Chart.chartTargetEuclid (I := I) α, F z) =
        ∫ y in (extChartAt I α).target, F (toEuclidean y) ∂modelHaar (E := E) :=
    hpres.setIntegral_image_emb hmeas F (extChartAt I α).target
  rw [htransport, htransport]
  have hleft_eq : (∫ y in (extChartAt I α).target,
      Chart.chartPushedRaw I α u (toEuclidean y) *
        fderiv ℝ ψ (toEuclidean y) (EuclideanSpace.single i 1) ∂modelHaar (E := E)) =
      ∫ y in (extChartAt I α).target, scalarOnE (I := I) α u y *
        partialDeriv i (scalarOnE (I := I) α (Chart.chartPullback I α ψ)) y ∂modelHaar (E := E) := by
    apply _root_.MeasureTheory.setIntegral_congr_fun (measurableSet_extChartAt_target (I := I) α)
    intro y hy
    have hyE : toEuclidean y ∈ Chart.chartTargetEuclid (I := I) α := ⟨y, hy, rfl⟩
    dsimp only
    rw [Chart.chartPushedRaw_apply_of_mem α u hyE,
      ContinuousLinearEquiv.symm_apply_apply, partialDeriv_scalarOnE_chartPullback α hψ i hy]
    rfl
  have hright_eq : (∫ y in (extChartAt I α).target,
      Chart.chartPushedRaw I α (fun x => g.inner x (G x) (chartBasisVecFiber (I := I) α i x))
        (toEuclidean y) * ψ (toEuclidean y) ∂modelHaar (E := E)) =
      ∫ y in (extChartAt I α).target,
        g.inner ((extChartAt I α).symm y) (G ((extChartAt I α).symm y))
          (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y)) *
            scalarOnE (I := I) α (Chart.chartPullback I α ψ) y ∂modelHaar (E := E) := by
    apply _root_.MeasureTheory.setIntegral_congr_fun (measurableSet_extChartAt_target (I := I) α)
    intro y hy
    have hyE : toEuclidean y ∈ Chart.chartTargetEuclid (I := I) α := ⟨y, hy, rfl⟩
    dsimp only
    rw [Chart.chartPushedRaw_apply_of_mem α _ hyE, ContinuousLinearEquiv.symm_apply_apply,
      scalarOnE_chartPullback α ψ hy]
  rw [hleft_eq, hright_eq]
  linarith only [hpair]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.hasWeakPartialDeriv_chartPushedRaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.hasWeakPartialDeriv_chartPushedRaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.hasWeakPartialDeriv_chartPushedRaw ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.hasWeakPartialDeriv_chartPushedRaw

end DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
