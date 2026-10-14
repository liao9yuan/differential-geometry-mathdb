import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Integrability
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.ChartFamilyIdentification
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Topology.Algebra.Support

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Set _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem mvfderiv_eq_zero_of_notMem_tsupport
    {f : M → ℝ} {x : M} (hx : x ∉ tsupport f) : mvfderiv I f x = 0 := by
  have heq : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    notMem_tsupport_iff_eventuallyEq.mp hx
  have hd := heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ))
  simp only [mfderiv_const] at hd
  rw [mvfderiv, hd]
  ext v
  change NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x) 0 = 0
  exact map_zero _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.mvfderiv_eq_zero_of_notMem_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.mvfderiv_eq_zero_of_notMem_tsupport target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem time_spatial_residual_eq_zero_of_notMem_tsupport
    (u ψ : ℝ × M → ℝ) (V : (t : ℝ) → (x : M) → TangentSpace I x)
    {z : ℝ × M} (hz : z ∉ tsupport ψ) :
    u z * (deriv (fun t => ψ (t, z.2)) z.1 +
      mvfderiv I (fun x => ψ (z.1, x)) z.2 (V z.1 z.2)) = 0 := by
  have ht : z.1 ∉ tsupport (fun t => ψ (t, z.2)) := by
    intro h
    apply hz
    exact tsupport_comp_subset_preimage (f := fun t => (t, z.2)) ψ
      (continuous_id.prodMk continuous_const) h
  have hx : z.2 ∉ tsupport (fun x => ψ (z.1, x)) := by
    intro h
    apply hz
    exact tsupport_comp_subset_preimage (f := fun x => (z.1, x)) ψ
      (continuous_const.prodMk continuous_id) h
  rw [deriv_of_notMem_tsupport ht, mvfderiv_eq_zero_of_notMem_tsupport hx]
  simp only [zero_apply, zero_add, _root_.MulZeroClass.mul_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.time_spatial_residual_eq_zero_of_notMem_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.time_spatial_residual_eq_zero_of_notMem_tsupport target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem tsupport_time_spatial_residual_subset
    (u ψ : ℝ × M → ℝ) (V : (t : ℝ) → (x : M) → TangentSpace I x) :
    tsupport (fun z : ℝ × M => u z * (deriv (fun t => ψ (t, z.2)) z.1 +
      mvfderiv I (fun x => ψ (z.1, x)) z.2 (V z.1 z.2))) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro z hz
  by_contra hnot
  exact hz (time_spatial_residual_eq_zero_of_notMem_tsupport u ψ V hnot)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.tsupport_time_spatial_residual_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.tsupport_time_spatial_residual_subset target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem hasCompactSupport_time_spatial_residual_slice
    [T2Space M] (u ψ : ℝ × M → ℝ)
    (V : (t : ℝ) → (x : M) → TangentSpace I x) (hψ : HasCompactSupport ψ) (t : ℝ) :
    HasCompactSupport (fun x => u (t, x) * (deriv (fun s => ψ (s, x)) t +
      mvfderiv I (fun y => ψ (t, y)) x (V t x))) := by
  apply HasCompactSupport.of_support_subset_isCompact (hψ.image continuous_snd)
  intro x hx
  exact ⟨(t, x), by
    by_contra hn
    exact hx (time_spatial_residual_eq_zero_of_notMem_tsupport u ψ V hn), rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.hasCompactSupport_time_spatial_residual_slice
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.hasCompactSupport_time_spatial_residual_slice target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem tsupport_time_spatial_residual_slice_subset
    [T2Space M] (u ψ : ℝ × M → ℝ)
    (V : (t : ℝ) → (x : M) → TangentSpace I x) (hψ : HasCompactSupport ψ) (t : ℝ) :
    tsupport (fun x => u (t, x) * (deriv (fun s => ψ (s, x)) t +
      mvfderiv I (fun y => ψ (t, y)) x (V t x))) ⊆ Prod.snd '' tsupport ψ := by
  apply closure_minimal _ (hψ.image continuous_snd).isClosed
  intro x hx
  exact ⟨(t, x), by
    by_contra hn
    exact hx (time_spatial_residual_eq_zero_of_notMem_tsupport u ψ V hn), rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.tsupport_time_spatial_residual_slice_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.tsupport_time_spatial_residual_slice_subset target :: scope.openDecls } }

private theorem inner_gradientFun_eq_mvfderiv
    (g : SmoothRiemannianMetric I M) (f ψ : M → ℝ) (x : M) :
    g.inner x (gradientFun g f x) (gradientFun g ψ x) =
      mvfderiv I ψ x (gradientFun g f x) := by
  rw [g.symm, inner_gradientFun]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.inner_gradientFun_eq_mvfderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.inner_gradientFun_eq_mvfderiv target :: scope.openDecls } }

end DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Integral.Measure

open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {μ : Measure ℝ} [Measure.IsAddHaarMeasure μ]

private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

private theorem ae_integrable_and_integral_time_gradient_residual_eq_chartDensity
    (g : ℝ → SmoothRiemannianMetric I M) (α : M)
    (u f ψ : ℝ × M → ℝ) {S : Set ℝ} {W : Set E}
    (hS : IsOpen S) (hW : IsOpen W) (hWt : W ⊆ (extChartAt I α).target)
    (hψc : HasCompactSupport ψ)
    (hψs : Prod.snd '' tsupport ψ ⊆ (chartAt H α).source)
    (hψW : ∀ z ∈ tsupport ψ, extChartAt I α z.2 ∈ W)
    (hf : LocallyLipschitzOn (S ×ˢ W)
      (fun z : ℝ × E => f (z.1, (extChartAt I α).symm z.2)))
    (hψ : LocallyLipschitzOn (S ×ˢ W)
      (fun z : ℝ × E => ψ (z.1, (extChartAt I α).symm z.2)))
    (hi : ∀ᵐ t ∂μ, t ∈ S → _root_.MeasureTheory.Integrable
      (fun y => chartDensity (g t) α ((extChartAt I α).symm y) *
        (u (t, (extChartAt I α).symm y) *
          (deriv (fun s => ψ (s, (extChartAt I α).symm y)) t +
            chartGradientBilin (g t) α ((extChartAt I α).symm y)
              (fderiv ℝ (fun v : E => f (t, (extChartAt I α).symm v)) y)
              (fderiv ℝ (fun v : E => ψ (t, (extChartAt I α).symm v)) y))))
      ((modelHaar (E := E)).restrict W)) :
    ∀ᵐ t ∂μ, t ∈ S →
      _root_.MeasureTheory.Integrable (fun x => u (t, x) * (deriv (fun s => ψ (s, x)) t +
        (g t).inner x (gradientFun (g t) (fun y => f (t, y)) x)
          (gradientFun (g t) (fun y => ψ (t, y)) x)))
        (riemannianVolumeMeasure (I := I) (M := M) (g t)) ∧
      (∫ x, u (t, x) * (deriv (fun s => ψ (s, x)) t +
        (g t).inner x (gradientFun (g t) (fun y => f (t, y)) x)
          (gradientFun (g t) (fun y => ψ (t, y)) x))
        ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) =
      ∫ y in W, chartDensity (g t) α ((extChartAt I α).symm y) *
        (u (t, (extChartAt I α).symm y) *
          (deriv (fun s => ψ (s, (extChartAt I α).symm y)) t +
            chartGradientBilin (g t) α ((extChartAt I α).symm y)
              (fderiv ℝ (fun v : E => f (t, (extChartAt I α).symm v)) y)
              (fderiv ℝ (fun v : E => ψ (t, (extChartAt I α).symm v)) y)))
        ∂modelHaar := by
  let R : ℝ × M → ℝ := fun z => u z * (deriv (fun t => ψ (t, z.2)) z.1 +
    (g z.1).inner z.2 (gradientFun (g z.1) (fun y => f (z.1, y)) z.2)
      (gradientFun (g z.1) (fun y => ψ (z.1, y)) z.2))
  let V : (t : ℝ) → (x : M) → TangentSpace I x :=
    fun t x => gradientFun (g t) (fun y => f (t, y)) x
  have hR (t : ℝ) : (fun x => R (t, x)) =
      fun x => u (t, x) * (deriv (fun s => ψ (s, x)) t +
        mvfderiv I (fun y => ψ (t, y)) x (V t x)) := by
    funext x
    dsimp only [R]
    rw [inner_gradientFun_eq_mvfderiv]
  have hRc (t : ℝ) : HasCompactSupport (fun x => R (t, x)) := by
    rw [hR t]
    exact hasCompactSupport_time_spatial_residual_slice u ψ V hψc t
  have hRs (t : ℝ) : tsupport (fun x => R (t, x)) ⊆ (chartAt H α).source := by
    rw [hR t]
    exact (tsupport_time_spatial_residual_slice_subset u ψ V hψc t).trans hψs
  have hgrad := ae_chartGradientBilin_fderiv_eq_inner_gradientFun_family
    (μ := μ) (ν := modelHaar (E := E))
    (f := fun t x => f (t, x)) (h := fun t x => ψ (t, x)) g α hS hW hWt hf hψ
  filter_upwards [Measure.ae_ae_of_ae_prod hgrad, hi] with t hgt hit ht
  have hzero (y : E) (hy : y ∈ (extChartAt I α).target \ W) :
      chartDensity (g t) α ((extChartAt I α).symm y) *
        R (t, (extChartAt I α).symm y) = 0 := by
    have hn : (t, (extChartAt I α).symm y) ∉ tsupport ψ := by
      intro hz
      apply hy.2
      simpa only [(extChartAt I α).right_inv hy.1] using hψW _ hz
    have hz := time_spatial_residual_eq_zero_of_notMem_tsupport u ψ V hn
    rw [← congrFun (hR t) ((extChartAt I α).symm y)] at hz
    rw [hz, _root_.MulZeroClass.mul_zero]
  have hEq : (fun y => chartDensity (g t) α ((extChartAt I α).symm y) *
      R (t, (extChartAt I α).symm y)) =ᵐ[(modelHaar (E := E)).restrict W]
      (fun y => chartDensity (g t) α ((extChartAt I α).symm y) *
        (u (t, (extChartAt I α).symm y) *
          (deriv (fun s => ψ (s, (extChartAt I α).symm y)) t +
            chartGradientBilin (g t) α ((extChartAt I α).symm y)
              (fderiv ℝ (fun v : E => f (t, (extChartAt I α).symm v)) y)
              (fderiv ℝ (fun v : E => ψ (t, (extChartAt I α).symm v)) y)))) := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_of_ae hgt, _root_.MeasureTheory.ae_restrict_mem hW.measurableSet]
      with y hy hyW
    dsimp only [R]
    rw [hy ⟨ht, hyW⟩]
  have hIntW : _root_.MeasureTheory.IntegrableOn (fun y => chartDensity (g t) α ((extChartAt I α).symm y) *
      R (t, (extChartAt I α).symm y)) W (modelHaar (E := E)) :=
    (hit ht).congr hEq.symm
  have hIntT := hIntW.of_forall_sdiff_eq_zero
    (measurableSet_extChartAt_target (I := I) α) hzero
  have hLocal : _root_.MeasureTheory.Integrable (fun x => R (t, x)) (chartLocalMeasure (g t) α) := by
    apply (integrable_chartLocalMeasure_iff (g t) α).mpr
    simpa only [_root_.MeasureTheory.IntegrableOn, smul_eq_mul] using hIntT
  have hIntrinsic : _root_.MeasureTheory.Integrable (fun x => R (t, x))
      (riemannianVolumeMeasure (I := I) (M := M) (g t)) :=
    (integrable_riemannianVolumeMeasure_iff_chartLocalMeasure_of_tsupport_subset
      (g t) α (hRc t) (by simpa only [extChartAt_source] using hRs t)).mpr hLocal
  have hcoord := integral_riemannianVolumeMeasure_eq_chartDensity_of_tsupport_subset
    (g t) α (hRc t) (hRs t) hLocal.aestronglyMeasurable
  refine ⟨hIntrinsic, ?_⟩
  calc
    (∫ x, R (t, x) ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) =
        ∫ y in (extChartAt I α).target,
          chartDensity (g t) α ((extChartAt I α).symm y) *
            R (t, (extChartAt I α).symm y) ∂modelHaar := hcoord
    _ = ∫ y in W, chartDensity (g t) α ((extChartAt I α).symm y) *
          R (t, (extChartAt I α).symm y) ∂modelHaar :=
      (_root_.MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        (measurableSet_extChartAt_target (I := I) α) hWt hzero)
    _ = _ := _root_.MeasureTheory.integral_congr_ae hEq

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.ae_integrable_and_integral_time_gradient_residual_eq_chartDensity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.ae_integrable_and_integral_time_gradient_residual_eq_chartDensity target :: scope.openDecls } }

end DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry.Integral.Measure

open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_2 : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_2 : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_3 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_3 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_3 target :: scope.openDecls } }

theorem integral_chart_time_gradient_residual_eq_of_extension
    (g : ℝ → SmoothRiemannianMetric I M) (α : M) (u f Ψ : ℝ × M → ℝ)
    (ψ : ℝ × E → ℝ) {a b : ℝ} {W : Set E}
    (hW : IsOpen W) (hWt : W ⊆ (extChartAt I α).target)
    (hΨc : HasCompactSupport Ψ)
    (hΨs : Prod.snd '' tsupport Ψ ⊆ (chartAt H α).source)
    (hΨW : ∀ z ∈ tsupport Ψ, extChartAt I α z.2 ∈ W)
    (hext : ∀ t y, y ∈ W → Ψ (t, (extChartAt I α).symm y) = ψ (t, y))
    (hf : LocallyLipschitzOn (_root_.Set.Ioo a b ×ˢ W)
      (fun z : ℝ × E => f (z.1, (extChartAt I α).symm z.2)))
    (hψ : LocallyLipschitzOn (_root_.Set.Ioo a b ×ˢ W) ψ)
    (hi : _root_.MeasureTheory.Integrable (fun z : ℝ × E =>
      chartDensity (g z.1) α ((extChartAt I α).symm z.2) *
        u (z.1, (extChartAt I α).symm z.2) *
          (deriv (fun t => ψ (t, z.2)) z.1 +
            chartGradientBilin (g z.1) α ((extChartAt I α).symm z.2)
              (fderiv ℝ (fun y => f (z.1, (extChartAt I α).symm y)) z.2)
              (fderiv ℝ (fun y => ψ (z.1, y)) z.2)))
      ((volume.restrict (_root_.Set.Ioc a b)).prod ((modelHaar (E := E)).restrict W))) :
    (∫ z, chartDensity (g z.1) α ((extChartAt I α).symm z.2) *
      u (z.1, (extChartAt I α).symm z.2) *
        (deriv (fun t => ψ (t, z.2)) z.1 +
          chartGradientBilin (g z.1) α ((extChartAt I α).symm z.2)
            (fderiv ℝ (fun y => f (z.1, (extChartAt I α).symm y)) z.2)
            (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
      ∂(volume.restrict (_root_.Set.Ioc a b)).prod ((modelHaar (E := E)).restrict W)) =
      ∫ t in _root_.Set.Ioc a b, ∫ x, u (t, x) * (deriv (fun s => Ψ (s, x)) t +
        (g t).inner x (gradientFun (g t) (fun y => f (t, y)) x)
          (gradientFun (g t) (fun y => Ψ (t, y)) x))
        ∂riemannianVolumeMeasure (I := I) (M := M) (g t) := by
  let ψc : ℝ × E → ℝ := fun z => Ψ (z.1, (extChartAt I α).symm z.2)
  have hψc : LocallyLipschitzOn (_root_.Set.Ioo a b ×ˢ W) ψc := by
    intro z hz
    obtain ⟨C, V, hV, hC⟩ := hψ hz
    refine ⟨C, V ∩ (_root_.Set.Ioo a b ×ˢ W), _root_.Filter.inter_mem hV self_mem_nhdsWithin, ?_⟩
    intro x hx y hy
    rw [show ψc x = ψ x from hext x.1 x.2 hx.2.2,
      show ψc y = ψ y from hext y.1 y.2 hy.2.2]
    exact hC hx.1 hy.1
  have htime (t : ℝ) (y : E) (hy : y ∈ W) :
      deriv (fun s => Ψ (s, (extChartAt I α).symm y)) t =
        deriv (fun s => ψ (s, y)) t := by
    congr 1
    funext s
    exact hext s y hy
  have hspace (t : ℝ) (y : E) (hy : y ∈ W) :
      fderiv ℝ (fun v => Ψ (t, (extChartAt I α).symm v)) y =
        fderiv ℝ (fun v => ψ (t, v)) y := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hW.mem_nhds hy] with v hv
    exact hext t v hv
  have hislice := (_root_.MeasureTheory.integrable_prod_iff hi.aestronglyMeasurable).mp hi |>.1
  have hiwhole : ∀ᵐ t ∂volume, t ∈ _root_.Set.Ioo a b → _root_.MeasureTheory.Integrable
      (fun y => chartDensity (g t) α ((extChartAt I α).symm y) *
        (u (t, (extChartAt I α).symm y) *
          (deriv (fun s => Ψ (s, (extChartAt I α).symm y)) t +
            chartGradientBilin (g t) α ((extChartAt I α).symm y)
              (fderiv ℝ (fun v => f (t, (extChartAt I α).symm v)) y)
              (fderiv ℝ (fun v => Ψ (t, (extChartAt I α).symm v)) y))))
      ((modelHaar (E := E)).restrict W) := by
    have haeslice := (_root_.MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mp hislice
    filter_upwards [haeslice] with t ht htS
    apply (ht ⟨htS.1, htS.2.le⟩).congr
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hW.measurableSet] with y hy
    rw [htime t y hy, hspace t y hy, mul_assoc]
  have htransport := ae_integrable_and_integral_time_gradient_residual_eq_chartDensity
    (μ := _root_.MeasureTheory.MeasureSpace.volume) g α u f Ψ isOpen_Ioo hW hWt hΨc hΨs hΨW hf hψc hiwhole
  have hmem : ∀ᵐ t ∂volume.restrict (_root_.Set.Ioc a b), t ∈ _root_.Set.Ioo a b := by
    rw [← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    exact _root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo
  rw [_root_.MeasureTheory.integral_prod _ hi]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [_root_.MeasureTheory.ae_restrict_of_ae htransport, hmem] with t ht htS
  rw [(ht htS).2]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem hW.measurableSet] with y hy
  rw [htime t y hy, hspace t y hy, mul_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integral_chart_time_gradient_residual_eq_of_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integral_chart_time_gradient_residual_eq_of_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integral_chart_time_gradient_residual_eq_of_extension ``Submission.DifferentialGeometry.Integral.Measure.integral_chart_time_gradient_residual_eq_of_extension

end DifferentialGeometry.Integral.Measure
