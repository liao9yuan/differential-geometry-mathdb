import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakChartDerivative
import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakChartLp
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.SmoothMul

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
open _root_.Submission.DifferentialGeometry.Geometry.Operator

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


theorem MemW1pIntrinsicLp.memWkpChart [CompactSpace M] [T2Space M] [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ} (hu : MemW1pIntrinsicLp g p u) :
    Chart.MemWkpChart (I := I) 1 p u := by
  classical
  let μ := riemannianVolumeMeasure I M g
  let : _root_.MeasureTheory.IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  obtain ⟨hu, G₀, hG₀, hGn₀⟩ := hu
  let G : ∀ x : M, TangentSpace I x := fun x => G₀ x
  have hG : HasWeakRiemannianGradLp g u G := hG₀
  intro α
  let ρ : M → ℝ := chartAtlasPOU I M α
  have hρ : ContMDiff I 𝓘(ℝ) ∞ ρ := (chartAtlasPOU I M α).contMDiff
  have hρs : tsupport ρ ⊆ (chartAt H α).source := chartAtlasPOU_isSubordinate I M α
  let v : M → ℝ := fun x => ρ x * u x
  let V : ∀ x : M, TangentSpace I x := fun x => ρ x • G x + u x • gradFun (I := I) g ρ x
  obtain ⟨hv, hV, hVn⟩ := hG.smooth_mul_witness hp hu hGn₀ hρ
  have hvs : tsupport v ⊆ (chartAt H α).source :=
    (tsupport_mul_subset_left : tsupport (fun x => ρ x * u x) ⊆ tsupport ρ).trans hρs
  have hVzero : ∀ x, x ∉ tsupport ρ → V x = 0 := by
    intro x hx
    have hρx : ρ x = 0 := image_eq_zero_of_notMem_tsupport hx
    have hgrad : gradFun (I := I) g ρ x = 0 :=
      Function.notMem_support.mp (fun h => hx (support_gradFun_subset g ρ h))
    dsimp only [V]
    rw [hρx, hgrad, zero_smul, smul_zero, add_zero]
  obtain ⟨χ, hχ, _hχrange, hχone, hχs⟩ := Chart.exists_chart_cutoff_M (I := I) α
  have hraw : DeGiorgi.MemW1p p (Chart.chartPushedRaw I α v)
      (Chart.chartTargetEuclid (I := I) α) := by
    refine ⟨memLp_chartPushedRaw_of_support g α hv hvs, fun i => ?_⟩
    let T := _root_.FiberBundle.trivializationAt E (TangentSpace I) α
    have hχT : tsupport χ ⊆ T.baseSet := by
      simpa only [T, TangentBundle.trivializationAt_baseSet] using hχs
    let X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨fun x => χ x • chartBasisVecFiber (I := I) α i x,
        hχ.contMDiffOn.smul_section_of_tsupport T.open_baseSet hχT
          (chartBasisVec_contMDiffOn α i)⟩
    let a : M → ℝ := fun x => g.inner x (V x) (chartBasisVecFiber (I := I) α i x)
    have haeq : (fun x => g.inner x (V x) (X x)) = a := by
      funext x
      by_cases hx : x ∈ tsupport ρ
      · change g.inner x (V x) (χ x • chartBasisVecFiber (I := I) α i x) = _
        rw [hχone x hx, one_smul]
      · dsimp only [a]
        rw [hVzero x hx, map_zero, zero_apply, zero_apply]
    have ha : _root_.MeasureTheory.MemLp a p μ := by
      rw [← haeq]
      exact hV.pairing_memLp hVn X
    have has : tsupport a ⊆ (chartAt H α).source := by
      apply subset_trans (closure_minimal (t := tsupport ρ) ?_ (isClosed_tsupport ρ)) hρs
      intro x hx
      by_contra hxρ
      apply hx
      dsimp only [a]
      rw [hVzero x hxρ, map_zero, zero_apply]
    refine ⟨Chart.chartPushedRaw I α a, memLp_chartPushedRaw_of_support g α ha has, ?_⟩
    exact hV.hasWeakPartialDeriv_chartPushedRaw
      (memLp_one_iff_integrable.mp (hv.mono_exponent hp))
      (memLp_one_iff_integrable.mp (hVn.mono_exponent hp)) α i
  apply Euclidean.MemWkp.one_iff_memW1p.mpr
  apply (Euclidean.MemW1p_congr_ae (Chart.chartTargetEuclid_isOpen (I := I) (α := α)) ?_).mp hraw
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem (Chart.chartTargetEuclid_measurableSet (I := I) α)] with y hy
  rw [Chart.chartPushedRaw_apply_of_mem α v hy]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp.memWkpChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp.memWkpChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp.memWkpChart ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp.memWkpChart

end DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
