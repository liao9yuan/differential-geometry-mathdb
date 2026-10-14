import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointDensityLipschitzTests
import Submission.DifferentialGeometry.Analysis.Parabolic.WeakEquation.PartitionOfUnity
import Submission.DifferentialGeometry.Geometry.Coordinates.Calculus.ParametricZeroExtension
import Submission.DifferentialGeometry.Topology.Manifold.CompactChartNeighborhood
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Integrability
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.ChartFamilyIdentification
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Integral.Prod

import Submission.DifferentialGeometry.Geometry.Measure.ManifoldRademacher
import Submission.DifferentialGeometry.Geometry.Coordinates.Fields.Scalar
import Mathlib.Analysis.Calculus.ContDiff.RCLike

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


section

open _root_.Filter _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates (scalarOnE)
open scoped _root_.Topology _root_.Submission.Topology _root_.ContDiff

namespace DifferentialGeometry.Geometry.Measure

private theorem locallyLipschitzOn_slice
    {P X F : Type*} [PseudoEMetricSpace P] [PseudoEMetricSpace X] [PseudoEMetricSpace F]
    {S : Set P} {T : Set X} {f : P × X → F}
    (hf : LocallyLipschitzOn (S ×ˢ T) f) {t : P} (ht : t ∈ S) :
    LocallyLipschitzOn T (fun x => f (t, x)) := by
  intro x hx
  obtain ⟨K, V, hV, hK⟩ := hf (show (t, x) ∈ S ×ˢ T from ⟨ht, hx⟩)
  have hpair : _root_.Filter.Tendsto (fun y : X => (t, y)) (𝓝[T] x) (𝓝[S ×ˢ T] (t, x)) := by
    apply (continuous_const.prodMk continuous_id).continuousWithinAt.tendsto_nhdsWithin
    exact fun _ hy => ⟨ht, hy⟩
  refine ⟨K, (fun y : X => (t, y)) ⁻¹' V, hpair hV, ?_⟩
  intro y hy z hz
  simpa only [Prod.edist_eq, _root_.PseudoEMetricSpace.edist_self, zero_max] using hK hy hz

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.locallyLipschitzOn_slice
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.locallyLipschitzOn_slice target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }

private theorem ae_mdifferentiableAt_slice_of_chart_locallyLipschitzOn
    [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    {P : Type*} [PseudoEMetricSpace P]
    (g : P → SmoothRiemannianMetric I M) {S : Set P} {ψ : P × M → ℝ}
    (hψ : ∀ alpha : M, LocallyLipschitzOn (S ×ˢ (extChartAt I alpha).target)
      (fun z : P × E => ψ (z.1, (extChartAt I alpha).symm z.2)))
    {t : P} (ht : t ∈ S) :
    ∀ᵐ x ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) (g t),
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => ψ (t, x)) x := by
  apply ae_iff.mpr
  apply riemannianVolumeMeasure_nondiff_null
  intro alpha
  exact locallyLipschitzOn_slice (hψ alpha) ht

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.ae_mdifferentiableAt_slice_of_chart_locallyLipschitzOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.ae_mdifferentiableAt_slice_of_chart_locallyLipschitzOn target :: scope.openDecls } }

private theorem locallyLipschitzOn_chart_mul
    [I.Boundaryless] {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (alpha : M) {S : Set P} {rho : M → ℝ} {ψ : P × M → ℝ}
    (hrho : ContMDiff I 𝓘(ℝ, ℝ) ∞ rho)
    (hψ : LocallyLipschitzOn (S ×ˢ (extChartAt I alpha).target)
      (fun z : P × E => ψ (z.1, (extChartAt I alpha).symm z.2))) :
    LocallyLipschitzOn (S ×ˢ (extChartAt I alpha).target)
      (fun z : P × E => rho ((extChartAt I alpha).symm z.2) *
        ψ (z.1, (extChartAt I alpha).symm z.2)) := by
  have hrhoC : ContDiffOn ℝ ∞
      (fun z : P × E => rho ((extChartAt I alpha).symm z.2))
      (_root_.Set.univ ×ˢ (extChartAt I alpha).target) := by
    exact (Tensor.Coordinates.scalarOnE_contDiffOn alpha hrho).comp
      contDiffOn_snd (fun _ hz => hz.2)
  have hrhoL : LocallyLipschitzOn (S ×ˢ (extChartAt I alpha).target)
      (fun z : P × E => rho ((extChartAt I alpha).symm z.2)) := by
    intro z hz
    have hat : ContDiffAt ℝ 1
        (fun z : P × E => rho ((extChartAt I alpha).symm z.2)) z :=
      (hrhoC.of_le (by simp)).contDiffAt
        ((isOpen_univ.prod (isOpen_extChartAt_target (I := I) alpha)).mem_nhds
          ⟨mem_univ _, hz.2⟩)
    obtain ⟨K, V, hV, hK⟩ := hat.exists_lipschitzOnWith
    exact ⟨K, V, mem_nhdsWithin_of_mem_nhds hV, hK⟩
  have hmul : LocallyLipschitz (fun z : ℝ × ℝ => z.1 * z.2) :=
    (contDiff_fst.mul contDiff_snd : ContDiff ℝ 1 (fun z : ℝ × ℝ => z.1 * z.2)).locallyLipschitz
  rw [locallyLipschitzOn_iff_restrict]
  exact hmul.comp (hrhoL.restrict.prodMk hψ.restrict)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.locallyLipschitzOn_chart_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.locallyLipschitzOn_chart_mul target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private theorem contDiffOn_scalarOnE_prod
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {k : WithTop ℕ∞} [IsManifold I k M]
    (alpha : M) {f : P × M → ℝ} {s : Set P}
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) k f (s ×ˢ _root_.Set.univ)) :
    ContDiffOn ℝ k
      (fun z : P × E => scalarOnE (I := I) alpha (fun x => f (z.1, x)) z.2)
      (s ×ˢ (extChartAt I alpha).target) := by
  have hfst : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, P) k
      (fun z : P × E => z.1) (s ×ˢ (extChartAt I alpha).target) := contMDiffOn_fst
  have hsnd : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, E)) I k
      (fun z : P × E => (extChartAt I alpha).symm z.2)
      (s ×ˢ (extChartAt I alpha).target) := by
    refine (contMDiffOn_extChartAt_symm (I := I) alpha).comp contMDiffOn_snd ?_
    exact fun _ hz => hz.2
  have hpair := hfst.prodMk hsnd
  have hcomp := hf.comp hpair (fun _ hz => ⟨hz.1, _root_.Set.mem_univ _⟩)
  have hcont : ContDiffOn ℝ k
      (fun z : P × E => f (z.1, (extChartAt I alpha).symm z.2))
      (s ×ˢ (extChartAt I alpha).target) := by
    rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hcomp
  exact hcont

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.contDiffOn_scalarOnE_prod
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.contDiffOn_scalarOnE_prod target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private theorem locallyLipschitzOn_chart_prod_of_contMDiff
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [IsManifold I 1 M] [I.Boundaryless]
    (alpha : M) {S : Set P} {ψ : P × M → ℝ}
    (hψ : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) 1 ψ) :
    LocallyLipschitzOn (S ×ˢ (extChartAt I alpha).target)
      (fun z : P × E => ψ (z.1, (extChartAt I alpha).symm z.2)) := by
  have hraw : ContDiffOn ℝ 1
      (fun z : P × E => ψ (z.1, (extChartAt I alpha).symm z.2))
      (_root_.Set.univ ×ˢ (extChartAt I alpha).target) :=
    contDiffOn_scalarOnE_prod alpha hψ.contMDiffOn
  intro z hz
  have hat : ContDiffAt ℝ 1
      (fun z : P × E => ψ (z.1, (extChartAt I alpha).symm z.2)) z :=
    hraw.contDiffAt
      ((isOpen_univ.prod (isOpen_extChartAt_target (I := I) alpha)).mem_nhds
        ⟨mem_univ _, hz.2⟩)
  obtain ⟨K, V, hV, hK⟩ := hat.exists_lipschitzOnWith
  exact ⟨K, V, mem_nhdsWithin_of_mem_nhds hV, hK⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.locallyLipschitzOn_chart_prod_of_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.locallyLipschitzOn_chart_prod_of_contMDiff target :: scope.openDecls } }

end DifferentialGeometry.Geometry.Measure

end

noncomputable section

open _root_.Filter _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

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

open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.MeasureTheory _root_.Submission.MeasureTheory

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
namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Set _root_.Submission.Set _root_.TopologicalSpace _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Analysis.Calculus
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_3 : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_3 : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_2 : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2 : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2 target :: scope.openDecls } }

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instBorelSpace_differentialGeometry target :: scope.openDecls } }

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorNormedSpace target :: scope.openDecls } }

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedSpace target :: scope.openDecls } }

private local instance covectorBilinNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorBilinNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedSpace target :: scope.openDecls } }

namespace HalfLineMetricConvergenceData

private theorem integrable_density_residual_of_chart_support
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y : P.M, ∀ t ∈ _root_.Set.Icc a c,
      _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) _root_.Filter.atTop (𝓝 (ell (y, t))))
    (x : P.M)
    {a' c' : ℝ} (haa : a < a') (hcc : c' < c)
    (ψ : ℝ × P.M → ℝ)
    (hψ : LocallyLipschitzOn (_root_.Set.Ioo a c ×ˢ (extChartAt I x).target)
      (fun z : ℝ × E => ψ (z.1, (extChartAt I x).symm z.2)))
    (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ _root_.Set.Ioo a' c' ×ˢ (_root_.Set.univ : Set P.M))
    (hψsource : Prod.snd '' tsupport ψ ⊆ (chartAt H x).source) :
    let g := fun t : ℝ => co.gInf (1 - t)
    let density := fun z : ℝ × P.M => Real.exp (-ell (z.2, z.1) -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    let residual := fun (t : ℝ) (x : P.M) => density (t, x) *
      (deriv (fun s => ψ (s, x)) t +
        (g t).inner x (gradientFun (g t) (fun y => ell (y, t)) x)
          (gradientFun (g t) (fun y => ψ (t, y)) x))
    (∀ᵐ t ∂volume.restrict (_root_.Set.Ioc a' c'),
      _root_.MeasureTheory.Integrable (residual t)
        (Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t))) ∧
    _root_.MeasureTheory.Integrable (fun t => ∫ x, residual t x
      ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t))
      (volume.restrict (_root_.Set.Ioc a' c')) := by
  let C : Set P.M := Prod.snd '' tsupport ψ
  have hC : IsCompact C := hψc.image continuous_snd
  have hCs : C ⊆ (extChartAt I x).source := by
    simpa only [extChartAt_source] using hψsource
  obtain ⟨W, hW, hCW, hWclosure, _, hJ, _, hWJ⟩ :=
    exists_open_extChartAt_image_isCompact_closure x hC hCs
  let J : Set P.M := (extChartAt I x).symm '' closure W
  have hWt : W ⊆ (extChartAt I x).target := subset_closure.trans hWclosure
  let g := fun t : ℝ => co.gInf (1 - t)
  let u : ℝ × P.M → ℝ := fun z => Real.exp (-ell (z.2, z.1) -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
  let f : ℝ × P.M → ℝ := fun z => ell (z.2, z.1)
  let v : ℝ × E → ℝ := fun z =>
    Integral.DivergenceTheorem.chartPullZero (I := I) x (fun y => ψ (z.1, y)) z.2
  let raw : ℝ × E → ℝ := fun z => ψ (z.1, (extChartAt I x).symm z.2)
  let B := fun z : ℝ × E => chartGradientBilin (g z.1) x ((extChartAt I x).symm z.2)
  let d := fun z : ℝ × E =>
    fderiv ℝ (fun y : E => ell ((extChartAt I x).symm y, z.1)) z.2
  let Q : ℝ × E → ℝ := fun z => chartDensity (g z.1) x ((extChartAt I x).symm z.2) *
    (u (z.1, (extChartAt I x).symm z.2) *
      (deriv (fun t => raw (t, z.2)) z.1 +
        B z (d z) (fderiv ℝ (fun y : E => raw (z.1, y)) z.2)))
  let μ : _root_.MeasureTheory.Measure ℝ := volume.restrict (_root_.Set.Ioo a' c')
  let ν : _root_.MeasureTheory.Measure E := (modelHaar (E := E)).restrict W
  have hvCompact : HasCompactSupport v :=
    Integral.DivergenceTheorem.hasCompactSupport_chartPullZero_prod x hψc hψsource
  have hvSupport : tsupport v ⊆ _root_.Set.Ioo a' c' ×ˢ W := by
    intro z hz
    obtain ⟨z', hz', rfl⟩ :=
      Integral.DivergenceTheorem.tsupport_chartPullZero_prod_subset_image x hψc hψsource hz
    exact ⟨(hψsupp hz').1, hCW ⟨z'.2, ⟨z', hz', rfl⟩, rfl⟩⟩
  let Ω : Set (ℝ × E) := _root_.Set.Ioo a c ×ˢ (extChartAt I x).target
  have hΩ : IsOpen Ω := isOpen_Ioo.prod (isOpen_extChartAt_target (I := I) x)
  have hvLocal : LocallyLipschitzOn Ω v := by
    intro z hz
    obtain ⟨K, V, hV, hLip⟩ := hψ hz
    refine ⟨K, V ∩ Ω, _root_.Filter.inter_mem hV self_mem_nhdsWithin, ?_⟩
    intro z₁ hz₁ z₂ hz₂
    dsimp only [v]
    rw [Integral.DivergenceTheorem.chartPullZero_mem x _ hz₁.2.2,
      Integral.DivergenceTheorem.chartPullZero_mem x _ hz₂.2.2]
    exact hLip hz₁.1 hz₂.1
  have hvAmbient : tsupport v ⊆ Ω := by
    intro z hz
    have hz' := hvSupport hz
    exact ⟨⟨haa.trans hz'.1.1, hz'.1.2.trans hcc⟩, hWt hz'.2⟩
  have hvLip : LocallyLipschitz v :=
    hvLocal.locallyLipschitz_of_tsupport_subset hΩ hvAmbient
  have hrawLip : LocallyLipschitzOn (_root_.Set.Ioo a' c' ×ˢ W) raw :=
    hψ.mono (fun _ hz =>
      ⟨⟨haa.trans hz.1.1, hz.1.2.trans hcc⟩, hWt hz.2⟩)
  have hconvJ : ∀ y ∈ J, ∀ t ∈ _root_.Set.Icc a c,
      _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) _root_.Filter.atTop (𝓝 (ell (y, t))) :=
    fun y _ t ht => hconv y t ht
  have hlimitLip : LocallyLipschitzOn (_root_.Set.Ioo a' c' ×ˢ W)
      (fun z : ℝ × E => f (z.1, (extChartAt I x).symm z.2)) :=
    (locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbase
      rho hrho ell hconvJ x hWt hWJ).mono
        (fun _ hz => ⟨⟨(haa.trans hz.1.1).le, (hz.1.2.trans hcc).le⟩, hz.2⟩)
  have hvInt := integrable_poleEndpoint_redDensity_limit_chart_residual
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co
    kappa hF p hJ ha hbase rho hrho ell hconvJ x hW hWt hWJ haa hcc v
    hvLip.locallyLipschitzOn hvCompact hvSupport
  have htime (y : E) (hy : y ∈ W) :
      (fun t => v (t, y)) = fun t => raw (t, y) := by
    funext t
    exact Integral.DivergenceTheorem.chartPullZero_mem x _ (hWt hy)
  have hspace (t : ℝ) (y : E) (hy : y ∈ W) :
      fderiv ℝ (fun z : E => v (t, z)) y =
        fderiv ℝ (fun z : E => raw (t, z)) y := by
    have hEq : (fun z : E => v (t, z)) =ᶠ[𝓝 y] fun z : E => raw (t, z) := by
      filter_upwards [(isOpen_extChartAt_target (I := I) x).mem_nhds (hWt hy)] with z hz
      exact Integral.DivergenceTheorem.chartPullZero_mem x _ hz
    exact hEq.fderiv_eq
  have hEq : (fun z : ℝ × E => chartDensity (g z.1) x ((extChartAt I x).symm z.2) *
      u (z.1, (extChartAt I x).symm z.2) *
      (deriv (fun t => v (t, z.2)) z.1 +
        B z (d z) (fderiv ℝ (fun y : E => v (z.1, y)) z.2))) =ᵐ[
          (volume.restrict (_root_.Set.Ioc a' c')).prod ν] Q := by
    dsimp only [ν]
    rw [Measure.prod_restrict]
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem (measurableSet_Ioc.prod hW.measurableSet)] with z hz
    dsimp only [Q]
    rw [htime z.2 hz.2, hspace z.1 z.2 hz.2, mul_assoc]
  have hQInt : _root_.MeasureTheory.Integrable Q ((volume.restrict (_root_.Set.Ioc a' c')).prod ν) := hvInt.congr hEq
  have hQIntOpen : _root_.MeasureTheory.Integrable Q (μ.prod ν) := by
    simpa only [μ, _root_.MeasureTheory.restrict_Ioo_eq_restrict_Ioc] using hQInt
  have hslice : ∀ᵐ t ∂volume, t ∈ _root_.Set.Ioo a' c' → _root_.MeasureTheory.Integrable (fun y => Q (t, y)) ν :=
    (_root_.MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mp hQIntOpen.prod_right_ae
  have hψW : ∀ z ∈ tsupport ψ, extChartAt I x z.2 ∈ W := by
    intro z hz
    exact hCW ⟨z.2, ⟨z, hz, rfl⟩, rfl⟩
  have htransport :=
    Integral.Measure.ae_integrable_and_integral_time_gradient_residual_eq_chartDensity
      (μ := _root_.MeasureTheory.MeasureSpace.volume) g x u f ψ isOpen_Ioo hW hWt hψc hψsource hψW
      hlimitLip hrawLip hslice
  let intrinsic := fun (t : ℝ) (y : P.M) => u (t, y) *
    (deriv (fun s => ψ (s, y)) t +
      (g t).inner y (gradientFun (g t) (fun z => f (t, z)) y)
        (gradientFun (g t) (fun z => ψ (t, z)) y))
  have htransportOpen : ∀ᵐ t ∂μ,
      _root_.MeasureTheory.Integrable (intrinsic t)
        (Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t)) ∧
        (∫ y, intrinsic t y ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t)) =
          ∫ y, Q (t, y) ∂ν :=
    (_root_.MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr htransport
  have hspatial : ∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (intrinsic t)
      (Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t)) :=
    htransportOpen.mono fun _ h => h.1
  have hintegral : (fun t => ∫ y, intrinsic t y
      ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t)) =ᵐ[μ]
      (fun t => ∫ y, Q (t, y) ∂ν) := htransportOpen.mono fun _ h => h.2
  have houter : _root_.MeasureTheory.Integrable
      (fun t => ∫ y, intrinsic t y
        ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t)) μ :=
    hQIntOpen.integral_prod_left.congr hintegral.symm
  simpa only [μ, _root_.MeasureTheory.restrict_Ioo_eq_restrict_Ioc] using And.intro hspatial houter

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_density_residual_of_chart_support
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_density_residual_of_chart_support target :: scope.openDecls } }

theorem integrable_poleEndpoint_redDensity_limit_residual
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y : P.M, ∀ t ∈ _root_.Set.Icc a c,
      _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) _root_.Filter.atTop (𝓝 (ell (y, t))))
    {a' c' : ℝ} (haa : a < a') (hcc : c' < c)
    (ψ : ℝ × P.M → ℝ)
    (hψ : ∀ x : P.M, LocallyLipschitzOn (_root_.Set.Ioo a c ×ˢ (extChartAt I x).target)
      (fun z : ℝ × E => ψ (z.1, (extChartAt I x).symm z.2)))
    (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ _root_.Set.Ioo a' c' ×ˢ (_root_.Set.univ : Set P.M)) :
    let g := fun t : ℝ => co.gInf (1 - t)
    let density := fun z : ℝ × P.M => Real.exp (-ell (z.2, z.1) -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    let residual := fun (t : ℝ) (x : P.M) => density (t, x) *
      (deriv (fun s => ψ (s, x)) t +
        (g t).inner x (gradientFun (g t) (fun y => ell (y, t)) x)
          (gradientFun (g t) (fun y => ψ (t, y)) x))
    (∀ᵐ t ∂volume.restrict (_root_.Set.Ioc a' c'),
      _root_.MeasureTheory.Integrable (residual t)
        (Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t))) ∧
    _root_.MeasureTheory.Integrable (fun t => ∫ x, residual t x
      ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t))
      (volume.restrict (_root_.Set.Ioc a' c')) := by
  classical
  let : MeasurableSpace P.M := borel P.M
  let g := fun t : ℝ => co.gInf (1 - t)
  let density := fun z : ℝ × P.M => Real.exp (-ell (z.2, z.1) -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
  let V : (t : ℝ) → (x : P.M) → TangentSpace I x :=
    fun t x => gradientFun (g t) (fun y => ell (y, t)) x
  let Aop : ∀ z : ℝ × P.M, (TangentSpace I z.2 →L[ℝ] ℝ) →L[ℝ] ℝ :=
    fun z => density z • ContinuousLinearMap.apply ℝ ℝ (V z.1 z.2)
  let L := fun (v : ℝ × P.M → ℝ) (t : ℝ) (x : P.M) =>
    density (t, x) * deriv (fun r => v (r, x)) t +
      Aop (t, x) (mvfderiv I (fun y => v (t, y)) x)
  let μ : _root_.MeasureTheory.Measure ℝ := volume.restrict (_root_.Set.Ioc a' c')
  let ν := fun t => Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t)
  let ρ := chartAtlasPOU I P.M
  let K := Prod.snd '' tsupport ψ
  have hK : IsCompact K := hψc.image continuous_snd
  have hψK : ∀ t, Function.support (fun x => ψ (t, x)) ⊆ K := by
    intro t x hx
    exact ⟨(t, x), subset_tsupport ψ hx, rfl⟩
  have hρ : ρ.IsSubordinate (fun i : P.M => (chartAt H i).source) :=
    chartAtlasPOU_isSubordinate I P.M
  let v := fun (i : P.M) (z : ℝ × P.M) => ρ i z.2 * ψ z
  have hvc (i : P.M) : HasCompactSupport (v i) := hψc.mul_left
  have hvs (i : P.M) : tsupport (v i) ⊆ tsupport ψ := tsupport_mul_subset_right
  have hvsource (i : P.M) : Prod.snd '' tsupport (v i) ⊆ (chartAt H i).source := by
    rintro x ⟨z, hz, rfl⟩
    apply hρ i
    exact tsupport_comp_subset_preimage (f := Prod.snd) (ρ i) continuous_snd
      (tsupport_mul_subset_left hz)
  have hv (i : P.M) : LocallyLipschitzOn (_root_.Set.Ioo a c ×ˢ (extChartAt I i).target)
      (fun z : ℝ × E => v i (z.1, (extChartAt I i).symm z.2)) :=
    Geometry.Measure.locallyLipschitzOn_chart_mul i (ρ i).contMDiff (hψ i)
  have hlocal (i : P.M) :
      (∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (L (v i) t) (ν t)) ∧
      Integrable (fun t => ∫ x, L (v i) t x ∂ν t) μ := by
    have h := integrable_density_residual_of_chart_support
      F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co
      kappa hF p ha hbase rho hrho ell hconv i haa hcc (v i) (hv i) (hvc i)
      ((hvs i).trans hψsupp) (hvsource i)
    simpa only [inner_gradientFun_eq_mvfderiv, L, Aop, V, g, density, μ, ν,
      smul_apply, ContinuousLinearMap.apply_apply, smul_eq_mul, mul_add] using h
  have hlocalFinite : ∀ᵐ t ∂μ, ∀ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
      Integrable (L (v i) t) (ν t) :=
    (Filter.eventually_all_finset _).2 (fun i _ => (hlocal i).1)
  have htest : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t,
      MDifferentiableAt I 𝓘(ℝ) (fun y => ψ (t, y)) x := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    exact Geometry.Measure.ae_mdifferentiableAt_slice_of_chart_locallyLipschitzOn
      g hψ ⟨haa.trans ht.1, ht.2.trans_lt hcc⟩
  have hspatial : ∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (L ψ t) (ν t) := by
    filter_upwards [htest, hlocalFinite] with t hft hint
    apply (_root_.MeasureTheory.integrable_finsetSum _ hint).congr
    filter_upwards [hft] with x hx
    change (∑ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
      (density (t, x) * deriv (fun r => ρ i x * ψ (r, x)) t +
        Aop (t, x) (mvfderiv I (fun y => ρ i y * ψ (t, y)) x))) = L ψ t x
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      ρ.sum_deriv_mul_fintsupportOn hK hψK (fun _ => _root_.Set.subset_univ _) t x,
      ← map_sum, ρ.sum_mvfderiv_mul_fintsupportOn hK (hψK t) (_root_.Set.subset_univ _) hx]
  have houter :=
    (ρ.integrable_and_integral_integral_time_spatial_derivative_eq_sum_fintsupportOn
      μ ν hK hψK (fun _ => _root_.Set.subset_univ _) htest density Aop hlocalFinite
      (fun i _ => (hlocal i).2)).1
  simpa only [inner_gradientFun_eq_mvfderiv, L, Aop, V, g, density, μ, ν,
    smul_apply, ContinuousLinearMap.apply_apply, smul_eq_mul, mul_add] using
    And.intro hspatial houter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_poleEndpoint_redDensity_limit_residual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_poleEndpoint_redDensity_limit_residual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_poleEndpoint_redDensity_limit_residual ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_poleEndpoint_redDensity_limit_residual

theorem integrable_poleEndpoint_redDensity_limit_residual_of_contMDiff
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y : P.M, ∀ t ∈ _root_.Set.Icc a c,
      _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) _root_.Filter.atTop (𝓝 (ell (y, t))))
    {a' c' : ℝ} (haa : a < a') (hcc : c' < c)
    (ψ : ℝ × P.M → ℝ)
    (hψ : ContMDiff ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) 1 ψ)
    (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ _root_.Set.Ioo a' c' ×ˢ (_root_.Set.univ : Set P.M)) :
    let g := fun t : ℝ => co.gInf (1 - t)
    let density := fun z : ℝ × P.M => Real.exp (-ell (z.2, z.1) -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    let residual := fun (t : ℝ) (x : P.M) => density (t, x) *
      (deriv (fun s => ψ (s, x)) t +
        (g t).inner x (gradientFun (g t) (fun y => ell (y, t)) x)
          (gradientFun (g t) (fun y => ψ (t, y)) x))
    (∀ᵐ t ∂volume.restrict (_root_.Set.Ioc a' c'),
      _root_.MeasureTheory.Integrable (residual t)
        (Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t))) ∧
    _root_.MeasureTheory.Integrable (fun t => ∫ x, residual t x
      ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t))
      (volume.restrict (_root_.Set.Ioc a' c')) := by
  exact integrable_poleEndpoint_redDensity_limit_residual
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co kappa hF p ha hbase
    rho hrho ell hconv haa hcc ψ
    (fun x => Geometry.Measure.locallyLipschitzOn_chart_prod_of_contMDiff
      (S := _root_.Set.Ioo a c) x hψ) hψc hψsupp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_poleEndpoint_redDensity_limit_residual_of_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_poleEndpoint_redDensity_limit_residual_of_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_poleEndpoint_redDensity_limit_residual_of_contMDiff ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_poleEndpoint_redDensity_limit_residual_of_contMDiff

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
