import Submission.DifferentialGeometry.Geometry.Operator.DirectionalDerivative
import Submission.DifferentialGeometry.Topology.LipschitzSupport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter _root_.Set _root_.Manifold
open scoped _root_.Topology

namespace DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section TopologicalParameter

variable {P : Type*} [TopologicalSpace P] [T2Space P]

omit [T2Space P] in
private theorem isCompact_chart_image_prod
    (alpha : M) {f : P × M → ℝ} (hc : HasCompactSupport f)
    (hs : Prod.snd '' tsupport f ⊆ (chartAt H alpha).source) :
    IsCompact ((fun z : P × M => (z.1, extChartAt I alpha z.2)) '' tsupport f) := by
  apply hc.image_of_continuousOn
  refine continuous_fst.continuousOn.prodMk
    ((continuousOn_extChartAt alpha).comp continuous_snd.continuousOn ?_)
  intro z hz
  simpa only [extChartAt_source] using hs ⟨z, hz, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.isCompact_chart_image_prod
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.isCompact_chart_image_prod target :: scope.openDecls } }

theorem tsupport_chartPullZero_prod_subset_image
    (alpha : M) {f : P × M → ℝ} (hc : HasCompactSupport f)
    (hs : Prod.snd '' tsupport f ⊆ (chartAt H alpha).source) :
    tsupport (fun z : P × E => chartPullZero (I := I) alpha (fun x => f (z.1, x)) z.2) ⊆
      (fun z : P × M => (z.1, extChartAt I alpha z.2)) '' tsupport f := by
  apply closure_minimal _ (isCompact_chart_image_prod alpha hc hs).isClosed
  intro z hz
  by_cases hzt : z.2 ∈ (extChartAt I alpha).target
  · refine ⟨(z.1, (extChartAt I alpha).symm z.2), ?_, ?_⟩
    · apply subset_tsupport
      simpa only [Function.mem_support, chartPullZero_mem alpha _ hzt, scalarOnE_def]
        using hz
    · exact Prod.ext rfl ((extChartAt I alpha).right_inv hzt)
  · exact (hz (chartPullZero_nmem alpha _ hzt)).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.tsupport_chartPullZero_prod_subset_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.tsupport_chartPullZero_prod_subset_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.tsupport_chartPullZero_prod_subset_image ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.tsupport_chartPullZero_prod_subset_image

theorem hasCompactSupport_chartPullZero_prod
    (alpha : M) {f : P × M → ℝ} (hc : HasCompactSupport f)
    (hs : Prod.snd '' tsupport f ⊆ (chartAt H alpha).source) :
    HasCompactSupport
      (fun z : P × E => chartPullZero (I := I) alpha (fun x => f (z.1, x)) z.2) := by
  exact (isCompact_chart_image_prod alpha hc hs).of_isClosed_subset isClosed_closure
    (tsupport_chartPullZero_prod_subset_image alpha hc hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.hasCompactSupport_chartPullZero_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.hasCompactSupport_chartPullZero_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.hasCompactSupport_chartPullZero_prod ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.hasCompactSupport_chartPullZero_prod

theorem tsupport_chartPullZero_prod_subset_target
    (alpha : M) {f : P × M → ℝ} (hc : HasCompactSupport f)
    (hs : Prod.snd '' tsupport f ⊆ (chartAt H alpha).source) :
    tsupport (fun z : P × E => chartPullZero (I := I) alpha (fun x => f (z.1, x)) z.2) ⊆
      Set.univ ×ˢ (extChartAt I alpha).target := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := tsupport_chartPullZero_prod_subset_image alpha hc hs hz
  refine ⟨mem_univ _, (extChartAt I alpha).map_source ?_⟩
  simpa only [extChartAt_source] using hs ⟨x, hx, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.tsupport_chartPullZero_prod_subset_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.tsupport_chartPullZero_prod_subset_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.tsupport_chartPullZero_prod_subset_target ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.tsupport_chartPullZero_prod_subset_target

end TopologicalParameter

section NormedParameter

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [I.Boundaryless]

theorem contDiff_chartPullZero_prod
    {k : WithTop ℕ∞} (alpha : M) {f : P × M → ℝ} (hc : HasCompactSupport f)
    (hs : Prod.snd '' tsupport f ⊆ (chartAt H alpha).source)
    (hf : ContDiffOn ℝ k
      (fun z : P × E => scalarOnE (I := I) alpha (fun x => f (z.1, x)) z.2)
      (Set.univ ×ˢ (extChartAt I alpha).target)) :
    ContDiff ℝ k
      (fun z : P × E => chartPullZero (I := I) alpha (fun x => f (z.1, x)) z.2) := by
  apply ContDiffOn.contDiff_of_tsupport_subset
    (s := Set.univ ×ˢ (extChartAt I alpha).target)
  · exact hf.congr fun z hz => chartPullZero_mem alpha _ hz.2
  · exact isOpen_univ.prod (isOpen_extChartAt_target (I := I) alpha)
  · exact tsupport_chartPullZero_prod_subset_target alpha hc hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.contDiff_chartPullZero_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.contDiff_chartPullZero_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.contDiff_chartPullZero_prod ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.contDiff_chartPullZero_prod

omit [NormedSpace ℝ P] in
theorem locallyLipschitz_chartPullZero_prod
    (alpha : M) {f : P × M → ℝ} (hc : HasCompactSupport f)
    (hs : Prod.snd '' tsupport f ⊆ (chartAt H alpha).source)
    (hf : LocallyLipschitzOn (Set.univ ×ˢ (extChartAt I alpha).target)
      (fun z : P × E => scalarOnE (I := I) alpha (fun x => f (z.1, x)) z.2)) :
    LocallyLipschitz
      (fun z : P × E => chartPullZero (I := I) alpha (fun x => f (z.1, x)) z.2) := by
  apply LocallyLipschitzOn.locallyLipschitz_of_tsupport_subset
    (isOpen_univ.prod (isOpen_extChartAt_target (I := I) alpha))
  · intro z hz
    obtain ⟨C, V, hV, hC⟩ := hf hz
    refine ⟨C, V ∩ (Set.univ ×ˢ (extChartAt I alpha).target),
      _root_.Filter.inter_mem hV self_mem_nhdsWithin, ?_⟩
    intro w hw q hq
    dsimp only
    rw [chartPullZero_mem alpha _ hw.2.2, chartPullZero_mem alpha _ hq.2.2]
    exact hC hw.1 hq.1
  · exact tsupport_chartPullZero_prod_subset_target alpha hc hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.locallyLipschitz_chartPullZero_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.locallyLipschitz_chartPullZero_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.locallyLipschitz_chartPullZero_prod ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.locallyLipschitz_chartPullZero_prod

end NormedParameter

end DifferentialGeometry.Integral.DivergenceTheorem
