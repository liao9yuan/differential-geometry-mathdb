import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricPerturbationPath.ChartLieDerivative
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricPerturbationPath.ChartRicciDerivative
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ConnectionDifference.Coefficients
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricPrincipalDefect.Defs
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrection.TopOrderReanchoring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section


open _root_.Set _root_.Function _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.intervalIntegral
open scoped _root_.Topology _root_.Manifold _root_.BigOperators _root_.ContDiff

namespace DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
  [I.Boundaryless]

private local instance instCompleteSpaceE : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.instCompleteSpaceE
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.instCompleteSpaceE target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] in
private theorem unitModel_add_app
    (g₀ : SmoothRiemannianMetric I M) (A B : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g₀ 2 (A + B) x v =
      unitModel (I := I) (M := M) g₀ 2 A x v +
        unitModel (I := I) (M := M) g₀ 2 B x v := by
  have hfun : unitModel (I := I) (M := M) g₀ 2 (A + B) x =
      unitModel (I := I) (M := M) g₀ 2 A x +
        unitModel (I := I) (M := M) g₀ 2 B x := by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
      add_apply, Tensor0SBundle.Tensor0SSpace.toModel_add]
  rw [hfun, add_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.unitModel_add_app
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.unitModel_add_app target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] in
private theorem unitModel_sub_app
    (g₀ : SmoothRiemannianMetric I M) (A B : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g₀ 2 (A - B) x v =
      unitModel (I := I) (M := M) g₀ 2 A x v -
        unitModel (I := I) (M := M) g₀ 2 B x v := by
  have hfun : unitModel (I := I) (M := M) g₀ 2 (A - B) x =
      unitModel (I := I) (M := M) g₀ 2 A x -
        unitModel (I := I) (M := M) g₀ 2 B x := by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      sub_apply, Tensor0SBundle.Tensor0SSpace.toModel_sub]
  rw [hfun, sub_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.unitModel_sub_app
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.unitModel_sub_app target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] [T2Space M] in
private theorem ccBilin_sub
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (x : M) (v w : TangentSpace I x) :
    smoothCcTensorBilinForm (I := I) g₀ (T - T') x v w =
      smoothCcTensorBilinForm (I := I) g₀ T x v w - smoothCcTensorBilinForm (I := I) g₀ T' x v
        w := by
  rw [← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ (T - T') x v w,
    ← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T x v w,
    ← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T' x v w]
  exact unitModel_sub_app (I := I) (M := M) g₀ T T' x
    (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (![v, w] i))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.ccBilin_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.ccBilin_sub target :: scope.openDecls } }

def rhsPathSlope
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (s : ℝ) (y : E) : ℝ :=
  (-2 : ℝ) *
      (∑ j : Fin (Module.finrank ℝ E),
        deriv (fun t : ℝ =>
          chartRiemannTensor (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t)
            α i j k j y) s) +
    lieDeTurckChartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      g_bg α i k s y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsPathSlope then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsPathSlope"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsPathSlope ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsPathSlope

omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem hasDerivAt_rhsPath
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) {s : ℝ}
    (hs : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :
    HasDerivAt
      (fun t : ℝ => chartDeTurckRicciRHS (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) g_bg α i k y)
      (rhsPathSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        g_bg α i k s y) s := by
  let _ : NormedAddCommGroup ℝ := Real.normedAddCommGroup
  let _ : NormedSpace ℝ ℝ := NormedAlgebra.toNormedSpace ℝ
  rw [show (fun t : ℝ => chartDeTurckRicciRHS (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) g_bg α i k y) =
      (fun t : ℝ =>
        (-2 : ℝ) * chartRicciTensor (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) α i k y +
          chartLieDeTurckComp (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) g_bg α i k y) by
    funext t
    rw [chartDeTurckRicciRHS_def]]
  have hRic := hasDerivAt_metricPerturbationPath_chartRicciTensor (I := I)
    g₀ T T' hδ hδ' α i k hy hs
  have hLie := hasDerivAt_metricPerturbationPath_chartLieDeTurckComp_chartSlope (I := I)
    g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg α i k hy hs
  have hsum := (hRic.const_mul (-2 : ℝ)).add hLie
  change HasDerivAt
    (fun t : ℝ =>
      (-2 : ℝ) * chartRicciTensor (I := I)
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) α i k y +
        chartLieDeTurckComp (I := I)
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) g_bg α i k y)
    (rhsPathSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      g_bg α i k s y) s at hsum
  exact hsum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.hasDerivAt_rhsPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.hasDerivAt_rhsPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.hasDerivAt_rhsPath ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.hasDerivAt_rhsPath

omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem deriv_rhsPath
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) {s : ℝ}
    (hs : s ∈ _root_.Set.Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => chartDeTurckRicciRHS (I := I)
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) g_bg α i k y) s =
      rhsPathSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        g_bg α i k s y := by
  exact (hasDerivAt_rhsPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
    g_bg α i k hy (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt ⟨hs.1.le, hs.2.le⟩)).deriv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.deriv_rhsPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.deriv_rhsPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.deriv_rhsPath ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.deriv_rhsPath
omit [SigmaCompactSpace M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem metricPerturbationPath_zero
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    metricPerturbationPath (I := I) g₀ T T' hδ hδ' 0 =
      tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' := by
  refine riemannianMetric_eq_of_inner _ _ (fun x v w => ?_)
  rw [metricPerturbationPath_inner_of_mem (I := I) g₀ T T' hδ hδ'
      (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt ⟨le_rfl, zero_le_one⟩),
    tensorSectionRealizeMetric_inner, convexPerturbation_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricPerturbationPath_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricPerturbationPath_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricPerturbationPath_zero ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricPerturbationPath_zero
omit [SigmaCompactSpace M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem metricPerturbationPath_one
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    metricPerturbationPath (I := I) g₀ T T' hδ hδ' 1 =
      tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ := by
  refine riemannianMetric_eq_of_inner _ _ (fun x v w => ?_)
  rw [metricPerturbationPath_inner_of_mem (I := I) g₀ T T' hδ hδ'
      (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt ⟨zero_le_one, le_rfl⟩),
    tensorSectionRealizeMetric_inner, convexPerturbation_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricPerturbationPath_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricPerturbationPath_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricPerturbationPath_one ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricPerturbationPath_one

def rhsChartSum
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      chartDeTurckRicciRHS (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x i k (extChartAt I x x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsChartSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsChartSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsChartSum ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsChartSum


def rhsSumSlope
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      rhsPathSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        g_bg x i k s (extChartAt I x x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSumSlope then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSumSlope"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSumSlope ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSumSlope


def lieSumSlope
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      lieDeTurckChartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        g_bg x i k s (extChartAt I x x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieSumSlope then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieSumSlope"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieSumSlope ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieSumSlope


def lieTopSum
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      chartDeTurckCorrectionPrincipalSymbolExprRaw (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x)
        i k (extChartAt I x x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTopSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTopSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTopSum ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTopSum

def lieTopCovSum
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckLieSecondOrderPrincipalCoeff (I := I) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTopCovSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTopCovSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTopCovSum ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTopCovSum

def lieTopTailSum
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      lieTopTail (I := I) g₀ T T'
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x i k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTopTailSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTopTailSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTopTailSum ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTopTailSum

def lieTopTailSwap
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      lieTopTail (I := I) g₀ T T'
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x k i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTopTailSwap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTopTailSwap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTopTailSwap ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTopTailSwap

omit [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lieTopRaw_symm
    (g : SmoothRiemannianMetric I M) (x : M)
    (f : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionPrincipalSymbolExprRaw (I := I) g x f i j y =
      chartDeTurckCorrectionPrincipalSymbolExprRaw (I := I) g x f j i y := by
  unfold chartDeTurckCorrectionPrincipalSymbolExprRaw
  have h₁ : (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g x k j y *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g x a b y *
            chartDeTurckCorrectionHessBlockRaw (I := I) g x f i a b k y) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g x j k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g x a b y *
              chartDeTurckCorrectionHessBlockRaw (I := I) g x f i a b k y := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartGramOnE_symm (I := I) g x k j y]
  have h₂ : (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g x i k y *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g x a b y *
            chartDeTurckCorrectionHessBlockRaw (I := I) g x f j a b k y) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g x k i y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g x a b y *
              chartDeTurckCorrectionHessBlockRaw (I := I) g x f j a b k y := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartGramOnE_symm (I := I) g x i k y]
  rw [h₁, h₂]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTopRaw_symm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTopRaw_symm target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lieTop_add_tail
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) :
    lieTopSum (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s +
        lieTopTailSum (I := I) g₀ T T' hδ hδ' x v w s =
      lieTopCovSum (I := I) g₀ T T' hδ hδ' x v w s := by
  classical
  unfold lieTopSum lieTopTailSum lieTopCovSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← mul_add]
  rw [← lieTop_cov_eq_principalSymbolExprRaw_add_tail (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
    (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x i k]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTop_add_tail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTop_add_tail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTop_add_tail ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTop_add_tail

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lieTop_add_swap
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) :
    lieTopSum (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s +
        lieTopTailSwap (I := I) g₀ T T' hδ hδ' x v w s =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckLieSecondOrderPrincipalCoeff (I := I) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (![v, w] j)) := by
  classical
  unfold lieTopSum lieTopTailSwap
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
          unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 4 2
              (deTurckLieSecondOrderPrincipalCoeff (I := I) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
              (iteratedCovGrad (I := I) g₀ 0 2 2
                (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
            ![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i] := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← mul_add]
      rw [lieTopRaw_symm (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i k
        (extChartAt I x x)]
      rw [← lieTop_cov_eq_principalSymbolExprRaw_add_tail (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x k i]
    _ = _ := by
      simpa using unitModel_basis_expand_two (I := I) (M := M) g₀
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckLieSecondOrderPrincipalCoeff (I := I) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (![v, w] j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTop_add_swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTop_add_swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTop_add_swap ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieTop_add_swap


def lieOneSum
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      lieDeTurckOrder1Raw (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x)
        i k (extChartAt I x x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieOneSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieOneSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieOneSum ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieOneSum


def lieZeroSum
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      order0PartRaw (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x)
        i k (extChartAt I x x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieZeroSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieZeroSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieZeroSum ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieZeroSum

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lieSum_eq_split
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) :
    lieSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      lieTopSum (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s +
      lieOneSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s +
      lieZeroSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  have hy : extChartAt I x x ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  unfold lieSumSlope lieTopSum lieOneSum lieZeroSum
  simp_rw [lieDeTurckChartSlope_eq_orderSplit (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' g_bg x _ _ s hy]
  simp only [mul_add, Finset.sum_add_distrib]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieSum_eq_split then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieSum_eq_split"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieSum_eq_split ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieSum_eq_split

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem ricciSum_eq_lin
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ _root_.Set.Ioo (0 : ℝ) 1) :
    (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
        (∑ j : Fin (Module.finrank ℝ E),
          deriv (fun t : ℝ => chartRiemannTensor (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) x i j k j
              (extChartAt I x x)) s)) =
      linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  have hderiv := (hasDerivAt_realizedRicciChartSum (I := I)
    g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w hs).deriv
  calc
    _ = deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) s := hderiv.symm
    _ = linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s :=
      (linearizedRicciAt_eq_deriv_chartSum_on_Ioo (I := I)
        g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w hs).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.ricciSum_eq_lin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.ricciSum_eq_lin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.ricciSum_eq_lin ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.ricciSum_eq_lin

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem rhsSlope_eq_lin
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ _root_.Set.Ioo (0 : ℝ) 1) :
    rhsSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      (-2 : ℝ) * linearizedRicciAt (I := I) g₀ T T'
        hδ_lt hδ hδ'_lt hδ' x v w s +
      lieSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  rw [rhsSumSlope, lieSumSlope]
  simp only [rhsPathSlope, mul_add, Finset.sum_add_distrib]
  have hscale : (∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
            ((-2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
              deriv (fun t : ℝ => chartRiemannTensor (I := I)
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) x i j k j
                  (extChartAt I x x)) s)) =
      (-2 : ℝ) *
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
              ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
              (∑ j : Fin (Module.finrank ℝ E),
                deriv (fun t : ℝ => chartRiemannTensor (I := I)
                  (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) x i j k j
                    (extChartAt I x x)) s)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [hscale, ricciSum_eq_lin (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w hs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSlope_eq_lin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSlope_eq_lin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSlope_eq_lin ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSlope_eq_lin

omit [SigmaCompactSpace M] in
theorem rhsSumSlope_eq_covariantJet_expansion [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ _root_.Set.Ioo (0 : ℝ) 1) :
    rhsSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (linearizedRicciOrderZeroBaseCoeff (I := I) g₀ T T' hδ hδ' s +
              (linearizedRicciConnectionDifferenceOrder0Coeff (I := I) g₀ T T' hδ hδ' s -
                linearizedRicciOrderZeroBaseCoeff (I := I) g₀ T T' hδ hδ' s))
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
          operatorFieldApply (I := I) (M := M) g₀ 3 2
            (linearizedRicciFirstOrderBaseCoeff (I := I) g₀ T T' hδ hδ' s +
              (linearizedRicciConnectionDifferenceOrder1Coeff (I := I) g₀ T T' hδ hδ' s -
                linearizedRicciFirstOrderBaseCoeff (I := I) g₀ T T' hδ hδ' s))
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
          operatorFieldApply (I := I) (M := M) g₀ 4 2
            (linearizedRicciSecondOrderFieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
        (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (![v, w] j)) +
      lieTopSum (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s +
      lieOneSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s +
      lieZeroSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  rw [rhsSlope_eq_lin (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w hs]
  have hRic := linearizedRicciAt_eq_covariantJet_connectionDifferenceCoeff (I := I) g₀ T T'
    hTsymm hT'symm hδ_lt hδ hδ'_lt hδ' s hs x ![v, w]
  have hRic' : linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      x v w s = unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (linearizedRicciOrderZeroBaseCoeff (I := I) g₀ T T' hδ hδ' s +
              (linearizedRicciConnectionDifferenceOrder0Coeff (I := I) g₀ T T' hδ hδ' s -
                linearizedRicciOrderZeroBaseCoeff (I := I) g₀ T T' hδ hδ' s))
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
          operatorFieldApply (I := I) (M := M) g₀ 3 2
            (linearizedRicciFirstOrderBaseCoeff (I := I) g₀ T T' hδ hδ' s +
              (linearizedRicciConnectionDifferenceOrder1Coeff (I := I) g₀ T T' hδ hδ' s -
                linearizedRicciFirstOrderBaseCoeff (I := I) g₀ T T' hδ hδ' s))
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
          operatorFieldApply (I := I) (M := M) g₀ 4 2
            (linearizedRicciSecondOrderFieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
        (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (![v, w] j)) := by
    simpa using hRic
  rw [hRic']
  rw [lieSum_eq_split (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSumSlope_eq_covariantJet_expansion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSumSlope_eq_covariantJet_expansion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSumSlope_eq_covariantJet_expansion ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSumSlope_eq_covariantJet_expansion

def rhsTopTerm
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  unitModel (I := I) (M := M) g₀ 2
    (operatorFieldApply (I := I) (M := M) g₀ 4 2
      (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
    (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (![v, w] j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsTopTerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsTopTerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsTopTerm ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsTopTerm

def rhsLowTerm
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (linearizedRicciOrderZeroBaseCoeff (I := I) g₀ T T' hδ hδ' s +
            (linearizedRicciConnectionDifferenceOrder0Coeff (I := I) g₀ T T' hδ hδ' s -
              linearizedRicciOrderZeroBaseCoeff (I := I) g₀ T T' hδ hδ' s))
          (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
        operatorFieldApply (I := I) (M := M) g₀ 3 2
          (linearizedRicciFirstOrderBaseCoeff (I := I) g₀ T T' hδ hδ' s +
            (linearizedRicciConnectionDifferenceOrder1Coeff (I := I) g₀ T T' hδ hδ' s -
              linearizedRicciFirstOrderBaseCoeff (I := I) g₀ T T' hδ hδ' s))
          (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x
      (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (![v, w] j)) +
    lieOneSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s +
    lieZeroSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s -
    lieTopTailSwap (I := I) g₀ T T' hδ hδ' x v w s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsLowTerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsLowTerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsLowTerm ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsLowTerm

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem rhsTopTerm_eq_principal_lie_expansion
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) :
    rhsTopTerm (I := I) g₀ T T' hδ hδ' x v w s =
      (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (linearizedRicciSecondOrderFieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
        (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (![v, w] j)) +
      lieTopSum (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s +
      lieTopTailSwap (I := I) g₀ T T' hδ hδ' x v w s := by
  have hSsymm : ∀ (y : M) (u z : TangentSpace I y),
      smoothCcTensorBilinForm (I := I) g₀ (T - T') y u z =
        smoothCcTensorBilinForm (I := I) g₀ (T - T') y z u := by
    intro y u z
    rw [ccBilin_sub (I := I) (M := M) g₀ T T' y u z,
      ccBilin_sub (I := I) (M := M) g₀ T T' y z u,
      hTsymm y u z, hT'symm y u z]
  have hccTensor02Symm : ccTensor02Symm (I := I) (M := M) g₀ (T - T') = T - T' :=
    ccTensor02Symm_eq_self (I := I) (M := M) g₀ (T - T') hSsymm
  have hLie := lieTop_add_swap (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x v w s
  rw [hccTensor02Symm] at hLie
  unfold rhsTopTerm
  rw [deTurckMetricPrincipalDefectTotal_metricPerturbationPath_eq (I := I) (M := M) g₀ T T' hδ hδ' s,
    operatorFieldApplication_sub_left, operatorFieldApplication_add_left, unitModel_sub_app, unitModel_add_app,
    ← hLie]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsTopTerm_eq_principal_lie_expansion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsTopTerm_eq_principal_lie_expansion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsTopTerm_eq_principal_lie_expansion ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsTopTerm_eq_principal_lie_expansion

omit [SigmaCompactSpace M] in
theorem rhsSlope_eq_split [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ _root_.Set.Ioo (0 : ℝ) 1) :
    rhsSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      rhsTopTerm (I := I) g₀ T T' hδ hδ' x v w s +
        rhsLowTerm (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  rw [rhsSumSlope_eq_covariantJet_expansion (I := I) g₀ g_bg T T' hTsymm hT'symm
    hδ_lt hδ hδ'_lt hδ' x v w hs]
  rw [rhsTopTerm_eq_principal_lie_expansion (I := I) g₀ T T' hTsymm hT'symm
    hδ_lt hδ hδ'_lt hδ' x v w s]
  unfold rhsLowTerm
  rw [unitModel_add_app, unitModel_add_app]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSlope_eq_split then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSlope_eq_split"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSlope_eq_split ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSlope_eq_split

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem rhsSum_contDiffAt [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ}
    (hs : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :
    ContDiffAt ℝ ∞ (rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) s := by
  have hy : extChartAt I x x ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  have heq : rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w =
      (fun t : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
          DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
            (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) x i k (extChartAt I x x)) := by
    funext t
    unfold rhsChartSum
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [chartFComponentOnE_deTurckRicciRHS_eq (I := I) g_bg
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) x i k hy]
  rw [heq]
  exact realizedDeTurckRicciChartSum_contDiffAt (I := I)
    g₀ g_bg T T' hδ hδ' x v w hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSum_contDiffAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSum_contDiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSum_contDiffAt ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSum_contDiffAt

omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem hasDerivAt_rhsSum
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ}
    (hs : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :
    HasDerivAt (rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w)
      (rhsSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s) s := by
  have hy : extChartAt I x x ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  unfold rhsChartSum rhsSumSlope
  refine HasDerivAt.fun_sum (fun i _ => ?_)
  refine HasDerivAt.fun_sum (fun k _ => ?_)
  exact (hasDerivAt_rhsPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
    g_bg x i k hy hs).const_mul _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.hasDerivAt_rhsSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.hasDerivAt_rhsSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.hasDerivAt_rhsSum ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.hasDerivAt_rhsSum


omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem deriv_rhsSum
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ _root_.Set.Ioo (0 : ℝ) 1) :
    deriv (rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) s =
      rhsSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  exact (hasDerivAt_rhsSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
    x v w (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt ⟨hs.1.le, hs.2.le⟩)).deriv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.deriv_rhsSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.deriv_rhsSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.deriv_rhsSum ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.deriv_rhsSum


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem rhsSum_continuous [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) (_root_.Set.Icc (0 : ℝ) 1) := by
  intro s hs
  exact (rhsSum_contDiffAt (I := I) g₀ g_bg T T' hδ hδ'
    x v w (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt hs)).continuousAt.continuousWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSum_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSum_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSum_continuous ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSum_continuous

omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem rhsSlope_integrable [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    IntervalIntegrable
      (rhsSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w)
      volume 0 1 := by
  let f : ℝ → ℝ := rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w
  have hcd : ContDiffOn ℝ ∞ f (metricPerturbationPathDomain (δ := δ) (δ' := δ')) :=
    fun s hs => (rhsSum_contDiffAt (I := I) g₀ g_bg T T' hδ hδ'
      x v w hs).contDiffWithinAt
  have hcont : ContinuousOn (deriv f) (_root_.Set.Icc (0 : ℝ) 1) :=
    (hcd.continuousOn_deriv_of_isOpen metricPerturbationPathDomain_isOpen
      (by exact_mod_cast le_top)).mono
        (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt)
  have hint : IntervalIntegrable (deriv f) _root_.MeasureTheory.MeasureSpace.volume 0 1 :=
    hcont.intervalIntegrable_of_Icc zero_le_one
  refine hint.congr_ae ?_
  have hsub : _root_.Set.Ioo (0 : ℝ) 1 ⊆
      {s | deriv f s = rhsSumSlope (I := I) g₀ g_bg T T'
        hδ_lt hδ hδ'_lt hδ' x v w s} := by
    intro s hs
    exact deriv_rhsSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w hs
  have hnull : (volume.restrict (_root_.Set.uIoc (0 : ℝ) 1)) (_root_.Set.Ioo (0 : ℝ) 1)ᶜ = 0 := by
    rw [_root_.Set.uIoc_of_le zero_le_one]
    rw [Measure.restrict_apply (measurableSet_Ioo.compl)]
    have hsub1 : (_root_.Set.Ioo (0 : ℝ) 1)ᶜ ∩ _root_.Set.Ioc 0 1 ⊆ {1} := by
      intro s hs
      obtain ⟨hsc, hs0, hs1⟩ := hs
      rw [_root_.Set.mem_compl_iff, _root_.Set.mem_Ioo, not_and_or, not_lt, not_lt] at hsc
      rcases hsc with h | h
      · exact absurd hs0 (not_lt.mpr h)
      · exact (le_antisymm hs1 h) ▸ rfl
    exact _root_.MeasureTheory.measure_mono_null hsub1 (by simp)
  refine _root_.MeasureTheory.measure_mono_null (fun s hs => ?_) hnull
  exact fun hs' => hs (hsub hs')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSlope_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSlope_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSlope_integrable ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSlope_integrable

omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem rhsSum_sub_eq_int [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w 1 -
        rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w 0 =
      ∫ s in (0 : ℝ)..1,
        rhsSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  have hcont := rhsSum_continuous (I := I) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' x v w
  have hderiv : ∀ s ∈ _root_.Set.Ioo (0 : ℝ) 1,
      HasDerivAt (rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w)
        (rhsSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s) s := by
    intro s hs
    exact hasDerivAt_rhsSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      x v w (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt ⟨hs.1.le, hs.2.le⟩)
  have hint := rhsSlope_integrable (I := I) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' x v w
  exact (_root_.intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSum_sub_eq_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSum_sub_eq_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSum_sub_eq_int ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.rhsSum_sub_eq_int

end DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
