import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorReprFromFrame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

structure TensorChartBilinearH1ComplData
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (_P₀ : TensorCompIdx (E := E) r s) where
  toChartData : ChartBilinearH1ComplData (I := I) (M := M) g α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData

namespace TensorChartBilinearH1ComplData

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

def uChart {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    EuclN → ℝ :=
  D.toChartData.uChart

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.uChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.uChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.uChart ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.uChart

def fChart {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    EuclN → ℝ :=
  D.toChartData.fChart

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.fChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.fChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.fChart ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.fChart

def weakPartial {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    Fin (Module.finrank ℝ E) → EuclN → ℝ :=
  D.toChartData.weakPartial

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.weakPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.weakPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.weakPartial ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.weakPartial

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma u_chart_eq {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    D.uChart = D.toChartData.uChart := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.u_chart_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.u_chart_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.u_chart_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.u_chart_eq

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma f_chart_eq {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    D.fChart = D.toChartData.fChart := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.f_chart_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.f_chart_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.f_chart_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.f_chart_eq

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma weak_partial_eq {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    D.weakPartial = D.toChartData.weakPartial := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.weak_partial_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.weak_partial_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.weak_partial_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.weak_partial_eq

omit [NeZero (Module.finrank ℝ E)] in
lemma u_chart_memLp_weighted {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    _root_.MeasureTheory.MemLp D.uChart 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  D.toChartData.u_chart_memLp_weighted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.u_chart_memLp_weighted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.u_chart_memLp_weighted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.u_chart_memLp_weighted ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.u_chart_memLp_weighted

omit [NeZero (Module.finrank ℝ E)] in
lemma f_chart_memLp_weighted {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    _root_.MeasureTheory.MemLp D.fChart 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  D.toChartData.f_chart_memLp_weighted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.f_chart_memLp_weighted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.f_chart_memLp_weighted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.f_chart_memLp_weighted ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.f_chart_memLp_weighted

omit [NeZero (Module.finrank ℝ E)] in
lemma weak_partial_locally_memLp {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {α : M} {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    (i : Fin (Module.finrank ℝ E)) {K : Set EuclN} (hK : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (D.weakPartial i) 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) :=
  D.toChartData.weak_partial_locally_memLp i K hK hK_in

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.weak_partial_locally_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.weak_partial_locally_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.weak_partial_locally_memLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.weak_partial_locally_memLp

omit [NeZero (Module.finrank ℝ E)] in
lemma weak_partial_isWeakPartial {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {α : M} {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (D.weakPartial i) D.uChart
      (chartTargetEuclid (I := I) (M := M) α) :=
  D.toChartData.weak_partial_isWeakPartial i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.weak_partial_isWeakPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.weak_partial_isWeakPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.weak_partial_isWeakPartial ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.weak_partial_isWeakPartial

omit [NeZero (Module.finrank ℝ E)] in
lemma variational_identity {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    (ψ : EuclN → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.uChart y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.fChart y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
  D.toChartData.variational_identity ψ hψ hψ_cs hψ_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.variational_identity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.variational_identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.variational_identity ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.variational_identity

omit [NeZero (Module.finrank ℝ E)] in
lemma memLp_volume_restrict_u_chart {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {α : M} {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp D.uChart 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) :=
  memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
    D.u_chart_memLp_weighted hK_compact hK_meas hK_in

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.memLp_volume_restrict_u_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.memLp_volume_restrict_u_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.memLp_volume_restrict_u_chart ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.memLp_volume_restrict_u_chart

omit [NeZero (Module.finrank ℝ E)] in
lemma memLp_volume_restrict_f_chart {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {α : M} {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp D.fChart 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) :=
  memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
    D.f_chart_memLp_weighted hK_compact hK_meas hK_in

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.memLp_volume_restrict_f_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.memLp_volume_restrict_f_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.memLp_volume_restrict_f_chart ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartBilinearH1ComplData.memLp_volume_restrict_f_chart

end TensorChartBilinearH1ComplData

omit [NeZero (Module.finrank ℝ E)] in
theorem tensor_chart_bilinear_identity_h1Compl
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.uChart y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.fChart y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
  D.variational_identity ψ hψ hψ_cs hψ_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensor_chart_bilinear_identity_h1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensor_chart_bilinear_identity_h1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensor_chart_bilinear_identity_h1Compl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensor_chart_bilinear_identity_h1Compl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
