import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.SmoothRepresentative.ChartComponentExistence
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.SmoothRepresentative.Approximation
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorChartFrameSection
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorL2ChartComponentExt
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.PouComponentBound.PouCutoffComponentBridge
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.TensorChartTransition
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.TensorChartTransitionTransport
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.ChartTransitionTransportCLM

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

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

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma toEuclidean_extChartAt_mem_chartTargetEuclid
    (α : M) {x : M} (hx : x ∈ (chartAt H α).source) :
    (toEuclidean (E := E)) (extChartAt I α x) ∈
      chartTargetEuclid (I := I) (M := M) α := by
  refine ⟨extChartAt I α x, ?_, rfl⟩
  exact (extChartAt I α).map_source
    (by rw [extChartAt_source (I := I)]; exact hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toEuclidean_extChartAt_mem_chartTargetEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toEuclidean_extChartAt_mem_chartTargetEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toEuclidean_extChartAt_mem_chartTargetEuclid ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toEuclidean_extChartAt_mem_chartTargetEuclid

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma symm_toEuclidean_symm_toEuclidean_extChartAt
    (α : M) {x : M} (hx : x ∈ (chartAt H α).source) :
    (extChartAt I α).symm
        ((toEuclidean (E := E)).symm
          ((toEuclidean (E := E)) (extChartAt I α x))) = x := by
  rw [(toEuclidean (E := E)).symm_apply_apply]
  exact (extChartAt I α).left_inv
    (by rw [extChartAt_source (I := I)]; exact hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symm_toEuclidean_symm_toEuclidean_extChartAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symm_toEuclidean_symm_toEuclidean_extChartAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symm_toEuclidean_symm_toEuclidean_extChartAt ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symm_toEuclidean_symm_toEuclidean_extChartAt

section MainResults

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

def chosenComp (α : M) (P : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  Classical.choose
    (exists_smooth_eigenvectorChartComponent_representative
      (I := I) (M := M) g r s i α P)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenComp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenComp

omit [CompleteSpace E] in
private lemma chosenComp_contDiffOn
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞ (chosenComp (I := I) (M := M) g r s i α P)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (Classical.choose_spec
    (exists_smooth_eigenvectorChartComponent_representative
      (I := I) (M := M) g r s i α P)).1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenComp_contDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenComp_contDiffOn target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma chosenComp_hasCompactSupport
    (α : M) (P : TensorCompIdx (E := E) r s) :
    HasCompactSupport (chosenComp (I := I) (M := M) g r s i α P) :=
  (Classical.choose_spec
    (exists_smooth_eigenvectorChartComponent_representative
      (I := I) (M := M) g r s i α P)).2.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenComp_hasCompactSupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenComp_hasCompactSupport target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma chosenComp_tsupport (α : M) (P : TensorCompIdx (E := E) r s) :
    tsupport (chosenComp (I := I) (M := M) g r s i α P) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  (Classical.choose_spec
    (exists_smooth_eigenvectorChartComponent_representative
      (I := I) (M := M) g r s i α P)).2.2.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenComp_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenComp_tsupport target :: scope.openDecls } }

omit [CompleteSpace E] in
lemma chosenComp_ae_eq (α : M) (P : TensorCompIdx (E := E) r s) :
    chosenComp (I := I) (M := M) g r s i α P
      =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartComponentFun (I := I) (M := M) g r s i α P :=
  (Classical.choose_spec
    (exists_smooth_eigenvectorChartComponent_representative
      (I := I) (M := M) g r s i α P)).2.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenComp_ae_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenComp_ae_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenComp_ae_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenComp_ae_eq

omit [CompleteSpace E] in
private lemma chosenComp_hu (α : M) :
    ∀ P : TensorCompIdx (E := E) r s,
      ContDiffOn ℝ ∞ (chosenComp (I := I) (M := M) g r s i α P)
        (chartTargetEuclid (I := I) (M := M) α) :=
  fun P => chosenComp_contDiffOn (I := I) (M := M) g r s i α P

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenComp_hu
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenComp_hu target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma chosenComp_hsupp (α : M) :
    ∀ P : TensorCompIdx (E := E) r s,
      HasCompactSupport (chosenComp (I := I) (M := M) g r s i α P) ∧
        tsupport (chosenComp (I := I) (M := M) g r s i α P) ⊆
          chartTargetEuclid (I := I) (M := M) α :=
  fun P => ⟨chosenComp_hasCompactSupport (I := I) (M := M) g r s i α P,
    chosenComp_tsupport (I := I) (M := M) g r s i α P⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenComp_hsupp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenComp_hsupp target :: scope.openDecls } }

def eigenvectorSmoothChart (α : M) : SmoothCcTensor g r s :=
  tensorBundleSectionOfChartComponents (I := I) (M := M) g r s α
    (chosenComp (I := I) (M := M) g r s i α)
    (chosenComp_hu (I := I) (M := M) g r s i α)
    (chosenComp_hsupp (I := I) (M := M) g r s i α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmoothChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmoothChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmoothChart ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmoothChart

omit [CompleteSpace E] in
lemma tensorChartComponentRaw_eigenvectorSmoothChart_self
    (α : M) (P : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
        α P.1 P.2 ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      chosenComp (I := I) (M := M) g r s i α P y :=
  tensorChartComponentRaw_tensorBundleSectionOfChartComponents
    (I := I) (M := M) g r s α
    (chosenComp (I := I) (M := M) g r s i α)
    (chosenComp_hu (I := I) (M := M) g r s i α)
    (chosenComp_hsupp (I := I) (M := M) g r s i α) P hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_eigenvectorSmoothChart_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_eigenvectorSmoothChart_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_eigenvectorSmoothChart_self ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_eigenvectorSmoothChart_self

noncomputable def eigenvectorSmooth : SmoothCcTensor g r s :=
  ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
    eigenvectorSmoothChart (I := I) (M := M) g r s i α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth

omit [CompleteSpace E] in
lemma eigenvectorSmooth_eq :
    eigenvectorSmooth (I := I) (M := M) g r s i =
      ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        eigenvectorSmoothChart (I := I) (M := M) g r s i α := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_eq

omit [CompleteSpace E] in
private lemma eigenvectorSmoothChart_toSection_eq_zero_off_source
    (α : M) {x : M} (hx : x ∉ (chartAt H α).source) :
    (eigenvectorSmoothChart (I := I) (M := M) g r s i α).toSection x =
      0 :=
  tensorBundleSectionOfChartComponents_toSection_eq_zero_off_source
    (I := I) (M := M) g r s α
    (chosenComp (I := I) (M := M) g r s i α)
    (chosenComp_hu (I := I) (M := M) g r s i α)
    (chosenComp_hsupp (I := I) (M := M) g r s i α) hx

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmoothChart_toSection_eq_zero_off_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmoothChart_toSection_eq_zero_off_source target :: scope.openDecls } }

omit [CompleteSpace E] in
lemma tensorChartComponentRaw_eigenvectorSmoothChart_eq_zero_off_source
    (α β : M) (P : TensorCompIdx (E := E) r s) {x : M}
    (hx : x ∉ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
        β P.1 P.2 x = 0 := by
  rw [tensorChartComponentRaw_def]
  have hsec :
      (eigenvectorSmoothChart (I := I) (M := M) g r s i α).toSection x = 0 :=
    eigenvectorSmoothChart_toSection_eq_zero_off_source
      (I := I) (M := M) g r s i α hx
  rw [show tensorTrivProj (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s i α) β x =
      (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) β).continuousLinearMapAt ℝ x
        ((eigenvectorSmoothChart (I := I) (M := M) g r s i α).toSection x)
      from rfl, hsec, ContinuousLinearMap.map_zero, ContinuousLinearMap.map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_eigenvectorSmoothChart_eq_zero_off_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_eigenvectorSmoothChart_eq_zero_off_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_eigenvectorSmoothChart_eq_zero_off_source ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_eigenvectorSmoothChart_eq_zero_off_source

end MainResults

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
