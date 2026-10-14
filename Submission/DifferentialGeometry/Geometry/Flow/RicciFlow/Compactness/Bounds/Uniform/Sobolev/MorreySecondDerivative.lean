import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.JetComparison.Tower

import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.JetComparison.ReverseSecondDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

noncomputable def morreyTwoC
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) : ℝ :=
  let L₁ := _root_.Max.max (revJetOneC (E := E) Λ) Λ
  let L₂ := revJetTwoC (E := E) Λ
  morreyUniformConst Λ
    (baseMorreyConst (I := I) (M := M) gBase 0 2)
    (kjetConst (Module.finrank ℝ E) Λ L₁ L₂ 2)
    (Module.finrank ℝ E) 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.morreyTwoC then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.morreyTwoC"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.morreyTwoC ``Submission.DifferentialGeometry.PDE.RicciFlow.morreyTwoC

theorem morreyTwoC_spec
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hdim : Module.finrank ℝ E / 2 + 2 = 3) :
    0 ≤ morreyTwoC (I := I) (M := M) gBase Λ ∧
      ∀ (g : SmoothRiemannianMetric I M),
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
        ∀ (T : SmoothCcTensor g 0 2) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
            morreyTwoC (I := I) (M := M) gBase Λ ^ 2 *
              ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := by
  have hC : 0 ≤ morreyTwoC (I := I) (M := M) gBase Λ := by
    dsimp only [morreyTwoC]
    exact morreyUniformConst_nonneg hΛ
      (baseMorreyConst_nonneg (I := I) (M := M) gBase 0 2)
      (kjetConst_nonneg hΛ
        (hΛ.trans (le_max_right _ _))
        (by
          dsimp [revJetTwoC]
          exact le_max_left _ _)
        (Module.finrank ℝ E) 2)
      (Module.finrank ℝ E) 2
  refine ⟨hC, ?_⟩
  intro g hEq hjet1 hjet2 T x
  obtain ⟨hL₁, hL₂, hfwd1, hrev1, hrev2⟩ :=
    reverseJetPack (I := I) gBase g hEq hjet1 hjet2
  have hmorrey := fibreMorrey_uniform_class (I := I) gBase g hEq
    hfwd1 hrev1 hrev2 hL₁ hL₂ hdim 2 T x
  simpa only [morreyTwoC] using hmorrey

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.morreyTwoC_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.morreyTwoC_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.morreyTwoC_spec ``Submission.DifferentialGeometry.PDE.RicciFlow.morreyTwoC_spec

end RicciFlow
end PDE
end DifferentialGeometry
