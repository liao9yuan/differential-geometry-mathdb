import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.LoweringJetTower

import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.JetComparison.Tower
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.JetComparison.ReverseSecondDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

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
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

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

def morreyRSC (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (r s : ℕ) : ℝ :=
  let L₁ := _root_.Max.max (revJetOneC (E := E) Λ) Λ
  let L₂ := revJetTwoC (E := E) Λ
  morreyUniformConst Λ
    (baseMorreyConst (I := I) (M := M) gBase 0 (r + s))
    (kjetConst (Module.finrank ℝ E) Λ L₁ L₂ (r + s))
    (Module.finrank ℝ E) (r + s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.morreyRSC then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.morreyRSC"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.morreyRSC ``Submission.DifferentialGeometry.PDE.RicciFlow.morreyRSC

omit [BoundarylessManifold I M] in
lemma morreyRSC_nonneg (gBase : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (r s : ℕ) :
    0 ≤ morreyRSC (I := I) (M := M) gBase Λ r s := by
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ
  have hL₁ : 0 ≤ _root_.Max.max (revJetOneC (E := E) Λ) Λ :=
    hΛ0.trans (le_max_right _ _)
  have hL₂ : 0 ≤ revJetTwoC (E := E) Λ := by
    dsimp [revJetTwoC]
    exact le_max_left _ _
  unfold morreyRSC
  exact morreyUniformConst_nonneg hΛ0
    (baseMorreyConst_nonneg (I := I) (M := M) gBase 0 (r + s))
    (kjetConst_nonneg hΛ0 hL₁ hL₂ (Module.finrank ℝ E) (r + s))
    (Module.finrank ℝ E) (r + s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.morreyRSC_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.morreyRSC_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.morreyRSC_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.morreyRSC_nonneg

theorem morreyRS_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
        ∀ (S : SmoothCcTensor g r s) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g r s x
              (S.toSection x) ≤
            C ^ 2 * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g r s j S‖ ^ 2 := by
  refine ⟨morreyRSC (I := I) (M := M) gBase Λ r s,
    morreyRSC_nonneg (I := I) (M := M) gBase hΛ r s, ?_⟩
  intro g hEq hjet1 hjet2 S x
  let L₁ := _root_.Max.max (revJetOneC (E := E) Λ) Λ
  let L₂ := revJetTwoC (E := E) Λ
  obtain ⟨hL₁, hL₂, hfwd1, hrev1, hrev2⟩ :=
    reverseJetPack (I := I) gBase g hEq hjet1 hjet2
  have hwin : Module.finrank ℝ E / 2 + 2 = 3 := by omega
  have hcov := fibreMorrey_uniform_class (I := I) gBase g
    (Λ' := L₁) (Λ'' := L₂) hEq hfwd1 hrev1 hrev2 hL₁ hL₂ hwin
    (r + s) (lowerCc (I := I) (M := M) g r s S) x
  have hcov3 :
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + s) x
          ((lowerCc (I := I) (M := M) g r s S).toSection x) ≤
        morreyRSC (I := I) (M := M) gBase Λ r s ^ 2 *
          ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 (r + s) j
              (lowerCc (I := I) (M := M) g r s S)‖ ^ 2 := by
    simpa only [morreyRSC, L₁, L₂, hwin] using hcov
  calc
    riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + s) x
          ((lowerCc (I := I) (M := M) g r s S).toSection x) :=
      (lowerCc_riemannianFiberNormSq (I := I) (M := M) g r s S x).symm
    _ ≤ morreyRSC (I := I) (M := M) gBase Λ r s ^ 2 *
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 (r + s) j
            (lowerCc (I := I) (M := M) g r s S)‖ ^ 2 := hcov3
    _ = morreyRSC (I := I) (M := M) gBase Λ r s ^ 2 *
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s j S‖ ^ 2 := by
      apply congrArg (fun z : ℝ => morreyRSC (I := I) (M := M) gBase Λ r s ^ 2 * z)
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hj2 : j ≤ 2 := by
        have hj3 := Finset.mem_range.mp hj
        omega
      rw [lowerCc_jet_norm (I := I) (M := M) g r s j S hj2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.morreyRS_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.morreyRS_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.morreyRS_uniform ``Submission.DifferentialGeometry.PDE.RicciFlow.morreyRS_uniform

end RicciFlow
end PDE
end DifferentialGeometry

end
