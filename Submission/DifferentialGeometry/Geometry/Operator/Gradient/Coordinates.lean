import Submission.DifferentialGeometry.Geometry.Operator.Gradient.NormSquared

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology
namespace DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem partialDeriv_eq_zero_of_not_mdifferentiableAt
    (α : M) {f : M → ℝ} {x : M}
    (hx : x ∈ (chartAt H α).source)
    (hf : ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (i : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) = 0 := by
  have hnf : ¬ DifferentiableAt ℝ (scalarOnE (I := I) α f) (extChartAt I α x) := by
    intro hd
    apply hf
    have hc := hd.mdifferentiableAt.comp x (mdifferentiableAt_extChartAt hx)
    apply hc.congr_of_eventuallyEq
    filter_upwards [(chartAt H α).open_source.mem_nhds hx] with y hy
    change f y = f ((extChartAt I α).symm (extChartAt I α y))
    rw [(extChartAt I α).left_inv (by simpa only [extChartAt_source_eq_chartAt_source] using hy)]
  simp only [partialDeriv, fderiv_zero_of_not_differentiableAt hnf, zero_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.partialDeriv_eq_zero_of_not_mdifferentiableAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.partialDeriv_eq_zero_of_not_mdifferentiableAt target :: scope.openDecls } }

theorem inner_gradFun_eq_chartInvGram_sum
    (g : SmoothRiemannianMetric I M) (α : M) (f h : M → ℝ) {x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hxint : extChartAt I α x ∈ interior (extChartAt I α).target) :
    g.inner x (gradFun g f x) (gradFun g h x) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x i j *
          partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) *
          partialDeriv (E := E) j (scalarOnE (I := I) α h) (extChartAt I α x) := by
  have hxchart : x ∈ (chartAt H α).source := by
    rwa [trivializationAt_baseSet_eq_chartAt_source (I := I)] at hx
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x
  · by_cases hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x
    · rw [inner_gradFun, ← gradChartLocal_eq_gradFun g α hh hx hxint]
      change (mfderiv I 𝓘(ℝ, ℝ) f x) (∑ i : Fin (Module.finrank ℝ E),
        gradChartCoeff g α h i x • chartBasisVecFiber α i x) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, mfderiv_chartBasisVecFiber_of_mdifferentiableAt α hf hxchart hxint i]
      change (∑ j, chartInvGramMatrix (I := I) g α x i j *
        partialDeriv (E := E) j (scalarOnE (I := I) α h) (extChartAt I α x)) * _ = _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · rw [gradFun_eq_zero_of_mfderiv_eq_zero g h (mfderiv_zero_of_not_mdifferentiableAt hh)]
      simp only [map_zero, partialDeriv_eq_zero_of_not_mdifferentiableAt α hxchart hh,
        _root_.MulZeroClass.mul_zero, Finset.sum_const_zero]
  · rw [gradFun_eq_zero_of_mfderiv_eq_zero g f (mfderiv_zero_of_not_mdifferentiableAt hf)]
    simp only [map_zero, zero_apply,
      partialDeriv_eq_zero_of_not_mdifferentiableAt α hxchart hf, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.zero_mul,
      Finset.sum_const_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.inner_gradFun_eq_chartInvGram_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.inner_gradFun_eq_chartInvGram_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.inner_gradFun_eq_chartInvGram_sum ``Submission.DifferentialGeometry.Geometry.Operator.inner_gradFun_eq_chartInvGram_sum
theorem normGradSqFun_eq_chartInvGram_sum
    (g : SmoothRiemannianMetric I M) (α : M) {f : M → ℝ} {x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hxint : extChartAt I α x ∈ interior (extChartAt I α).target) :
    normGradSqFun g f x =
      ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x k i *
          partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) *
          partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := by
  rw [normGradSqFun_def, inner_gradFun_eq_chartInvGram_sum g α f f hx hxint]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.normGradSqFun_eq_chartInvGram_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.normGradSqFun_eq_chartInvGram_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.normGradSqFun_eq_chartInvGram_sum ``Submission.DifferentialGeometry.Geometry.Operator.normGradSqFun_eq_chartInvGram_sum

theorem normGradSqFun_comp_extChartAt
    (g : SmoothRiemannianMetric I M) (α : M) {f : E → ℝ} {x : M}
    (hx : x ∈ (chartAt H α).source)
    (hxint : extChartAt I α x ∈ interior (extChartAt I α).target) :
    normGradSqFun g (f ∘ extChartAt I α) x =
      ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k i (extChartAt I α x) *
          fderiv ℝ f (extChartAt I α x) (chartModelBasis E i) *
          fderiv ℝ f (extChartAt I α x) (chartModelBasis E k) := by
  have hbase : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source (I := I)]
  have hxsrc : x ∈ (extChartAt I α).source := by
    rwa [extChartAt_source_eq_chartAt_source (I := I)]
  have heq : scalarOnE (I := I) α (f ∘ extChartAt I α) =ᶠ[𝓝 (extChartAt I α x)] f := by
    filter_upwards [isOpen_interior.mem_nhds hxint] with y hy
    change f (extChartAt I α ((extChartAt I α).symm y)) = f y
    rw [(extChartAt I α).right_inv (interior_subset hy)]
  rw [normGradSqFun_eq_chartInvGram_sum g α hbase hxint]
  simp only [partialDeriv, heq.fderiv_eq, chartInvGramOnE_def, (extChartAt I α).left_inv hxsrc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.normGradSqFun_comp_extChartAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.normGradSqFun_comp_extChartAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.normGradSqFun_comp_extChartAt ``Submission.DifferentialGeometry.Geometry.Operator.normGradSqFun_comp_extChartAt

end DifferentialGeometry.Geometry.Operator
