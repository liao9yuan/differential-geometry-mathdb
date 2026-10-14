import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Local.Formula

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

lemma chartCoeff_pullback
    (α β : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M}
    (hα : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hβ : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) β).baseSet)
    (k : Fin (Module.finrank ℝ E)) :
    chartCoeff (I := I) α X k x =
      ∑ j, transitionMatrix (I := I) α β x k j *
        chartCoeff (I := I) β X j x := by
  classical
  have hβ_recompose := chartCoeff_recompose (I := I) β X hβ
  have hα_recompose := chartCoeff_recompose (I := I) α X hα
  have hbasis : ∀ j : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) β j x =
        ∑ k, transitionMatrix (I := I) α β x k j •
          DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x :=
    fun j => chartBasisVecFiber_pullback (I := I) α β hα hβ j
  have hexpand :
      X x = ∑ k : Fin (Module.finrank ℝ E),
              (∑ j, transitionMatrix (I := I) α β x k j *
                chartCoeff (I := I) β X j x) •
                DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x := by
    rw [hβ_recompose]
    simp_rw [hbasis]
    have hsmul_sum : ∀ j,
        chartCoeff (I := I) β X j x •
            ∑ k, transitionMatrix (I := I) α β x k j •
              DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x =
          ∑ k, (transitionMatrix (I := I) α β x k j *
                  chartCoeff (I := I) β X j x) •
            DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x := by
      intro j
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [smul_smul, mul_comm]
    simp_rw [hsmul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.sum_smul]
  have hli := DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_linearIndependent (I := I) α hα
  rw [Fintype.linearIndependent_iff] at hli
  set f : Fin (Module.finrank ℝ E) → ℝ := fun k =>
    chartCoeff (I := I) α X k x -
      ∑ j, transitionMatrix (I := I) α β x k j *
        chartCoeff (I := I) β X j x
  have hf : ∑ k, f k • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x = 0 := by
    simp only [f, sub_smul]
    rw [Finset.sum_sub_distrib]
    rw [← hα_recompose, ← hexpand, sub_self]
  have hf0 : f = 0 := funext (hli f hf)
  have := congrFun hf0 k
  simp only [f, Pi.zero_apply, sub_eq_zero] at this
  exact this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.chartCoeff_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.chartCoeff_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.chartCoeff_pullback ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.chartCoeff_pullback

end DivergenceTheorem
end Integral
end DifferentialGeometry
