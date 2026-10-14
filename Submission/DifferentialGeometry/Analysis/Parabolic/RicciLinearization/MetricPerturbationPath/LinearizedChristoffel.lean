import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricPerturbationPath.ChartRicciDerivative
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.Variation.Christoffel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix _root_.Submission.Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

def realizedLinearizedChristoffelPrincipal (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j k : Fin (Module.finrank ℝ E)) (y : E) (s₀ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramOnE (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s₀) x k l y *
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l j) y +
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l i) y -
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j) y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedLinearizedChristoffelPrincipal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedLinearizedChristoffelPrincipal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedLinearizedChristoffelPrincipal ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedLinearizedChristoffelPrincipal

def realizedChristoffelNonPrincipal (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j k : Fin (Module.finrank ℝ E)) (y : E) (s₀ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s₀) x k p y *
          realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q y *
          chartInvGramOnE (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s₀) x q l y)) *
      chartChristoffelBracket (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s₀) x i j l y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedChristoffelNonPrincipal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedChristoffelNonPrincipal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedChristoffelNonPrincipal ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedChristoffelNonPrincipal

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem linearizedChristoffel_eq_principal_add_nonPrincipal
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :
    deriv (fun s : ℝ =>
        chartChristoffel (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x i j k y) s₀ =
      realizedLinearizedChristoffelPrincipal (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j k y s₀ +
        realizedChristoffelNonPrincipal (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j k y s₀ := by
  classical
  rw [(hasDerivAt_metricPerturbationPath_chartChristoffel
    (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j k hy hs₀).deriv]
  rw [realizedLinearizedChristoffelPrincipal, realizedChristoffelNonPrincipal]
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine congrArg (HMul.hMul (1 / 2 : ℝ)) (Finset.sum_congr rfl (fun l _ => ?_))
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.linearizedChristoffel_eq_principal_add_nonPrincipal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.linearizedChristoffel_eq_principal_add_nonPrincipal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.linearizedChristoffel_eq_principal_add_nonPrincipal ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.linearizedChristoffel_eq_principal_add_nonPrincipal

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem realizedLinearizedChristoffelPrincipal_eq_chartLinearizedPrincipal
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j k : Fin (Module.finrank ℝ E)) (y : E) (s₀ : ℝ)
    (h : ChartMetricPerturbation E)
    (hh : ∀ a b : Fin (Module.finrank ℝ E),
      Set.EqOn (h a b) (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b)
        (extChartAt I x).target)
    (hy : y ∈ (extChartAt I x).target) :
    realizedLinearizedChristoffelPrincipal (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j k y s₀ =
      chartLinearizedChristoffelPrincipal (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s₀) x h i j k y := by
  classical
  rw [realizedLinearizedChristoffelPrincipal, chartLinearizedChristoffelPrincipal_def]
  refine congrArg (HMul.hMul (1 / 2 : ℝ)) (Finset.sum_congr rfl (fun l _ => ?_))
  have hopen : IsOpen (extChartAt I x).target := isOpen_extChartAt_target x
  have hpd : ∀ a b c : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (h b c) y =
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b c)
          y := by
    intro a b c
    have hEv : (h b c) =ᶠ[nhds y]
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b c) :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hy) (hh b c)
    unfold DifferentialGeometry.Tensor.Coordinates.partialDeriv
    rw [hEv.fderiv_eq]
  rw [hpd i l j, hpd j l i, hpd l i j]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedLinearizedChristoffelPrincipal_eq_chartLinearizedPrincipal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedLinearizedChristoffelPrincipal_eq_chartLinearizedPrincipal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedLinearizedChristoffelPrincipal_eq_chartLinearizedPrincipal ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedLinearizedChristoffelPrincipal_eq_chartLinearizedPrincipal

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem realizedGramDeriv_self_eq_zero (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (α : M) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    realizedGramDeriv (I := I) g₀ T T hδ_lt hδ hδ_lt hδ α i j y = 0 := by
  rw [realizedGramDeriv, sub_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedGramDeriv_self_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedGramDeriv_self_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedGramDeriv_self_eq_zero ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedGramDeriv_self_eq_zero

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem realizedLinearizedChristoffelPrincipal_self_eq_zero
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) (i j k : Fin (Module.finrank ℝ E)) (y : E) (s₀ : ℝ) :
    realizedLinearizedChristoffelPrincipal (I := I) g₀ T T hδ_lt hδ hδ_lt hδ x i j k y s₀ = 0 := by
  classical
  rw [realizedLinearizedChristoffelPrincipal]
  have hzero : ∀ l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) (metricPerturbationPath (I := I) g₀ T T hδ hδ s₀) x k l y *
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
            (realizedGramDeriv (I := I) g₀ T T hδ_lt hδ hδ_lt hδ x l j) y +
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
            (realizedGramDeriv (I := I) g₀ T T hδ_lt hδ hδ_lt hδ x l i) y -
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l
            (realizedGramDeriv (I := I) g₀ T T hδ_lt hδ hδ_lt hδ x i j) y) = 0 := by
    intro l
    have h1 : (realizedGramDeriv (I := I) g₀ T T hδ_lt hδ hδ_lt hδ x l j) = fun _ : E
      => (0 : ℝ) := by
      funext z; exact realizedGramDeriv_self_eq_zero (I := I) g₀ T hδ_lt hδ x l j z
    have h2 : (realizedGramDeriv (I := I) g₀ T T hδ_lt hδ hδ_lt hδ x l i) = fun _ : E
      => (0 : ℝ) := by
      funext z; exact realizedGramDeriv_self_eq_zero (I := I) g₀ T hδ_lt hδ x l i z
    have h3 : (realizedGramDeriv (I := I) g₀ T T hδ_lt hδ hδ_lt hδ x i j) = fun _ : E
      => (0 : ℝ) := by
      funext z; exact realizedGramDeriv_self_eq_zero (I := I) g₀ T hδ_lt hδ x i j z
    rw [h1, h2, h3, partialDeriv_const, partialDeriv_const, partialDeriv_const]
    ring
  rw [Finset.sum_congr rfl (fun l _ => hzero l), Finset.sum_const_zero, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedLinearizedChristoffelPrincipal_self_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedLinearizedChristoffelPrincipal_self_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedLinearizedChristoffelPrincipal_self_eq_zero ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedLinearizedChristoffelPrincipal_self_eq_zero

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry

end
