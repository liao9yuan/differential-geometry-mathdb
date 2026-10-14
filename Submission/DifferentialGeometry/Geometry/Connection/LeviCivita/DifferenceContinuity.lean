import Submission.DifferentialGeometry.Geometry.Metric.Family.TensorNorm
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.DifferenceCoordinates
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Connection.Frame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Filter
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M]

private theorem connectionDifferenceLowAt_chart_tendsto_zero
    {T : Type*} {l : Filter T}
    (g₁ g₂ : T → SmoothRiemannianMetric I M)
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      Tendsto (fun t => chartGramMatrix (I := I) (g₁ t) x x i j) l
        (𝓝 (chartGramMatrix (I := I) g₀ x x i j)))
    (hconn₁ : ∀ i j k : Fin (Module.finrank ℝ E),
      Tendsto (fun t => chartChristoffel (I := I) (g₁ t) x i j k (extChartAt I x x)) l
        (𝓝 (chartChristoffel (I := I) g₀ x i j k (extChartAt I x x))))
    (hconn₂ : ∀ i j k : Fin (Module.finrank ℝ E),
      Tendsto (fun t => chartChristoffel (I := I) (g₂ t) x i j k (extChartAt I x x)) l
        (𝓝 (chartChristoffel (I := I) g₀ x i j k (extChartAt I x x))))
    (K : Fin 3 → Fin (Module.finrank ℝ E)) :
    Tendsto (fun t => connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x
      (fun a => chartBasisVecFiber (I := I) x (K a) x)) l (𝓝 0) := by
  have hterm (m : Fin (Module.finrank ℝ E)) :
      _root_.Filter.Tendsto (fun t =>
        (chartChristoffel (I := I) (g₁ t) x (K 0) (K 1) m (extChartAt I x x) -
          chartChristoffel (I := I) (g₂ t) x (K 0) (K 1) m (extChartAt I x x)) *
            chartGramMatrix (I := I) (g₁ t) x x m (K 2)) l (𝓝 0) := by
    simpa only [sub_self, _root_.MulZeroClass.zero_mul] using
      ((hconn₁ (K 0) (K 1) m).sub (hconn₂ (K 0) (K 1) m)).mul (hgram m (K 2))
  simpa only [connChartComp (g₁ _) (g₂ _) x K
      (self_mem_chartLeviCivitaGoodSet (I := I) (α := x)), Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun m _ => hterm m)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.connectionDifferenceLowAt_chart_tendsto_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.connectionDifferenceLowAt_chart_tendsto_zero target :: scope.openDecls } }

theorem tendsto_connectionDifferenceSq_zero_of_chartChristoffel
    {T : Type*} {l : Filter T}
    (g₁ g₂ : T → SmoothRiemannianMetric I M)
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      Tendsto (fun t => chartGramMatrix (I := I) (g₁ t) x x i j) l
        (𝓝 (chartGramMatrix (I := I) g₀ x x i j)))
    (hconn₁ : ∀ i j k : Fin (Module.finrank ℝ E),
      Tendsto (fun t => chartChristoffel (I := I) (g₁ t) x i j k (extChartAt I x x)) l
        (𝓝 (chartChristoffel (I := I) g₀ x i j k (extChartAt I x x))))
    (hconn₂ : ∀ i j k : Fin (Module.finrank ℝ E),
      Tendsto (fun t => chartChristoffel (I := I) (g₂ t) x i j k (extChartAt I x x)) l
        (𝓝 (chartChristoffel (I := I) g₀ x i j k (extChartAt I x x)))) :
    Tendsto (fun t => connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x) l (𝓝 0) := by
  exact DifferentialGeometry.Tensor0SBundle.tendsto_normSq0S_zero_of_chart_components
    g₁ g₀ x (fun t => connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x) hgram
    (connectionDifferenceLowAt_chart_tendsto_zero g₁ g₂ g₀ x hgram hconn₁ hconn₂)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.tendsto_connectionDifferenceSq_zero_of_chartChristoffel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.tendsto_connectionDifferenceSq_zero_of_chartChristoffel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.tendsto_connectionDifferenceSq_zero_of_chartChristoffel ``Submission.DifferentialGeometry.PDE.RicciFlow.tendsto_connectionDifferenceSq_zero_of_chartChristoffel

end DifferentialGeometry.PDE.RicciFlow

end

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private theorem leviCivita_difference_eq_sum
    (g g₀ : SmoothRiemannianMetric I M) (x : M)
    (u w : TangentSpace I x)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet) :
    CovariantDerivative.difference (LeviCivita (I := I) g) (LeviCivita (I := I) g₀) x u w =
      ∑ j, ∑ i,
        ((chartBasisFamily (I := I) x hx).repr u j *
          (chartBasisFamily (I := I) x hx).repr w i) •
          ∑ k, (chartChristoffel (I := I) g x i j k (extChartAt I x x) -
            chartChristoffel (I := I) g₀ x i j k (extChartAt I x x)) •
              chartBasisVecFiber (I := I) x k x := by
  classical
  let b := chartBasisFamily (I := I) x hx
  let A := CovariantDerivative.difference
    (LeviCivita (I := I) g) (LeviCivita (I := I) g₀) x
  have hchart (i j : Fin (Module.finrank ℝ E)) :
      A (b j) (b i) =
        ∑ k, (chartChristoffel (I := I) g x i j k (extChartAt I x x) -
          chartChristoffel (I := I) g₀ x i j k (extChartAt I x x)) •
            chartBasisVecFiber (I := I) x k x := by
    dsimp only [A, b]
    rw [chartBasisFamily_apply, chartBasisFamily_apply,
      christoffelSymbolDifference_expansion _ _ _ (chartBasisVecFiber_isLocalFrame x) hx]
    refine Finset.sum_congr rfl fun k _ => ?_
    apply congrArg (fun c : ℝ => c • chartBasisVecFiber (I := I) x k x)
    rw [christoffelSymbolDifferenceInFrame_eq_sub _ _ _ _ i j k
      (chartBasisVec_alpha_mdifferentiableAt (I := I) x j
        (self_mem_chartLeviCivitaGoodSet (I := I) (α := x))),
      christoffelSymbolInFrame_chartBasisVecFiber g x
        (self_mem_chartLeviCivitaGoodSet (I := I) (α := x)),
      christoffelSymbolInFrame_chartBasisVecFiber g₀ x
        (self_mem_chartLeviCivitaGoodSet (I := I) (α := x))]
  have hu : A u = ∑ j, b.repr u j • A (b j) := by
    conv_lhs => rw [← b.sum_repr u]
    simp only [map_sum, map_smul]
  have hw (j) : A (b j) w = ∑ i, b.repr w i • A (b j) (b i) := by
    conv_lhs => rw [← b.sum_repr w]
    simp only [map_sum, map_smul]
  change A u w = _
  rw [hu]
  simp only [sum_apply, smul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hw j, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, hchart]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.leviCivita_difference_eq_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.leviCivita_difference_eq_sum target :: scope.openDecls } }

theorem tendsto_leviCivita_difference_zero_of_chartChristoffel
    {T : Type*} {l : Filter T}
    (g : T → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (x : M)
    (hconn : ∀ i j k : Fin (Module.finrank ℝ E),
      Tendsto (fun t => chartChristoffel (I := I) (g t) x i j k (extChartAt I x x)) l
        (𝓝 (chartChristoffel (I := I) g₀ x i j k (extChartAt I x x))))
    (u w : TangentSpace I x) :
    _root_.Filter.Tendsto (fun t => CovariantDerivative.difference
      (LeviCivita (I := I) (g t)) (LeviCivita (I := I) g₀) x u w) l (𝓝 0) := by
  classical
  have hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet :=
    _root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  let b := chartBasisFamily (I := I) x hx
  have hsum (i j) : _root_.Filter.Tendsto (fun t =>
      ∑ k, (chartChristoffel (I := I) (g t) x i j k (extChartAt I x x) -
        chartChristoffel (I := I) g₀ x i j k (extChartAt I x x)) •
          chartBasisVecFiber (I := I) x k x) l (𝓝 0) := by
    simpa only [sub_self, zero_smul, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun k _ =>
        ((hconn i j k).sub (tendsto_const_nhds (x :=
          chartChristoffel (I := I) g₀ x i j k (extChartAt I x x)))).smul
          (tendsto_const_nhds (x := chartBasisVecFiber (I := I) x k x)))
  have h := tendsto_finsetSum Finset.univ fun j _ =>
    tendsto_finsetSum Finset.univ fun i _ =>
      (tendsto_const_nhds (x := b.repr u j * b.repr w i)).smul (hsum i j)
  simpa only [b, leviCivita_difference_eq_sum _ _ x u w hx,
    smul_zero, Finset.sum_const_zero] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tendsto_leviCivita_difference_zero_of_chartChristoffel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tendsto_leviCivita_difference_zero_of_chartChristoffel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tendsto_leviCivita_difference_zero_of_chartChristoffel ``Submission.DifferentialGeometry.Geometry.Connection.tendsto_leviCivita_difference_zero_of_chartChristoffel

theorem tendsto_leviCivita_difference_pairing_zero_of_chartChristoffel
    {T : Type*} {l : Filter T}
    (g : T → SmoothRiemannianMetric I M) (g₀ h : SmoothRiemannianMetric I M)
    (x : M)
    (hconn : ∀ i j k : Fin (Module.finrank ℝ E),
      Tendsto (fun t => chartChristoffel (I := I) (g t) x i j k (extChartAt I x x)) l
        (𝓝 (chartChristoffel (I := I) g₀ x i j k (extChartAt I x x))))
    (u w v : TangentSpace I x) :
    _root_.Filter.Tendsto (fun t => h.inner x (CovariantDerivative.difference
      (LeviCivita (I := I) (g t)) (LeviCivita (I := I) g₀) x u w) v) l (𝓝 0) := by
  have ht := tendsto_leviCivita_difference_zero_of_chartChristoffel g g₀ x hconn u w
  have hc : Continuous (fun z : TangentSpace I x => h.inner x z v) :=
    (h.inner x).continuous.clm_apply continuous_const
  simpa only [Function.comp_def, map_zero, zero_apply] using
    hc.continuousAt.tendsto.comp ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tendsto_leviCivita_difference_pairing_zero_of_chartChristoffel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tendsto_leviCivita_difference_pairing_zero_of_chartChristoffel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tendsto_leviCivita_difference_pairing_zero_of_chartChristoffel ``Submission.DifferentialGeometry.Geometry.Connection.tendsto_leviCivita_difference_pairing_zero_of_chartChristoffel

end DifferentialGeometry.Geometry.Connection

end
