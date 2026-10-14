import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.BilinearH1Compl
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev

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
namespace Laplacian
namespace DiffTwiceChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

def weightedInvGramSecondDerivOnEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (i j l₁ l₂ : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  (fderiv ℝ
      (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
    (EuclideanSpace.single l₂ 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weightedInvGramSecondDerivOnEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weightedInvGramSecondDerivOnEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weightedInvGramSecondDerivOnEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weightedInvGramSecondDerivOnEuclid

def densitySecondDerivOnEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  (fderiv ℝ (densityDerivOnEuclid (I := I) g α l₁) y)
    (EuclideanSpace.single l₂ 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.densitySecondDerivOnEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.densitySecondDerivOnEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.densitySecondDerivOnEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.densitySecondDerivOnEuclid

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedInvGramSecondDerivOnEuclid_contDiffOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l₁ l₂ : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_smooth :
      ContDiffOn ℝ ∞ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁)
        (chartTargetEuclid (I := I) (M := M) α) :=
    weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l₁
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_fderiv :
      ContDiffOn ℝ ∞ (fun y => fderiv ℝ
        (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_smooth).2
  have h_eval : ContDiff ℝ ∞
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single l₂ 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l₂ (1 : ℝ))).contDiff
  exact h_eval.contDiffOn.comp h_fderiv (_root_.Set.mapsTo_univ _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weightedInvGramSecondDerivOnEuclid_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weightedInvGramSecondDerivOnEuclid_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weightedInvGramSecondDerivOnEuclid_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weightedInvGramSecondDerivOnEuclid_contDiffOn

omit [NeZero (Module.finrank ℝ E)] in
lemma densitySecondDerivOnEuclid_contDiffOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (densitySecondDerivOnEuclid (I := I) g α l₁ l₂)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_smooth :
      ContDiffOn ℝ ∞ (densityDerivOnEuclid (I := I) g α l₁)
        (chartTargetEuclid (I := I) (M := M) α) :=
    densityDerivOnEuclid_contDiffOn (I := I) g α l₁
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_fderiv :
      ContDiffOn ℝ ∞ (fun y => fderiv ℝ
        (densityDerivOnEuclid (I := I) g α l₁) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_smooth).2
  have h_eval : ContDiff ℝ ∞
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single l₂ 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l₂ (1 : ℝ))).contDiff
  exact h_eval.contDiffOn.comp h_fderiv (_root_.Set.mapsTo_univ _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.densitySecondDerivOnEuclid_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.densitySecondDerivOnEuclid_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.densitySecondDerivOnEuclid_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.densitySecondDerivOnEuclid_contDiffOn

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedInvGramSecondDerivOnEuclid_continuousOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l₁ l₂ : Fin (Module.finrank ℝ E)) :
    ContinuousOn (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (weightedInvGramSecondDerivOnEuclid_contDiffOn (I := I) g α i j l₁ l₂).continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weightedInvGramSecondDerivOnEuclid_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weightedInvGramSecondDerivOnEuclid_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weightedInvGramSecondDerivOnEuclid_continuousOn ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weightedInvGramSecondDerivOnEuclid_continuousOn

omit [NeZero (Module.finrank ℝ E)] in
lemma densitySecondDerivOnEuclid_continuousOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E)) :
    ContinuousOn (densitySecondDerivOnEuclid (I := I) g α l₁ l₂)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (densitySecondDerivOnEuclid_contDiffOn (I := I) g α l₁ l₂).continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.densitySecondDerivOnEuclid_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.densitySecondDerivOnEuclid_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.densitySecondDerivOnEuclid_continuousOn ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.densitySecondDerivOnEuclid_continuousOn

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedInvGramSecondDerivOnEuclid_bounded_on_compact
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l₁ l₂ : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, ∀ y ∈ K,
      |weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_K_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have h_cont_K : ContinuousOn
      (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) K :=
    (weightedInvGramSecondDerivOnEuclid_continuousOn (I := I) g α i j l₁ l₂).mono hK_in
  have h_abs_K : ContinuousOn
      (fun y => |weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y|) K :=
    continuous_abs.comp_continuousOn h_cont_K
  obtain ⟨y_max, hy_max, h_max⟩ :=
    hK_compact.exists_isMaxOn h_K_ne h_abs_K
  refine ⟨|weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y_max|, ?_⟩
  intro y hy
  exact h_max hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weightedInvGramSecondDerivOnEuclid_bounded_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weightedInvGramSecondDerivOnEuclid_bounded_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weightedInvGramSecondDerivOnEuclid_bounded_on_compact ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weightedInvGramSecondDerivOnEuclid_bounded_on_compact

omit [NeZero (Module.finrank ℝ E)] in
lemma densitySecondDerivOnEuclid_bounded_on_compact
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, ∀ y ∈ K, |densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_K_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have h_cont_K : ContinuousOn (densitySecondDerivOnEuclid (I := I) g α l₁ l₂) K :=
    (densitySecondDerivOnEuclid_continuousOn (I := I) g α l₁ l₂).mono hK_in
  have h_abs_K : ContinuousOn
      (fun y => |densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y|) K :=
    continuous_abs.comp_continuousOn h_cont_K
  obtain ⟨y_max, hy_max, h_max⟩ :=
    hK_compact.exists_isMaxOn h_K_ne h_abs_K
  refine ⟨|densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y_max|, ?_⟩
  intro y hy
  exact h_max hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.densitySecondDerivOnEuclid_bounded_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.densitySecondDerivOnEuclid_bounded_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.densitySecondDerivOnEuclid_bounded_on_compact ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.densitySecondDerivOnEuclid_bounded_on_compact

structure DiffTwiceChartBilinearH1ComplData
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) where
  base1 : DiffChartBilinearH1ComplData (I := I) (M := M) g α
  direction2 : Fin (Module.finrank ℝ E)
  uChartDeriv2 : EuclN → ℝ
  fChartDeriv2 : EuclN → ℝ
  uChartSecondDeriv : EuclN → ℝ
  weakPartialDeriv2 : Fin (Module.finrank ℝ E) → EuclN → ℝ
  weakPartialSecondDeriv : Fin (Module.finrank ℝ E) → EuclN → ℝ
  u_chart_deriv2_isWeakPartial :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction2
      uChartDeriv2 base1.uChartDeriv
      (chartTargetEuclid (I := I) (M := M) α)
  f_chart_deriv2_isWeakPartial :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction2
      fChartDeriv2 base1.fChartDeriv
      (chartTargetEuclid (I := I) (M := M) α)
  u_chart_second_deriv_isWeakPartial :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction2
      uChartSecondDeriv base1.uChartDeriv
      (chartTargetEuclid (I := I) (M := M) α)
  weak_partial_deriv2_isWeakPartial :
    ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction2
      (weakPartialDeriv2 i) (base1.weakPartialDeriv i)
      (chartTargetEuclid (I := I) (M := M) α)
  weak_partial_second_deriv_isWeakPartial :
    ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction2
      (weakPartialSecondDeriv i) (base1.weakPartialDeriv i)
      (chartTargetEuclid (I := I) (M := M) α)
  u_chart_deriv2_locally_memLp :
    ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      _root_.MeasureTheory.MemLp uChartDeriv2 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K)
  f_chart_deriv2_locally_memLp :
    ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      _root_.MeasureTheory.MemLp fChartDeriv2 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K)
  u_chart_second_deriv_locally_memLp :
    ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      _root_.MeasureTheory.MemLp uChartSecondDeriv 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K)
  weak_partial_deriv2_locally_memLp :
    ∀ i, ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      _root_.MeasureTheory.MemLp (weakPartialDeriv2 i) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K)
  weak_partial_second_deriv_locally_memLp :
    ∀ i, ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      _root_.MeasureTheory.MemLp (weakPartialSecondDeriv i) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K)
  twice_differentiated_variational_identity :
    ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              weakPartialSecondDeriv i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * uChartSecondDeriv y * ψ y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * fChartDeriv2 y * ψ y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α i j direction2 y *
              weakPartialDeriv2 i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityDerivOnEuclid (I := I) g α direction2 y *
          uChartDeriv2 y * ψ y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityDerivOnEuclid (I := I) g α direction2 y *
          fChartDeriv2 y * ψ y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α i j base1.direction y *
              weakPartialDeriv2 i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramSecondDerivOnEuclid (I := I) g α i j
                base1.direction direction2 y *
              base1.base.weakPartial i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densitySecondDerivOnEuclid (I := I) g α
            base1.direction direction2 y *
          base1.base.uChart y * ψ y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityDerivOnEuclid (I := I) g α base1.direction y *
          base1.base.weakPartial direction2 y * ψ y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densitySecondDerivOnEuclid (I := I) g α
            base1.direction direction2 y *
          base1.base.fChart y * ψ y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityDerivOnEuclid (I := I) g α base1.direction y *
          fChartDeriv2 y * ψ y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.DiffTwiceChartBilinearH1ComplData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.DiffTwiceChartBilinearH1ComplData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.DiffTwiceChartBilinearH1ComplData ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.DiffTwiceChartBilinearH1ComplData

omit [NeZero (Module.finrank ℝ E)] in
theorem twice_differentiated_chart_bilinear_identity
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartialSecondDeriv i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.uChartSecondDeriv y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.fChartDeriv2 y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j D.direction2 y *
            D.weakPartialDeriv2 i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.direction2 y *
        D.uChartDeriv2 y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.direction2 y *
        D.fChartDeriv2 y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j D.base1.direction y *
            D.weakPartialDeriv2 i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramSecondDerivOnEuclid (I := I) g α i j
              D.base1.direction D.direction2 y *
            D.base1.base.weakPartial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densitySecondDerivOnEuclid (I := I) g α
          D.base1.direction D.direction2 y *
        D.base1.base.uChart y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.base1.direction y *
        D.base1.base.weakPartial D.direction2 y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densitySecondDerivOnEuclid (I := I) g α
          D.base1.direction D.direction2 y *
        D.base1.base.fChart y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.base1.direction y *
        D.fChartDeriv2 y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) :=
  D.twice_differentiated_variational_identity ψ hψ hψ_cs hψ_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.twice_differentiated_chart_bilinear_identity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.twice_differentiated_chart_bilinear_identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.twice_differentiated_chart_bilinear_identity ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.twice_differentiated_chart_bilinear_identity

omit [NeZero (Module.finrank ℝ E)] in
theorem differentiated_chart_bilinear_identity_of_twice_differentiated
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.base1.weakPartialDeriv i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.base1.uChartDeriv y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.base1.fChartDeriv y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j D.base1.direction y *
            D.base1.base.weakPartial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.base1.direction y *
        D.base1.base.uChart y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.base1.direction y *
        D.base1.base.fChart y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) :=
  D.base1.differentiated_variational_identity ψ hψ hψ_cs hψ_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.differentiated_chart_bilinear_identity_of_twice_differentiated then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.differentiated_chart_bilinear_identity_of_twice_differentiated"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.differentiated_chart_bilinear_identity_of_twice_differentiated ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.differentiated_chart_bilinear_identity_of_twice_differentiated

omit [NeZero (Module.finrank ℝ E)] in
theorem base_chart_bilinear_identity_of_twice_differentiated
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.base1.base.weakPartial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.base1.base.uChart y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.base1.base.fChart y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
  D.base1.base.variational_identity ψ hψ hψ_cs hψ_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.base_chart_bilinear_identity_of_twice_differentiated then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.base_chart_bilinear_identity_of_twice_differentiated"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.base_chart_bilinear_identity_of_twice_differentiated ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.base_chart_bilinear_identity_of_twice_differentiated

omit [NeZero (Module.finrank ℝ E)] in
theorem u_chart_second_deriv_isMixedWeakPartial
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) D.direction2
      D.uChartSecondDeriv D.base1.uChartDeriv
      (chartTargetEuclid (I := I) (M := M) α) ∧
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) D.base1.direction
      D.base1.uChartDeriv D.base1.base.uChart
      (chartTargetEuclid (I := I) (M := M) α) :=
  ⟨D.u_chart_second_deriv_isWeakPartial,
   D.base1.u_chart_deriv_isWeakPartial⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.u_chart_second_deriv_isMixedWeakPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.u_chart_second_deriv_isMixedWeakPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.u_chart_second_deriv_isMixedWeakPartial ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.u_chart_second_deriv_isMixedWeakPartial

omit [NeZero (Module.finrank ℝ E)] in
theorem weak_partial_second_deriv_isMixedWeakPartial
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) D.direction2
      (D.weakPartialSecondDeriv i) (D.base1.weakPartialDeriv i)
      (chartTargetEuclid (I := I) (M := M) α) ∧
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) D.base1.direction
      (D.base1.weakPartialDeriv i) (D.base1.base.weakPartial i)
      (chartTargetEuclid (I := I) (M := M) α) :=
  ⟨D.weak_partial_second_deriv_isWeakPartial i,
   D.base1.weak_partial_deriv_isWeakPartial i⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weak_partial_second_deriv_isMixedWeakPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weak_partial_second_deriv_isMixedWeakPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weak_partial_second_deriv_isMixedWeakPartial ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.weak_partial_second_deriv_isMixedWeakPartial

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def chosenSecondPartialUChartDeriv
    {g : SmoothRiemannianMetric I M} {α : M}
    (D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    (l₂ : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
    (d := Module.finrank ℝ E) 2 l₂ D₁.uChartDeriv
    (chartTargetEuclid (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialUChartDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialUChartDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialUChartDeriv ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialUChartDeriv

noncomputable def chosenSecondPartialFChartDeriv
    {g : SmoothRiemannianMetric I M} {α : M}
    (D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    (l₂ : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
    (d := Module.finrank ℝ E) 2 l₂ D₁.fChartDeriv
    (chartTargetEuclid (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialFChartDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialFChartDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialFChartDeriv ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialFChartDeriv

noncomputable def chosenSecondPartialWeakPartialDeriv
    {g : SmoothRiemannianMetric I M} {α : M}
    (D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    (i l₂ : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
    (d := Module.finrank ℝ E) 2 l₂ (D₁.weakPartialDeriv i)
    (chartTargetEuclid (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialWeakPartialDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialWeakPartialDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialWeakPartialDeriv ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialWeakPartialDeriv

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenSecondPartialUChartDeriv_isWeakPartial
    {g : SmoothRiemannianMetric I M} {α : M}
    {D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α}
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D₁.uChartDeriv (chartTargetEuclid (I := I) (M := M) α))
    (l₂ : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂
      (chosenSecondPartialUChartDeriv (I := I) (M := M) D₁ l₂)
      D₁.uChartDeriv
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold chosenSecondPartialUChartDeriv
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero_isWeakPartial_of_mem
    h_memW1p l₂

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialUChartDeriv_isWeakPartial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialUChartDeriv_isWeakPartial target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenSecondPartialFChartDeriv_isWeakPartial
    {g : SmoothRiemannianMetric I M} {α : M}
    {D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α}
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D₁.fChartDeriv (chartTargetEuclid (I := I) (M := M) α))
    (l₂ : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂
      (chosenSecondPartialFChartDeriv (I := I) (M := M) D₁ l₂)
      D₁.fChartDeriv
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold chosenSecondPartialFChartDeriv
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero_isWeakPartial_of_mem
    h_memW1p l₂

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialFChartDeriv_isWeakPartial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialFChartDeriv_isWeakPartial target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenSecondPartialWeakPartialDeriv_isWeakPartial
    {g : SmoothRiemannianMetric I M} {α : M}
    {D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α}
    {i : Fin (Module.finrank ℝ E)}
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (D₁.weakPartialDeriv i) (chartTargetEuclid (I := I) (M := M) α))
    (l₂ : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂
      (chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂)
      (D₁.weakPartialDeriv i)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold chosenSecondPartialWeakPartialDeriv
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero_isWeakPartial_of_mem
    h_memW1p l₂

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialWeakPartialDeriv_isWeakPartial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialWeakPartialDeriv_isWeakPartial target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenSecondPartialUChartDeriv_memLp
    {g : SmoothRiemannianMetric I M} {α : M}
    {D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α}
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D₁.uChartDeriv (chartTargetEuclid (I := I) (M := M) α))
    (l₂ : Fin (Module.finrank ℝ E)) :
    MemLp (chosenSecondPartialUChartDeriv (I := I) (M := M) D₁ l₂) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold chosenSecondPartialUChartDeriv
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
    h_memW1p l₂

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialUChartDeriv_memLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialUChartDeriv_memLp target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenSecondPartialFChartDeriv_memLp
    {g : SmoothRiemannianMetric I M} {α : M}
    {D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α}
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D₁.fChartDeriv (chartTargetEuclid (I := I) (M := M) α))
    (l₂ : Fin (Module.finrank ℝ E)) :
    MemLp (chosenSecondPartialFChartDeriv (I := I) (M := M) D₁ l₂) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold chosenSecondPartialFChartDeriv
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
    h_memW1p l₂

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialFChartDeriv_memLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialFChartDeriv_memLp target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenSecondPartialWeakPartialDeriv_memLp
    {g : SmoothRiemannianMetric I M} {α : M}
    {D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α}
    {i : Fin (Module.finrank ℝ E)}
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (D₁.weakPartialDeriv i) (chartTargetEuclid (I := I) (M := M) α))
    (l₂ : Fin (Module.finrank ℝ E)) :
    MemLp (chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold chosenSecondPartialWeakPartialDeriv
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
    h_memW1p l₂

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialWeakPartialDeriv_memLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.chosenSecondPartialWeakPartialDeriv_memLp target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma memLp_restrict_of_memLp_chartTarget
    (α : M)
    {f : EuclN → ℝ}
    (hf : _root_.MeasureTheory.MemLp f 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp f 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) := by
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_eq : ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)).restrict K =
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [← h_eq]
  exact hf.restrict K

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.memLp_restrict_of_memLp_chartTarget
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.memLp_restrict_of_memLp_chartTarget target :: scope.openDecls } }

noncomputable def diffTwiceChartBilinearH1ComplDataOfDiff
    {g : SmoothRiemannianMetric I M} {α : M}
    (D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    (l₂ : Fin (Module.finrank ℝ E))
    (h_uDeriv_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D₁.uChartDeriv (chartTargetEuclid (I := I) (M := M) α))
    (h_fDeriv_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D₁.fChartDeriv (chartTargetEuclid (I := I) (M := M) α))
    (h_wpDeriv_memW1p : ∀ i, DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (D₁.weakPartialDeriv i) (chartTargetEuclid (I := I) (M := M) α))
    (h_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chosenSecondPartialUChartDeriv (I := I) (M := M) D₁ l₂) y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chosenSecondPartialFChartDeriv (I := I) (M := M) D₁ l₂) y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                (chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₂ y *
            (chosenSecondPartialUChartDeriv (I := I) (M := M) D₁ l₂) y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₂ y *
            (chosenSecondPartialFChartDeriv (I := I) (M := M) D₁ l₂) y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j D₁.direction y *
                (chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramSecondDerivOnEuclid (I := I) g α i j
                  D₁.direction l₂ y *
                D₁.base.weakPartial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densitySecondDerivOnEuclid (I := I) g α
              D₁.direction l₂ y *
            D₁.base.uChart y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α D₁.direction y *
            D₁.base.weakPartial l₂ y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densitySecondDerivOnEuclid (I := I) g α
              D₁.direction l₂ y *
            D₁.base.fChart y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α D₁.direction y *
            (chosenSecondPartialFChartDeriv (I := I) (M := M) D₁ l₂) y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))) :
    DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α where
  base1 := D₁
  direction2 := l₂
  uChartDeriv2 := chosenSecondPartialUChartDeriv (I := I) (M := M) D₁ l₂
  fChartDeriv2 := chosenSecondPartialFChartDeriv (I := I) (M := M) D₁ l₂
  uChartSecondDeriv := chosenSecondPartialUChartDeriv (I := I) (M := M) D₁ l₂
  weakPartialDeriv2 := fun i =>
    chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂
  weakPartialSecondDeriv := fun i =>
    chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂
  u_chart_deriv2_isWeakPartial :=
    chosenSecondPartialUChartDeriv_isWeakPartial
      (I := I) (M := M) h_uDeriv_memW1p l₂
  f_chart_deriv2_isWeakPartial :=
    chosenSecondPartialFChartDeriv_isWeakPartial
      (I := I) (M := M) h_fDeriv_memW1p l₂
  u_chart_second_deriv_isWeakPartial :=
    chosenSecondPartialUChartDeriv_isWeakPartial
      (I := I) (M := M) h_uDeriv_memW1p l₂
  weak_partial_deriv2_isWeakPartial := fun i =>
    chosenSecondPartialWeakPartialDeriv_isWeakPartial
      (I := I) (M := M) (h_wpDeriv_memW1p i) l₂
  weak_partial_second_deriv_isWeakPartial := fun i =>
    chosenSecondPartialWeakPartialDeriv_isWeakPartial
      (I := I) (M := M) (h_wpDeriv_memW1p i) l₂
  u_chart_deriv2_locally_memLp := fun _K hK hKin =>
    memLp_restrict_of_memLp_chartTarget (I := I) (M := M) α
      (chosenSecondPartialUChartDeriv_memLp
        (I := I) (M := M) h_uDeriv_memW1p l₂) hK hKin
  f_chart_deriv2_locally_memLp := fun _K hK hKin =>
    memLp_restrict_of_memLp_chartTarget (I := I) (M := M) α
      (chosenSecondPartialFChartDeriv_memLp
        (I := I) (M := M) h_fDeriv_memW1p l₂) hK hKin
  u_chart_second_deriv_locally_memLp := fun _K hK hKin =>
    memLp_restrict_of_memLp_chartTarget (I := I) (M := M) α
      (chosenSecondPartialUChartDeriv_memLp
        (I := I) (M := M) h_uDeriv_memW1p l₂) hK hKin
  weak_partial_deriv2_locally_memLp := fun i _K hK hKin =>
    memLp_restrict_of_memLp_chartTarget (I := I) (M := M) α
      (chosenSecondPartialWeakPartialDeriv_memLp
        (I := I) (M := M) (h_wpDeriv_memW1p i) l₂) hK hKin
  weak_partial_second_deriv_locally_memLp := fun i _K hK hKin =>
    memLp_restrict_of_memLp_chartTarget (I := I) (M := M) α
      (chosenSecondPartialWeakPartialDeriv_memLp
        (I := I) (M := M) (h_wpDeriv_memW1p i) l₂) hK hKin
  twice_differentiated_variational_identity := h_identity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.diffTwiceChartBilinearH1ComplDataOfDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.diffTwiceChartBilinearH1ComplDataOfDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.diffTwiceChartBilinearH1ComplDataOfDiff ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.diffTwiceChartBilinearH1ComplDataOfDiff

noncomputable def diffTwiceChartBilinearH1ComplDataOfLaplacianDomainPowTwo
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (h_base_f_chart_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).fChart
      (chartTargetEuclid (I := I) (M := M) α))
    (h_once_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weakPartial l₁ y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1 hu_h)).weakPartial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₁ y *
            (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).uChart y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₁ y *
            (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).fChart y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)))
    (h_uDeriv_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
        (I := I) (M := M) g α hu_h l₁
        h_base_f_chart_memW1p h_once_identity).uChartDeriv
      (chartTargetEuclid (I := I) (M := M) α))
    (h_fDeriv_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
        (I := I) (M := M) g α hu_h l₁
        h_base_f_chart_memW1p h_once_identity).fChartDeriv
      (chartTargetEuclid (I := I) (M := M) α))
    (h_wpDeriv_memW1p : ∀ i,
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        ((diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
          (I := I) (M := M) g α hu_h l₁
          h_base_f_chart_memW1p h_once_identity).weakPartialDeriv i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_twice_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialWeakPartialDeriv (I := I) (M := M)
                  (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
                    (I := I) (M := M) g α hu_h l₁
                    h_base_f_chart_memW1p h_once_identity) i l₂) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chosenSecondPartialUChartDeriv (I := I) (M := M)
              (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity) l₂) y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chosenSecondPartialFChartDeriv (I := I) (M := M)
              (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity) l₂) y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                (chosenSecondPartialWeakPartialDeriv (I := I) (M := M)
                  (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
                    (I := I) (M := M) g α hu_h l₁
                    h_base_f_chart_memW1p h_once_identity) i l₂) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₂ y *
            (chosenSecondPartialUChartDeriv (I := I) (M := M)
              (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity) l₂) y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₂ y *
            (chosenSecondPartialFChartDeriv (I := I) (M := M)
              (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity) l₂) y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j
                  (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
                    (I := I) (M := M) g α hu_h l₁
                    h_base_f_chart_memW1p h_once_identity).direction y *
                (chosenSecondPartialWeakPartialDeriv (I := I) (M := M)
                  (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
                    (I := I) (M := M) g α hu_h l₁
                    h_base_f_chart_memW1p h_once_identity) i l₂) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramSecondDerivOnEuclid (I := I) g α i j
                  (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
                    (I := I) (M := M) g α hu_h l₁
                    h_base_f_chart_memW1p h_once_identity).direction l₂ y *
                (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
                  (I := I) (M := M) g α hu_h l₁
                  h_base_f_chart_memW1p h_once_identity).base.weakPartial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densitySecondDerivOnEuclid (I := I) g α
              (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity).direction l₂ y *
            (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
              (I := I) (M := M) g α hu_h l₁
              h_base_f_chart_memW1p h_once_identity).base.uChart y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α
              (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity).direction y *
            (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
              (I := I) (M := M) g α hu_h l₁
              h_base_f_chart_memW1p h_once_identity).base.weakPartial l₂ y *
            ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densitySecondDerivOnEuclid (I := I) g α
              (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity).direction l₂ y *
            (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
              (I := I) (M := M) g α hu_h l₁
              h_base_f_chart_memW1p h_once_identity).base.fChart y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α
              (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity).direction y *
            (chosenSecondPartialFChartDeriv (I := I) (M := M)
              (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity) l₂) y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))) :
    DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α :=
  diffTwiceChartBilinearH1ComplDataOfDiff (I := I) (M := M)
    (diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
      (I := I) (M := M) g α hu_h l₁
      h_base_f_chart_memW1p h_once_identity)
    l₂
    h_uDeriv_memW1p h_fDeriv_memW1p h_wpDeriv_memW1p
    h_twice_identity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.diffTwiceChartBilinearH1ComplDataOfLaplacianDomainPowTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.diffTwiceChartBilinearH1ComplDataOfLaplacianDomainPowTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.diffTwiceChartBilinearH1ComplDataOfLaplacianDomainPowTwo ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl.diffTwiceChartBilinearH1ComplDataOfLaplacianDomainPowTwo

end DiffTwiceChartBilinearH1Compl
end Laplacian
end Analysis
end DifferentialGeometry

end
