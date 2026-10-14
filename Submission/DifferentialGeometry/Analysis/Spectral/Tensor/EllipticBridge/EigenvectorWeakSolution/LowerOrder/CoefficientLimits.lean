import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.WeakSolution.WeakSolutionGlobal
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.L2Approximation
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.PartitionOfUnityBridge
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.ChartAtomLimits

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix _root_.ENNReal _root_.NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
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

noncomputable def covPrincipalRotationCoeffLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
              (partialLpLimit (I := I) (M := M) g r s i α P k :
                EuclN → ℝ) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit

omit [CompleteSpace E] in
private lemma covPrincipalRotationCoeff_pouSmul_eq_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) (y : EuclN) :
    covPrincipalRotationCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) α P₀ y =
      ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l y *
                euclidPartial (E := E) k
                  (tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor α P.1 P.2) y := by
  classical
  rw [covPrincipalRotationCoeff_def]
  refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [chartPushedRaw_tensorChartComponentRaw_pouSmul_eq (I := I) (M := M)
    g r s α (eigenvectorSmoothApprox (I := I) (M := M)
      g r s i n).toCcTensor P.1 P.2]
  rw [principalRotationFactor]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeff_pouSmul_eq_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeff_pouSmul_eq_sum target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem covPrincipalRotationCoeff_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    _root_.MeasureTheory.MemLp
      (covPrincipalRotationCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) α P₀) 2
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  refine (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P _ => _root_.MeasureTheory.memLp_finsetSum
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q _ => _root_.MeasureTheory.memLp_finsetSum
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k _ => _root_.MeasureTheory.memLp_finsetSum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun l _ =>
            memLp_factor_mul_partialAtom (I := I) (M := M)
              g r s i α P k n
              (principalRotationFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ P Q k l)))))).ae_eq ?_
  exact Filter.EventuallyEq.symm (Filter.Eventually.of_forall (fun y =>
    covPrincipalRotationCoeff_pouSmul_eq_sum (I := I) (M := M)
      g r s i α P₀ n y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeff_pouSmul_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeff_pouSmul_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeff_pouSmul_memLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeff_pouSmul_memLp

omit [CompleteSpace E] in
theorem covPrincipalRotationCoeffLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s i α P₀) 2
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  unfold covPrincipalRotationCoeffLimit
  exact _root_.MeasureTheory.memLp_finsetSum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P _ => _root_.MeasureTheory.memLp_finsetSum
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q _ => _root_.MeasureTheory.memLp_finsetSum
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k _ => _root_.MeasureTheory.memLp_finsetSum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun l _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
            (principalRotationFactor_contDiffOn (I := I) (M := M)
              g r s α P₀ P Q k l)
            (partialLpLimit (I := I) (M := M) g r s i α P k)))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit_memLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit_memLp

omit [CompleteSpace E] in
theorem covPrincipalRotationCoeff_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => (covPrincipalRotationCoeff_pouSmul_memLp
        (I := I) (M := M) g r s i α P₀ n).toLp _)
      _root_.Filter.atTop
      (𝓝 ((covPrincipalRotationCoeffLimit_memLp (I := I) (M := M)
        g r s i α P₀).toLp _)) := by
  classical
  have hf : ∀ (a : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) (n : ℕ),
      MemLp (fun y => principalRotationFactor (I := I) (M := M)
            g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2 y *
          euclidPartial (E := E) a.2.2.1
            (tensorChartComponent (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α a.1.1 a.1.2) y) 2
        (chartLebesgueMeasure (I := I) (M := M) α) := fun a n =>
    memLp_factor_mul_partialAtom (I := I) (M := M) g r s i α a.1
      a.2.2.1 n (principalRotationFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2)
  have hflim : ∀ a : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      MemLp (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
            (principalRotationFactor (I := I) (M := M)
              g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2) y *
          (partialLpLimit (I := I) (M := M) g r s i α a.1 a.2.2.1 :
            EuclN → ℝ) y) 2
        (chartLebesgueMeasure (I := I) (M := M) α) := fun a =>
    memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (principalRotationFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2)
      (partialLpLimit (I := I) (M := M) g r s i α a.1 a.2.2.1)
  have h_tendsto : ∀ a : TensorCompIdx (E := E) r s ×
        TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      Filter.Tendsto (fun n => (hf a n).toLp _) _root_.Filter.atTop
        (𝓝 ((hflim a).toLp _)) := fun a =>
    tendsto_partialSummand (I := I) (M := M) g r s i α a.1 a.2.2.1
      (principalRotationFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2)
      (fun n => hf a n) (hflim a)
  have hFn_eq : ∀ n : ℕ,
      covPrincipalRotationCoeff (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) α P₀
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
        fun y => ∑ a : TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s ×
            Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          principalRotationFactor (I := I) (M := M)
              g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2 y *
            euclidPartial (E := E) a.2.2.1
              (tensorChartComponent (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n).toCcTensor α a.1.1 a.1.2) y := by
    intro n
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [covPrincipalRotationCoeff_pouSmul_eq_sum (I := I) (M := M)
      g r s i α P₀ n y]
    simp only [Fintype.sum_prod_type]
  have hFlim_eq :
      covPrincipalRotationCoeffLimit (I := I) (M := M) g r s i α P₀
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
        fun y => ∑ a : TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s ×
            Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (principalRotationFactor (I := I) (M := M)
                g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2) y *
            (partialLpLimit (I := I) (M := M)
              g r s i α a.1 a.2.2.1 : EuclN → ℝ) y := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [covPrincipalRotationCoeffLimit]
    simp only [Fintype.sum_prod_type]
  exact tendsto_toLp_finsetSum (I := I) (M := M) α Finset.univ
    hf hflim h_tendsto
    (fun n => covPrincipalRotationCoeff_pouSmul_memLp (I := I) (M := M)
      g r s i α P₀ n)
    (covPrincipalRotationCoeffLimit_memLp (I := I) (M := M)
      g r s i α P₀)
    hFn_eq hFlim_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeff_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeff_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeff_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeff_tendsto

noncomputable def weightedGradCoeffLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
              (componentLpLimit (I := I) (M := M) g r s i α p :
                EuclN → ℝ) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffLimit ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffLimit

omit [CompleteSpace E] in
private lemma weightedGradCoeff_pouSmul_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (n : ℕ)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    weightedGradCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) α P₀ l y =
      ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p y *
                tensorChartComponent (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor α p.1 p.2 y := by
  classical
  simp only [weightedGradCoeff, covLowerOrderRotationGradCoeff_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [covDerivLowerOrderTerm_pouSmul_eqOn_coeffFactors (I := I) (M := M) g r s α
    (eigenvectorSmoothApprox (I := I) (M := M)
      g r s i n).toCcTensor k P.1 P.2 hy]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [weightedGradFactor]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeff_pouSmul_eqOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeff_pouSmul_eqOn target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem weightedGradCoeff_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (n : ℕ) :
    _root_.MeasureTheory.MemLp
      (weightedGradCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) α P₀ l) 2
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  refine (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P _ => _root_.MeasureTheory.memLp_finsetSum
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q _ => _root_.MeasureTheory.memLp_finsetSum
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k _ => _root_.MeasureTheory.memLp_finsetSum
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun p _ =>
            memLp_factor_mul_componentAtom (I := I) (M := M)
              g r s i α p n
              (weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)))))).ae_eq ?_
  refine Filter.EventuallyEq.symm ?_
  rw [chartLebesgueMeasure]
  refine (_root_.MeasureTheory.ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  exact Filter.Eventually.of_forall (fun y hy =>
    weightedGradCoeff_pouSmul_eqOn (I := I) (M := M)
      g r s i α P₀ l n hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeff_pouSmul_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeff_pouSmul_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeff_pouSmul_memLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeff_pouSmul_memLp

omit [CompleteSpace E] in
theorem weightedGradCoeffLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    MemLp (weightedGradCoeffLimit (I := I) (M := M)
        g r s i α P₀ l) 2
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  unfold weightedGradCoeffLimit
  exact _root_.MeasureTheory.memLp_finsetSum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P _ => _root_.MeasureTheory.memLp_finsetSum
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q _ => _root_.MeasureTheory.memLp_finsetSum
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k _ => _root_.MeasureTheory.memLp_finsetSum
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
            (weightedGradFactor_contDiffOn (I := I) (M := M)
              g r s α P₀ l P Q k p)
            (componentLpLimit (I := I) (M := M) g r s i α p)))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffLimit_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffLimit_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffLimit_memLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffLimit_memLp

omit [CompleteSpace E] in
theorem weightedGradCoeff_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
        g r s i α P₀ l n).toLp _)
      _root_.Filter.atTop
      (𝓝 ((weightedGradCoeffLimit_memLp (I := I) (M := M)
        g r s i α P₀ l).toLp _)) := by
  classical
  have hf : ∀ (a : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) (n : ℕ),
      MemLp (fun y => weightedGradFactor (I := I) (M := M)
            g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2 y *
          tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α a.2.2.2.1 a.2.2.2.2 y) 2
        (chartLebesgueMeasure (I := I) (M := M) α) := fun a n =>
    memLp_factor_mul_componentAtom (I := I) (M := M) g r s i α
      a.2.2.2 n (weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2)
  have hflim : ∀ a : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      MemLp (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
            (weightedGradFactor (I := I) (M := M)
              g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2) y *
          (componentLpLimit (I := I) (M := M) g r s i α a.2.2.2 :
            EuclN → ℝ) y) 2
        (chartLebesgueMeasure (I := I) (M := M) α) := fun a =>
    memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2)
      (componentLpLimit (I := I) (M := M) g r s i α a.2.2.2)
  have h_tendsto : ∀ a : TensorCompIdx (E := E) r s ×
        TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      Filter.Tendsto (fun n => (hf a n).toLp _) _root_.Filter.atTop
        (𝓝 ((hflim a).toLp _)) := fun a =>
    tendsto_componentSummand (I := I) (M := M) g r s i α a.2.2.2
      (weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2)
      (fun n => hf a n) (hflim a)
  have hFn_eq : ∀ n : ℕ,
      weightedGradCoeff (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) α P₀ l
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
        fun y => ∑ a : TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s ×
            Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
          weightedGradFactor (I := I) (M := M)
              g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2 y *
            tensorChartComponent (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α a.2.2.2.1 a.2.2.2.2 y := by
    intro n
    rw [chartLebesgueMeasure]
    refine (_root_.MeasureTheory.ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [weightedGradCoeff_pouSmul_eqOn (I := I) (M := M)
      g r s i α P₀ l n hy]
    simp only [Fintype.sum_prod_type]
  have hFlim_eq :
      weightedGradCoeffLimit (I := I) (M := M) g r s i α P₀ l
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
        fun y => ∑ a : TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s ×
            Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (weightedGradFactor (I := I) (M := M)
                g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2) y *
            (componentLpLimit (I := I) (M := M)
              g r s i α a.2.2.2 : EuclN → ℝ) y := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [weightedGradCoeffLimit]
    simp only [Fintype.sum_prod_type]
  exact tendsto_toLp_finsetSum (I := I) (M := M) α Finset.univ
    hf hflim h_tendsto
    (fun n => weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
      g r s i α P₀ l n)
    (weightedGradCoeffLimit_memLp (I := I) (M := M) g r s i α P₀ l)
    hFn_eq hFlim_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeff_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeff_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeff_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeff_tendsto

noncomputable def weightedGradCoeffDivLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    (∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (euclidPartial (E := E) l
                    (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p))
                  y *
                (componentLpLimit (I := I) (M := M) g r s i α p :
                  EuclN → ℝ) y)
      + ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p)
                    y *
                  (partialLpLimit (I := I) (M := M) g r s i α p l :
                    EuclN → ℝ) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit

omit [CompleteSpace E] in
theorem euclidPartial_weightedGradCoeff_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (n : ℕ) :
    _root_.MeasureTheory.MemLp
      (euclidPartial (E := E) l
        (weightedGradCoeff (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) α P₀ l)) 2
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  have hcomp : _root_.MeasureTheory.MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              euclidPartial (E := E) l
                  (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
                tensorChartComponent (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor α p.1 p.2 y) 2
      (chartLebesgueMeasure (I := I) (M := M) α) :=
    memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => _root_.MeasureTheory.memLp_finsetSum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => _root_.MeasureTheory.memLp_finsetSum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => _root_.MeasureTheory.memLp_finsetSum
            (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p _ => memLp_factor_mul_componentAtom (I := I) (M := M)
              g r s i α p n
              (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)))))
  have hpart : _root_.MeasureTheory.MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p y *
                euclidPartial (E := E) l
                  (tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor α p.1 p.2) y) 2
      (chartLebesgueMeasure (I := I) (M := M) α) :=
    memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => _root_.MeasureTheory.memLp_finsetSum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => _root_.MeasureTheory.memLp_finsetSum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => _root_.MeasureTheory.memLp_finsetSum
            (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p _ => memLp_factor_mul_partialAtom (I := I) (M := M)
              g r s i α p l n
              (weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)))))
  refine (hcomp.add hpart).ae_eq ?_
  refine Filter.EventuallyEq.symm ?_
  rw [chartLebesgueMeasure]
  refine (_root_.MeasureTheory.ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  exact Filter.Eventually.of_forall (fun y hy =>
    euclidPartial_weightedGradCoeff_pouSmul_eqOn_section (I := I) (M := M)
      g r s α P₀ l
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
      hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_weightedGradCoeff_pouSmul_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_weightedGradCoeff_pouSmul_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_weightedGradCoeff_pouSmul_memLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_weightedGradCoeff_pouSmul_memLp

omit [CompleteSpace E] in
theorem weightedGradCoeffDivLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    MemLp (weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l) 2
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  unfold weightedGradCoeffDivLimit
  refine MemLp.add ?_ ?_
  · exact _root_.MeasureTheory.memLp_finsetSum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => _root_.MeasureTheory.memLp_finsetSum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => _root_.MeasureTheory.memLp_finsetSum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => _root_.MeasureTheory.memLp_finsetSum
            (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
              (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)
              (componentLpLimit (I := I) (M := M) g r s i α p)))))
  · exact _root_.MeasureTheory.memLp_finsetSum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => _root_.MeasureTheory.memLp_finsetSum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => _root_.MeasureTheory.memLp_finsetSum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => _root_.MeasureTheory.memLp_finsetSum
            (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
              (weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)
              (partialLpLimit (I := I) (M := M) g r s i α p l)))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit_memLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit_memLp

omit [CompleteSpace E] in
theorem weightedGradCoeffDiv_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (euclidPartial_weightedGradCoeff_pouSmul_memLp
        (I := I) (M := M) g r s i α P₀ l n).toLp _)
      _root_.Filter.atTop
      (𝓝 ((weightedGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s i α P₀ l).toLp _)) := by
  classical
  have h_comp := tendsto_sum4 (I := I) (M := M) α
    (f := fun P Q k p n y =>
      euclidPartial (E := E) l
          (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α p.1 p.2 y)
    (flim := fun P Q k p y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (euclidPartial (E := E) l
            (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p)) y *
        (componentLpLimit (I := I) (M := M) g r s i α p :
          EuclN → ℝ) y)
    (fun P Q k p n => memLp_factor_mul_componentAtom (I := I) (M := M)
      g r s i α p n
      (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l P Q k p))
    (fun P Q k p => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l P Q k p)
      (componentLpLimit (I := I) (M := M) g r s i α p))
    (fun P Q k p => tendsto_componentSummand (I := I) (M := M)
      g r s i α p
      (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l P Q k p)
      (fun n => memLp_factor_mul_componentAtom (I := I) (M := M)
        g r s i α p n
        (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l P Q k p))
      (memLp_indicatorFactor_mul_lp (I := I) (M := M) α
        (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l P Q k p)
        (componentLpLimit (I := I) (M := M) g r s i α p)))
  have h_part := tendsto_sum4 (I := I) (M := M) α
    (f := fun P Q k p n y =>
      weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p y *
        euclidPartial (E := E) l
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α p.1 p.2) y)
    (flim := fun P Q k p y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
        (partialLpLimit (I := I) (M := M) g r s i α p l :
          EuclN → ℝ) y)
    (fun P Q k p n => memLp_factor_mul_partialAtom (I := I) (M := M)
      g r s i α p l n
      (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p))
    (fun P Q k p => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)
      (partialLpLimit (I := I) (M := M) g r s i α p l))
    (fun P Q k p => tendsto_partialSummand (I := I) (M := M)
      g r s i α p l
      (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)
      (fun n => memLp_factor_mul_partialAtom (I := I) (M := M)
        g r s i α p l n
        (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p))
      (memLp_indicatorFactor_mul_lp (I := I) (M := M) α
        (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)
        (partialLpLimit (I := I) (M := M) g r s i α p l)))
  have h_add := h_comp.add h_part
  have h_termN : ∀ n : ℕ,
      (euclidPartial_weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
        g r s i α P₀ l n).toLp _ =
      (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
          Finset.univ (fun P _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
            (fun Q _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
              (fun k _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                (fun p _ => memLp_factor_mul_componentAtom
                  (I := I) (M := M) g r s i α p n
                  (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)))))).toLp _ +
        (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
          Finset.univ (fun P _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
            (fun Q _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
              (fun k _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                (fun p _ => memLp_factor_mul_partialAtom
                  (I := I) (M := M) g r s i α p l n
                  (weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)))))).toLp _ := by
    intro n
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    rw [chartLebesgueMeasure]
    refine (_root_.MeasureTheory.ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    exact Filter.Eventually.of_forall (fun y hy =>
      euclidPartial_weightedGradCoeff_pouSmul_eqOn_section (I := I) (M := M)
        g r s α P₀ l
        (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
        hy)
  have h_termLim :
      (weightedGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s i α P₀ l).toLp _ =
      (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
          Finset.univ (fun P _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
            (fun Q _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
              (fun k _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                  (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)
                  (componentLpLimit (I := I) (M := M)
                    g r s i α p)))))).toLp _ +
        (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
          Finset.univ (fun P _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
            (fun Q _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
              (fun k _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                  (weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)
                  (partialLpLimit (I := I) (M := M)
                    g r s i α p l)))))).toLp _ := by
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [weightedGradCoeffDivLimit]
  rw [show (fun n => (euclidPartial_weightedGradCoeff_pouSmul_memLp
        (I := I) (M := M) g r s i α P₀ l n).toLp _) =
      (fun n => (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
          Finset.univ (fun P _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
            (fun Q _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
              (fun k _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                (fun p _ => memLp_factor_mul_componentAtom
                  (I := I) (M := M) g r s i α p n
                  (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)))))).toLp _ +
        (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
          Finset.univ (fun P _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
            (fun Q _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
              (fun k _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                (fun p _ => memLp_factor_mul_partialAtom
                  (I := I) (M := M) g r s i α p l n
                  (weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)))))).toLp _)
      from funext h_termN, h_termLim]
  exact h_add

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDiv_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDiv_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDiv_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDiv_tendsto

omit [CompleteSpace E] in
theorem weightedGradCoeffDivSum_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => ∑ l : Fin (Module.finrank ℝ E),
        (euclidPartial_weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
          g r s i α P₀ l n).toLp _)
      _root_.Filter.atTop
      (𝓝 (∑ l : Fin (Module.finrank ℝ E),
        (weightedGradCoeffDivLimit_memLp (I := I) (M := M)
          g r s i α P₀ l).toLp _)) :=
  tendsto_finsetSum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun l _ => weightedGradCoeffDiv_tendsto (I := I) (M := M)
      g r s i α P₀ l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivSum_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivSum_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivSum_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivSum_tendsto

noncomputable def covLowerOrderRotationValueCoeffLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    (∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
                (partialLpLimit (I := I) (M := M) g r s i α P k :
                  EuclN → ℝ) y)
      + ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (valueComponentFactor (I := I) (M := M)
                        g r s α P₀ P Q k l p) y *
                    (componentLpLimit (I := I) (M := M)
                      g r s i α p : EuclN → ℝ) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit

omit [CompleteSpace E] in
theorem covLowerOrderRotationValueCoeff_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    _root_.MeasureTheory.MemLp
      (covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) α P₀) 2
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  have hpart : _root_.MeasureTheory.MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l y *
                euclidPartial (E := E) k
                  (tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor α P.1 P.2) y) 2
      (chartLebesgueMeasure (I := I) (M := M) α) :=
    memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => _root_.MeasureTheory.memLp_finsetSum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => _root_.MeasureTheory.memLp_finsetSum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => _root_.MeasureTheory.memLp_finsetSum
            (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l _ => memLp_factor_mul_partialAtom (I := I) (M := M)
              g r s i α P k n
              (valuePartialFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ P Q k l)))))
  have hcomp : _root_.MeasureTheory.MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p y *
                  tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor α p.1 p.2 y) 2
      (chartLebesgueMeasure (I := I) (M := M) α) :=
    memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => _root_.MeasureTheory.memLp_finsetSum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => _root_.MeasureTheory.memLp_finsetSum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => _root_.MeasureTheory.memLp_finsetSum
            (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l _ => _root_.MeasureTheory.memLp_finsetSum
              (Finset.univ : Finset (TensorCompIdx (E := E) r s))
              (fun p _ => memLp_factor_mul_componentAtom (I := I) (M := M)
                g r s i α p n
                (valueComponentFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ P Q k l p))))))
  refine (hpart.add hcomp).ae_eq ?_
  refine Filter.EventuallyEq.symm ?_
  rw [chartLebesgueMeasure]
  refine (_root_.MeasureTheory.ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  exact Filter.Eventually.of_forall (fun y hy =>
    covLowerOrderRotationValueCoeff_pouSmul_eqOn_section (I := I) (M := M)
      g r s α P₀
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
      hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeff_pouSmul_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeff_pouSmul_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeff_pouSmul_memLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeff_pouSmul_memLp

omit [CompleteSpace E] in
theorem covLowerOrderRotationValueCoeffLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s i α P₀) 2
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  unfold covLowerOrderRotationValueCoeffLimit
  refine MemLp.add ?_ ?_
  · exact _root_.MeasureTheory.memLp_finsetSum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => _root_.MeasureTheory.memLp_finsetSum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => _root_.MeasureTheory.memLp_finsetSum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => _root_.MeasureTheory.memLp_finsetSum
            (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
              (valuePartialFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ P Q k l)
              (partialLpLimit (I := I) (M := M) g r s i α P k)))))
  · exact _root_.MeasureTheory.memLp_finsetSum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => _root_.MeasureTheory.memLp_finsetSum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => _root_.MeasureTheory.memLp_finsetSum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => _root_.MeasureTheory.memLp_finsetSum
            (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l _ => _root_.MeasureTheory.memLp_finsetSum
              (Finset.univ : Finset (TensorCompIdx (E := E) r s))
              (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                (valueComponentFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ P Q k l p)
                (componentLpLimit (I := I) (M := M)
                  g r s i α p))))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit_memLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit_memLp

omit [CompleteSpace E] in
theorem covLowerOrderRotationValueCoeff_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => (covLowerOrderRotationValueCoeff_pouSmul_memLp
        (I := I) (M := M) g r s i α P₀ n).toLp _)
      _root_.Filter.atTop
      (𝓝 ((covLowerOrderRotationValueCoeffLimit_memLp (I := I) (M := M)
        g r s i α P₀).toLp _)) := by
  classical
  have h_part := tendsto_sum4 (I := I) (M := M) α
    (f := fun P Q k l n y =>
      valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l y *
        euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2) y)
    (flim := fun P Q k l y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
        (partialLpLimit (I := I) (M := M) g r s i α P k :
          EuclN → ℝ) y)
    (fun P Q k l n => memLp_factor_mul_partialAtom (I := I) (M := M)
      g r s i α P k n
      (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l))
    (fun P Q k l => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l)
      (partialLpLimit (I := I) (M := M) g r s i α P k))
    (fun P Q k l => tendsto_partialSummand (I := I) (M := M)
      g r s i α P k
      (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l)
      (fun n => memLp_factor_mul_partialAtom (I := I) (M := M)
        g r s i α P k n
        (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l))
      (memLp_indicatorFactor_mul_lp (I := I) (M := M) α
        (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l)
        (partialLpLimit (I := I) (M := M) g r s i α P k)))
  have h_comp := tendsto_sum5 (I := I) (M := M) α
    (f := fun P Q k l p n y =>
      valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p y *
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α p.1 p.2 y)
    (flim := fun P Q k l p y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p) y *
        (componentLpLimit (I := I) (M := M) g r s i α p :
          EuclN → ℝ) y)
    (fun P Q k l p n => memLp_factor_mul_componentAtom (I := I) (M := M)
      g r s i α p n
      (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p))
    (fun P Q k l p => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p)
      (componentLpLimit (I := I) (M := M) g r s i α p))
    (fun P Q k l p => tendsto_componentSummand (I := I) (M := M)
      g r s i α p
      (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p)
      (fun n => memLp_factor_mul_componentAtom (I := I) (M := M)
        g r s i α p n
        (valueComponentFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ P Q k l p))
      (memLp_indicatorFactor_mul_lp (I := I) (M := M) α
        (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p)
        (componentLpLimit (I := I) (M := M) g r s i α p)))
  have h_add := h_part.add h_comp
  have h_termN : ∀ n : ℕ,
      (covLowerOrderRotationValueCoeff_pouSmul_memLp (I := I) (M := M)
        g r s i α P₀ n).toLp _ =
      (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
          Finset.univ (fun P _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
            (fun Q _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
              (fun k _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                (fun l _ => memLp_factor_mul_partialAtom
                  (I := I) (M := M) g r s i α P k n
                  (valuePartialFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ P Q k l)))))).toLp _ +
        (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
          Finset.univ (fun P _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
            (fun Q _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
              (fun k _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                (fun l _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                  (fun p _ => memLp_factor_mul_componentAtom
                    (I := I) (M := M) g r s i α p n
                    (valueComponentFactor_contDiffOn (I := I) (M := M)
                      g r s α P₀ P Q k l p))))))).toLp _ := by
    intro n
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    rw [chartLebesgueMeasure]
    refine (_root_.MeasureTheory.ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    exact Filter.Eventually.of_forall (fun y hy =>
      covLowerOrderRotationValueCoeff_pouSmul_eqOn_section (I := I) (M := M)
        g r s α P₀
        (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
        hy)
  have h_termLim :
      (covLowerOrderRotationValueCoeffLimit_memLp (I := I) (M := M)
        g r s i α P₀).toLp _ =
      (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
          Finset.univ (fun P _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
            (fun Q _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
              (fun k _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                (fun l _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                  (valuePartialFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ P Q k l)
                  (partialLpLimit (I := I) (M := M)
                    g r s i α P k)))))).toLp _ +
        (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
          Finset.univ (fun P _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
            (fun Q _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
              (fun k _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                (fun l _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                  (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                    (valueComponentFactor_contDiffOn (I := I) (M := M)
                      g r s α P₀ P Q k l p)
                    (componentLpLimit (I := I) (M := M)
                      g r s i α p))))))).toLp _ := by
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [covLowerOrderRotationValueCoeffLimit]
  rw [show (fun n => (covLowerOrderRotationValueCoeff_pouSmul_memLp
        (I := I) (M := M) g r s i α P₀ n).toLp _) =
      (fun n => (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
          Finset.univ (fun P _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
            (fun Q _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
              (fun k _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                (fun l _ => memLp_factor_mul_partialAtom
                  (I := I) (M := M) g r s i α P k n
                  (valuePartialFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ P Q k l)))))).toLp _ +
        (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
          Finset.univ (fun P _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
            (fun Q _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
              (fun k _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                (fun l _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                  (fun p _ => memLp_factor_mul_componentAtom
                    (I := I) (M := M) g r s i α p n
                    (valueComponentFactor_contDiffOn (I := I) (M := M)
                      g r s α P₀ P Q k l p))))))).toLp _)
      from funext h_termN, h_termLim]
  exact h_add

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeff_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeff_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeff_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeff_tendsto

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
