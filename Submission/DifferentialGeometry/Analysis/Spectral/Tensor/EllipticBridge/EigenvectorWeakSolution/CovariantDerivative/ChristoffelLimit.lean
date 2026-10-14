import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.CoefficientLimits

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
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

omit [CompactSpace M] in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma covDerivLowerOrderTerm_pouSmul_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covDerivLowerOrderTerm (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α m Idx Jdx y =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
          tensorChartComponent (I := I) (M := M) g r s S α p.1 p.2 y := by
  classical
  rw [covDerivLowerOrderTerm_def]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou
    (I := I) (M := M) g r s α S p.1 p.2,
    tensorChartComponent_def,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (tensorChartComponentPou (I := I) (M := M) g r s S α p.1 p.2) hy]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivLowerOrderTerm_pouSmul_eqOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivLowerOrderTerm_pouSmul_eqOn target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem covDerivLowerOrderTerm_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    _root_.MeasureTheory.MemLp
      (covDerivLowerOrderTerm (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) α k P₀.1 P₀.2) 2
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  refine (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun p _ =>
      memLp_factor_mul_componentAtom (I := I) (M := M) g r s i α p n
        (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
          g r s α k P₀.1 p.1 P₀.2 p.2))).ae_eq ?_
  refine Filter.EventuallyEq.symm ?_
  rw [chartLebesgueMeasure]
  refine (_root_.MeasureTheory.ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  exact Filter.Eventually.of_forall (fun y hy =>
    covDerivLowerOrderTerm_pouSmul_eqOn (I := I) (M := M) g r s α
      (eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor k P₀.1 P₀.2 hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivLowerOrderTerm_pouSmul_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivLowerOrderTerm_pouSmul_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivLowerOrderTerm_pouSmul_memLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivLowerOrderTerm_pouSmul_memLp

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
noncomputable def covGradChristoffelLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    ∑ p : TensorCompIdx (E := E) r s,
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (covDerivLowerOrderCoeff (I := I) (M := M)
            g r s α k P₀.1 p.1 P₀.2 p.2) y *
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α p :
          EuclN → ℝ) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradChristoffelLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradChristoffelLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradChristoffelLimit ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradChristoffelLimit

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
theorem covGradChristoffelLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemLp (covGradChristoffelLimit (I := I) (M := M)
        g r s i α P₀ k) 2
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  unfold covGradChristoffelLimit
  exact _root_.MeasureTheory.memLp_finsetSum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
        g r s α k P₀.1 p.1 P₀.2 p.2)
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) α p))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradChristoffelLimit_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradChristoffelLimit_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradChristoffelLimit_memLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradChristoffelLimit_memLp

private noncomputable def covGradChristoffelUnscaledLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    ∑ p : TensorCompIdx (E := E) r s,
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (covDerivLowerOrderCoeff (I := I) (M := M)
            g r s α k P₀.1 p.1 P₀.2 p.2) y *
        (componentLpLimit (I := I) (M := M) g r s i α p :
          EuclN → ℝ) y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradChristoffelUnscaledLimit
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradChristoffelUnscaledLimit target :: scope.openDecls } }

omit [CompleteSpace E] in
private theorem covGradChristoffelUnscaledLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemLp (covGradChristoffelUnscaledLimit (I := I) (M := M)
        g r s i α P₀ k) 2
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  unfold covGradChristoffelUnscaledLimit
  exact _root_.MeasureTheory.memLp_finsetSum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
        g r s α k P₀.1 p.1 P₀.2 p.2)
      (componentLpLimit (I := I) (M := M) g r s i α p))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradChristoffelUnscaledLimit_memLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradChristoffelUnscaledLimit_memLp target :: scope.openDecls } }

omit [CompleteSpace E] in
private theorem covDerivLowerOrderTerm_pouSmul_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (covDerivLowerOrderTerm_pouSmul_memLp (I := I) (M := M)
        g r s i α P₀ k n).toLp _)
      _root_.Filter.atTop
      (𝓝 ((covGradChristoffelUnscaledLimit_memLp (I := I) (M := M)
        g r s i α P₀ k).toLp _)) := by
  classical
  have hf : ∀ (p : TensorCompIdx (E := E) r s) (n : ℕ),
      MemLp (fun y => covDerivLowerOrderCoeff (I := I) (M := M)
            g r s α k P₀.1 p.1 P₀.2 p.2 y *
          tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α p.1 p.2 y) 2
        (chartLebesgueMeasure (I := I) (M := M) α) := fun p n =>
    memLp_factor_mul_componentAtom (I := I) (M := M) g r s i α p n
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
        g r s α k P₀.1 p.1 P₀.2 p.2)
  have hflim : ∀ p : TensorCompIdx (E := E) r s,
      MemLp (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
            (covDerivLowerOrderCoeff (I := I) (M := M)
              g r s α k P₀.1 p.1 P₀.2 p.2) y *
          (componentLpLimit (I := I) (M := M) g r s i α p :
            EuclN → ℝ) y) 2
        (chartLebesgueMeasure (I := I) (M := M) α) := fun p =>
    memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
        g r s α k P₀.1 p.1 P₀.2 p.2)
      (componentLpLimit (I := I) (M := M) g r s i α p)
  have h_tendsto : ∀ p : TensorCompIdx (E := E) r s,
      Filter.Tendsto (fun n => (hf p n).toLp _) _root_.Filter.atTop
        (𝓝 ((hflim p).toLp _)) := fun p =>
    tendsto_componentSummand (I := I) (M := M) g r s i α p
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
        g r s α k P₀.1 p.1 P₀.2 p.2)
      (fun n => hf p n) (hflim p)
  have hFn_eq : ∀ n : ℕ,
      covDerivLowerOrderTerm (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) α k P₀.1 P₀.2
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
        fun y => ∑ p : TensorCompIdx (E := E) r s,
          covDerivLowerOrderCoeff (I := I) (M := M)
              g r s α k P₀.1 p.1 P₀.2 p.2 y *
            tensorChartComponent (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α p.1 p.2 y := by
    intro n
    rw [chartLebesgueMeasure]
    refine (_root_.MeasureTheory.ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    exact Filter.Eventually.of_forall (fun y hy =>
      covDerivLowerOrderTerm_pouSmul_eqOn (I := I) (M := M) g r s α
        (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor k P₀.1 P₀.2 hy)
  have hFlim_eq :
      covGradChristoffelUnscaledLimit (I := I) (M := M)
          g r s i α P₀ k
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
        fun y => ∑ p : TensorCompIdx (E := E) r s,
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (covDerivLowerOrderCoeff (I := I) (M := M)
                g r s α k P₀.1 p.1 P₀.2 p.2) y *
            (componentLpLimit (I := I) (M := M) g r s i α p :
              EuclN → ℝ) y :=
    Filter.EventuallyEq.rfl
  exact tendsto_toLp_finsetSum (I := I) (M := M) α Finset.univ
    hf hflim h_tendsto
    (fun n => covDerivLowerOrderTerm_pouSmul_memLp (I := I) (M := M)
      g r s i α P₀ k n)
    (covGradChristoffelUnscaledLimit_memLp (I := I) (M := M)
      g r s i α P₀ k)
    hFn_eq hFlim_eq

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivLowerOrderTerm_pouSmul_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivLowerOrderTerm_pouSmul_tendsto target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
private lemma smul_componentLpLimit_coeFn_ae
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (p : TensorCompIdx (E := E) r s) :
    (fun y : EuclN => (i.fst.val)⁻¹ *
        (componentLpLimit (I := I) (M := M) g r s i α p :
          EuclN → ℝ) y)
      =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      (fun y : EuclN =>
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α p :
          EuclN → ℝ) y) := by
  classical
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  have h_lp_eq :
      (i.fst.val)⁻¹ • componentLpLimit (I := I) (M := M)
          g r s i α p =
        tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α p := by
    rw [componentLpLimit, smul_smul, inv_mul_cancel₀ hμ_ne, one_smul]
  refine (Lp.coeFn_smul (i.fst.val)⁻¹
    (componentLpLimit (I := I) (M := M) g r s i α p)).symm.trans ?_
  exact Filter.EventuallyEq.of_eq
    (congrArg (fun z : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) =>
      (z : EuclN → ℝ)) h_lp_eq)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smul_componentLpLimit_coeFn_ae
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smul_componentLpLimit_coeFn_ae target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
private lemma smul_unscaledLimit_toLp_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    (i.fst.val)⁻¹ •
        (covGradChristoffelUnscaledLimit_memLp (I := I) (M := M)
          g r s i α P₀ k).toLp _ =
      (covGradChristoffelLimit_memLp (I := I) (M := M)
        g r s i α P₀ k).toLp _ := by
  classical
  apply Lp.ext
  refine (Lp.coeFn_smul (i.fst.val)⁻¹
    ((covGradChristoffelUnscaledLimit_memLp (I := I) (M := M)
      g r s i α P₀ k).toLp _)).trans ?_
  refine Filter.EventuallyEq.trans ?_
    (MemLp.coeFn_toLp (covGradChristoffelLimit_memLp (I := I) (M := M)
      g r s i α P₀ k)).symm
  have h_all : ∀ᵐ y ∂(chartLebesgueMeasure (I := I) (M := M) α),
      ∀ p : TensorCompIdx (E := E) r s,
        (i.fst.val)⁻¹ *
            (componentLpLimit (I := I) (M := M) g r s i α p :
              EuclN → ℝ) y =
          (tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) α p :
            EuclN → ℝ) y :=
    (_root_.MeasureTheory.ae_all_iff).mpr (fun p =>
      smul_componentLpLimit_coeFn_ae (I := I) (M := M)
        g r s i α p)
  filter_upwards [MemLp.coeFn_toLp (covGradChristoffelUnscaledLimit_memLp
    (I := I) (M := M) g r s i α P₀ k), h_all] with y hy hy_all
  rw [Pi.smul_apply, hy]
  rw [covGradChristoffelUnscaledLimit,
    covGradChristoffelLimit, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [mul_left_comm, hy_all p]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smul_unscaledLimit_toLp_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smul_unscaledLimit_toLp_eq target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem covGradChristoffel_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (i.fst.val)⁻¹ •
        ((covDerivLowerOrderTerm_pouSmul_memLp (I := I) (M := M)
          g r s i α P₀ k n).toLp
          (covDerivLowerOrderTerm (I := I) (M := M) g r s
            (pouSmul (I := I) (M := M) g r s α
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor) α k P₀.1 P₀.2) :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)))
      _root_.Filter.atTop
      (𝓝 ((covGradChristoffelLimit_memLp (I := I) (M := M)
        g r s i α P₀ k).toLp
        (covGradChristoffelLimit (I := I) (M := M)
          g r s i α P₀ k))) := by
  classical
  have h_smul :=
    (covDerivLowerOrderTerm_pouSmul_tendsto (I := I) (M := M)
      g r s i α P₀ k).const_smul (i.fst.val)⁻¹
  rwa [smul_unscaledLimit_toLp_eq (I := I) (M := M)
    g r s i α P₀ k] at h_smul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradChristoffel_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradChristoffel_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradChristoffel_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradChristoffel_tendsto

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
