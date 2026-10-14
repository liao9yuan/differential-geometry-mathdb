import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyPoissonPairing
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceRicciAlgebra
import Submission.DifferentialGeometry.Geometry.Curvature.Bochner.Scalar.CoordinateFormula
import Submission.DifferentialGeometry.Geometry.Coordinates.Frame.Chart
import Submission.DifferentialGeometry.Geometry.Operator.Hessian.Trace.Inequality
import Submission.DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators _root_.Matrix

private theorem surfaceSquares_fin_two_sum
    {Idx : Type*} [Fintype Idx] (G : (Fin 2 → Idx) → Real) :
    (∑ a : Fin 2 → Idx, G a) =
      ∑ i : Idx, ∑ j : Idx, G (fun a : Fin 2 => if a = 0 then i else j) := by
  classical
  let etof : (Fin 2 → Idx) → Idx × Idx := fun a => (a 0, a 1)
  let einv : Idx × Idx → (Fin 2 → Idx) :=
    fun p a => if a = 0 then p.1 else p.2
  let e : (Fin 2 → Idx) ≃ Idx × Idx :=
    { toFun := etof
      invFun := einv
      left_inv := by
        intro a
        funext k
        fin_cases k <;> simp [etof, einv]
      right_inv := by
        rintro ⟨i, j⟩
        simp [etof, einv] }
  rw [Fintype.sum_equiv e G (fun p : Idx × Idx =>
    G (fun a : Fin 2 => if a = 0 then p.1 else p.2))]
  · rw [Fintype.sum_prod_type]
  · intro a
    congr 1
    change a = fun k : Fin 2 => if k = 0 then (etof a).1 else (etof a).2
    funext k
    fin_cases k <;> simp [etof]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceSquares_fin_two_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceSquares_fin_two_sum target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [I.Boundaryless] [T2Space M]

local instance surfaceSquaresMeasurable : MeasurableSpace M := borel M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceSquaresMeasurable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceSquaresMeasurable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceSquaresMeasurable ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceSquaresMeasurable
local instance surfaceSquaresBorel : BorelSpace M := ⟨rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceSquaresBorel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceSquaresBorel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceSquaresBorel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceSquaresBorel

omit [CompleteSpace E] in
theorem surfaceEntropy_hessian_norm_eq_chart
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (x : M) :
    normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) =
      chartHessFrobeniusSq (I := I) g f x := by
  classical
  let hbase : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet :=
    _root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  let cbasis : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x) :=
    chartBasisFamily (I := I) x hbase
  let cgInv : Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real :=
    fun i j => chartInvGramMatrix (I := I) g x x i j
  have hcinv : MetricInverseInBasis (I := I) g x cbasis cgInv := by
    intro i j
    constructor
    · have hmatrix := congrArg (fun A => A i j)
        (chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hbase)
      simpa [Matrix.mul_apply, Matrix.one_apply, cbasis, cgInv,
        chartBasisFamily_apply] using hmatrix
    · have hmatrix := congrArg (fun A => A i j)
        (chartGramMatrix_mul_chartInvGramMatrix (I := I) g x hbase)
      simpa [Matrix.mul_apply, Matrix.one_apply, cbasis, cgInv,
        chartBasisFamily_apply] using hmatrix
  have hcb : ∀ i : Fin (Module.finrank Real E),
      cbasis i = centeredChartTangentBasis (I := I) x i := by
    intro i
    have hb : cbasis i = chartBasisVecFiber (I := I) x i x :=
      chartBasisFamily_apply (I := I) x hbase i
    rw [hb]
    exact chartBasisVecFiber_self (I := I) x i
  have hvec : ∀ i j : Fin (Module.finrank Real E),
      (fun a : Fin 2 => cbasis (if a = 0 then i else j)) = vec2 (cbasis i) (cbasis j) := by
    intro i j
    funext a
    fin_cases a <;> simp [vec2]
  have hcomp : ∀ i j : Fin (Module.finrank Real E),
      hessTensorAt (I := I) g f x (vec2 (cbasis i) (cbasis j)) =
        chartHessianTensor (I := I) g x f i j x := by
    intro i j
    rw [hessTensorAt_apply, hcb i, hcb j]
    rw [hessFun_eq_cov_grad (I := I) g f.contMDiff x
      (centeredChartTangentBasis (I := I) x i)
      (centeredChartTangentBasis (I := I) x j)]
    rw [← chartHessianTensor_eq_inner_cov_gradFun_basis_of_matrix_identity
      (I := I) g f.contMDiff x
      (chartHessianMatrixIdentity_holds (I := I) g f.contMDiff x) i j]
  rw [normSq0S_eq_coord (I := I) g x 2 cbasis cgInv hcinv
    (hessTensorAt (I := I) g f x)]
  unfold coordInner0S
  simp only [tensor0SComponent_apply]
  rw [chartHessFrobeniusSq_def, surfaceSquares_fin_two_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [surfaceSquares_fin_two_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hprod :
      (∏ a : Fin 2, cgInv ((fun a' : Fin 2 => if a' = 0 then i else j) a)
        ((fun a' : Fin 2 => if a' = 0 then k else l) a)) = cgInv i k * cgInv j l := by
    rw [Fin.prod_univ_two]
    simp
  rw [hprod, hvec i j, hvec k l, hcomp i j, hcomp k l]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_hessian_norm_eq_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_hessian_norm_eq_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_hessian_norm_eq_chart ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_hessian_norm_eq_chart

omit [CompleteSpace E] [IsManifold I 1 M] in
theorem surfaceEntropy_traceFree_hessian_norm
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 2)
    (f : C^∞⟮I, M; Real⟯) (x : M) :
    normSq0S (I := I) g x 2
      (hessTensorAt (I := I) g f x -
        (ΔG (I := I) g f x / 2) • metricTensor0S (I := I) g x) =
      normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) -
        (ΔG (I := I) g f x) ^ 2 / 2 := by
  have htrace : metricTracePair0SAt (I := I) g (hessTensorAt (I := I) g f x) =
      ΔG (I := I) g f x := by
    rw [← lap_eq_hess_on (I := I) g isOpen_univ f.contMDiff.contMDiffOn
      (Set.mem_univ x)]
    exact laplacian_levi_eq (I := I) g f.contMDiff x
  have hmetric : normSq0S (I := I) g x 2 (metricTensor0S (I := I) g x) = 2 := by
    change metricTracePair0SAt (I := I) g (metricTensor0S (I := I) g x) = 2
    simpa only [hdim, Nat.cast_ofNat] using metricTracePair0SAt_metric (I := I) g x
  have hpair : inner0S (I := I) g x 2
      (hessTensorAt (I := I) g f x) (metricTensor0S (I := I) g x) =
      ΔG (I := I) g f x := by
    rw [_root_.Submission.Tensor0SBundle.inner0S_comm]
    exact htrace
  rw [_root_.Submission.Tensor0SBundle.normSq0S_sub,
    _root_.Submission.Tensor0SBundle.inner0S_smul_right, normSq0S_smul, hpair, hmetric]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_traceFree_hessian_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_traceFree_hessian_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_traceFree_hessian_norm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_traceFree_hessian_norm

omit [CompleteSpace E] [IsManifold I 1 M] [T2Space M] in
private theorem surfaceSquares_gradient_pair_continuous
    (g : SmoothRiemannianMetric I M) (f h : C^∞⟮I, M; Real⟯) :
    Continuous (fun x : M => g.inner x (gradFun (I := I) g f x)
      (gradFun (I := I) g h x)) := by
  exact (contMDiff_g_inner_of_smooth_sections (I := I) g
    (gradG (I := I) g f) (gradG (I := I) g h)).continuous

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceSquares_gradient_pair_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceSquares_gradient_pair_continuous target :: scope.openDecls } }

private theorem surfaceSquares_bochner_pointwise
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 2)
    (f : C^∞⟮I, M; Real⟯) (x : M) :
    normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) =
      (1 / 2 : Real) * ΔG (I := I) g
        ⟨normGradSqFun (I := I) g f, normGradSqFun_contMDiff g f.contMDiff⟩ x -
      (1 / 2 : Real) * (metricScalarAt (I := I) g x * normGradSqFun (I := I) g f x) -
      g.inner x (gradFun (I := I) g f x)
        (gradFun (I := I) g (ΔG (I := I) g f) x) := by
  let dimensionPositive : NeZero (Module.finrank Real E) := ⟨by rw [hdim]; decide⟩
  have hb := bochner_pointwise_half_grad_normSq_of_boundaryless (I := I) g f.contMDiff x
  rw [← surfaceEntropy_hessian_norm_eq_chart g f x,
    ricciTensor_apply_of_finrank_two g hdim] at hb
  change (1 / 2 : Real) * ΔG (I := I) g
      ⟨normGradSqFun (I := I) g f, normGradSqFun_contMDiff g f.contMDiff⟩ x =
    normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) +
      (metricScalarAt (I := I) g x / 2) * normGradSqFun (I := I) g f x +
      g.inner x (gradFun (I := I) g f x)
        (gradFun (I := I) g (ΔG (I := I) g f) x) at hb
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceSquares_bochner_pointwise
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceSquares_bochner_pointwise target :: scope.openDecls } }

private theorem surfaceSquares_hessian_norm_continuous
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 2)
    (f : C^∞⟮I, M; Real⟯) :
    Continuous (fun x : M => normSq0S (I := I) g x 2
      (hessTensorAt (I := I) g f x)) := by
  let n : C^∞⟮I, M; Real⟯ :=
    ⟨normGradSqFun (I := I) g f, normGradSqFun_contMDiff g f.contMDiff⟩
  let d : C^∞⟮I, M; Real⟯ := ⟨ΔG (I := I) g f, Δ_g_contMDiff g f⟩
  have hc := (((Δ_g_contMDiff g n).continuous.const_mul (1 / 2 : Real)).sub
    (((metricScalar_smooth g).continuous.mul
      (normGradSqFun_continuous g f.contMDiff)).const_mul (1 / 2 : Real))).sub
        (surfaceSquares_gradient_pair_continuous g f d)
  exact hc.congr (fun x => (surfaceSquares_bochner_pointwise g hdim f x).symm)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceSquares_hessian_norm_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceSquares_hessian_norm_continuous target :: scope.openDecls } }

section ClosedSurface

variable [CompactSpace M]

theorem surfaceEntropy_integrated_bochner
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 2)
    (f : C^∞⟮I, M; Real⟯) :
    let μ := riemannianVolumeMeasure (I := I) (M := M) g
    (∫ x, (ΔG (I := I) g f x) ^ 2 ∂μ) =
      (∫ x, normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) ∂μ) +
        (1 / 2 : Real) * ∫ x, metricScalarAt (I := I) g x *
          normGradSqFun (I := I) g f x ∂μ := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let finiteVolume : _root_.MeasureTheory.IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  let n : C^∞⟮I, M; Real⟯ :=
    ⟨normGradSqFun (I := I) g f, normGradSqFun_contMDiff g f.contMDiff⟩
  let d : C^∞⟮I, M; Real⟯ := ⟨ΔG (I := I) g f, Δ_g_contMDiff g f⟩
  have hLint : _root_.MeasureTheory.Integrable (ΔG (I := I) g n) μ :=
    (Δ_g_contMDiff g n).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hRint : _root_.MeasureTheory.Integrable (fun x : M => metricScalarAt (I := I) g x *
      normGradSqFun (I := I) g f x) μ :=
    ((metricScalar_smooth g).continuous.mul
      (normGradSqFun_continuous g f.contMDiff)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hPint : _root_.MeasureTheory.Integrable (fun x : M => g.inner x (gradFun (I := I) g f x)
      (gradFun (I := I) g (ΔG (I := I) g f) x)) μ :=
    (surfaceSquares_gradient_pair_continuous g f d).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hLapzero : (∫ x, ΔG (I := I) g n x ∂μ) = 0 :=
    integral_divergence_eq_zero_of_compact (I := I) g (gradG (I := I) g n)
  have hPair : (∫ x, g.inner x (gradFun (I := I) g f x)
      (gradFun (I := I) g (ΔG (I := I) g f) x) ∂μ) =
      -(∫ x, (ΔG (I := I) g f x) ^ 2 ∂μ) := by
    calc
      (∫ x, g.inner x (gradFun (I := I) g f x)
          (gradFun (I := I) g (ΔG (I := I) g f) x) ∂μ) =
          ∫ x, g.inner x (gradFun (I := I) g (ΔG (I := I) g f) x)
            (gradFun (I := I) g f x) ∂μ := by
        exact _root_.MeasureTheory.integral_congr_ae (Eventually.of_forall (fun x => g.symm x _ _))
      _ = -(∫ x, ΔG (I := I) g f x * ΔG (I := I) g f x ∂μ) :=
        green_first_integral_inner_grad_eq_neg_integral_smul_laplacian (I := I)
          g d.contMDiff f.contMDiff (HasCompactSupport.of_compactSpace _)
      _ = -(∫ x, (ΔG (I := I) g f x) ^ 2 ∂μ) := by simp only [pow_two]
  have hIntegral :
      (∫ x, normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) ∂μ) =
      ∫ x, (1 / 2 : Real) * ΔG (I := I) g n x -
        (1 / 2 : Real) * (metricScalarAt (I := I) g x * normGradSqFun (I := I) g f x) -
        g.inner x (gradFun (I := I) g f x)
          (gradFun (I := I) g (ΔG (I := I) g f) x) ∂μ :=
    _root_.MeasureTheory.integral_congr_ae (Eventually.of_forall (surfaceSquares_bochner_pointwise g hdim f))
  have hsplit := _root_.MeasureTheory.integral_sub
    ((hLint.const_mul (1 / 2 : Real)).sub (hRint.const_mul (1 / 2 : Real))) hPint
  simp only [Pi.sub_apply] at hsplit
  rw [hsplit,
    _root_.MeasureTheory.integral_sub (hLint.const_mul (1 / 2 : Real)) (hRint.const_mul (1 / 2 : Real)),
    _root_.MeasureTheory.integral_const_mul,
    _root_.MeasureTheory.integral_const_mul, hLapzero, hPair] at hIntegral
  change (∫ x, (ΔG (I := I) g f x) ^ 2 ∂μ) =
    (∫ x, normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) ∂μ) +
      (1 / 2 : Real) * ∫ x, metricScalarAt (I := I) g x *
        normGradSqFun (I := I) g f x ∂μ
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_integrated_bochner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_integrated_bochner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_integrated_bochner ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_integrated_bochner

theorem surfaceEntropy_poisson_bochner
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 2)
    (f : C^∞⟮I, M; Real⟯) (r : Real)
    (hpoisson : ∀ x : M, ΔG (I := I) g f x = r - metricScalarAt (I := I) g x) :
    let μ := riemannianVolumeMeasure (I := I) (M := M) g
    (∫ x, (metricScalarAt (I := I) g x - r) ^ 2 ∂μ) =
      (∫ x, normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) ∂μ) +
        (1 / 2 : Real) * ∫ x, metricScalarAt (I := I) g x *
          normGradSqFun (I := I) g f x ∂μ := by
  have hb := surfaceEntropy_integrated_bochner g hdim f
  have heq : (∫ x, (ΔG (I := I) g f x) ^ 2
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, (metricScalarAt (I := I) g x - r) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    apply _root_.MeasureTheory.integral_congr_ae
    refine Eventually.of_forall (fun x => ?_)
    change (ΔG (I := I) g f x) ^ 2 = (metricScalarAt (I := I) g x - r) ^ 2
    rw [hpoisson x]
    ring
  dsimp only at hb ⊢
  rw [heq] at hb
  exact hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_poisson_bochner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_poisson_bochner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_poisson_bochner ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_poisson_bochner

end ClosedSurface

omit [I.Boundaryless] in
private theorem surfaceSquares_log_gradient_expansion
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (x : M)
    (hpositive : 0 < metricScalarAt (I := I) g x) :
    let R := fun y : M => metricScalarAt (I := I) g y
    let V := gradFun (I := I) g (fun y => Real.log (R y)) x - gradFun (I := I) g f x
    R x * g.inner x V V =
      normGradSqFun (I := I) g R x / R x -
        2 * g.inner x (gradFun (I := I) g R x) (gradFun (I := I) g f x) +
        R x * normGradSqFun (I := I) g f x := by
  let R := fun y : M => metricScalarAt (I := I) g y
  have hlog : gradFun (I := I) g (fun y => Real.log (R y)) x =
      (R x)⁻¹ • gradFun (I := I) g R x := by
    simpa only [gradient_eq_gradFun] using gradientFun_log (I := I) g
      ((metricScalar_smooth g).mdifferentiableAt (by decide)) hpositive
  change R x * g.inner x
      (gradFun (I := I) g (fun y => Real.log (R y)) x - gradFun (I := I) g f x)
      (gradFun (I := I) g (fun y => Real.log (R y)) x - gradFun (I := I) g f x) = _
  rw [hlog]
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, normGradSqFun_def]
  rw [g.symm x (gradFun (I := I) g f x) (gradFun (I := I) g R x)]
  dsimp only [R]
  field_simp [ne_of_gt hpositive]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceSquares_log_gradient_expansion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceSquares_log_gradient_expansion target :: scope.openDecls } }

section EntropySquares

variable [CompactSpace M] [Nonempty M]

theorem surfaceEntropy_static_two_squares
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 2)
    (hpositive : ∀ x : M, 0 < metricScalarAt (I := I) g x)
    (f : C^∞⟮I, M; Real⟯)
    (hpoisson : ∀ x : M, ΔG (I := I) g f x =
      (∫ y, metricScalarAt (I := I) g y
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) /
          (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ -
        metricScalarAt (I := I) g x) :
    let μ := riemannianVolumeMeasure (I := I) (M := M) g
    let R := fun x : M => metricScalarAt (I := I) g x
    let r := (∫ x, R x ∂μ) / μ.real Set.univ
    let V := fun x => gradFun (I := I) g (fun y => Real.log (R y)) x -
      gradFun (I := I) g f x;
    -(∫ x, normGradSqFun (I := I) g R x / R x ∂μ) + (∫ x, (R x - r) ^ 2 ∂μ) =
      -(∫ x, R x * g.inner x (V x) (V x) ∂μ) -
        2 * ∫ x, normSq0S (I := I) g x 2
          (hessTensorAt (I := I) g f x -
            (ΔG (I := I) g f x / 2) • metricTensor0S (I := I) g x) ∂μ := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let R := fun x : M => metricScalarAt (I := I) g x
  let r := (∫ x, R x ∂μ) / μ.real Set.univ
  let V := fun x : M => gradFun (I := I) g (fun y => Real.log (R y)) x -
    gradFun (I := I) g f x
  let finiteVolume : _root_.MeasureTheory.IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hRcont : Continuous R := (metricScalar_smooth g).continuous
  have hFint : _root_.MeasureTheory.Integrable (fun x : M => normGradSqFun (I := I) g R x / R x) μ :=
    ((normGradSqFun_continuous g (metricScalar_smooth g)).div hRcont
      (fun x => ne_of_gt (hpositive x))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hPint : _root_.MeasureTheory.Integrable (fun x : M => g.inner x (gradFun (I := I) g R x)
      (gradFun (I := I) g f x)) μ :=
    (surfaceSquares_gradient_pair_continuous
      g ⟨R, metricScalar_smooth g⟩ f).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hQint : _root_.MeasureTheory.Integrable (fun x : M => R x * normGradSqFun (I := I) g f x) μ :=
    (hRcont.mul (normGradSqFun_continuous g f.contMDiff)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hHint : _root_.MeasureTheory.Integrable (fun x : M => normSq0S (I := I) g x 2
      (hessTensorAt (I := I) g f x)) μ :=
    (surfaceSquares_hessian_norm_continuous g hdim f).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSint : _root_.MeasureTheory.Integrable (fun x : M => (R x - r) ^ 2) μ :=
    ((hRcont.sub continuous_const).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPair : (∫ x, g.inner x (gradFun (I := I) g R x)
      (gradFun (I := I) g f x) ∂μ) = ∫ x, (R x - r) ^ 2 ∂μ :=
    surfaceEntropy_poisson_gradient_pairing g f hpoisson
  have hBochner : (∫ x, (R x - r) ^ 2 ∂μ) =
      (∫ x, normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) ∂μ) +
        (1 / 2 : Real) * ∫ x, R x * normGradSqFun (I := I) g f x ∂μ :=
    surfaceEntropy_poisson_bochner g hdim f r hpoisson
  have hFirstSquare : (∫ x, R x * g.inner x (V x) (V x) ∂μ) =
      (∫ x, normGradSqFun (I := I) g R x / R x ∂μ) -
        2 * (∫ x, (R x - r) ^ 2 ∂μ) +
        (∫ x, R x * normGradSqFun (I := I) g f x ∂μ) := by
    calc
      (∫ x, R x * g.inner x (V x) (V x) ∂μ) =
          ∫ x, normGradSqFun (I := I) g R x / R x -
            2 * g.inner x (gradFun (I := I) g R x) (gradFun (I := I) g f x) +
            R x * normGradSqFun (I := I) g f x ∂μ :=
        _root_.MeasureTheory.integral_congr_ae (Eventually.of_forall (fun x =>
          surfaceSquares_log_gradient_expansion g f x (hpositive x)))
      _ = _ := by
        have hsplit := _root_.MeasureTheory.integral_add (hFint.sub (hPint.const_mul (2 : Real))) hQint
        simp only [Pi.sub_apply] at hsplit
        rw [hsplit, _root_.MeasureTheory.integral_sub hFint (hPint.const_mul (2 : Real)),
          _root_.MeasureTheory.integral_const_mul, hPair]
  have hSecondSquare :
      (∫ x, normSq0S (I := I) g x 2
        (hessTensorAt (I := I) g f x -
          (ΔG (I := I) g f x / 2) • metricTensor0S (I := I) g x) ∂μ) =
      (∫ x, normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) ∂μ) -
        (1 / 2 : Real) * ∫ x, (R x - r) ^ 2 ∂μ := by
    calc
      (∫ x, normSq0S (I := I) g x 2
          (hessTensorAt (I := I) g f x -
            (ΔG (I := I) g f x / 2) • metricTensor0S (I := I) g x) ∂μ) =
          ∫ x, normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) -
            (1 / 2 : Real) * (R x - r) ^ 2 ∂μ := by
        apply _root_.MeasureTheory.integral_congr_ae
        refine Eventually.of_forall (fun x => ?_)
        change normSq0S (I := I) g x 2
            (hessTensorAt (I := I) g f x -
              (ΔG (I := I) g f x / 2) • metricTensor0S (I := I) g x) =
          normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) -
            (1 / 2 : Real) * (R x - r) ^ 2
        rw [surfaceEntropy_traceFree_hessian_norm g hdim f x, hpoisson x]
        change _ - (r - R x) ^ 2 / 2 = _ - (1 / 2 : Real) * (R x - r) ^ 2
        ring
      _ = _ := by rw [_root_.MeasureTheory.integral_sub hHint (hSint.const_mul _), _root_.MeasureTheory.integral_const_mul]
  change -(∫ x, normGradSqFun (I := I) g R x / R x ∂μ) +
      (∫ x, (R x - r) ^ 2 ∂μ) =
    -(∫ x, R x * g.inner x (V x) (V x) ∂μ) -
      2 * ∫ x, normSq0S (I := I) g x 2
        (hessTensorAt (I := I) g f x -
          (ΔG (I := I) g f x / 2) • metricTensor0S (I := I) g x) ∂μ
  rw [hFirstSquare, hSecondSquare]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_static_two_squares then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_static_two_squares"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_static_two_squares ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_static_two_squares

theorem surfaceEntropy_static_first_variation_nonpos
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 2)
    (hpositive : ∀ x : M, 0 < metricScalarAt (I := I) g x)
    (f : C^∞⟮I, M; Real⟯)
    (hpoisson : ∀ x : M, ΔG (I := I) g f x =
      (∫ y, metricScalarAt (I := I) g y
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) /
          (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ -
        metricScalarAt (I := I) g x) :
    let μ := riemannianVolumeMeasure (I := I) (M := M) g
    let R := fun x : M => metricScalarAt (I := I) g x
    let r := (∫ x, R x ∂μ) / μ.real Set.univ;
    -(∫ x, normGradSqFun (I := I) g R x / R x ∂μ) +
      (∫ x, (R x - r) ^ 2 ∂μ) ≤ 0 := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let R := fun x : M => metricScalarAt (I := I) g x
  let r := (∫ x, R x ∂μ) / μ.real Set.univ
  let V := fun x : M => gradFun (I := I) g (fun y => Real.log (R y)) x -
    gradFun (I := I) g f x
  have hFirst : 0 ≤ ∫ x, R x * g.inner x (V x) (V x) ∂μ := by
    apply _root_.MeasureTheory.integral_nonneg
    intro x
    apply mul_nonneg (le_of_lt (hpositive x))
    by_cases hv : V x = 0
    · simp only [hv, map_zero]
      exact le_rfl
    · exact le_of_lt (g.pos x (V x) hv)
  have hSecond : 0 ≤ ∫ x, normSq0S (I := I) g x 2
      (hessTensorAt (I := I) g f x -
        (ΔG (I := I) g f x / 2) • metricTensor0S (I := I) g x) ∂μ :=
    _root_.MeasureTheory.integral_nonneg (fun x => normSq0S_nonneg g x 2 _)
  have hIdentity := surfaceEntropy_static_two_squares g hdim hpositive f hpoisson
  change -(∫ x, normGradSqFun (I := I) g R x / R x ∂μ) +
      (∫ x, (R x - r) ^ 2 ∂μ) =
    -(∫ x, R x * g.inner x (V x) (V x) ∂μ) -
      2 * ∫ x, normSq0S (I := I) g x 2
        (hessTensorAt (I := I) g f x -
          (ΔG (I := I) g f x / 2) • metricTensor0S (I := I) g x) ∂μ at hIdentity
  change -(∫ x, normGradSqFun (I := I) g R x / R x ∂μ) +
    (∫ x, (R x - r) ^ 2 ∂μ) ≤ 0
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_static_first_variation_nonpos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_static_first_variation_nonpos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_static_first_variation_nonpos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_static_first_variation_nonpos

end EntropySquares

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
