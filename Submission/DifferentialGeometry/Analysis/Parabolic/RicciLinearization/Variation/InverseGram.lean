import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.Operator
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Const

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Set _root_.Function
open scoped _root_.Topology _root_.ContDiff _root_.Matrix _root_.Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

section PartialDerivAlgebra

variable {i : Fin (Module.finrank ℝ E)} {y : E}

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_add (u v : E → ℝ)
    (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (fun y => u y + v y) y =
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u y + DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i v y := by
  unfold DifferentialGeometry.Tensor.Coordinates.partialDeriv
  rw [fderiv_fun_add hu hv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_add ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_add

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_sub (u v : E → ℝ)
    (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (fun y => u y - v y) y =
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u y - DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i v y := by
  unfold DifferentialGeometry.Tensor.Coordinates.partialDeriv
  rw [fderiv_fun_sub hu hv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_sub ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_sub

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_smul (c u : E → ℝ)
    (hc : DifferentiableAt ℝ c y) (hu : DifferentiableAt ℝ u y) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (fun y => c y • u y) y =
      c y • DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u y + DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i c y • u y := by
  unfold DifferentialGeometry.Tensor.Coordinates.partialDeriv
  rw [fderiv_fun_smul hc hu]
  simp [ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_smul ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_smul

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_const_smul (c : ℝ) (u : E → ℝ)
    (hu : DifferentiableAt ℝ u y) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (fun y => c • u y) y =
      c • DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u y := by
  unfold DifferentialGeometry.Tensor.Coordinates.partialDeriv
  rw [fderiv_fun_const_smul hu c]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_const_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_const_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_const_smul ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_const_smul

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_const_mul (c : ℝ) (u : E → ℝ)
    (hu : DifferentiableAt ℝ u y) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (fun y => c * u y) y =
      c * DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u y := by
  unfold DifferentialGeometry.Tensor.Coordinates.partialDeriv
  rw [fderiv_const_mul hu c]
  simp [smul_apply, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_const_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_const_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_const_mul ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_const_mul

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_mul (u v : E → ℝ)
    (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (fun y => u y * v y) y =
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u y * v y + u y * DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i v y := by
  unfold DifferentialGeometry.Tensor.Coordinates.partialDeriv
  rw [fderiv_fun_mul hu hv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_mul ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_mul

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_sum {ι : Type*} (s : Finset ι) (A : ι → E → ℝ)
    (hA : ∀ k ∈ s, DifferentiableAt ℝ (A k) y) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (fun y => ∑ k ∈ s, A k y) y =
      ∑ k ∈ s, DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (A k) y := by
  unfold DifferentialGeometry.Tensor.Coordinates.partialDeriv
  rw [fderiv_fun_sum hA]
  rw [sum_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_sum ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_sum

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma partialDeriv_const (c : ℝ) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (fun _ : E => c) y = 0 := by
  unfold DifferentialGeometry.Tensor.Coordinates.partialDeriv
  rw [show (fun _ : E => c) = Function.const E c from rfl, fderiv_const]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_const ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_const

end PartialDerivAlgebra

structure ChartMetricPerturbation (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] where
  toFun : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → (E → ℝ)
  symmetric : ∀ i j y, toFun i j y = toFun j i y
  contDiff : ∀ i j, ContDiff ℝ ∞ (toFun i j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation

namespace ChartMetricPerturbation

instance _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instCoeFunForallFinFinrankRealForallForall : CoeFun (ChartMetricPerturbation E)
    (fun _ => Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → (E → ℝ)) :=
  ⟨ChartMetricPerturbation.toFun⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instCoeFunForallFinFinrankRealForallForall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instCoeFunForallFinFinrankRealForallForall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instCoeFunForallFinFinrankRealForallForall ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instCoeFunForallFinFinrankRealForallForall

omit [NeZero (Module.finrank ℝ E)] in
lemma symm (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    h i j y = h j i y := h.symmetric i j y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.symm ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.symm

omit [NeZero (Module.finrank ℝ E)] in
lemma symm_fun (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) :
    h i j = h j i := funext (h.symm i j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.symm_fun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.symm_fun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.symm_fun ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.symm_fun

omit [NeZero (Module.finrank ℝ E)] in
lemma smooth (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (h i j) := h.contDiff i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.smooth ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.smooth

omit [NeZero (Module.finrank ℝ E)] in
lemma differentiableAt (h : ChartMetricPerturbation E)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    DifferentiableAt ℝ (h i j) y :=
  ((h.smooth i j).differentiable (by simp)).differentiableAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.differentiableAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.differentiableAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.differentiableAt ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.differentiableAt

instance _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instZero : Zero (ChartMetricPerturbation E) :=
  ⟨{ toFun := fun _ _ _ => 0
     symmetric := fun _ _ _ => rfl
     contDiff := fun _ _ => contDiff_const }⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instZero ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instZero

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma zero_apply (i j : Fin (Module.finrank ℝ E)) (y : E) :
    (0 : ChartMetricPerturbation E) i j y = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.zero_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.zero_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.zero_apply ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.zero_apply

omit [NeZero (Module.finrank ℝ E)] in
@[ext] lemma ext {h h' : ChartMetricPerturbation E}
    (hyperbolic : ∀ i j, (h i j) = (h' i j)) : h = h' := by
  cases h; cases h'; congr 1; funext i j; exact hyperbolic i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.ext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.ext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.ext ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.ext

end ChartMetricPerturbation

section TraceAndRaising

def raisedCovectorComp (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (m : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ n : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g x x m n * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedCovectorComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedCovectorComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedCovectorComp ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedCovectorComp

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma raisedCovectorComp_def (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (m : Fin (Module.finrank ℝ E)) :
    raisedCovectorComp (I := I) g x ξ m =
      ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x m n * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedCovectorComp_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedCovectorComp_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedCovectorComp_def ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedCovectorComp_def

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma raisedCovectorComp_zero (g : SmoothRiemannianMetric I M) (x : M)
    (m : Fin (Module.finrank ℝ E)) :
    raisedCovectorComp (I := I) g x (0 : E) m = 0 := by
  simp [raisedCovectorComp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedCovectorComp_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedCovectorComp_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedCovectorComp_zero ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedCovectorComp_zero

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma sum_raisedCovectorComp_mul_repr
    (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    ∑ m : Fin (Module.finrank ℝ E),
        raisedCovectorComp (I := I) g x ξ m * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ m =
      metricCovectorNormSq (I := I) g x ξ := by
  rw [metricCovectorNormSq_def]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [raisedCovectorComp_def, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.sum_raisedCovectorComp_mul_repr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.sum_raisedCovectorComp_mul_repr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.sum_raisedCovectorComp_mul_repr ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.sum_raisedCovectorComp_mul_repr

def metricTrace (g : SmoothRiemannianMetric I M) (x : M)
    (h : ChartMetricPerturbation E) : ℝ :=
  ∑ m : Fin (Module.finrank ℝ E),
    ∑ n : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x m n * h m n (extChartAt I x x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma metricTrace_def (g : SmoothRiemannianMetric I M) (x : M)
    (h : ChartMetricPerturbation E) :
    metricTrace (I := I) g x h =
      ∑ m : Fin (Module.finrank ℝ E),
        ∑ n : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x m n * h m n (extChartAt I x x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace_def ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace_def

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma metricTrace_zero (g : SmoothRiemannianMetric I M) (x : M) :
    metricTrace (I := I) g x (0 : ChartMetricPerturbation E) = 0 := by
  simp [metricTrace]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace_zero ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace_zero

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma metricTrace_congr (g : SmoothRiemannianMetric I M) (x : M)
    {h h' : ChartMetricPerturbation E}
    (hyperbolic : ∀ m n, h m n (extChartAt I x x) = h' m n (extChartAt I x x)) :
    metricTrace (I := I) g x h = metricTrace (I := I) g x h' := by
  rw [metricTrace_def, metricTrace_def]
  exact Finset.sum_congr rfl (fun m _ =>
    Finset.sum_congr rfl (fun n _ => by rw [hyperbolic m n]))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace_congr ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace_congr

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma metricTrace_eq_sum (g : SmoothRiemannianMetric I M) (x : M)
    (h : ChartMetricPerturbation E) :
    metricTrace (I := I) g x h =
      ∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x p.1 p.2 *
          h p.1 p.2 (extChartAt I x x) := by
  rw [metricTrace_def, ← Finset.sum_product', Finset.univ_product_univ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace_eq_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace_eq_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace_eq_sum ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricTrace_eq_sum

end TraceAndRaising

section InvGramPerturbation

def invGramPerturbation (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (l m : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  -∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α l a y *
        chartInvGramOnE (I := I) g α b m y * h a b y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.invGramPerturbation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.invGramPerturbation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.invGramPerturbation ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.invGramPerturbation

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma invGramPerturbation_def (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (l m : Fin (Module.finrank ℝ E)) (y : E) :
    invGramPerturbation (I := I) g α h l m y =
      -∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α l a y *
            chartInvGramOnE (I := I) g α b m y * h a b y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.invGramPerturbation_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.invGramPerturbation_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.invGramPerturbation_def ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.invGramPerturbation_def

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma invGramPerturbation_zero (g : SmoothRiemannianMetric I M) (α : M)
    (l m : Fin (Module.finrank ℝ E)) (y : E) :
    invGramPerturbation (I := I) g α (0 : ChartMetricPerturbation E) l m y = 0 := by
  simp [invGramPerturbation]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.invGramPerturbation_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.invGramPerturbation_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.invGramPerturbation_zero ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.invGramPerturbation_zero

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma invGramPerturbation_symm (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (l m : Fin (Module.finrank ℝ E)) (y : E) :
    invGramPerturbation (I := I) g α h l m y =
      invGramPerturbation (I := I) g α h m l y := by
  rw [invGramPerturbation_def, invGramPerturbation_def]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [chartInvGramOnE_symm (I := I) g α l b y,
    chartInvGramOnE_symm (I := I) g α a m y, h.symm b a y]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.invGramPerturbation_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.invGramPerturbation_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.invGramPerturbation_symm ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.invGramPerturbation_symm

end InvGramPerturbation

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
