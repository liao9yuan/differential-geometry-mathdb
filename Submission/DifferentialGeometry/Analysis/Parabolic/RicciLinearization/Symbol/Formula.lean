import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.Symbol.SecondOrderPart
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.Variation.InverseGram
import Submission.DifferentialGeometry.Analysis.Parabolic.PrincipalSymbol.Defs

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

section InvGramBridge

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartInvGramOnE_extChartAt_self (g : SmoothRiemannianMetric I M) (x : M)
    (j l : Fin (Module.finrank ℝ E)) :
    chartInvGramOnE (I := I) g x j l (extChartAt I x x) =
      chartInvGramMatrix (I := I) g x x j l := by
  rw [chartInvGramOnE_def, extChartAt_to_inv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartInvGramOnE_extChartAt_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartInvGramOnE_extChartAt_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartInvGramOnE_extChartAt_self ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartInvGramOnE_extChartAt_self

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartInvGramMatrix_self_symm (g : SmoothRiemannianMetric I M) (x : M)
    (j l : Fin (Module.finrank ℝ E)) :
    chartInvGramMatrix (I := I) g x x j l =
      chartInvGramMatrix (I := I) g x x l j := by
  have hHerm : (chartInvGramMatrix (I := I) g x x).IsHermitian := by
    unfold chartInvGramMatrix
    exact (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_isHermitian (I := I) g x x).inv
  have hentry := hHerm.apply l j
  rwa [_root_.TrivialStar.star_trivial] at hentry

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartInvGramMatrix_self_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartInvGramMatrix_self_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartInvGramMatrix_self_symm ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartInvGramMatrix_self_symm

end InvGramBridge

section FibreForm

def formComp (x : M)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (c d : Fin (Module.finrank ℝ E)) : ℝ :=
  t (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x c)
    (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
@[simp] lemma formComp_def (x : M)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (c d : Fin (Module.finrank ℝ E)) :
    formComp (I := I) x t c d =
      t (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x c)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x d) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_def ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_def

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
@[simp] lemma formComp_zero (x : M) (c d : Fin (Module.finrank ℝ E)) :
    formComp (I := I) x
      (0 : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) c d = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_zero ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_zero

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
lemma formComp_add (x : M)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (c d : Fin (Module.finrank ℝ E)) :
    formComp (I := I) x (t + t') c d =
      formComp (I := I) x t c d + formComp (I := I) x t' c d := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_add ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_add

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
lemma formComp_smul (x : M) (a : ℝ)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (c d : Fin (Module.finrank ℝ E)) :
    formComp (I := I) x (a • t) c d = a * formComp (I := I) x t c d := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_smul ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_smul

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
lemma formComp_symm (x : M)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) (c d : Fin (Module.finrank ℝ E)) :
    formComp (I := I) x t c d = formComp (I := I) x t d c := by
  rw [formComp_def, formComp_def, ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_symm ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.formComp_symm

def formMetricTrace (g : SmoothRiemannianMetric I M) (x : M)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) : ℝ :=
  ∑ m : Fin (Module.finrank ℝ E),
    ∑ n : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x m n * formComp (I := I) x t m n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma formMetricTrace_def (g : SmoothRiemannianMetric I M) (x : M)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    formMetricTrace (I := I) g x t =
      ∑ m : Fin (Module.finrank ℝ E),
        ∑ n : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x m n * formComp (I := I) x t m n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace_def ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace_def

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma formMetricTrace_zero (g : SmoothRiemannianMetric I M) (x : M) :
    formMetricTrace (I := I) g x
      (0 : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) = 0 := by
  rw [formMetricTrace_def]
  exact Finset.sum_eq_zero fun m _ =>
    Finset.sum_eq_zero fun n _ => by rw [formComp_zero, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace_zero ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace_zero

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma formMetricTrace_add (g : SmoothRiemannianMetric I M) (x : M)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    formMetricTrace (I := I) g x (t + t') =
      formMetricTrace (I := I) g x t + formMetricTrace (I := I) g x t' := by
  rw [formMetricTrace_def, formMetricTrace_def, formMetricTrace_def,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [formComp_add]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace_add ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace_add

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma formMetricTrace_smul (g : SmoothRiemannianMetric I M) (x : M) (a : ℝ)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    formMetricTrace (I := I) g x (a • t) = a * formMetricTrace (I := I) g x t := by
  rw [formMetricTrace_def, formMetricTrace_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [formComp_smul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace_smul ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.formMetricTrace_smul

def raisedFormContraction (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (k : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ l : Fin (Module.finrank ℝ E),
    raisedCovectorComp (I := I) g x ξ l * formComp (I := I) x t l k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma raisedFormContraction_def (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    raisedFormContraction (I := I) g x ξ t k =
      ∑ l : Fin (Module.finrank ℝ E),
        raisedCovectorComp (I := I) g x ξ l * formComp (I := I) x t l k := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction_def ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction_def

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma raisedFormContraction_zero (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (k : Fin (Module.finrank ℝ E)) :
    raisedFormContraction (I := I) g x ξ
      (0 : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) k = 0 := by
  rw [raisedFormContraction_def]
  exact Finset.sum_eq_zero fun l _ => by rw [formComp_zero, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction_zero ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction_zero

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma raisedFormContraction_add (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    raisedFormContraction (I := I) g x ξ (t + t') k =
      raisedFormContraction (I := I) g x ξ t k +
        raisedFormContraction (I := I) g x ξ t' k := by
  rw [raisedFormContraction_def, raisedFormContraction_def, raisedFormContraction_def,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [formComp_add]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction_add ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction_add

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma raisedFormContraction_smul (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) (a : ℝ)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    raisedFormContraction (I := I) g x ξ (a • t) k =
      a * raisedFormContraction (I := I) g x ξ t k := by
  rw [raisedFormContraction_def, raisedFormContraction_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [formComp_smul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction_smul ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContraction_smul

def raisedFormContractionSnd (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    raisedCovectorComp (I := I) g x ξ j * formComp (I := I) x t i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma raisedFormContractionSnd_def (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    raisedFormContractionSnd (I := I) g x ξ t i =
      ∑ j : Fin (Module.finrank ℝ E),
        raisedCovectorComp (I := I) g x ξ j * formComp (I := I) x t i j := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_def ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_def

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma raisedFormContractionSnd_zero (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (i : Fin (Module.finrank ℝ E)) :
    raisedFormContractionSnd (I := I) g x ξ
      (0 : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) i = 0 := by
  rw [raisedFormContractionSnd_def]
  exact Finset.sum_eq_zero fun j _ => by rw [formComp_zero, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_zero ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_zero

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma raisedFormContractionSnd_add (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    raisedFormContractionSnd (I := I) g x ξ (t + t') i =
      raisedFormContractionSnd (I := I) g x ξ t i +
        raisedFormContractionSnd (I := I) g x ξ t' i := by
  rw [raisedFormContractionSnd_def, raisedFormContractionSnd_def,
    raisedFormContractionSnd_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [formComp_add]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_add ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_add

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma raisedFormContractionSnd_smul (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (a : ℝ) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    raisedFormContractionSnd (I := I) g x ξ (a • t) i =
      a * raisedFormContractionSnd (I := I) g x ξ t i := by
  rw [raisedFormContractionSnd_def, raisedFormContractionSnd_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [formComp_smul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_smul ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_smul

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma raisedFormContractionSnd_eq_of_symm (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) (i : Fin (Module.finrank ℝ E)) :
    raisedFormContractionSnd (I := I) g x ξ t i =
      raisedFormContraction (I := I) g x ξ t i := by
  rw [raisedFormContractionSnd_def, raisedFormContraction_def]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [formComp_symm (I := I) x t ht i j]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_eq_of_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_eq_of_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_eq_of_symm ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.raisedFormContractionSnd_eq_of_symm

end FibreForm

section SymbolComponent

def ricciSymbolComp (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) : ℝ :=
  (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
    ∑ l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g x j l (extChartAt I x x) *
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
            formComp (I := I) x t l k +
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
            formComp (I := I) x t i j -
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
            formComp (I := I) x t i k -
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
            formComp (I := I) x t l j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma ricciSymbolComp_def (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ricciSymbolComp (I := I) g x ξ t i k =
      (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g x j l (extChartAt I x x) *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k +
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j -
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                formComp (I := I) x t i k -
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_def ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_def

end SymbolComponent

section ClosedForm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma sum_term_one (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
              formComp (I := I) x t l k) =
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
        raisedFormContraction (I := I) g x ξ t k := by
  calc
    ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k)
      = ∑ l : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k) := Finset.sum_comm
    _ = ∑ l : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
            (raisedCovectorComp (I := I) g x ξ l * formComp (I := I) x t l k) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [raisedCovectorComp_def, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [chartInvGramMatrix_self_symm (I := I) g x j l]
        ring
    _ = (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
          raisedFormContraction (I := I) g x ξ t k := by
        rw [raisedFormContraction_def, Finset.mul_sum]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.sum_term_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.DeTurck.RicciLinearization.sum_term_one target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma sum_term_two (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
              formComp (I := I) x t i j) =
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k *
        raisedFormContractionSnd (I := I) g x ξ t i := by
  calc
    ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j)
      = ∑ j : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k *
            (raisedCovectorComp (I := I) g x ξ j * formComp (I := I) x t i j) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [raisedCovectorComp_def, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring
    _ = (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k *
          raisedFormContractionSnd (I := I) g x ξ t i := by
        rw [raisedFormContractionSnd_def, Finset.mul_sum]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.sum_term_two
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.DeTurck.RicciLinearization.sum_term_two target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma sum_term_three (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
              formComp (I := I) x t i k) =
      metricCovectorNormSq (I := I) g x ξ * formComp (I := I) x t i k := by
  rw [metricCovectorNormSq_def, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.sum_term_three
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.DeTurck.RicciLinearization.sum_term_three target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma sum_term_four (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
              formComp (I := I) x t l j) =
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
        formMetricTrace (I := I) g x t := by
  calc
    ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j)
      = ∑ m : Fin (Module.finrank ℝ E),
          ∑ n : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
              (chartInvGramMatrix (I := I) g x x m n *
                formComp (I := I) x t m n) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [chartInvGramMatrix_self_symm (I := I) g x n m]
        ring
    _ = (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
          formMetricTrace (I := I) g x t := by
        rw [formMetricTrace_def, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Finset.mul_sum]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.sum_term_four
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.DeTurck.RicciLinearization.sum_term_four target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma ricciSymbol_doubleSum_split (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k +
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j -
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                formComp (I := I) x t i k -
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j) =
      (∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k)) +
      (∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j)) -
      (∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                formComp (I := I) x t i k)) -
      (∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j)) := by
  have hdist : ∀ j l : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x j l *
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
              formComp (I := I) x t l k +
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
              formComp (I := I) x t i j -
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
              formComp (I := I) x t i k -
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
              formComp (I := I) x t l j) =
        chartInvGramMatrix (I := I) g x x j l *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
              formComp (I := I) x t l k) +
          chartInvGramMatrix (I := I) g x x j l *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
              formComp (I := I) x t i j) -
          chartInvGramMatrix (I := I) g x x j l *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
              formComp (I := I) x t i k) -
          chartInvGramMatrix (I := I) g x x j l *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
              formComp (I := I) x t l j) := fun j l => by ring
  have hrow : ∀ j : Fin (Module.finrank ℝ E),
      (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k +
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j -
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                formComp (I := I) x t i k -
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j)) =
        (∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k)) +
          (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x j l *
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                  formComp (I := I) x t i j)) -
          (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x j l *
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                  formComp (I := I) x t i k)) -
          (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x j l *
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
                  formComp (I := I) x t l j)) := by
    intro j
    rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hdist j l),
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hrow j),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbol_doubleSum_split
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbol_doubleSum_split target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem ricciSymbolComp_eq_closedForm (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ricciSymbolComp (I := I) g x ξ t i k =
      (1 / 2 : ℝ) * ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
          raisedFormContraction (I := I) g x ξ t k) +
        (1 / 2 : ℝ) * ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k *
          raisedFormContractionSnd (I := I) g x ξ t i) -
        (1 / 2 : ℝ) * (metricCovectorNormSq (I := I) g x ξ *
          formComp (I := I) x t i k) -
        (1 / 2 : ℝ) * ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * formMetricTrace (I := I) g x t) := by
  rw [ricciSymbolComp_def]
  have hgram : ∀ j l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g x j l (extChartAt I x x) =
        chartInvGramMatrix (I := I) g x x j l :=
    fun j l => chartInvGramOnE_extChartAt_self (I := I) g x j l
  rw [show (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g x j l (extChartAt I x x) *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k +
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j -
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                formComp (I := I) x t i k -
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j)) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k +
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j -
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                formComp (I := I) x t i k -
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j)) from by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hgram j l]]
  rw [ricciSymbol_doubleSum_split (I := I) g x ξ t i k,
    sum_term_one (I := I) g x ξ t i k, sum_term_two (I := I) g x ξ t i k,
    sum_term_three (I := I) g x ξ t i k, sum_term_four (I := I) g x ξ t i k]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_eq_closedForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_eq_closedForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_eq_closedForm ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_eq_closedForm

end ClosedForm

section Linearity

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem ricciSymbolComp_add (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ricciSymbolComp (I := I) g x ξ (t + t') i k =
      ricciSymbolComp (I := I) g x ξ t i k +
        ricciSymbolComp (I := I) g x ξ t' i k := by
  rw [ricciSymbolComp_eq_closedForm (I := I) g x ξ (t + t') i k,
    ricciSymbolComp_eq_closedForm (I := I) g x ξ t i k,
    ricciSymbolComp_eq_closedForm (I := I) g x ξ t' i k,
    raisedFormContraction_add, raisedFormContractionSnd_add, formComp_add,
    formMetricTrace_add]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_add ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_add

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem ricciSymbolComp_smul (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) (a : ℝ)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ricciSymbolComp (I := I) g x ξ (a • t) i k =
      a * ricciSymbolComp (I := I) g x ξ t i k := by
  rw [ricciSymbolComp_eq_closedForm (I := I) g x ξ (a • t) i k,
    ricciSymbolComp_eq_closedForm (I := I) g x ξ t i k,
    raisedFormContraction_smul, raisedFormContractionSnd_smul, formComp_smul,
    formMetricTrace_smul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_smul ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_smul

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem ricciSymbolComp_zero (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (i k : Fin (Module.finrank ℝ E)) :
    ricciSymbolComp (I := I) g x ξ
      (0 : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) i k = 0 := by
  rw [ricciSymbolComp_eq_closedForm, raisedFormContraction_zero,
    raisedFormContractionSnd_zero, formComp_zero, formMetricTrace_zero]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_zero ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_zero

end Linearity

section Symmetry

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem ricciSymbolComp_symm (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) (i k : Fin (Module.finrank ℝ E)) :
    ricciSymbolComp (I := I) g x ξ t i k =
      ricciSymbolComp (I := I) g x ξ t k i := by
  rw [ricciSymbolComp_eq_closedForm (I := I) g x ξ t i k,
    ricciSymbolComp_eq_closedForm (I := I) g x ξ t k i]
  rw [raisedFormContractionSnd_eq_of_symm (I := I) g x ξ t ht i,
    raisedFormContractionSnd_eq_of_symm (I := I) g x ξ t ht k,
    formComp_symm (I := I) x t ht i k]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_symm ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciSymbolComp_symm

end Symmetry

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
