import Submission.DifferentialGeometry.Geometry.Geodesic.Equation.Koszul
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Add

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance productHorizontalOneNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productHorizontalOneNormedGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productHorizontalOneNormedGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productHorizontalOneNormedGroup ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productHorizontalOneNormedGroup
local instance productHorizontalOneNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productHorizontalOneNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productHorizontalOneNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productHorizontalOneNormedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productHorizontalOneNormedSpace
local instance productHorizontalTwoNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productHorizontalTwoNormedGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productHorizontalTwoNormedGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productHorizontalTwoNormedGroup ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productHorizontalTwoNormedGroup
local instance productHorizontalTwoNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productHorizontalTwoNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productHorizontalTwoNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productHorizontalTwoNormedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productHorizontalTwoNormedSpace
local instance productOneNormedGroup : NormedAddCommGroup ((E × ℝ) →L[ℝ] ℝ) :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productOneNormedGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productOneNormedGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productOneNormedGroup ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productOneNormedGroup
local instance productOneNormedSpace : NormedSpace ℝ ((E × ℝ) →L[ℝ] ℝ) :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productOneNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productOneNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productOneNormedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productOneNormedSpace
local instance productTwoNormedGroup : NormedAddCommGroup ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ) :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productTwoNormedGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productTwoNormedGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productTwoNormedGroup ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productTwoNormedGroup
local instance productTwoNormedSpace : NormedSpace ℝ ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ) :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productTwoNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productTwoNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productTwoNormedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productTwoNormedSpace


def lineProductMetricForm (B : E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ) :
    (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ :=
  c • B.bilinearComp (ContinuousLinearMap.fst ℝ E ℝ) (ContinuousLinearMap.fst ℝ E ℝ) +
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      (ContinuousLinearMap.snd ℝ E ℝ) (ContinuousLinearMap.snd ℝ E ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricForm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricForm

@[simp] theorem lineProductMetricForm_apply (B : E →L[ℝ] E →L[ℝ] ℝ)
    (c : ℝ) (v w : E × ℝ) :
    lineProductMetricForm B c v w = c * B v.1 w.1 + v.2 * w.2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricForm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricForm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricForm_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricForm_apply


def lineProductMetricDerivative (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ) :
    (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ :=
  let p := ContinuousLinearMap.fst ℝ E ℝ
  let pre : (E →L[ℝ] ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (E × ℝ) E ℝ).flip p
  c • (ContinuousLinearMap.compL ℝ (E × ℝ) (E →L[ℝ] ℝ) ((E × ℝ) →L[ℝ] ℝ) pre).comp
    (D.bilinearComp p p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricDerivative ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricDerivative

@[simp] theorem lineProductMetricDerivative_apply
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ) (u v w : E × ℝ) :
    lineProductMetricDerivative D c u v w = c * D u.1 v.1 w.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricDerivative_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricDerivative_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricDerivative_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricDerivative_apply

private def lineProductHorizontalCLM :
    (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ :=
  let p := ContinuousLinearMap.fst ℝ E ℝ
  let pre : (E →L[ℝ] ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (E × ℝ) E ℝ).flip p
  (ContinuousLinearMap.compL ℝ (E × ℝ) (E →L[ℝ] ℝ) ((E × ℝ) →L[ℝ] ℝ) pre).comp
    ((ContinuousLinearMap.compL ℝ (E × ℝ) E (E →L[ℝ] ℝ)).flip p)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductHorizontalCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductHorizontalCLM target :: scope.openDecls } }


theorem hasFDerivAt_lineProductMetricForm
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ}
    {x : E × ℝ} (hB : HasFDerivAt B D x.1) (c : ℝ) :
    HasFDerivAt (fun y : E × ℝ => lineProductMetricForm (B y.1) c)
      (lineProductMetricDerivative D c) x := by
  have hfirst : HasFDerivAt (fun y : E × ℝ => B y.1)
      (D.comp (ContinuousLinearMap.fst ℝ E ℝ)) x :=
    hB.comp x (hasFDerivAt_fst (𝕜 := ℝ) (p := x))
  have hhorizontal := (lineProductHorizontalCLM (E := E)).hasFDerivAt.comp x hfirst
  have hproduct := (hhorizontal.const_smul c).add_const
    ((ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      (ContinuousLinearMap.snd ℝ E ℝ) (ContinuousLinearMap.snd ℝ E ℝ))
  exact hproduct

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasFDerivAt_lineProductMetricForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasFDerivAt_lineProductMetricForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasFDerivAt_lineProductMetricForm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasFDerivAt_lineProductMetricForm


theorem fderiv_lineProductMetricForm
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E × ℝ}
    (hB : DifferentiableAt ℝ B x.1) (c : ℝ) :
    fderiv ℝ (fun y : E × ℝ => lineProductMetricForm (B y.1) c) x =
      lineProductMetricDerivative (fderiv ℝ B x.1) c :=
  (hasFDerivAt_lineProductMetricForm hB.hasFDerivAt c).fderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fderiv_lineProductMetricForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fderiv_lineProductMetricForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fderiv_lineProductMetricForm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fderiv_lineProductMetricForm


theorem lineProductMetricForm_isCoercive
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : IsCoercive B) (c : ℝ) (hc : 0 < c) :
    IsCoercive (lineProductMetricForm B c) := by
  obtain ⟨mu, hmu, hbound⟩ := hB
  refine ⟨min (c * mu) 1, lt_min (mul_pos hc hmu) zero_lt_one, ?_⟩
  intro v
  have hBnonneg : 0 ≤ B v.1 v.1 :=
    (mul_nonneg (mul_nonneg hmu.le (norm_nonneg _)) (norm_nonneg _)).trans (hbound v.1)
  have hcnonneg : 0 ≤ c * B v.1 v.1 := mul_nonneg hc.le hBnonneg
  have hreal : ‖v.2‖ * ‖v.2‖ = v.2 * v.2 := by
    rw [Real.norm_eq_abs, ← abs_mul, abs_of_nonneg (mul_self_nonneg _)]
  rw [lineProductMetricForm_apply, Prod.norm_def]
  by_cases hnorm : ‖v.1‖ ≤ ‖v.2‖
  · rw [max_eq_right hnorm]
    have hle := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_right (c * mu) 1) (norm_nonneg v.2))
      (norm_nonneg v.2)
    have hle' : _root_.Min.min (c * mu) 1 * ‖v.2‖ * ‖v.2‖ ≤ v.2 * v.2 := by
      simpa only [one_mul, hreal] using hle
    exact hle'.trans (le_add_of_nonneg_left hcnonneg)
  · rw [max_eq_left (le_of_lt (lt_of_not_ge hnorm))]
    calc
      min (c * mu) 1 * ‖v.1‖ * ‖v.1‖ ≤ c * (mu * ‖v.1‖ * ‖v.1‖) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (min_le_left (c * mu) 1) (norm_nonneg v.1))
          (norm_nonneg v.1)
      _ ≤ c * B v.1 v.1 := mul_le_mul_of_nonneg_left (hbound v.1) hc.le
      _ ≤ c * B v.1 v.1 + v.2 * v.2 := le_add_of_nonneg_right (mul_self_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricForm_isCoercive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricForm_isCoercive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricForm_isCoercive ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineProductMetricForm_isCoercive


theorem koszulCov_lineProduct
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ) (u v w : E × ℝ) :
    MetricKoszul.koszulCov (lineProductMetricDerivative D c) v w u =
      c * MetricKoszul.koszulCov D v.1 w.1 u.1 := by
  simp only [MetricKoszul.koszul_cov_apply, lineProductMetricDerivative_apply]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.koszulCov_lineProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.koszulCov_lineProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.koszulCov_lineProduct ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.koszulCov_lineProduct

variable [FiniteDimensional ℝ E] [CompleteSpace E]


theorem koszulVec_lineProduct
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : IsCoercive B)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ) (hc : 0 < c) (v w : E × ℝ) :
    MetricKoszul.koszulVec (lineProductMetricForm_isCoercive B hB c hc)
        (lineProductMetricDerivative D c) v w =
      (MetricKoszul.koszulVec hB D v.1 w.1, 0) := by
  apply (lineProductMetricForm_isCoercive B hB c hc).bilin_injective
  apply ContinuousLinearMap.ext
  intro u
  calc
    _ = MetricKoszul.koszulCov (lineProductMetricDerivative D c) v w u :=
      DFunLike.congr_fun (MetricKoszul.apply_koszul_vec
        (lineProductMetricForm_isCoercive B hB c hc) (lineProductMetricDerivative D c) v w) u
    _ = c * MetricKoszul.koszulCov D v.1 w.1 u.1 := koszulCov_lineProduct D c u v w
    _ = c * B (MetricKoszul.koszulVec hB D v.1 w.1) u.1 :=
      congrArg (fun a : ℝ => c * a)
        (DFunLike.congr_fun (MetricKoszul.apply_koszul_vec hB D v.1 w.1) u.1).symm
    _ = lineProductMetricForm B c (MetricKoszul.koszulVec hB D v.1 w.1, 0) u := by
      simp only [lineProductMetricForm_apply, _root_.MulZeroClass.zero_mul, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.koszulVec_lineProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.koszulVec_lineProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.koszulVec_lineProduct ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.koszulVec_lineProduct


theorem koszulVec_lineProduct_scale_independent
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : IsCoercive B)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (c d : ℝ) (hc : 0 < c) (hd : 0 < d) (v w : E × ℝ) :
    MetricKoszul.koszulVec (lineProductMetricForm_isCoercive B hB c hc)
        (lineProductMetricDerivative D c) v w =
      MetricKoszul.koszulVec (lineProductMetricForm_isCoercive B hB d hd)
        (lineProductMetricDerivative D d) v w :=
  (koszulVec_lineProduct B hB D c hc v w).trans (koszulVec_lineProduct B hB D d hd v w).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.koszulVec_lineProduct_scale_independent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.koszulVec_lineProduct_scale_independent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.koszulVec_lineProduct_scale_independent ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.koszulVec_lineProduct_scale_independent

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
