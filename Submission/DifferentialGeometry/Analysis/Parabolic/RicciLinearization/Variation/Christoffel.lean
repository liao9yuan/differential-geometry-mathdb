import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.Variation.InverseGram

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

namespace ChartMetricPerturbation

instance _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instAdd : Add (ChartMetricPerturbation E) :=
  ⟨fun h₁ h₂ =>
    { toFun := fun i j y => h₁ i j y + h₂ i j y
      symmetric := fun i j y => by
        simp only [ChartMetricPerturbation.symm h₁ i j y, ChartMetricPerturbation.symm h₂ i j y]
      contDiff := fun i j => (h₁.smooth i j).add (h₂.smooth i j) }⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instAdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instAdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instAdd ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instAdd

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma add_apply (h₁ h₂ : ChartMetricPerturbation E)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    (h₁ + h₂) i j y = h₁ i j y + h₂ i j y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.add_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.add_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.add_apply ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.add_apply

instance _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instSMulReal : SMul ℝ (ChartMetricPerturbation E) :=
  ⟨fun c h =>
    { toFun := fun i j y => c • h i j y
      symmetric := fun i j y => by
        simp only [ChartMetricPerturbation.symm h i j y]
      contDiff := fun i j => (h.smooth i j).const_smul c }⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instSMulReal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instSMulReal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instSMulReal ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.instSMulReal

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma smul_apply (c : ℝ) (h : ChartMetricPerturbation E)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    (c • h) i j y = c • h i j y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.smul_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.smul_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.smul_apply ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation.smul_apply

end ChartMetricPerturbation

def chartLinearizedChristoffelPrincipal (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramOnE (I := I) g α k l y *
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (h l j) y +
       DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (h l i) y -
       DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h i j) y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartLinearizedChristoffelPrincipal_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedChristoffelPrincipal (I := I) g α h i j k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (h l j) y +
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (h l i) y -
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h i j) y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_def ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_def

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartLinearizedChristoffelPrincipal_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedChristoffelPrincipal (I := I) g α h i j k y =
      chartLinearizedChristoffelPrincipal (I := I) g α h j i k y := by
  classical
  rw [chartLinearizedChristoffelPrincipal_def, chartLinearizedChristoffelPrincipal_def]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  congr 1
  rw [show DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h i j) y =
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h j i) y from by rw [h.symm_fun i j]]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_symm ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_symm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartLinearizedChristoffelPrincipal_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedChristoffelPrincipal (I := I) g α
      (0 : ChartMetricPerturbation E) i j k y = 0 := by
  classical
  rw [chartLinearizedChristoffelPrincipal_def]
  have hzero : ∀ l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α k l y *
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i ((0 : ChartMetricPerturbation E) l j) y +
         DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j ((0 : ChartMetricPerturbation E) l i) y -
         DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l ((0 : ChartMetricPerturbation E) i j) y) = 0 := by
    intro l
    have hlj : ((0 : ChartMetricPerturbation E) l j) = fun _ : E => (0 : ℝ) := rfl
    have hli : ((0 : ChartMetricPerturbation E) l i) = fun _ : E => (0 : ℝ) := rfl
    have hij : ((0 : ChartMetricPerturbation E) i j) = fun _ : E => (0 : ℝ) := rfl
    rw [hlj, hli, hij, partialDeriv_const, partialDeriv_const, partialDeriv_const]
    ring
  rw [Finset.sum_congr rfl (fun l _ => hzero l), Finset.sum_const_zero, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_zero ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_zero

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartLinearizedChristoffelPrincipal_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedChristoffelPrincipal (I := I) g α (h₁ + h₂) i j k y =
      chartLinearizedChristoffelPrincipal (I := I) g α h₁ i j k y +
        chartLinearizedChristoffelPrincipal (I := I) g α h₂ i j k y := by
  classical
  rw [chartLinearizedChristoffelPrincipal_def, chartLinearizedChristoffelPrincipal_def,
    chartLinearizedChristoffelPrincipal_def]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hi : DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i ((h₁ + h₂) l j) y =
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (h₁ l j) y + DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (h₂ l j) y := by
    have heq : ((h₁ + h₂) l j) = fun y => h₁ l j y + h₂ l j y := rfl
    rw [heq, partialDeriv_add _ _ (h₁.differentiableAt l j y) (h₂.differentiableAt l j y)]
  have hj : DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j ((h₁ + h₂) l i) y =
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (h₁ l i) y + DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (h₂ l i) y := by
    have heq : ((h₁ + h₂) l i) = fun y => h₁ l i y + h₂ l i y := rfl
    rw [heq, partialDeriv_add _ _ (h₁.differentiableAt l i y) (h₂.differentiableAt l i y)]
  have hl : DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l ((h₁ + h₂) i j) y =
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h₁ i j) y + DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h₂ i j) y := by
    have heq : ((h₁ + h₂) i j) = fun y => h₁ i j y + h₂ i j y := rfl
    rw [heq, partialDeriv_add _ _ (h₁.differentiableAt i j y) (h₂.differentiableAt i j y)]
  rw [hi, hj, hl]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_add ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_add

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartLinearizedChristoffelPrincipal_smul
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedChristoffelPrincipal (I := I) g α (c • h) i j k y =
      c • chartLinearizedChristoffelPrincipal (I := I) g α h i j k y := by
  classical
  rw [chartLinearizedChristoffelPrincipal_def, chartLinearizedChristoffelPrincipal_def,
    smul_eq_mul]
  have hsummand : ∀ l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α k l y *
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i ((c • h) l j) y +
         DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j ((c • h) l i) y -
         DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l ((c • h) i j) y) =
      c * (chartInvGramOnE (I := I) g α k l y *
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (h l j) y +
         DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (h l i) y -
         DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h i j) y)) := by
    intro l
    have hi : DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i ((c • h) l j) y =
        c * DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (h l j) y := by
      have heq : ((c • h) l j) = fun y => c • h l j y := rfl
      rw [heq, partialDeriv_const_smul c _ (h.differentiableAt l j y), smul_eq_mul]
    have hj : DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j ((c • h) l i) y =
        c * DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (h l i) y := by
      have heq : ((c • h) l i) = fun y => c • h l i y := rfl
      rw [heq, partialDeriv_const_smul c _ (h.differentiableAt l i y), smul_eq_mul]
    have hl : DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l ((c • h) i j) y =
        c * DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h i j) y := by
      have heq : ((c • h) i j) = fun y => c • h i j y := rfl
      rw [heq, partialDeriv_const_smul c _ (h.differentiableAt i j y), smul_eq_mul]
    rw [hi, hj, hl]
    ring
  rw [Finset.sum_congr rfl (fun l _ => hsummand l), ← Finset.mul_sum]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_smul ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_smul

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_contDiff_of_contDiff
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u) := by
  have hfderiv : ContDiff ℝ ∞ (fderiv ℝ u) :=
    hu.fderiv_right (by rw [ENat.coe_top_add_one])
  unfold DifferentialGeometry.Tensor.Coordinates.partialDeriv
  exact hfderiv.clm_apply contDiff_const

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_contDiff_of_contDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_contDiff_of_contDiff target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_perturbation_contDiff
    (h : ChartMetricPerturbation E) (i a b : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (h a b)) :=
  partialDeriv_contDiff_of_contDiff (h.smooth a b) i

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_perturbation_contDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_perturbation_contDiff target :: scope.openDecls } }

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartLinearizedChristoffelPrincipal_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y => chartLinearizedChristoffelPrincipal (I := I) g α h i j k y)
      (extChartAt I α).target := by
  classical
  have hsummand : ∀ l : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun y => chartInvGramOnE (I := I) g α k l y *
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (h l j) y +
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (h l i) y -
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h i j) y))
        (extChartAt I α).target := by
    intro l
    have hG : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α k l)
        (extChartAt I α).target :=
      chartInvGramOnE_contDiffOn (I := I) g α k l
    have hdi : ContDiffOn ℝ ∞ (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (h l j))
        (extChartAt I α).target :=
      (partialDeriv_perturbation_contDiff h i l j).contDiffOn
    have hdj : ContDiffOn ℝ ∞ (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (h l i))
        (extChartAt I α).target :=
      (partialDeriv_perturbation_contDiff h j l i).contDiffOn
    have hdl : ContDiffOn ℝ ∞ (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h i j))
        (extChartAt I α).target :=
      (partialDeriv_perturbation_contDiff h l i j).contDiffOn
    exact hG.mul ((hdi.add hdj).sub hdl)
  have hsum : ContDiffOn ℝ ∞
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (h l j) y +
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (h l i) y -
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h i j) y))
      (extChartAt I α).target :=
    ContDiffOn.sum (fun l _ => hsummand l)
  have hresult : ContDiffOn ℝ ∞
      (fun y => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (h l j) y +
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (h l i) y -
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h i j) y))
      (extChartAt I α).target :=
    contDiffOn_const.mul hsum
  refine hresult.congr (fun y _ => ?_)
  rw [chartLinearizedChristoffelPrincipal_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_contDiffOn ``Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartLinearizedChristoffelPrincipal_contDiffOn

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
