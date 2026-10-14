import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.LieHigherOrderCoefficientField

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

def deTurckMetricPrincipalDefectTotal (g₀ g : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 :=
  deTurckLieSecondOrderPrincipalCoeff (I := I) g₀ g
    + traceHessianCoeff (I := I) (M := M) g₀ g
    - (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g
        + ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.deTurckMetricPrincipalDefectTotal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.deTurckMetricPrincipalDefectTotal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.deTurckMetricPrincipalDefectTotal ``Submission.DifferentialGeometry.Analysis.Spectral.deTurckMetricPrincipalDefectTotal

private theorem trace_perm_comp (σ : Equiv.Perm (Fin 4)) (j : Fin 4) :
    traceHessianSlotPerm ((traceHessianSlotPerm⁻¹ * σ) j) = σ j := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.trace_perm_comp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.trace_perm_comp target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
  [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem lieTrace_reindex (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ ρ : Equiv.Perm (Fin 4))
    (hcomp : ∀ j : Fin 4, traceHessianSlotPerm (ρ j) = σ j) :
    deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ =
      reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2
        (traceHessianCoeff (I := I) (M := M) g₀ g₁) ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieTraceCoeff_toSection, reindexCoefficientInputSlots_toSection,
    traceHessianCoeff_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoefficientInputSlotsFiber_apply, deTurckLieTraceFib, traceHessianFib,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    domDomCongrFibPerm_apply, domDomCongrFib_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  have harg : ContinuousMultilinearMap.domDomCongr σ
      (Tensor0SBundle.Tensor0SSpace.toModel D) =
      ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
        (ContinuousMultilinearMap.domDomCongr ρ
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [ContinuousMultilinearMap.domDomCongr_apply]
    refine congrArg _ (funext fun j => ?_)
    rw [hcomp j]
  rw [harg]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.lieTrace_reindex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.lieTrace_reindex target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [I.Boundaryless] in
theorem deTurckMetricPrincipalDefectTotal_eq_reindex (g₀ g : SmoothRiemannianMetric I M) :
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g =
      reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2
          (traceHessianCoeff (I := I) (M := M) g₀ g)
          (traceHessianSlotPerm⁻¹ * deTurckLieSecondOrderDivSlotPermA)
        + reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2
          (traceHessianCoeff (I := I) (M := M) g₀ g)
          (traceHessianSlotPerm⁻¹ * deTurckLieSecondOrderDivSlotPermAT)
        - (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g
            + ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g) := by
  have hPhi : deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g =
      (deTurckLieTraceCoeff (I := I) (M := M) g₀ g deTurckLieSecondOrderDivSlotPermA
        + deTurckLieTraceCoeff (I := I) (M := M) g₀ g deTurckLieSecondOrderDivSlotPermAT
        - traceHessianCoeff (I := I) (M := M) g₀ g)
      + traceHessianCoeff (I := I) (M := M) g₀ g
      - (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g
          + ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g) := rfl
  rw [hPhi,
    lieTrace_reindex (I := I) (M := M) g₀ g deTurckLieSecondOrderDivSlotPermA
      (traceHessianSlotPerm⁻¹ * deTurckLieSecondOrderDivSlotPermA)
      (trace_perm_comp deTurckLieSecondOrderDivSlotPermA),
    lieTrace_reindex (I := I) (M := M) g₀ g deTurckLieSecondOrderDivSlotPermAT
      (traceHessianSlotPerm⁻¹ * deTurckLieSecondOrderDivSlotPermAT)
      (trace_perm_comp deTurckLieSecondOrderDivSlotPermAT)]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.deTurckMetricPrincipalDefectTotal_eq_reindex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.deTurckMetricPrincipalDefectTotal_eq_reindex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.deTurckMetricPrincipalDefectTotal_eq_reindex ``Submission.DifferentialGeometry.Analysis.Spectral.deTurckMetricPrincipalDefectTotal_eq_reindex

omit [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem deTurckMetricPrincipalDefectTotal_metricPerturbationPath_eq
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) =
      deTurckLieSecondOrderPrincipalCoeff (I := I) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
        - (linearizedRicciSecondOrderFieldLichnerowicz (I := I) g₀ T T' hδ hδ' s
            + linearizedRicciSecondOrderFieldLichnerowicz (I := I) g₀ T T' hδ hδ' s) := by
  rw [deTurckMetricPrincipalDefectTotal, linearizedRicciSecondOrderFieldLichnerowicz]
  set X : SmoothCcTensor g₀ 4 2 :=
    ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
  set Y : SmoothCcTensor g₀ 4 2 :=
    traceHessianCoeff (I := I) (M := M) g₀
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
  have hhalf : (1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Y = Y := by
    rw [← add_smul]
    norm_num
  have hgroup : (X - (1 / 2 : ℝ) • Y) + (X - (1 / 2 : ℝ) • Y) =
      (X + X) - ((1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Y) := by
    abel
  rw [hgroup, hhalf]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.deTurckMetricPrincipalDefectTotal_metricPerturbationPath_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.deTurckMetricPrincipalDefectTotal_metricPerturbationPath_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.deTurckMetricPrincipalDefectTotal_metricPerturbationPath_eq ``Submission.DifferentialGeometry.Analysis.Spectral.deTurckMetricPrincipalDefectTotal_metricPerturbationPath_eq

omit [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem deTurckMetricPrincipalDefectTotal_metricPerturbationPath_eq_neg_two_smul
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) =
      (-2 : ℝ) • linearizedRicciSecondOrderFieldLichnerowicz (I := I) g₀ T T' hδ hδ' s
        + deTurckLieSecondOrderPrincipalCoeff (I := I) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) := by
  rw [deTurckMetricPrincipalDefectTotal_metricPerturbationPath_eq (I := I) (M := M)
    g₀ T T' hδ hδ' s]
  rw [show (-2 : ℝ) • linearizedRicciSecondOrderFieldLichnerowicz (I := I) g₀ T T' hδ hδ' s =
      -(linearizedRicciSecondOrderFieldLichnerowicz (I := I) g₀ T T' hδ hδ' s
        + linearizedRicciSecondOrderFieldLichnerowicz (I := I) g₀ T T' hδ hδ' s) from by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, neg_smul, two_smul]]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.deTurckMetricPrincipalDefectTotal_metricPerturbationPath_eq_neg_two_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.deTurckMetricPrincipalDefectTotal_metricPerturbationPath_eq_neg_two_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.deTurckMetricPrincipalDefectTotal_metricPerturbationPath_eq_neg_two_smul ``Submission.DifferentialGeometry.Analysis.Spectral.deTurckMetricPrincipalDefectTotal_metricPerturbationPath_eq_neg_two_smul

end DifferentialGeometry.Analysis.Spectral
