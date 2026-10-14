import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.Coefficient.L2JetMoser
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.LieHigherOrderCoefficientField
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.FiberNorm
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.SymmetricCoefficientBounds
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Iterated.Linear
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Algebra

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (traceHessianCoeff traceHessianCoeff_toSection traceHessianFib traceHessianSlotPerm
    domDomCongrFib domDomCongrFib_apply reindexCoefficientInputSlots reindexCoefficientInputSlots_toSection
    reindexCoefficientInputSlotsFiber reindexCoefficientInputSlotsFiber_apply riemannianFiberNormSq_reindexCoefficientInputSlotsFiber
    deTurckLieTraceCoeff deTurckLieTraceCoeff_toSection deTurckLieTraceFib
    domDomCongrFibPerm domDomCongrFibPerm_apply deTurckLieSecondOrderDivSlotPermA
    deTurckLieSecondOrderDivSlotPermAT deTurckLieSecondOrderPrincipalCoeff
    exists_lichnerowicz_cometric_metricPerturbationPath_riemannianFiberNormSq_ballUniform)
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization (metricPerturbationPath)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private theorem traceHessianSlotPerm_inv_mul_apply (σ : Equiv.Perm (Fin 4)) (j : Fin 4) :
    traceHessianSlotPerm ((traceHessianSlotPerm⁻¹ * σ) j) = σ j := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.traceHessianSlotPerm_inv_mul_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.traceHessianSlotPerm_inv_mul_apply target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem deTurckLieTraceCoeff_eq_reindex_traceHessianCoeff
    (g₀ g₁ : SmoothRiemannianMetric I M) (σ ρ : Equiv.Perm (Fin 4))
    (hcomp : ∀ j : Fin 4, traceHessianSlotPerm (ρ j) = σ j) :
    deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ =
      reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2
        (traceHessianCoeff (I := I) (M := M) g₀ g₁) ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieTraceCoeff_toSection, reindexCoefficientInputSlots_toSection, traceHessianCoeff_toSection]
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
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieTraceCoeff_eq_reindex_traceHessianCoeff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.deTurckLieTraceCoeff_eq_reindex_traceHessianCoeff target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private theorem riemannianFiberNormSq_toSection_reindexCoefficientInputSlots_eq
    (g₀ : SmoothRiemannianMetric I M) (R : SmoothCcTensor g₀ 4 2)
    (ρ : Equiv.Perm (Fin 4)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2 R ρ).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R.toSection x) := by
  rw [reindexCoefficientInputSlots_toSection]
  exact riemannianFiberNormSq_reindexCoefficientInputSlotsFiber (I := I) (M := M) g₀ 4 2 x ρ
    (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      R.toSection x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.riemannianFiberNormSq_toSection_reindexCoefficientInputSlots_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.riemannianFiberNormSq_toSection_reindexCoefficientInputSlots_eq target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem riemannianFiberNormSq_neg_local
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.riemannianFiberNormSq_neg_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.riemannianFiberNormSq_neg_local target :: scope.openDecls } }

theorem deTurckLieSecondOrderPrincipalCoeff_metricPerturbationPath_jetL2_perOrder_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (deTurckLieSecondOrderPrincipalCoeff (I := I) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤ P i := by
  obtain ⟨Q, hQ_nn, hQ⟩ :=
    traceHessianCoeff_metricPerturbationPath_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  refine ⟨fun i => 9 * Q i, fun i => by linarith [hQ_nn i], ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  set g₁ : SmoothRiemannianMetric I M := metricPerturbationPath (I := I) g₀ T T' hδ hδ' s with hg₁
  have hH : ‖iteratedCovGrad (I := I) g₀ 4 2 i
      (traceHessianCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ Q i := by
    rw [hg₁]
    exact hQ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
  have hA : ‖iteratedCovGrad (I := I) g₀ 4 2 i
      (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieSecondOrderDivSlotPermA)‖ ^ 2 ≤ Q i := by
    rw [deTurckLieTraceCoeff_eq_reindex_traceHessianCoeff (I := I) (M := M) g₀ g₁
        deTurckLieSecondOrderDivSlotPermA (traceHessianSlotPerm⁻¹ * deTurckLieSecondOrderDivSlotPermA)
        (traceHessianSlotPerm_inv_mul_apply deTurckLieSecondOrderDivSlotPermA),
      norm_sq_iteratedCovGrad_reindexCoefficientInputSlots_eq]
    exact hH
  have hAT : ‖iteratedCovGrad (I := I) g₀ 4 2 i
      (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieSecondOrderDivSlotPermAT)‖ ^ 2 ≤ Q i := by
    rw [deTurckLieTraceCoeff_eq_reindex_traceHessianCoeff (I := I) (M := M) g₀ g₁
        deTurckLieSecondOrderDivSlotPermAT (traceHessianSlotPerm⁻¹ * deTurckLieSecondOrderDivSlotPermAT)
        (traceHessianSlotPerm_inv_mul_apply deTurckLieSecondOrderDivSlotPermAT),
      norm_sq_iteratedCovGrad_reindexCoefficientInputSlots_eq]
    exact hH
  have hdecomp : iteratedCovGrad (I := I) g₀ 4 2 i
      (deTurckLieSecondOrderPrincipalCoeff (I := I) g₀ g₁)
      = iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieSecondOrderDivSlotPermA)
        + iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieSecondOrderDivSlotPermAT)
        - iteratedCovGrad (I := I) g₀ 4 2 i
          (traceHessianCoeff (I := I) (M := M) g₀ g₁) := by
    rw [deTurckLieSecondOrderPrincipalCoeff, iteratedCovGrad_sub, iteratedCovGrad_add]
  rw [hdecomp]
  set X := iteratedCovGrad (I := I) g₀ 4 2 i
    (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieSecondOrderDivSlotPermA) with hX
  set Y := iteratedCovGrad (I := I) g₀ 4 2 i
    (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieSecondOrderDivSlotPermAT) with hY
  set Z := iteratedCovGrad (I := I) g₀ 4 2 i
    (traceHessianCoeff (I := I) (M := M) g₀ g₁) with hZ
  have htri : ‖X + Y - Z‖ ≤ ‖X‖ + ‖Y‖ + ‖Z‖ :=
    le_trans (norm_sub_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
  nlinarith only [htri, hA, hAT, hH, norm_nonneg X, norm_nonneg Y, norm_nonneg Z,
    norm_nonneg (X + Y - Z), sq_nonneg (‖X‖ - ‖Y‖), sq_nonneg (‖X‖ - ‖Z‖),
    sq_nonneg (‖Y‖ - ‖Z‖),
    mul_le_mul htri htri (norm_nonneg (X + Y - Z))
      (add_nonneg (add_nonneg (norm_nonneg X) (norm_nonneg Y)) (norm_nonneg Z))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.deTurckLieSecondOrderPrincipalCoeff_metricPerturbationPath_jetL2_perOrder_ballUniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.deTurckLieSecondOrderPrincipalCoeff_metricPerturbationPath_jetL2_perOrder_ballUniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.deTurckLieSecondOrderPrincipalCoeff_metricPerturbationPath_jetL2_perOrder_ballUniform ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieSecondOrderPrincipalCoeff_metricPerturbationPath_jetL2_perOrder_ballUniform

omit [BoundarylessManifold I M] in
theorem deTurckLieSecondOrderPrincipalCoeff_metricPerturbationPath_riemannianFiberNormSq_order0_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    {R : ℝ}
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
              ((deTurckLieSecondOrderPrincipalCoeff (I := I) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λ := by
  obtain ⟨Λcom, hΛ_nn, hΛ⟩ :=
    exists_lichnerowicz_cometric_metricPerturbationPath_riemannianFiberNormSq_ballUniform (I := I) (M := M) g₀ a (R := R) hδ₀
  refine ⟨10 * Λcom, by linarith, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  set g₁ : SmoothRiemannianMetric I M := metricPerturbationPath (I := I) g₀ T T' hδ hδ' s with hg₁
  have hH : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x) ≤ Λcom := by
    rw [hg₁]
    exact (hΛ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁
        deTurckLieSecondOrderDivSlotPermA).toSection x) ≤ Λcom := by
    rw [deTurckLieTraceCoeff_eq_reindex_traceHessianCoeff (I := I) (M := M) g₀ g₁
        deTurckLieSecondOrderDivSlotPermA (traceHessianSlotPerm⁻¹ * deTurckLieSecondOrderDivSlotPermA)
        (traceHessianSlotPerm_inv_mul_apply deTurckLieSecondOrderDivSlotPermA),
      riemannianFiberNormSq_toSection_reindexCoefficientInputSlots_eq]
    exact hH
  have hAT : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁
        deTurckLieSecondOrderDivSlotPermAT).toSection x) ≤ Λcom := by
    rw [deTurckLieTraceCoeff_eq_reindex_traceHessianCoeff (I := I) (M := M) g₀ g₁
        deTurckLieSecondOrderDivSlotPermAT (traceHessianSlotPerm⁻¹ * deTurckLieSecondOrderDivSlotPermAT)
        (traceHessianSlotPerm_inv_mul_apply deTurckLieSecondOrderDivSlotPermAT),
      riemannianFiberNormSq_toSection_reindexCoefficientInputSlots_eq]
    exact hH
  have hsec : (deTurckLieSecondOrderPrincipalCoeff (I := I) g₀ g₁).toSection x
      = (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁
            deTurckLieSecondOrderDivSlotPermA).toSection x
        + (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁
            deTurckLieSecondOrderDivSlotPermAT).toSection x
        - (traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x := by
    rw [deTurckLieSecondOrderPrincipalCoeff, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
      Pi.sub_apply, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  rw [hsec, sub_eq_add_neg]
  have h1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 4 2 x
    ((deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁
        deTurckLieSecondOrderDivSlotPermA).toSection x
      + (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁
        deTurckLieSecondOrderDivSlotPermAT).toSection x)
    (-(traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x)
  have h2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 4 2 x
    ((deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁
        deTurckLieSecondOrderDivSlotPermA).toSection x)
    ((deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁
        deTurckLieSecondOrderDivSlotPermAT).toSection x)
  have hneg := riemannianFiberNormSq_neg_local (I := I) (M := M) g₀ 4 2 x
    ((traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x)
  linarith [h1, h2, hneg, hA, hAT, hH]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.deTurckLieSecondOrderPrincipalCoeff_metricPerturbationPath_riemannianFiberNormSq_order0_ballUniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.deTurckLieSecondOrderPrincipalCoeff_metricPerturbationPath_riemannianFiberNormSq_order0_ballUniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.deTurckLieSecondOrderPrincipalCoeff_metricPerturbationPath_riemannianFiberNormSq_order0_ballUniform ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieSecondOrderPrincipalCoeff_metricPerturbationPath_riemannianFiberNormSq_order0_ballUniform

end DifferentialGeometry.Analysis.Sobolev

end
