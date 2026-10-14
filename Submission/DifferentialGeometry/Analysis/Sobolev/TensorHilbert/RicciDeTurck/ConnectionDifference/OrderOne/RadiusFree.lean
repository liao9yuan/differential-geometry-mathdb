import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.GridWindow.OperatorComposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Integral.Connection

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Integral.Connection.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Connection.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Connection.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem permAppEqRs (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) :
    ccOperatorFieldComp (I := I) (M := M) g r s s
        (slotPermCc (I := I) (M := M) g σ) S =
      rsDomDomCongrSection (I := I) (M := M) g r s σ S := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  rw [operatorFieldComposition_toSection, ContinuousLinearMap.comp_apply,
    rsDomDomCongrSection_toSection]
  change Tensor0SSpace.toModel
      (slotPermCLM (I := I) σ x
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          S.toSection x) D)) =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (S.toSection x)) D)
  rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel,
    toModel_rsDomDomCongr_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.permAppEqRs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.permAppEqRs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.permAppEqRs ``Submission.DifferentialGeometry.Integral.Connection.permAppEqRs

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem linearizedRicciConnectionDifferenceOrderOneKernel_expansion (g₀ g₁ : SmoothRiemannianMetric I M) :
    linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g₀ g₁ =
      -(reindexCoefficientInputSlots (I := I) (M := M) g₀ 3 4
          (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm0312
            (connectionDifferenceContravariantInsertionField (I := I) g₀ g₁)) kInPerm102
        + reindexCoefficientInputSlots (I := I) (M := M) g₀ 3 4
            (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm0213
              (connectionDifferenceContravariantInsertionField (I := I) g₀ g₁)) kInPerm120
        + rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm2301
            (connectionDifferenceContravariantInsertionField (I := I) g₀ g₁)
        + reindexCoefficientInputSlots (I := I) (M := M) g₀ 3 4
            (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm1302
              (connectionDifferenceContravariantInsertionField (I := I) g₀ g₁)) kInPerm102
        + reindexCoefficientInputSlots (I := I) (M := M) g₀ 3 4
            (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm1203
              (connectionDifferenceContravariantInsertionField (I := I) g₀ g₁)) kInPerm120) := by
  rw [kernelField_eq_neg_term_combination (I := I) (M := M) g₀ g₁]
  simp only [permAppEqRs, kInPerm102, kInPerm120]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.linearizedRicciConnectionDifferenceOrderOneKernel_expansion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.linearizedRicciConnectionDifferenceOrderOneKernel_expansion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.linearizedRicciConnectionDifferenceOrderOneKernel_expansion ``Submission.DifferentialGeometry.Integral.Connection.linearizedRicciConnectionDifferenceOrderOneKernel_expansion

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma iteratedCovGradSmul (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Connection.iteratedCovGradSmul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Connection.iteratedCovGradSmul target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSqSmul (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Connection.riemannianFiberNormSqSmul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Connection.riemannianFiberNormSqSmul target :: scope.openDecls } }

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma riemannianFiberNormSqNegIteratedCovGrad (g : SmoothRiemannianMetric I M) {r s : ℕ} (l : ℕ) (x : M)
    (X : SmoothCcTensor g r s) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + l) x
        ((iteratedCovGrad (I := I) g r s l (-X)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + l) x
        ((iteratedCovGrad (I := I) g r s l X).toSection x) := by
  have hneg : (-X) = (-1 : ℝ) • X := by
    rw [neg_smul, one_smul]
  rw [hneg, iteratedCovGradSmul, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
    Pi.smul_apply, riemannianFiberNormSqSmul]
  norm_num

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Connection.riemannianFiberNormSqNegIteratedCovGrad
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Connection.riemannianFiberNormSqNegIteratedCovGrad target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
private lemma riemannianFiberNormSqTermEq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (l : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 3 4 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 σ
            (connectionDifferenceContravariantInsertionField (I := I) g₀ g₁))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 3 4 l
          (connectionDifferenceContravariantInsertionField (I := I) g₀ g₁)).toSection x) :=
  riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 3 4 σ
    (connectionDifferenceContravariantInsertionField (I := I) g₀ g₁)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 σ
      (connectionDifferenceContravariantInsertionField (I := I) g₀ g₁))
    (fun y d => by
      rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) l x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Connection.riemannianFiberNormSqTermEq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Connection.riemannianFiberNormSqTermEq target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem insertAntidiagonalTupleGridWindow (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Cins : ℕ → ℝ, (∀ l, 0 ≤ Cins l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 3 4 l
              (connectionDifferenceContravariantInsertionField (I := I) g₀ g₁)).toSection x) ≤
          Cins l * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (l + 2) := by
  classical
  obtain ⟨Ccd, hCcd_nn, hcd⟩ := riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_antidiagonalTupleGridWindow_rf (I := I) (M := M) g₀ hδ₀
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine ⟨fun l => (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * Ccd l),
    fun l => mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCcd_nn l)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ l x
  rw [connectionDifferenceContravariantInsertionField_eq_reindex_slotExtend_two (I := I) (M := M) g₀ g₁]
  rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoefficientInputSlots_eq (I := I) (M := M) g₀ 3 4
    (slotExtend (I := I) (M := M) g₀ 2 3
      (slotExtend (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀)))
    connectionDifferenceContrInsertionReindexPerm l x]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 3
    (slotExtend (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀)) l x) ?_
  refine le_trans (mul_le_mul_of_nonneg_left
    (riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2
      (connectionDifferenceSection (I := I) g₁ g₀) l x) hfr_nn) ?_
  have hgb : Combinatorics.antidiagonalTupleGridWindow
        (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (l + 2) =
      Combinatorics.antidiagonalTupleGridWindow
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (l + 2) := rfl
  rw [hgb]
  set W : ℝ := Combinatorics.antidiagonalTupleGridWindow
    (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (l + 2) with hW_def
  calc (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (connectionDifferenceSection (I := I) g₁ g₀)).toSection x))
      ≤ (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (Ccd l * W)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (hcd g₁ P htie hδ_le hδ0 hδ l x) hfr_nn) hfr_nn
    _ = (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * Ccd l) * W := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.insertAntidiagonalTupleGridWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.insertAntidiagonalTupleGridWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.insertAntidiagonalTupleGridWindow ``Submission.DifferentialGeometry.Integral.Connection.insertAntidiagonalTupleGridWindow

omit [SigmaCompactSpace M] in
theorem ricciKerAntidiagonalTupleGridWindow (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kk : ℕ → ℝ, (∀ l, 0 ≤ Kk l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 3 4 l
              (linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g₀ g₁)).toSection x) ≤
          Kk l * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (l + 2) := by
  classical
  obtain ⟨Cins, hCins_nn, hins⟩ := insertAntidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀
  refine ⟨fun l => 46 * Cins l, fun l => by have := hCins_nn l; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ l x
  set O : SmoothCcTensor g₀ 3 4 := connectionDifferenceContravariantInsertionField (I := I) g₀ g₁ with hO_def
  set A0 : SmoothCcTensor g₀ 3 4 :=
    reindexCoefficientInputSlots (I := I) (M := M) g₀ 3 4
      (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm0312 O) kInPerm102 with hA0_def
  set A1 : SmoothCcTensor g₀ 3 4 :=
    reindexCoefficientInputSlots (I := I) (M := M) g₀ 3 4
      (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm0213 O) kInPerm120 with hA1_def
  set A2 : SmoothCcTensor g₀ 3 4 :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm2301 O with hA2_def
  set A3 : SmoothCcTensor g₀ 3 4 :=
    reindexCoefficientInputSlots (I := I) (M := M) g₀ 3 4
      (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm1302 O) kInPerm102 with hA3_def
  set A4 : SmoothCcTensor g₀ 3 4 :=
    reindexCoefficientInputSlots (I := I) (M := M) g₀ 3 4
      (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm1203 O) kInPerm120 with hA4_def
  set F : SmoothCcTensor g₀ 3 4 → ℝ := fun X =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 3 4 l X).toSection x) with hF_def
  have hFnn : ∀ X, 0 ≤ F X := fun X => riemannianFiberNormSq_nonneg _ _ _ _ _
  have hFadd : ∀ X Y : SmoothCcTensor g₀ 3 4, F (X + Y) ≤ 2 * F X + 2 * F Y := by
    intro X Y
    simp only [hF_def]
    rw [iteratedCovGrad_add (I := I) g₀ 3 4 l X Y, SmoothCcTensor.toSection_add,
      ContMDiffSection.coe_add, Pi.add_apply]
    exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 (4 + l) x _ _
  have harm : ∀ (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      F (reindexCoefficientInputSlots (I := I) (M := M) g₀ 3 4
        (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 σ O) ρ) = F O := by
    intro σ ρ
    simp only [hF_def]
    rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoefficientInputSlots_eq (I := I) (M := M) g₀ 3 4
      (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 σ O) ρ l x]
    exact riemannianFiberNormSqTermEq (I := I) (M := M) g₀ g₁ σ l x
  have h0 : F A0 = F O := harm _ _
  have h1 : F A1 = F O := harm _ _
  have h2 : F A2 = F O := riemannianFiberNormSqTermEq (I := I) (M := M) g₀ g₁ kOutPerm2301 l x
  have h3 : F A3 = F O := harm _ _
  have h4 : F A4 = F O := harm _ _
  have hOnn : 0 ≤ F O := hFnn O
  have hsum : F (A0 + A1 + A2 + A3 + A4) ≤ 46 * F O := by
    have s01 := hFadd A0 A1
    have s012 := hFadd (A0 + A1) A2
    have s0123 := hFadd (A0 + A1 + A2) A3
    have s01234 := hFadd (A0 + A1 + A2 + A3) A4
    rw [h0, h1] at s01
    rw [h2] at s012
    rw [h3] at s0123
    rw [h4] at s01234
    linarith
  have hker : F (linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g₀ g₁) =
      F (A0 + A1 + A2 + A3 + A4) := by
    rw [linearizedRicciConnectionDifferenceOrderOneKernel_expansion (I := I) (M := M) g₀ g₁]
    simp only [hF_def, ← hO_def, ← hA0_def, ← hA1_def, ← hA2_def, ← hA3_def, ← hA4_def]
    exact riemannianFiberNormSqNegIteratedCovGrad (I := I) (M := M) g₀ l x (A0 + A1 + A2 + A3 + A4)
  change F (linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g₀ g₁) ≤ _
  rw [hker]
  refine hsum.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hins g₁ P htie hδ_le hδ0 hδ l x) (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.ricciKerAntidiagonalTupleGridWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.ricciKerAntidiagonalTupleGridWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.ricciKerAntidiagonalTupleGridWindow ``Submission.DifferentialGeometry.Integral.Connection.ricciKerAntidiagonalTupleGridWindow

end DifferentialGeometry.Integral.Connection

end
