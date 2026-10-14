import Mathlib.Analysis.Normed.Operator.NormedSpace
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Application.SecondOrderSobolevBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.SymmetricRaiseEndomorphism
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.FiberNormJets
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.ReindexingNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricH2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricH2 target :: scope.openDecls } }

private abbrev rank4H2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 4 (2 : ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rank4H2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rank4H2 target :: scope.openDecls } }

private abbrev rank4End (g : SmoothRiemannianMetric I M) :=
  rank4H2 (I := I) (M := M) g →L[ℝ] rank4H2 (I := I) (M := M) g

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rank4End
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rank4End target :: scope.openDecls } }

private local instance rank4EndNorm
    (g : SmoothRiemannianMetric I M) :
    NormedAddCommGroup (rank4End (I := I) (M := M) g) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rank4EndNorm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rank4EndNorm target :: scope.openDecls } }

private local instance rank4EndSpace
    (g : SmoothRiemannianMetric I M) :
    NormedSpace ℝ (rank4End (I := I) (M := M) g) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rank4EndSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rank4EndSpace target :: scope.openDecls } }

def metricPerturbationCoefficientH2
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 4 4 :=
  slotInsertEndoCc (I := I) (M := M) g 3
    (symmRaiseEndo (I := I) (M := M) g T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricPerturbationCoefficientH2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricPerturbationCoefficientH2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricPerturbationCoefficientH2 ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricPerturbationCoefficientH2

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma perturbCoeff4_add
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2) :
      metricPerturbationCoefficientH2 (I := I) (M := M) g (T + U) =
      metricPerturbationCoefficientH2 (I := I) (M := M) g T +
        metricPerturbationCoefficientH2 (I := I) (M := M) g U := by
  simp only [metricPerturbationCoefficientH2, symmRaiseEndo_add, slotInsertEndoCc_add]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.perturbCoeff4_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.perturbCoeff4_add target :: scope.openDecls } }

omit [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma perturbCoeff4_smul
    (g : SmoothRiemannianMetric I M) (a : ℝ) (T : SmoothCcTensor g 0 2) :
    metricPerturbationCoefficientH2 (I := I) (M := M) g (a • T) =
      a • metricPerturbationCoefficientH2 (I := I) (M := M) g T := by
  simp only [metricPerturbationCoefficientH2, symmRaiseEndo_smul, slotInsertEndoCc_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.perturbCoeff4_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.perturbCoeff4_smul target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma perm_iteratedCovGrad_norm
    (g : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 2))
    (T : SmoothCcTensor g 0 2) (k : ℕ) :
    ‖iteratedCovGrad (I := I) g 0 2 k
        (domDomCongrSection (I := I) g σ T)‖ =
      ‖iteratedCovGrad (I := I) g 0 2 k T‖ := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g
  have hbridge : ∀ W : SmoothCcTensor g 0 2,
      ‖iteratedCovGrad (I := I) g 0 2 k W‖ ^ 2 =
        ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (2 + k) x
          ((iteratedCovGrad (I := I) g 0 2 k W).toSection x) ∂μ := by
    intro W
    rw [SmoothCcTensor.norm_def (I := I) (M := M)
      (iteratedCovGrad (I := I) g 0 2 k W)]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
      (I := I) (M := M) g (2 + k)
        (iteratedCovGrad (I := I) g 0 2 k W)
  have hintegrand : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (2 + k) x
          ((iteratedCovGrad (I := I) g 0 2 k
            (domDomCongrSection (I := I) g σ T)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 0 (2 + k) x
          ((iteratedCovGrad (I := I) g 0 2 k T).toSection x) :=
    fun x => riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g (s := 2) σ T k x
  have hsq :
      ‖iteratedCovGrad (I := I) g 0 2 k
          (domDomCongrSection (I := I) g σ T)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g 0 2 k T‖ ^ 2 := by
    rw [hbridge (domDomCongrSection (I := I) g σ T), hbridge T]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall hintegrand)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.perm_iteratedCovGrad_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.perm_iteratedCovGrad_norm target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma symm_iteratedCovGrad_norm
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) (k : ℕ) :
    ‖iteratedCovGrad (I := I) g 0 2 k
        (ccTensor02Symm (I := I) (M := M) g T)‖ ≤
      ‖iteratedCovGrad (I := I) g 0 2 k T‖ := by
  classical
  let Tsw : SmoothCcTensor g 0 2 :=
    domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T
  have hiter :
      iteratedCovGrad (I := I) g 0 2 k
          (ccTensor02Symm (I := I) (M := M) g T) =
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k T +
          (1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k Tsw := by
    dsimp only [Tsw]
    exact iteratedCovGrad_ccTensor02Symm_eq (I := I) (M := M) g T k
  rw [hiter]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul]
  have habs : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by
    rw [Real.norm_eq_abs]
    norm_num
  rw [habs]
  have hperm :
      ‖iteratedCovGrad (I := I) g 0 2 k Tsw‖ =
        ‖iteratedCovGrad (I := I) g 0 2 k T‖ := by
    exact perm_iteratedCovGrad_norm (I := I) (M := M) g
      (Equiv.swap (0 : Fin 2) 1) T k
  rw [hperm]
  have hnn : 0 ≤ ‖iteratedCovGrad (I := I) g 0 2 k T‖ := norm_nonneg _
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.symm_iteratedCovGrad_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.symm_iteratedCovGrad_norm target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma raise_iteratedCovGrad_norm
    (g : SmoothRiemannianMetric I M) (s i : ℕ)
    (W : SmoothCcTensor g 0 (s + 2)) :
    ‖iteratedCovGrad (I := I) g 1 (s + 1) i
        (cometricRaiseSlot0Field (I := I) (M := M) g s W)‖ =
      ‖iteratedCovGrad (I := I) g 0 (s + 2) i W‖ := by
  have hsq :
      ‖iteratedCovGrad (I := I) g 1 (s + 1) i
          (cometricRaiseSlot0Field (I := I) (M := M) g s W)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g 0 (s + 2) i W‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => ?_)
    exact riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq
      (I := I) (M := M) g s W i x
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.raise_iteratedCovGrad_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.raise_iteratedCovGrad_norm target :: scope.openDecls } }

private lemma insert3_iteratedCovGrad_le
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (i : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ‖iteratedCovGrad (I := I) g 4 4 i
        (slotInsertEndoCc (I := I) (M := M) g 3 Λ)‖ ≤
      27 * ‖iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ := by
  classical
  set F : M → ℝ := fun x => 27 *
    riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
      ((iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x) with hF
  have hFint : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g 1 (1 + i)
        (iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ))).const_mul _
  have hpt : ∀ x,
      riemannianFiberNormSq (I := I) (M := M) g 4 (4 + i) x
          ((iteratedCovGrad (I := I) g 4 4 i
            (slotInsertEndoCc (I := I) (M := M) g 3 Λ)).toSection x) ≤
        F x := by
    intro x
    have h := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo
      (I := I) (M := M) g 3 Λ i x
    rw [hDim] at h
    norm_num at h
    simpa only [F, Nat.reduceAdd] using h
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g 4 (4 + i)
      (iteratedCovGrad (I := I) g 4 4 i
        (slotInsertEndoCc (I := I) (M := M) g 3 Λ)) F hFint hpt
  have hint :
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
          ((iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g 1 (1 + i)]
  rw [hF, MeasureTheory.integral_const_mul, hint] at hsq
  refine le_of_sq_le_sq ?_
    (mul_nonneg (by norm_num) (norm_nonneg _))
  calc
    ‖iteratedCovGrad (I := I) g 4 4 i
        (slotInsertEndoCc (I := I) (M := M) g 3 Λ)‖ ^ 2
        ≤ 27 * ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := hsq
    _ ≤ (27 * ‖iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖) ^ 2 := by
      nlinarith [sq_nonneg
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.insert3_iteratedCovGrad_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.insert3_iteratedCovGrad_le target :: scope.openDecls } }

private theorem perturbCc_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : SmoothCcTensor g 0 2,
      ‖appHs (I := I) (M := M) g 4 4 2
          (metricPerturbationCoefficientH2 (I := I) (M := M) g T)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ := by
  classical
  obtain ⟨Cin, hCin, hin⟩ := hsJet_le (I := I) (M := M) g 2 2
  obtain ⟨Capp, hCapp, happ⟩ :=
    appHs_h2_norm (I := I) (M := M) hDim g 4 4
  let C : ℝ := Capp * 27 * Cin
  refine ⟨C, by
    dsimp only [C]
    positivity, ?_⟩
  intro T
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let A : ℝ := 27 * (Cin * N)
  have hN : 0 ≤ N := norm_nonneg _
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hper : ∀ j,
      ‖iteratedCovGrad (I := I) g 4 4 j
          (metricPerturbationCoefficientH2 (I := I) (M := M) g T)‖ ≤
        27 * ‖iteratedCovGrad (I := I) g 0 2 j T‖ := by
    intro j
    let Λ := symmRaiseEndo (I := I) (M := M) g T
    have hslot := insert3_iteratedCovGrad_le (I := I) (M := M) hDim g j Λ
    have hbase :
        ‖iteratedCovGrad (I := I) g 1 1 j
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ≤
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ := by
      rw [show slotInsertEndoCc (I := I) (M := M) g 0 Λ =
          cometricRaiseSlot0Field (I := I) (M := M) g 0
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1)
              (ccTensor02Symm (I := I) (M := M) g T)) from by
        simpa only [Λ] using
          insert_symmRaise_eq (I := I) (M := M) g T]
      calc
        _ = ‖iteratedCovGrad (I := I) g 0 2 j
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1)
              (ccTensor02Symm (I := I) (M := M) g T))‖ := by
              simpa only [Nat.zero_add, Nat.reduceAdd] using
                raise_iteratedCovGrad_norm (I := I) (M := M) g 0 j
                  (domDomCongrSection (I := I) g
                    (Equiv.swap (0 : Fin 2) 1)
                    (ccTensor02Symm (I := I) (M := M) g T))
        _ = ‖iteratedCovGrad (I := I) g 0 2 j
            (ccTensor02Symm (I := I) (M := M) g T)‖ := by
              exact perm_iteratedCovGrad_norm (I := I) (M := M) g
                (Equiv.swap (0 : Fin 2) 1)
                (ccTensor02Symm (I := I) (M := M) g T) j
        _ ≤ _ := symm_iteratedCovGrad_norm (I := I) (M := M) g T j
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hbase (by norm_num))
    simpa only [metricPerturbationCoefficientH2, Λ] using hslot
  have hsum :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 4 4 j
            (metricPerturbationCoefficientH2 (I := I) (M := M) g T)‖ ≤
        A := by
    calc
      _ ≤ ∑ j ∈ Finset.range 3,
          27 * ‖iteratedCovGrad (I := I) g 0 2 j T‖ :=
        Finset.sum_le_sum fun j _ => hper j
      _ = 27 * ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ := by
        rw [Finset.mul_sum]
      _ ≤ 27 * (Cin * N) :=
        mul_le_mul_of_nonneg_left (by
          have h := hin T
          rw [show (((2 : ℕ) : ℝ)) = 2 by norm_num] at h
          simpa only [N, Nat.reduceAdd] using h) (by norm_num)
      _ = A := rfl
  have hsq :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 4 j
          (metricPerturbationCoefficientH2 (I := I) (M := M) g T)‖ ^ 2) ≤ A ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 4 4 j
            (metricPerturbationCoefficientH2 (I := I) (M := M) g T)‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg
          (fun j _ => norm_nonneg _)
      _ ≤ A ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hsum 2
  have hop := happ
    (metricPerturbationCoefficientH2 (I := I) (M := M) g T) A hA hsq
  calc
    _ ≤ Capp * A := hop
    _ = C * N := by
      dsimp only [A, C]
      ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.perturbCc_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.perturbCc_bound target :: scope.openDecls } }

private noncomputable def perturbCcLin
    (g : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 0 2 →ₗ[ℝ]
      rank4End (I := I) (M := M) g where
  toFun := fun T =>
    appHs (I := I) (M := M) g 4 4 2
      (metricPerturbationCoefficientH2 (I := I) (M := M) g T)
  map_add' := fun T U => by
    apply ContinuousLinearMap.ext
    intro V
    rw [perturbCoeff4_add, appHs_add, add_apply]
  map_smul' := fun a T => by
    apply ContinuousLinearMap.ext
    intro V
    simpa only [RingHom.id_apply, smul_apply,
      perturbCoeff4_smul] using
      appHs_smul (I := I) (M := M) g 4 4 2 a
        (metricPerturbationCoefficientH2 (I := I) (M := M) g T) V

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.perturbCcLin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.perturbCcLin target :: scope.openDecls } }

noncomputable def metricPerturbationOperatorH2
    (g : SmoothRiemannianMetric I M) :
    metricH2 (I := I) (M := M) g →L[ℝ]
      rank4End (I := I) (M := M) g :=
  LinearMap.extendOfNorm (σ₁₂ := RingHom.id ℝ)
    (perturbCcLin (I := I) (M := M) g)
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricPerturbationOperatorH2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricPerturbationOperatorH2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricPerturbationOperatorH2 ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricPerturbationOperatorH2

theorem metricPerturbationOperatorH2_apply_smoothCore
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    metricPerturbationOperatorH2 (I := I) (M := M) g
        (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T) =
      appHs (I := I) (M := M) g 4 4 2
        (metricPerturbationCoefficientH2 (I := I) (M := M) g T) := by
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  change
    ((perturbCcLin (I := I) (M := M) g).extendOfNorm
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)))
        ((ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) T) =
      perturbCcLin (I := I) (M := M) g T
  apply LinearMap.extendOfNorm_eq hdense
  obtain ⟨C, _, hC⟩ := perturbCc_bound (I := I) (M := M) hDim g
  exact ⟨C, hC⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricPerturbationOperatorH2_apply_smoothCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricPerturbationOperatorH2_apply_smoothCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricPerturbationOperatorH2_apply_smoothCore ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricPerturbationOperatorH2_apply_smoothCore

theorem metricPerturbationOperatorH2_norm_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : metricH2 (I := I) (M := M) g,
        ‖metricPerturbationOperatorH2 (I := I) (M := M) g T‖ ≤ C * ‖T‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    perturbCc_bound (I := I) (M := M) hDim g
  refine ⟨C, hC, fun T => ?_⟩
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hop : ‖metricPerturbationOperatorH2 (I := I) (M := M) g‖ ≤ C := by
    unfold metricPerturbationOperatorH2
    apply LinearMap.opNorm_extendOfNorm_le hdense hC
    exact hbound
  calc
    _ ≤ ‖metricPerturbationOperatorH2 (I := I) (M := M) g‖ * ‖T‖ :=
      (metricPerturbationOperatorH2 (I := I) (M := M) g).le_opNorm T
    _ ≤ C * ‖T‖ :=
      mul_le_mul_of_nonneg_right hop (norm_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricPerturbationOperatorH2_norm_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricPerturbationOperatorH2_norm_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricPerturbationOperatorH2_norm_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricPerturbationOperatorH2_norm_bound

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
