import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ComponentFormula
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorReprFromFrame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
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

private def pouTsupport (α : M) : Set M :=
  tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport target :: scope.openDecls } }

private lemma abs_prod_kronecker_le_one
    {ι : Type*} (t : Finset ι) (f : ι → Prop) [DecidablePred f] :
    |∏ i ∈ t, (if f i then (1 : ℝ) else 0)| ≤ 1 := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert i t hi ih =>
      rw [Finset.prod_insert hi, abs_mul]
      by_cases hf : f i
      · rw [if_pos hf, abs_one, one_mul]; exact ih
      · rw [if_neg hf, abs_zero, _root_.MulZeroClass.zero_mul]; exact zero_le_one

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_prod_kronecker_le_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_prod_kronecker_le_one target :: scope.openDecls } }

private lemma abs_kronecker_le_one {P : Prop} [Decidable P] :
    |if P then (1 : ℝ) else 0| ≤ 1 := by
  by_cases h : P
  · rw [if_pos h, abs_one]
  · rw [if_neg h, abs_zero]; exact zero_le_one

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_kronecker_le_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_kronecker_le_one target :: scope.openDecls } }

private lemma abs_sum_coeff_kronecker_le
    {ι : Type*} (t : Finset ι) (f : ι → ℝ) (P : ι → Prop) [DecidablePred P]
    {Cχ : ℝ} (hCχ_nn : 0 ≤ Cχ) (hf : ∀ i ∈ t, |f i| ≤ Cχ) :
    |∑ i ∈ t, f i * (if P i then (1 : ℝ) else 0)| ≤ t.card * Cχ := by
  classical
  have hbound : ∀ i ∈ t,
      |f i * (if P i then (1 : ℝ) else 0)| ≤ Cχ := by
    intro i hi
    rw [abs_mul]
    calc |f i| * |if P i then (1 : ℝ) else 0|
        ≤ Cχ * 1 :=
          mul_le_mul (hf i hi) abs_kronecker_le_one (abs_nonneg _) hCχ_nn
      _ = Cχ := mul_one _
  calc |∑ i ∈ t, f i * (if P i then (1 : ℝ) else 0)|
      ≤ ∑ i ∈ t, |f i * (if P i then (1 : ℝ) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ t, Cχ := Finset.sum_le_sum hbound
    _ = t.card * Cχ := by rw [Finset.sum_const, nsmul_eq_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_sum_coeff_kronecker_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_sum_coeff_kronecker_le target :: scope.openDecls } }

omit [CompleteSpace E] in
private theorem exists_const_covDerivLowerOrderCoeff_bdd
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m : Fin (Module.finrank ℝ E))
        (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
        (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E))
        {y : EuclN},
        y ∈ chartTargetEuclid (I := I) (M := M) α →
        (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
          pouTsupport (I := I) (M := M) α →
        |covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
          Jdx Jdx' y| ≤ C := by
  classical
  obtain ⟨Cχ, hCχ_nn, hCχ⟩ :=
    chartChristoffel_bdd_on_pou_tsupport (I := I) (M := M) g α
  refine ⟨(r + s) * Cχ, by positivity, ?_⟩
  intro m Idx Idx' Jdx Jdx' y hy hb
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  have himg : extChartAt I α b ∈ (extChartAt I α) ''
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    ⟨b, hb, rfl⟩
  have hinput : ∀ k : Fin r,
      |inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y| ≤ Cχ := by
    intro k
    rw [inputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g r α m k
      Idx Idx' hy,
      chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel
        (I := I) (M := M) g α hb_base m (Idx k) (Idx' k),
      abs_mul]
    calc |chartChristoffel (I := I) g α (Idx' k) m (Idx k)
              (extChartAt I α b)| *
            |∏ i ∈ Finset.univ.erase k,
              (if Idx' i = Idx i then (1 : ℝ) else 0)|
        ≤ Cχ * 1 := by
          refine mul_le_mul (hCχ _ himg _ _ _)
            (abs_prod_kronecker_le_one _ _) (abs_nonneg _) hCχ_nn
      _ = Cχ := mul_one _
  have houtput : ∀ l : Fin s,
      |outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y| ≤ Cχ := by
    intro l
    rw [outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g s α m l
      Jdx Jdx' hy,
      chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel
        (I := I) (M := M) g α hb_base m (Jdx' l) (Jdx l),
      abs_mul]
    calc |chartChristoffel (I := I) g α (Jdx l) m (Jdx' l)
              (extChartAt I α b)| *
            |∏ j ∈ Finset.univ.erase l,
              (if Jdx j = Jdx' j then (1 : ℝ) else 0)|
        ≤ Cχ * 1 := by
          refine mul_le_mul (hCχ _ himg _ _ _)
            (abs_prod_kronecker_le_one _ _) (abs_nonneg _) hCχ_nn
      _ = Cχ := mul_one _
  have hsum_input :
      |∑ k : Fin r,
          inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y *
            (if Jdx' = Jdx then (1 : ℝ) else 0)| ≤ r * Cχ := by
    have h := abs_sum_coeff_kronecker_le (Finset.univ : Finset (Fin r))
      (fun k => inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y)
      (fun _ => Jdx' = Jdx) hCχ_nn (fun k _ => hinput k)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hsum_output :
      |∑ l : Fin s,
          outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y *
            (if Idx' = Idx then (1 : ℝ) else 0)| ≤ s * Cχ := by
    have h := abs_sum_coeff_kronecker_le (Finset.univ : Finset (Fin s))
      (fun l => outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y)
      (fun _ => Idx' = Idx) hCχ_nn (fun l _ => houtput l)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  rw [covDerivLowerOrderCoeff_def]
  have habs_sub : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
    intro a b
    calc |a - b| = |a + -b| := by rw [sub_eq_add_neg]
      _ ≤ |a| + |-b| := abs_add_le a (-b)
      _ = |a| + |b| := by rw [abs_neg]
  refine (habs_sub _ _).trans ?_
  have := add_le_add hsum_input hsum_output
  rw [add_mul]
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_covDerivLowerOrderCoeff_bdd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_covDerivLowerOrderCoeff_bdd target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartPushedRaw_pou_mul_raw_eq_component
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw (I := I) (M := M) α
          (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) y *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx y := by
  classical
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) hy,
    tensorChartComponent_def,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx) hy]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_pou_mul_raw_eq_component
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_pou_mul_raw_eq_component target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartPushedRaw_pou_mul_lowerOrderTerm_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw (I := I) (M := M) α
          (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) y *
        covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
          tensorChartComponent (I := I) (M := M) g r s S α p.1 p.2 y := by
  classical
  rw [covDerivComponent_lowerOrder_eq_linearCombination
    (I := I) (M := M) g r s S α m Idx Jdx y, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← mul_assoc, mul_comm (chartPushedRaw (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) y)
      (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y),
    mul_assoc,
    chartPushedRaw_pou_mul_raw_eq_component (I := I) (M := M) g r s S α
      p.1 p.2 hy]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_pou_mul_lowerOrderTerm_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_pou_mul_lowerOrderTerm_eq target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma tensorChartComponent_continuous'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Continuous (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) :=
  (tensorChartComponent_contMDiff (I := I) (M := M) g r s S α Idx Jdx).continuous

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_continuous'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_continuous' target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma mem_pouTsupport_of_tensorChartComponent_ne_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hne : tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx y ≠ 0) :
    y ∈ chartTargetEuclid (I := I) (M := M) α ∧
      (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        pouTsupport (I := I) (M := M) α := by
  classical
  have hy : y ∈ chartTargetEuclid (I := I) (M := M) α := by
    by_contra hy
    exact hne (by
      rw [tensorChartComponent_def,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy])
  refine ⟨hy, ?_⟩
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hval : tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx y =
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
    rw [tensorChartComponent_def,
      chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx) hy]
    rfl
  rw [hval] at hne
  have hρ_ne : (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b ≠ 0 := by
    intro hρ_zero
    exact hne (by rw [hρ_zero, _root_.MulZeroClass.zero_mul])
  exact subset_tsupport
    (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) hρ_ne

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_pouTsupport_of_tensorChartComponent_ne_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_pouTsupport_of_tensorChartComponent_ne_zero target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma eLpNorm_coeff_mul_component_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E))
    {Ccoeff : ℝ} (hCcoeff_nn : 0 ≤ Ccoeff)
    (hCcoeff : ∀ {y : EuclN},
      y ∈ chartTargetEuclid (I := I) (M := M) α →
      (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        pouTsupport (I := I) (M := M) α →
      |covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
        Jdx Jdx' y| ≤ Ccoeff) :
    _root_.MeasureTheory.eLpNorm
        (fun y : EuclN =>
          covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
              Jdx Jdx' y *
            tensorChartComponent (I := I) (M := M) g r s S α Idx' Jdx' y) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      ENNReal.ofReal Ccoeff *
        eLpNorm (tensorChartComponent (I := I) (M := M) g r s S α Idx' Jdx') 2
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set μ : _root_.MeasureTheory.Measure EuclN :=
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)
  set comp : EuclN → ℝ :=
    tensorChartComponent (I := I) (M := M) g r s S α Idx' Jdx' with hcomp_def
  have hpt : ∀ y : EuclN,
      ‖covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
            Jdx Jdx' y * comp y‖ ≤
        ‖(Ccoeff : ℝ) • comp y‖ := by
    intro y
    rw [Real.norm_eq_abs, abs_mul, smul_eq_mul, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg hCcoeff_nn]
    by_cases hcz : comp y = 0
    · rw [hcz, abs_zero, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.mul_zero]
    · obtain ⟨hy, hb⟩ :=
        mem_pouTsupport_of_tensorChartComponent_ne_zero
          (I := I) (M := M) g r s S α Idx' Jdx' (by rw [← hcomp_def]; exact hcz)
      exact mul_le_mul_of_nonneg_right (hCcoeff hy hb) (abs_nonneg _)
  calc _root_.MeasureTheory.eLpNorm
          (fun y : EuclN =>
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
                Jdx Jdx' y * comp y) 2 μ
      ≤ _root_.MeasureTheory.eLpNorm ((Ccoeff : ℝ) • comp) 2 μ := _root_.MeasureTheory.eLpNorm_mono hpt
    _ = ‖(Ccoeff : ℝ)‖ₑ * _root_.MeasureTheory.eLpNorm comp 2 μ :=
        _root_.MeasureTheory.eLpNorm_const_smul (Ccoeff : ℝ) comp 2 _
    _ = ENNReal.ofReal Ccoeff * _root_.MeasureTheory.eLpNorm comp 2 μ := by
        rw [Real.enorm_eq_ofReal hCcoeff_nn]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_coeff_mul_component_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_coeff_mul_component_le target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem exists_const_sum_eLpNorm_pou_covDerivLowerOrderTerm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      ∑ m : Fin (Module.finrank ℝ E),
        _root_.MeasureTheory.eLpNorm
          (fun y : EuclN =>
            chartPushedRaw (I := I) (M := M) α
                (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) y *
              covDerivLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
                m Idx Jdx y) 2
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨Ccoeff, hCcoeff_nn, hCcoeff⟩ :=
    exists_const_covDerivLowerOrderCoeff_bdd (I := I) (M := M) g r s α
  obtain ⟨Ccomp, hCcomp_nn, hCcomp⟩ :=
    tensorChartComponent_eLpNorm_le_uniform (I := I) (M := M) g r s α
  set n : ℕ := Module.finrank ℝ E with hn_def
  set Npair : ℕ := Fintype.card ((Fin r → Fin n) × (Fin s → Fin n))
    with hNpair_def
  refine ⟨n * (Npair * (Ccoeff * Ccomp)), by positivity, ?_⟩
  intro S Idx Jdx
  set μ : _root_.MeasureTheory.Measure EuclN :=
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)
    with hμ_def
  have hμ_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  have hdir : ∀ m : Fin n,
      _root_.MeasureTheory.eLpNorm
          (fun y : EuclN =>
            chartPushedRaw (I := I) (M := M) α
                (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) y *
              covDerivLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
                m Idx Jdx y) 2 μ ≤
        ENNReal.ofReal (Npair * (Ccoeff * Ccomp)) * (‖S‖₊ : ℝ≥0∞) := by
    intro m
    have hae :
        (fun y : EuclN =>
            chartPushedRaw (I := I) (M := M) α
                (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) y *
              covDerivLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
                m Idx Jdx y)
          =ᵐ[μ]
        ∑ p : (Fin r → Fin n) × (Fin s → Fin n),
          (fun y : EuclN =>
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                Jdx p.2 y *
              tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α
                p.1 p.2 y) := by
      rw [hμ_def]
      refine (_root_.MeasureTheory.ae_restrict_iff' hμ_meas).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      rw [Finset.sum_apply]
      exact chartPushedRaw_pou_mul_lowerOrderTerm_eq
        (I := I) (M := M) g r s S.toCcTensor α m Idx Jdx hy
    rw [_root_.MeasureTheory.eLpNorm_congr_ae hae]
    have hmeas : ∀ p : (Fin r → Fin n) × (Fin s → Fin n),
        _root_.MeasureTheory.AEStronglyMeasurable
          (fun y : EuclN =>
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                Jdx p.2 y *
              tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α
                p.1 p.2 y) μ := by
      intro p
      rw [hμ_def]
      have hcont_on : ContinuousOn
          (fun y : EuclN =>
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                Jdx p.2 y *
              tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α
                p.1 p.2 y)
          (chartTargetEuclid (I := I) (M := M) α) := by
        refine ContinuousOn.mul ?_ ?_
        · exact (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
            g r s α m Idx p.1 Jdx p.2).continuousOn
        · exact (tensorChartComponent_continuous' (I := I) (M := M)
            g r s S.toCcTensor α p.1 p.2).continuousOn
      exact hcont_on.aestronglyMeasurable hμ_meas
    have hcomp_h1 : ∀ p : (Fin r → Fin n) × (Fin s → Fin n),
        eLpNorm (tensorChartComponent (I := I) (M := M)
            g r s S.toCcTensor α p.1 p.2) 2 μ ≤
          ENNReal.ofReal Ccomp * (‖S‖₊ : ℝ≥0∞) := by
      intro p
      rw [hμ_def]
      have hb := hCcomp S.toCcTensor p.1 p.2
      rw [chartLebesgueMeasure] at hb
      refine hb.trans (mul_le_mul_of_nonneg_left ?_ (zero_le))
      rw [show ((‖S‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖S‖ from by
        rw [show ((‖S‖₊ : ℝ≥0∞)) = ‖S‖ₑ from (enorm_eq_nnnorm S).symm,
          ← ofReal_norm S]]
      exact ENNReal.ofReal_le_ofReal
        (SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S)
    have hsummand : ∀ p : (Fin r → Fin n) × (Fin s → Fin n),
        _root_.MeasureTheory.eLpNorm
            (fun y : EuclN =>
              covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                  Jdx p.2 y *
                tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α
                  p.1 p.2 y) 2 μ ≤
          ENNReal.ofReal (Ccoeff * Ccomp) * (‖S‖₊ : ℝ≥0∞) := by
      intro p
      have h1 :
          _root_.MeasureTheory.eLpNorm
              (fun y : EuclN =>
                covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                    Jdx p.2 y *
                  tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α
                    p.1 p.2 y) 2 μ ≤
            ENNReal.ofReal Ccoeff *
              eLpNorm (tensorChartComponent (I := I) (M := M)
                g r s S.toCcTensor α p.1 p.2) 2 μ := by
        rw [hμ_def]
        exact eLpNorm_coeff_mul_component_le (I := I) (M := M) g r s
          S.toCcTensor α m Idx p.1 Jdx p.2 hCcoeff_nn
          (fun {y} hy hb => hCcoeff m Idx p.1 Jdx p.2 hy hb)
      refine (h1.trans
        (mul_le_mul_of_nonneg_left (hcomp_h1 p) (zero_le))).trans_eq ?_
      rw [ENNReal.ofReal_mul hCcoeff_nn, mul_assoc]
    refine (_root_.MeasureTheory.eLpNorm_sum_le (fun p _ => hmeas p) (by norm_num)).trans ?_
    refine (Finset.sum_le_sum (fun p _ => hsummand p)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, ← hNpair_def, nsmul_eq_mul]
    rw [show ((Npair : ℝ≥0∞)) = ENNReal.ofReal (Npair : ℝ) from by
      rw [ENNReal.ofReal_natCast]]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  refine (Finset.sum_le_sum (fun m _ => hdir m)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show ((n : ℝ≥0∞)) = ENNReal.ofReal (n : ℝ) from by
    rw [ENNReal.ofReal_natCast]]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_pou_covDerivLowerOrderTerm_le_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_pou_covDerivLowerOrderTerm_le_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_pou_covDerivLowerOrderTerm_le_uniform ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_pou_covDerivLowerOrderTerm_le_uniform

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
