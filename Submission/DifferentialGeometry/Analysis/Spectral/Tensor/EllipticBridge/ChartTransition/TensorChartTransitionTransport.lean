import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.ChartTransitionTransportCLM

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

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

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma coeFn_finsetSum_chartL2
    (α : M) {ι : Type*} (s : Finset ι)
    (G : ι → _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
    (((∑ a ∈ s, G a) : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
        EuclN → ℝ)
      =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, ((G a : EuclN → ℝ) y) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero _ _ _
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      refine (Lp.coeFn_add (G a) (∑ b ∈ t, G b)).trans ?_
      filter_upwards [ih] with y hy
      rw [Pi.add_apply, hy, Finset.sum_insert ha]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coeFn_finsetSum_chartL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coeFn_finsetSum_chartL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coeFn_finsetSum_chartL2 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coeFn_finsetSum_chartL2

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportChartCenters_finite (α : M) :
    {β : M |
        (Function.support
            (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          tsupport
            ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
              M → ℝ)).Nonempty}.Finite := by
  classical
  have hlf : LocallyFinite
      (fun β : M =>
        Function.support
          (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    (chartAtlasPOU I M).locallyFinite
  have hcompact : IsCompact
      (tsupport
        ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
    chartKernelCutoff_hasCompactSupport (I := I) (M := M) α
  exact hlf.finite_nonempty_inter_compact hcompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportChartCenters_finite
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportChartCenters_finite target :: scope.openDecls } }

def transportChartCenters (α : M) : Finset M :=
  (transportChartCenters_finite (I := I) (M := M) α).toFinset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportChartCenters then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportChartCenters"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportChartCenters ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportChartCenters

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma mem_transportChartCenters (α β : M) :
    β ∈ transportChartCenters (I := I) (M := M) α ↔
      (Function.support
          (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
        tsupport
          ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
            M → ℝ)).Nonempty := by
  unfold transportChartCenters
  rw [Set.Finite.mem_toFinset]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_transportChartCenters then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_transportChartCenters"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_transportChartCenters ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_transportChartCenters

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma mem_transportChartCenters_of_pou_cutoff_ne
    (α β : M) {x : M}
    (hβ : ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≠ 0)
    (hα : ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≠ 0) :
    β ∈ transportChartCenters (I := I) (M := M) α := by
  rw [mem_transportChartCenters]
  exact ⟨x, hβ, subset_tsupport _ hα⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_transportChartCenters_of_pou_cutoff_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_transportChartCenters_of_pou_cutoff_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_transportChartCenters_of_pou_cutoff_ne ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_transportChartCenters_of_pou_cutoff_ne

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma sum_chartAtlasPOU_transportChartCenters_eq_one
    (α : M) {x : M}
    (hα : ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≠ 0) :
    ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1 := by
  classical
  have hsubset :
      (chartAtlasPOU I M).finsupport x ⊆
        transportChartCenters (I := I) (M := M) α := by
    intro β hβ
    rw [SmoothPartitionOfUnity.mem_finsupport] at hβ
    exact mem_transportChartCenters_of_pou_cutoff_ne
      (I := I) (M := M) α β hβ hα
  exact (chartAtlasPOU I M).sum_finsupport' x (Set.mem_univ x) hsubset

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sum_chartAtlasPOU_transportChartCenters_eq_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sum_chartAtlasPOU_transportChartCenters_eq_one target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma pou_smul_raw_eq_transition_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (β α : M)
    (P₀ : TensorCompIdx (E := E) r s) {x : M}
    (hx_α : x ∈ (chartAt H α).source) :
    ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        tensorChartComponentRaw (I := I) (M := M) g r s S α P₀.1 P₀.2 x =
      ∑ Q : TensorCompIdx (E := E) r s,
        ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
          transitionCoeff (E := E) (I := I) (M := M) r s β α P₀ Q x *
            tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x := by
  classical
  by_cases hβ : ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0
  · rw [hβ, _root_.MulZeroClass.zero_mul]
    refine (Finset.sum_eq_zero (fun Q _ => ?_)).symm
    unfold tensorChartComponentPou
    rw [hβ]
    ring
  · have hx_support : x ∈
        tsupport
          (fun y : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) :=
      subset_tsupport _ hβ
    have hx_β : x ∈ (chartAt H β).source :=
      chartAtlasPOU_isSubordinate I M β hx_support
    have hχβ : ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) :
        M → ℝ) x = 1 :=
      chartKernelCutoff_eqOn_one (I := I) (M := M) β hx_support
    have hdecomp :=
      tensorChartComponentRaw_eq_transitionCoeff_sum
        (E := E) (I := I) (M := M) g r s S β α P₀ ⟨hx_β, hx_α⟩
    rw [hdecomp, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    unfold tensorChartComponentPou
    rw [hχβ]
    ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pou_smul_raw_eq_transition_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pou_smul_raw_eq_transition_sum target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentScalar_eq_pou_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) (x : M) :
    cutoffComponentScalar (I := I) (M := M) g r s S α P₀.1 P₀.2 x =
      ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          transportCoeffManifold (I := I) (M := M) r s β α P₀ Q x *
            tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x := by
  classical
  unfold cutoffComponentScalar
  set χα : ℝ := ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
    M → ℝ) x with hχα_def
  by_cases hχα : χα = 0
  · rw [hχα, _root_.MulZeroClass.zero_mul]
    refine (Finset.sum_eq_zero (fun β _ => Finset.sum_eq_zero (fun Q _ => ?_))).symm
    rw [transportCoeffManifold_apply]
    rw [show ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
          = χα from rfl, hχα]
    ring
  · have hx_support : x ∈
        tsupport
          ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      subset_tsupport _ hχα
    have hx_α : x ∈ (chartAt H α).source :=
      chartKernelCutoff_tsupport_subset_source (I := I) (M := M) α hx_support
    have h_rhs :
        (∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            transportCoeffManifold (I := I) (M := M) r s β α P₀ Q x *
              tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x) =
        χα *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ∑ Q : TensorCompIdx (E := E) r s,
              ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) :
                  M → ℝ) x *
                transitionCoeff (E := E) (I := I) (M := M) r s β α P₀ Q x *
                tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun β _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      rw [transportCoeffManifold_apply,
        show ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
          = χα from rfl]
      ring
    rw [h_rhs]
    have h_inner :
        (∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) :
                M → ℝ) x *
              transitionCoeff (E := E) (I := I) (M := M) r s β α P₀ Q x *
              tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x) =
        ∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
            tensorChartComponentRaw (I := I) (M := M) g r s S α P₀.1 P₀.2 x := by
      refine Finset.sum_congr rfl (fun β _ => ?_)
      exact (pou_smul_raw_eq_transition_sum
        (I := I) (M := M) g r s S β α P₀ hx_α).symm
    rw [h_inner, ← Finset.sum_mul,
      sum_chartAtlasPOU_transportChartCenters_eq_one (I := I) (M := M) α hχα,
      one_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentScalar_eq_pou_transport_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentScalar_eq_pou_transport_sum target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartPushedRaw_finsetSum
    (α : M) {ι : Type*} (s : Finset ι) (F : ι → M → ℝ) (y : EuclN) :
    chartPushedRaw I α (fun x : M => ∑ a ∈ s, F a x) y =
      ∑ a ∈ s, chartPushedRaw I α (F a) y := by
  classical
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]
    refine (Finset.sum_eq_zero (fun a _ => ?_)).symm
    rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_finsetSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_finsetSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_finsetSum ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_finsetSum

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentEuclid_eq_pou_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) (y : EuclN) :
    cutoffComponentEuclid (I := I) (M := M) g r s S α P₀.1 P₀.2 y =
      ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          chartPushedRaw I α
            (fun x : M =>
              transportCoeffManifold (I := I) (M := M) r s β α P₀ Q x *
                tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x)
            y := by
  classical
  rw [cutoffComponentEuclid_eq_chartPushedRaw (I := I) (M := M) g r s S α
    P₀.1 P₀.2]
  have h_scalar :
      cutoffComponentScalar (I := I) (M := M) g r s S α P₀.1 P₀.2 =
        fun x : M =>
          ∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ∑ Q : TensorCompIdx (E := E) r s,
              transportCoeffManifold (I := I) (M := M) r s β α P₀ Q x *
                tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x := by
    funext x
    exact cutoffComponentScalar_eq_pou_transport_sum
      (I := I) (M := M) g r s S α P₀ x
  rw [h_scalar]
  rw [chartPushedRaw_finsetSum (I := I) (M := M) α
    (transportChartCenters (I := I) (M := M) α)
    (fun β x => ∑ Q : TensorCompIdx (E := E) r s,
      transportCoeffManifold (I := I) (M := M) r s β α P₀ Q x *
        tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x) y]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  exact chartPushedRaw_finsetSum (I := I) (M := M) α
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q x => transportCoeffManifold (I := I) (M := M) r s β α P₀ Q x *
      tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x) y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_eq_pou_transport_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_eq_pou_transport_sum target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma finsetSum_ae_eq
    (α : M) {ι : Type*} (s : Finset ι) {f h : ι → EuclN → ℝ}
    (hfh : ∀ a ∈ s,
      f a =ᵐ[chartLebesgueMeasure (I := I) (M := M) α] h a) :
    (fun y => ∑ a ∈ s, f a y) =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, h a y := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      have hfh_a : f a =ᵐ[chartLebesgueMeasure (I := I) (M := M) α] h a :=
        hfh a (Finset.mem_insert_self a t)
      have hfh_t : ∀ b ∈ t,
          f b =ᵐ[chartLebesgueMeasure (I := I) (M := M) α] h b :=
        fun b hb => hfh b (Finset.mem_insert_of_mem hb)
      filter_upwards [hfh_a, ih hfh_t] with y hya hyt
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hya, hyt]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.finsetSum_ae_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.finsetSum_ae_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.finsetSum_ae_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.finsetSum_ae_eq

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorL2ChartComponentCutoff_smooth_eq_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (S : TensorL2 r s g) α P₀ =
      ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (S : TensorL2 r s g) β Q) := by
  classical
  apply Lp.ext
  refine (tensorL2ChartComponentCutoff_smoothToTensorL2_coeFn
    (I := I) (M := M) g r s S α P₀).trans ?_
  have h_rhs_coeFn :
      ((∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q
              (tensorL2ChartComponent (I := I) (M := M) g r s
                (S : TensorL2 r s g) β Q)) :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) =ᵐ[
          chartLebesgueMeasure (I := I) (M := M) α]
        fun y => ∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            chartPushedRaw I α
              (fun x : M =>
                transportCoeffManifold (I := I) (M := M) r s β α P₀ Q x *
                  tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x)
              y := by
    refine (coeFn_finsetSum_chartL2 (I := I) (M := M) α
      (transportChartCenters (I := I) (M := M) α)
      (fun β => ∑ Q : TensorCompIdx (E := E) r s,
        chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s
            (S : TensorL2 r s g) β Q))).trans ?_
    refine finsetSum_ae_eq (I := I) (M := M) α
      (transportChartCenters (I := I) (M := M) α) (fun β _ => ?_)
    refine (coeFn_finsetSum_chartL2 (I := I) (M := M) α
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q => chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (S : TensorL2 r s g) β Q))).trans ?_
    refine finsetSum_ae_eq (I := I) (M := M) α
      (Finset.univ : Finset (TensorCompIdx (E := E) r s)) (fun Q _ => ?_)
    exact chartTransitionTransportCLM_coeFn_smooth
      (I := I) (M := M) g r s β α S P₀ Q
  have h_pointwise :
      cutoffComponentEuclid (I := I) (M := M) g r s S α P₀.1 P₀.2 =
        fun y => ∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            chartPushedRaw I α
              (fun x : M =>
                transportCoeffManifold (I := I) (M := M) r s β α P₀ Q x *
                  tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x)
              y := by
    funext y
    exact cutoffComponentEuclid_eq_pou_transport_sum
      (I := I) (M := M) g r s S α P₀ y
  rw [h_pointwise]
  exact h_rhs_coeFn.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_smooth_eq_transport_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_smooth_eq_transport_sum target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma continuous_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    Continuous (fun u : TensorL2 r s g =>
      ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s u β Q)) := by
  classical
  refine continuous_finsetSum _ (fun β _ => ?_)
  refine continuous_finsetSum _ (fun Q _ => ?_)
  exact (chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q).continuous.comp
    (continuous_tensorL2ChartComponent (I := I) (M := M) g r s β Q)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.continuous_transport_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.continuous_transport_sum target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
theorem tensorL2ChartComponentCutoff_eq_pou_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ =
      ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) := by
  classical
  set lhs : TensorL2 r s g → _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
    fun v => tensorL2ChartComponentCutoff (I := I) (M := M) g r s v α P₀
    with hlhs_def
  set rhs : TensorL2 r s g → _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
    fun v => ∑ β ∈ transportChartCenters (I := I) (M := M) α,
      ∑ Q : TensorCompIdx (E := E) r s,
        chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s v β Q)
    with hrhs_def
  suffices h_eq : lhs = rhs by
    exact congrFun h_eq u
  have h_lhs_cont : Continuous lhs := by
    rw [hlhs_def]
    have h_fun : (fun v : TensorL2 r s g =>
        tensorL2ChartComponentCutoff (I := I) (M := M) g r s v α P₀) =
        (tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀) := by
      funext v
      rw [tensorL2ChartComponentCutoffCLM_apply]
    rw [h_fun]
    exact (tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀).continuous
  have h_rhs_cont : Continuous rhs := by
    rw [hrhs_def]
    exact continuous_transport_sum (I := I) (M := M) g r s α P₀
  have h_denseRange :
      DenseRange ((↑) : SmoothCcTensor g r s → TensorL2 r s g) :=
    UniformSpace.Completion.denseRange_coe
  refine h_denseRange.equalizer h_lhs_cont h_rhs_cont ?_
  funext S
  rw [Function.comp_apply, Function.comp_apply, hlhs_def, hrhs_def]
  exact tensorL2ChartComponentCutoff_smooth_eq_transport_sum
    (I := I) (M := M) g r s S α P₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_eq_pou_transport_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_eq_pou_transport_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_eq_pou_transport_sum ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_eq_pou_transport_sum

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
theorem tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ)
      =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      (fun y => ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          ((chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q
              (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
  classical
  rw [tensorL2ChartComponentCutoff_eq_pou_transport_sum
    (I := I) (M := M) g r s u α P₀]
  refine (coeFn_finsetSum_chartL2 (I := I) (M := M) α
    (transportChartCenters (I := I) (M := M) α)
    (fun β => ∑ Q : TensorCompIdx (E := E) r s,
      chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q
        (tensorL2ChartComponent (I := I) (M := M) g r s u β Q))).trans ?_
  refine finsetSum_ae_eq (I := I) (M := M) α
    (transportChartCenters (I := I) (M := M) α) (fun β _ => ?_)
  exact coeFn_finsetSum_chartL2 (I := I) (M := M) α
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q => chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q
      (tensorL2ChartComponent (I := I) (M := M) g r s u β Q))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
