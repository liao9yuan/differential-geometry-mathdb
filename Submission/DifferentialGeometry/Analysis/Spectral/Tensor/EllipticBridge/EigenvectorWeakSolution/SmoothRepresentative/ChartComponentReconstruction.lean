import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.SmoothRepresentative.ChartComponentTransport
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.PouComponentBound.PouCutoffComponentBridge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

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

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

private lemma ae_eq_of_ae_eq_restrict_of_eqOn_compl
    {X : Type*} [MeasurableSpace X] {μ : _root_.MeasureTheory.Measure X}
    {f h : X → ℝ} {t : Set X} (ht : MeasurableSet t)
    (h_restrict : f =ᵐ[μ.restrict t] h)
    (h_compl : ∀ x, x ∉ t → f x = h x) :
    f =ᵐ[μ] h := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  have h_diff_subset : {x | ¬ f x = h x} ⊆ t := by
    intro x hx
    by_contra hxt
    exact hx (h_compl x hxt)
  have h_inter : {x | ¬ f x = h x} = {x | ¬ f x = h x} ∩ t :=
    (Set.inter_eq_left.mpr h_diff_subset).symm
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at h_restrict
  rw [MeasureTheory.Measure.restrict_apply₀'] at h_restrict
  · rwa [h_inter]
  · exact ht.nullMeasurableSet

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ae_eq_of_ae_eq_restrict_of_eqOn_compl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ae_eq_of_ae_eq_restrict_of_eqOn_compl target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportChartCenters_subset_chartAtlasPOU_finset (β : M) :
    transportChartCenters (I := I) (M := M) β ⊆
      chartAtlasPOUFinset (I := I) (M := M) := by
  intro γ hγ
  rw [mem_transportChartCenters] at hγ
  rw [chartAtlasPOU_finset_mem]
  exact hγ.mono (Set.inter_subset_left)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportChartCenters_subset_chartAtlasPOU_finset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportChartCenters_subset_chartAtlasPOU_finset target :: scope.openDecls } }

private lemma ite_finsetSum_eq_finsetSum_ite
    {ι : Type*} (t : Finset ι) (p : Prop) [Decidable p] (f : ι → ℝ) :
    (if p then ∑ a ∈ t, f a else 0) = ∑ a ∈ t, (if p then f a else 0) := by
  by_cases hp : p
  · simp only [if_pos hp]
  · simp only [if_neg hp, Finset.sum_const_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ite_finsetSum_eq_finsetSum_ite
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ite_finsetSum_eq_finsetSum_ite target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartPushedPouWeight_toEuclidean_extChartAt
    (α : M) {z : M} (hz : z ∈ (chartAt H α).source) :
    chartPushedPouWeight (I := I) (M := M) α
        ((toEuclidean (E := E)) (extChartAt I α z)) =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) z := by
  unfold chartPushedPouWeight
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _
      (toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) α hz),
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) α hz]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedPouWeight_toEuclidean_extChartAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedPouWeight_toEuclidean_extChartAt target :: scope.openDecls } }

open _root_.Classical in
open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
private lemma chartPushedRaw_ite_transitionSum_eq_finsetSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α β : M) (P₀ : TensorCompIdx (E := E) r s) (y : EuclN) :
    chartPushedRaw I β
        (fun x => if x ∈ (chartAt H α).source then
          ∑ Q : TensorCompIdx (E := E) r s,
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
                α Q.1 Q.2 x
          else 0) y =
      ∑ Q : TensorCompIdx (E := E) r s,
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
                α Q.1 Q.2 x
          else 0) y := by
  classical
  have h_ite :
      (fun x => if x ∈ (chartAt H α).source then
          ∑ Q : TensorCompIdx (E := E) r s,
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
                α Q.1 Q.2 x
          else 0) =
        fun x => ∑ Q : TensorCompIdx (E := E) r s,
          (if x ∈ (chartAt H α).source then
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
                α Q.1 Q.2 x
          else 0) := by
    funext x
    exact ite_finsetSum_eq_finsetSum_ite (Finset.univ) _ _
  rw [h_ite]
  exact chartPushedRaw_finsetSum (I := I) (M := M) β
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q x => if x ∈ (chartAt H α).source then
      transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
        tensorChartComponentRaw (I := I) (M := M) g r s
          (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
          α Q.1 Q.2 x
    else 0) y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_ite_transitionSum_eq_finsetSum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_ite_transitionSum_eq_finsetSum target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
private lemma eigenvectorSmoothChart_tensorL2ChartComponent_eq_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α β : M) (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s i α :
          TensorL2 r s g) β P₀ :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ)
      =ᵐ[chartLebesgueMeasure (I := I) (M := M) β]
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ∑ Q : TensorCompIdx (E := E) r s,
          ((chartTransitionTransportCLM (I := I) (M := M) r s α β P₀ Q
              (tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i)
                α Q) :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
            EuclN → ℝ) y) := by
  classical
  refine (eigenvectorSmoothChart_tensorL2ChartComponent_coeFn_aeEq
    (I := I) (M := M) g r s i α β P₀).trans ?_
  have h_push : ∀ y : EuclN,
      chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            ∑ Q : TensorCompIdx (E := E) r s,
              transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
                tensorChartComponentRaw (I := I) (M := M) g r s
                  (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
                  α Q.1 Q.2 x
            else 0) y =
        ∑ Q : TensorCompIdx (E := E) r s,
          (chartPushedRaw I β
              (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
            chartPushedRaw I β
              (fun x => if x ∈ (chartAt H α).source then
                transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
                  tensorChartComponentRaw (I := I) (M := M) g r s
                    (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
                    α Q.1 Q.2 x
              else 0) y) := by
    intro y
    rw [chartPushedRaw_ite_transitionSum_eq_finsetSum
      (I := I) (M := M) g r s i α β P₀ y, Finset.mul_sum]
  have h_terms : ∀ Q : TensorCompIdx (E := E) r s,
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
                α Q.1 Q.2 x
          else 0) y)
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) β]
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ((chartTransitionTransportCLM (I := I) (M := M) r s α β P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i)
              α Q) :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y) :=
    fun Q => eigenvectorSmoothChart_transport_term_aeEq
      (I := I) (M := M) g r s i β α P₀ Q
  have h_sum := finsetSum_ae_eq (I := I) (M := M) β
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q _ => h_terms Q)
  refine Filter.EventuallyEq.trans (Filter.EventuallyEq.of_eq (funext h_push)) ?_
  refine h_sum.trans (Filter.EventuallyEq.of_eq ?_)
  funext y
  rw [Finset.mul_sum]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmoothChart_tensorL2ChartComponent_eq_transport_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmoothChart_tensorL2ChartComponent_eq_transport_sum target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
private lemma eigenvectorChartComponentFun_ite_chartPushedPouWeight_zero_ae_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (Q : TensorCompIdx (E := E) r s) :
    (fun y => if chartPushedPouWeight (I := I) (M := M) α y = 0 then
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s i α Q y
      else 0)
      =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  filter_upwards [eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero
    (I := I) (M := M) g r s i α Q] with y hy
  by_cases hw : chartPushedPouWeight (I := I) (M := M) α y = 0
  · rw [if_pos hw]
    exact hy hw
  · rw [if_neg hw]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentFun_ite_chartPushedPouWeight_zero_ae_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentFun_ite_chartPushedPouWeight_zero_ae_zero target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
private lemma chartTransitionTransportCLM_eigenvector_ae_zero_of_notMem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α β : M) (P₀ Q : TensorCompIdx (E := E) r s)
    (hα : α ∉ transportChartCenters (I := I) (M := M) β) :
    ((chartTransitionTransportCLM (I := I) (M := M) r s α β P₀ Q
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α Q) :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ)
      =ᵐ[chartLebesgueMeasure (I := I) (M := M) β]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have h_coeFn := chartTransitionTransportCLM_coeFn_aeEq (I := I) (M := M) r s α β P₀ Q (tensorL2ChartComponent (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i) α Q)
  refine h_coeFn.trans ?_
  have hΩ_open : IsOpen (chartOverlapEuclid (I := I) (M := M) β α) :=
    chartOverlapEuclid_isOpen (I := I) (M := M) β α
  have hΩ_meas : MeasurableSet (chartOverlapEuclid (I := I) (M := M) β α) :=
    hΩ_open.measurableSet
  have h_restrict_eq :
      (chartLebesgueMeasure (I := I) (M := M) β).restrict
        (chartOverlapEuclid (I := I) (M := M) β α) =
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartOverlapEuclid (I := I) (M := M) β α) := by
    rw [chartLebesgueMeasure, Measure.restrict_restrict hΩ_meas,
      Set.inter_eq_left.mpr
        (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β α)]
  have h_on_overlap :
      (fun y => chartPushedRaw (I := I) (M := M) β
          (transportCoeffManifold (I := I) (M := M) r s α β P₀ Q) y *
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α Q)
          (chartTransitionEuclid (I := I) (M := M) β α y))
        =ᵐ[(chartLebesgueMeasure (I := I) (M := M) β).restrict
            (chartOverlapEuclid (I := I) (M := M) β α)]
      (fun _ : EuclN => (0 : ℝ)) := by
    rw [h_restrict_eq]
    have h_gate_target :=
      eigenvectorChartComponentFun_ite_chartPushedPouWeight_zero_ae_zero
        (I := I) (M := M) g r s i α Q
    have h_gate_overlap :
        (fun y => if chartPushedPouWeight (I := I) (M := M) α y = 0 then
            eigenvectorChartComponentFun (I := I) (M := M)
              g r s i α Q y
          else 0)
          =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
              (chartOverlapEuclid (I := I) (M := M) α β)]
        (fun _ : EuclN => (0 : ℝ)) := by
      rw [chartLebesgueMeasure] at h_gate_target
      exact _root_.MeasureTheory.ae_mono (Measure.restrict_mono_set _
        (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) α β))
        h_gate_target
    have h_gate_transport := chartTransitionEuclid_comp_ae_eq_restrict
      (I := I) (M := M) β α h_gate_overlap
    have h_mem : ∀ᵐ y ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartOverlapEuclid (I := I) (M := M) β α)),
        y ∈ chartOverlapEuclid (I := I) (M := M) β α :=
      _root_.MeasureTheory.ae_restrict_mem hΩ_meas
    filter_upwards [h_mem, h_gate_transport] with y hy_mem hy_gate
    have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β :=
      chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β α hy_mem
    set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
      with hz_def
    have hz_sourceβ : z ∈ (chartAt H β).source :=
      symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) β hy_target
    have hz_sourceα : z ∈ (chartAt H α).source :=
      (mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
        (I := I) (M := M) β α hy_target).mp hy_mem
    have hsymm_target : (toEuclidean (E := E)).symm y ∈
        (extChartAt I β).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
      exact hy_target
    have hy_eq : (toEuclidean (E := E)) (extChartAt I β z) = y := by
      rw [hz_def, (extChartAt I β).right_inv hsymm_target]
      exact (toEuclidean (E := E)).apply_symm_apply y
    have hT_eq : chartTransitionEuclid (I := I) (M := M) β α y =
        (toEuclidean (E := E)) (extChartAt I α z) := by
      rw [← hy_eq]
      exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) β α hz_sourceβ
    have h_coeff : chartPushedRaw (I := I) (M := M) β
        (transportCoeffManifold (I := I) (M := M) r s α β P₀ Q) y =
        transportCoeffManifold (I := I) (M := M) r s α β P₀ Q z := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target, ← hz_def]
    by_cases hχβ : ((chartKernelCutoff (I := I) (M := M) β :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0
    · rw [h_coeff, transportCoeffManifold_apply, hχβ]
      ring
    · have hχβ_support : z ∈ tsupport
          ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
        subset_tsupport _ hχβ
      have hρα : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0 := by
        by_contra hρα_ne
        exact hα (mem_transportChartCenters_of_pou_cutoff_ne
          (I := I) (M := M) β α hρα_ne hχβ)
      have hw_zero : chartPushedPouWeight (I := I) (M := M) α
          (chartTransitionEuclid (I := I) (M := M) β α y) = 0 := by
        rw [hT_eq, chartPushedPouWeight_toEuclidean_extChartAt
          (I := I) (M := M) α hz_sourceα, hρα]
      have hy_gate' : (if chartPushedPouWeight (I := I) (M := M) α
            (chartTransitionEuclid (I := I) (M := M) β α y) = 0 then
          eigenvectorChartComponentFun (I := I) (M := M) g r s i α Q
            (chartTransitionEuclid (I := I) (M := M) β α y)
        else 0) = 0 := hy_gate
      rw [if_pos hw_zero] at hy_gate'
      rw [hy_gate', _root_.MulZeroClass.mul_zero]
  have h_off_overlap : ∀ y, y ∉ chartOverlapEuclid (I := I) (M := M) β α →
      chartPushedRaw (I := I) (M := M) β
          (transportCoeffManifold (I := I) (M := M) r s α β P₀ Q) y *
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α Q)
          (chartTransitionEuclid (I := I) (M := M) β α y) = 0 := by
    intro y hy_notin
    by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β
    · set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
        with hz_def
      have hz_notin_sourceα : z ∉ (chartAt H α).source := by
        intro hz_sourceα
        exact hy_notin
          ((mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
            (I := I) (M := M) β α hy_target).mpr hz_sourceα)
      have hχα_zero : ((chartKernelCutoff (I := I) (M := M) α :
          C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h =>
          hz_notin_sourceα
            (chartKernelCutoff_tsupport_subset_source (I := I) (M := M) α h))
      have h_coeff_zero : chartPushedRaw (I := I) (M := M) β
          (transportCoeffManifold (I := I) (M := M) r s α β P₀ Q) y = 0 := by
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
          ← hz_def, transportCoeffManifold_apply, hχα_zero]
        ring
      rw [h_coeff_zero, _root_.MulZeroClass.zero_mul]
    · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) β _ hy_target,
        _root_.MulZeroClass.zero_mul]
  exact ae_eq_of_ae_eq_restrict_of_eqOn_compl hΩ_meas h_on_overlap h_off_overlap

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM_eigenvector_ae_zero_of_notMem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM_eigenvector_ae_zero_of_notMem target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
private lemma transportSum_eigenvector_ae_zero_of_notMem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α β : M) (P₀ : TensorCompIdx (E := E) r s)
    (hα : α ∉ transportChartCenters (I := I) (M := M) β) :
    (fun y => ∑ Q : TensorCompIdx (E := E) r s,
        ((chartTransitionTransportCLM (I := I) (M := M) r s α β P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i)
              α Q) :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[chartLebesgueMeasure (I := I) (M := M) β]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have h_each : ∀ Q : TensorCompIdx (E := E) r s,
      ((chartTransitionTransportCLM (I := I) (M := M) r s α β P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i)
            α Q) :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ)
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) β] (fun _ : EuclN => (0 : ℝ)) :=
    fun Q => chartTransitionTransportCLM_eigenvector_ae_zero_of_notMem
      (I := I) (M := M) g r s i α β P₀ Q hα
  have h_sum := finsetSum_ae_eq (I := I) (M := M) β
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q _ => h_each Q)
  refine h_sum.trans (Filter.EventuallyEq.of_eq ?_)
  funext y
  rw [Finset.sum_const_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportSum_eigenvector_ae_zero_of_notMem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportSum_eigenvector_ae_zero_of_notMem target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
theorem eigenvectorSmooth_tensorL2ChartComponent_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent g r s
        (eigenvectorSmooth g r s i : TensorL2 r s g) β P₀ =
      tensorL2ChartComponent g r s
        (tensorResolventEigenbasisVec
          (tensorResolventL2_isCompactOperator g r s) i :
          TensorL2 r s g) β P₀ := by
  classical
  apply Lp.ext
  have h_coe_sum :
      (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g) =
        ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
          (eigenvectorSmoothChart (I := I) (M := M) g r s i α :
            TensorL2 r s g) := by
    rw [← smoothToTensorL2_apply (I := I) (M := M) g r s,
      eigenvectorSmooth_eq (I := I) (M := M) g r s i,
      map_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [smoothToTensorL2_apply]
  have h_lhs_sum :
      tensorL2ChartComponent (I := I) (M := M) g r s
          (eigenvectorSmooth (I := I) (M := M) g r s i :
            TensorL2 r s g) β P₀ =
        ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
          tensorL2ChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothChart (I := I) (M := M) g r s i α :
              TensorL2 r s g) β P₀ := by
    rw [← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s β P₀,
      h_coe_sum, map_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [tensorL2ChartComponentCLM_apply]
  rw [h_lhs_sum]
  refine (coeFn_finsetSum_chartL2 (I := I) (M := M) β
    (chartAtlasPOUFinset (I := I) (M := M))
    (fun α => tensorL2ChartComponent (I := I) (M := M) g r s
      (eigenvectorSmoothChart (I := I) (M := M) g r s i α :
        TensorL2 r s g) β P₀)).trans ?_
  have h_lhs_terms :
      (fun y => ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothChart (I := I) (M := M) g r s i α :
              TensorL2 r s g) β P₀ :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) β]
      (fun y => ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        (chartPushedRaw I β
            (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
          ∑ Q : TensorCompIdx (E := E) r s,
            ((chartTransitionTransportCLM (I := I) (M := M) r s α β P₀ Q
                (tensorL2ChartComponent (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M)
                      g r s) i)
                  α Q) :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
              EuclN → ℝ) y)) :=
    finsetSum_ae_eq (I := I) (M := M) β
      (chartAtlasPOUFinset (I := I) (M := M))
      (fun α _ => eigenvectorSmoothChart_tensorL2ChartComponent_eq_transport_sum
        (I := I) (M := M) g r s i α β P₀)
  refine h_lhs_terms.trans ?_
  refine Filter.EventuallyEq.symm
    ((tensorL2ChartComponent_ae_eq_pou_transport_sum (I := I) (M := M)
      g r s (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
      β P₀).trans ?_)
  have h_subset : transportChartCenters (I := I) (M := M) β ⊆
      chartAtlasPOUFinset (I := I) (M := M) :=
    transportChartCenters_subset_chartAtlasPOU_finset (I := I) (M := M) β
  set F : M → EuclN → ℝ := fun α y =>
    chartPushedRaw I β
        (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
      ∑ Q : TensorCompIdx (E := E) r s,
        ((chartTransitionTransportCLM (I := I) (M := M) r s α β P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i)
              α Q) :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y
    with hF_def
  have h_rhs_eq :
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ∑ γ ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            ((chartTransitionTransportCLM (I := I) (M := M) r s γ β P₀ Q
                (tensorL2ChartComponent (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M)
                      g r s) i)
                  γ Q) :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
              EuclN → ℝ) y) =
        fun y => ∑ γ ∈ transportChartCenters (I := I) (M := M) β, F γ y := by
    funext y
    rw [Finset.mul_sum]
  rw [h_rhs_eq]
  have h_union : chartAtlasPOUFinset (I := I) (M := M) =
      transportChartCenters (I := I) (M := M) β ∪
        (chartAtlasPOUFinset (I := I) (M := M) \
          transportChartCenters (I := I) (M := M) β) :=
    (Finset.union_sdiff_of_subset h_subset).symm
  have h_disjoint : Disjoint (transportChartCenters (I := I) (M := M) β)
      (chartAtlasPOUFinset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β) :=
    Finset.disjoint_sdiff
  have h_split : (fun y => ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        F α y) =
      fun y => (∑ γ ∈ transportChartCenters (I := I) (M := M) β, F γ y) +
        ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M) \
            transportChartCenters (I := I) (M := M) β, F α y := by
    funext y
    conv_lhs => rw [h_union]
    rw [Finset.sum_union h_disjoint]
  rw [h_split]
  have h_extra : (fun y => ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M) \
          transportChartCenters (I := I) (M := M) β, F α y)
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) β] (fun _ : EuclN => (0 : ℝ)) := by
    have h_each : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β,
        F α =ᵐ[chartLebesgueMeasure (I := I) (M := M) β] (fun _ : EuclN => (0 : ℝ)) := by
      intro α hα
      have hα_notin : α ∉ transportChartCenters (I := I) (M := M) β :=
        (Finset.mem_sdiff.mp hα).2
      have h_zero := transportSum_eigenvector_ae_zero_of_notMem
        (I := I) (M := M) g r s i α β P₀ hα_notin
      filter_upwards [h_zero] with y hy
      rw [hF_def]
      change chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ∑ Q : TensorCompIdx (E := E) r s,
          ((chartTransitionTransportCLM (I := I) (M := M) r s α β P₀ Q
              (tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i)
                α Q) :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y =
        (0 : ℝ)
      rw [hy, _root_.MulZeroClass.mul_zero]
    have h_sum := finsetSum_ae_eq (I := I) (M := M) β
      (chartAtlasPOUFinset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β)
      (fun α hα => h_each α hα)
    refine h_sum.trans (Filter.EventuallyEq.of_eq ?_)
    funext y
    rw [Finset.sum_const_zero]
  filter_upwards [h_extra] with y hy
  rw [show (∑ α ∈ chartAtlasPOUFinset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β, F α y) = 0 from hy,
    add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_tensorL2ChartComponent_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_tensorL2ChartComponent_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_tensorL2ChartComponent_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_tensorL2ChartComponent_eq

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
