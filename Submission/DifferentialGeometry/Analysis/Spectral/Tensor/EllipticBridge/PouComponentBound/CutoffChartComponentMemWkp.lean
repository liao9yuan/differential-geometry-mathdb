import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.TensorChartTransitionTransport
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBound
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK

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
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound

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

private lemma memWkp_finsetSum
    {d k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {ι : Type*} (T : Finset ι)
    (F : ι → EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : ∀ i ∈ T, MemWkp (d := d) k p (F i) Ω) :
    MemWkp (d := d) k p (fun y => ∑ i ∈ T, F i y) Ω := by
  classical
  induction T using Finset.induction with
  | empty =>
      simpa using MemWkp_zero_fun (d := d) (k := k) (p := p) hp hΩ
  | insert a s ha ih =>
      have hF_a : MemWkp (d := d) k p (F a) Ω :=
        hF a (Finset.mem_insert_self a s)
      have hF_s : ∀ i ∈ s, MemWkp (d := d) k p (F i) Ω :=
        fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have h_sum_s : MemWkp (d := d) k p (fun y => ∑ i ∈ s, F i y) Ω := ih hF_s
      have h_add : MemWkp (d := d) k p
          (fun y => F a y + ∑ i ∈ s, F i y) Ω :=
        MemWkp.add (d := d) hp hΩ hF_a h_sum_s
      have h_eq : (fun y => ∑ i ∈ _root_.Insert.insert a s, F i y) =
          fun y => F a y + ∑ i ∈ s, F i y := by
        funext y
        rw [Finset.sum_insert ha]
      rw [h_eq]
      exact h_add

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memWkp_finsetSum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memWkp_finsetSum target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma tsupport_chartPushedRaw_subset_chartImage
    (α : M) {u : M → ℝ}
    (hu_support : tsupport u ⊆ (chartAt H α).source) :
    tsupport (chartPushedRaw (I := I) (M := M) α u) ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' (tsupport u) := by
  classical
  have h_image_compact :
      IsCompact ((fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
        (tsupport u)) :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) α
      (isClosed_tsupport u).isCompact hu_support
  refine closure_minimal ?_ h_image_compact.isClosed
  intro y hy
  rw [Function.mem_support] at hy
  by_contra hy_off
  have hy_off' : y ∉ (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport u)) := by
    intro hy_in
    apply hy_off
    obtain ⟨z, ⟨x, hx_support, hxz⟩, hzy⟩ := hy_in
    exact ⟨x, hx_support, by rw [← hzy, ← hxz]⟩
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact hy (chartPushedRaw_eq_zero_off_image_tsupport
      (I := I) (M := M) (u := u) α hy_target hy_off')
  · exact hy (chartPushedRaw_apply_of_notMem (I := I) (M := M) α u hy_target)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tsupport_chartPushedRaw_subset_chartImage
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tsupport_chartPushedRaw_subset_chartImage target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma chartTransitionTransportCLM_memWkp
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) (k : ℕ)
    (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β))
    (hf : MemWkp (d := Module.finrank ℝ E) k 2
      (fun y => (f : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) k 2
      (fun y => ((chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q f :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set d : ℕ := Module.finrank ℝ E with hd_def
  set cM : M → ℝ := transportCoeffManifold (I := I) (M := M) r s β α P₀ Q
    with hcM_def
  set cE : EuclN → ℝ := chartPushedRaw (I := I) (M := M) α cM with hcE_def
  set T : EuclN → ℝ := fun y => (f : EuclN → ℝ) y with hT_def
  set Tα : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hTα_def
  set Tβ : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hTβ_def
  have hTα_open : IsOpen Tα := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hTβ_open : IsOpen Tβ := chartTargetEuclid_isOpen (I := I) (M := M) β
  have hcM_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ cM :=
    contMDiff_transportCoeffManifold (I := I) (M := M) r s β α P₀ Q
  have hcM_support_α : tsupport cM ⊆ (chartAt H α).source :=
    tsupport_transportCoeffManifold_subset_sourceα (I := I) (M := M) r s β α P₀ Q
  have hcM_support_β : tsupport cM ⊆ (chartAt H β).source :=
    tsupport_transportCoeffManifold_subset_sourceβ (I := I) (M := M) r s β α P₀ Q
  set Kc : Set M := tsupport cM with hKc_def
  have hKc_compact : IsCompact Kc := (isClosed_tsupport cM).isCompact
  have hKc_in_α : Kc ⊆ (chartAt H α).source := hcM_support_α
  have hKc_in_β : Kc ⊆ (chartAt H β).source := hcM_support_β
  have hcE_smooth : ContDiff ℝ ∞ cE :=
    Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
      (I := I) (M := M) hcM_smooth hcM_support_α
  have hcE_smooth' : ContDiff ℝ (⊤ : ℕ∞) cE := hcE_smooth
  have hcE_compact : HasCompactSupport cE :=
    chartPushedRaw_smooth_hasCompactSupport_local
      (I := I) (M := M) hcM_support_α
  obtain ⟨Ccoeff, _hCcoeff_nn, hCcoeff_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := d) hcE_smooth' hcE_compact k
  have hcE_tsupp_subset :
      tsupport cE ⊆ (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' Kc :=
    tsupport_chartPushedRaw_subset_chartImage (I := I) (M := M) α hcM_support_α
  obtain ⟨Ωαβ, Ωβα, hΩαβ_open, hΩβα_open, hΩαβ_subset_target,
    hΩβα_subset_target, _hΩαβ_overlap, _hΩβα_overlap, hKc_image_in_Ωαβ, Φ,
    hΦ_eq, _hΦ_inv_eq⟩ :=
    chartTransition_smoothDiffeoBoundedAtOrder_strict (I := I) (M := M)
      α β hKc_compact hKc_in_α hKc_in_β k
  set KEα : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' Kc with hKEα_def
  have hKEα_compact : IsCompact KEα :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) α hKc_compact hKc_in_α
  have hKEα_in_Ωαβ : KEα ⊆ Ωαβ := hKc_image_in_Ωαβ
  have hcE_tsupp_Ωαβ : tsupport cE ⊆ Ωαβ := hcE_tsupp_subset.trans hKEα_in_Ωαβ
  set KEβ : Set EuclN := Φ.toFun '' KEα with hKEβ_def
  have hKEβ_compact : IsCompact KEβ :=
    hKEα_compact.image Φ.continuous_toFun
  have hKEβ_in_Ωβα : KEβ ⊆ Ωβα := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hz
    have hy_Ωαβ : y ∈ Ωαβ := hKEα_in_Ωαβ hy
    rw [← hyz]
    exact Φ.bijOn.mapsTo hy_Ωαβ
  set Uβ : Set EuclN := Ωβα ∩ Tβ with hUβ_def
  have hUβ_open : IsOpen Uβ := hΩβα_open.inter hTβ_open
  have hKEβ_in_Uβ : KEβ ⊆ Uβ :=
    Set.subset_inter hKEβ_in_Ωβα (hKEβ_in_Ωβα.trans hΩβα_subset_target)
  obtain ⟨δ, χ, _hδ_pos, _hδ_subset, hχ_smooth, hχ_compact, _hχ_range,
    hχ_one, hχ_support⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := d) hKEβ_compact hUβ_open hKEβ_in_Uβ
  have hχ_support_Ωβα : tsupport χ ⊆ Ωβα := fun y hy => (hχ_support hy).1
  have hχ_support_Tβ : tsupport χ ⊆ Tβ := fun y hy => (hχ_support hy).2
  set v : EuclN → ℝ := fun y => χ y * T y with hv_def
  have hv_support_χ : tsupport v ⊆ tsupport χ :=
    tsupport_smul_subset_left χ T
  have hv_support_Ωβα : tsupport v ⊆ Ωβα := hv_support_χ.trans hχ_support_Ωβα
  have hv_compact : HasCompactSupport v := hχ_compact.mul_right
  obtain ⟨Cχ, _hCχ_nn, hCχ_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := d) (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ) hχ_compact k
  have hv_memWkp_Tβ : MemWkp (d := d) k 2 v Tβ :=
    MemWkp.smul_smooth_bounded (d := d) k (by norm_num) hTβ_open
      (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
      (fun j hj y _ => hCχ_bound y j hj) hf
  have hv_memWkp_Ωβα : MemWkp (d := d) k 2 v Ωβα :=
    MemWkp.mono_set (d := d) (by norm_num) hΩβα_open
      hΩβα_subset_target hv_memWkp_Tβ
  have hv_comp_memWkp_Ωαβ : MemWkp (d := d) k 2 (fun y => v (Φ.toFun y)) Ωαβ :=
    MemWkp.comp_smoothDiffeoBoundedAtOrder (d := d) k (le_refl k)
      (by norm_num) (by norm_num) hΩαβ_open hΩβα_open Φ
      hv_memWkp_Ωβα hv_compact hv_support_Ωβα
  set w : EuclN → ℝ := fun y => cE y * v (Φ.toFun y) with hw_def
  have hw_memWkp_Ωαβ : MemWkp (d := d) k 2 w Ωαβ :=
    MemWkp.smul_smooth_bounded (d := d) k (by norm_num) hΩαβ_open
      hcE_smooth' (fun j hj y _ => hCcoeff_bound y j hj) hv_comp_memWkp_Ωαβ
  have hw_support_cE : tsupport w ⊆ tsupport cE := by
    refine closure_mono ?_
    intro y hy
    rw [Function.mem_support] at hy
    have hcE_ne : cE y ≠ 0 := by
      intro h0
      apply hy
      simp only [hw_def, h0, _root_.MulZeroClass.zero_mul]
    exact Function.mem_support.mpr hcE_ne
  have hw_support_Ωαβ : tsupport w ⊆ Ωαβ := hw_support_cE.trans hcE_tsupp_Ωαβ
  have hw_compact : HasCompactSupport w :=
    hcE_compact.of_isClosed_subset (isClosed_tsupport w) hw_support_cE
  have hw_memWkp_Tα : MemWkp (d := d) k 2 w Tα :=
    MemWkp.extend_zero (d := d) (by norm_num)
      hΩαβ_open hTα_open hΩαβ_subset_target hw_memWkp_Ωαβ hw_support_Ωαβ hw_compact
  have h_coeFn : (fun y => ((chartTransitionTransportCLM
        (I := I) (M := M) r s β α P₀ Q f :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Tα]
      (fun y => cE y *
        (f : EuclN → ℝ) (chartTransitionEuclid (I := I) (M := M) α β y)) :=
    chartTransitionTransportCLM_coeFn_aeEq
      (I := I) (M := M) r s β α P₀ Q f
  have h_pointwise : (fun y => cE y *
        (f : EuclN → ℝ) (chartTransitionEuclid (I := I) (M := M) α β y)) = w := by
    funext y
    by_cases hcE_zero : cE y = 0
    · simp only [hw_def, hcE_zero, _root_.MulZeroClass.zero_mul]
    · have hy_tsupp_cE : y ∈ tsupport cE :=
        subset_tsupport cE (Function.mem_support.mpr hcE_zero)
      have hy_KEα : y ∈ KEα := hcE_tsupp_subset hy_tsupp_cE
      have hy_Ωαβ : y ∈ Ωαβ := hKEα_in_Ωαβ hy_KEα
      have hT_eq : chartTransitionEuclid (I := I) (M := M) α β y = Φ.toFun y :=
        (hΦ_eq y hy_Ωαβ).symm
      have hΦy_KEβ : Φ.toFun y ∈ KEβ := ⟨y, hy_KEα, rfl⟩
      have hχ_Φy : χ (Φ.toFun y) = 1 :=
        hχ_one (Φ.toFun y) (Metric.self_subset_cthickening KEβ hΦy_KEβ)
      have hv_Φy : v (Φ.toFun y) =
          (f : EuclN → ℝ) (Φ.toFun y) := by
        simp only [hv_def, hT_def, hχ_Φy, one_mul]
      simp only [hw_def, hT_eq, hv_Φy]
  have h_ae : (fun y => ((chartTransitionTransportCLM
        (I := I) (M := M) r s β α P₀ Q f :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Tα] w := by
    refine h_coeFn.trans ?_
    rw [h_pointwise]
  exact (MemWkp_congr_ae (d := d) (by norm_num) hTα_open h_ae).mpr hw_memWkp_Tα

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM_memWkp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM_memWkp target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem tensorL2ChartComponentCutoff_memWkp_of_pou
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) (k : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) k 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) k 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set d : ℕ := Module.finrank ℝ E with hd_def
  set Tα : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hTα_def
  have hTα_open : IsOpen Tα := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_decomp : (fun y => ((tensorL2ChartComponentCutoff
        (I := I) (M := M) g r s u α P₀ :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Tα]
      (fun y => ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          ((chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q
              (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) :=
    tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum
      (I := I) (M := M) g r s u α P₀
  refine (MemWkp_congr_ae (d := d) (by norm_num) hTα_open h_decomp).mpr ?_
  refine memWkp_finsetSum (d := d) (by norm_num) hTα_open
    (transportChartCenters (I := I) (M := M) α)
    (fun β y => ∑ Q : TensorCompIdx (E := E) r s,
      ((chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
    (fun β _ => ?_)
  refine memWkp_finsetSum (d := d) (by norm_num) hTα_open
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q y =>
      ((chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
    (fun Q _ => ?_)
  exact chartTransitionTransportCLM_memWkp (I := I) (M := M) r s β α P₀ Q k
    (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) (h_pou β Q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_memWkp_of_pou then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_memWkp_of_pou"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_memWkp_of_pou ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_memWkp_of_pou

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
