import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.ChartBilinearDischarge.SubstitutionSmoothApprox

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal Pointwise

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace SubstitutionDischargeIBPExpand

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTranslatedCutoffDiffQuot
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionNonSmoothChartBilinear

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
theorem chart_bilinear_identity_h1_0_smooth_seq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ} (hh : h ≠ 0)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    {uSeq : ℕ → EuclN → ℝ}
    (hu_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (uSeq n)) :
    ∀ n,
      (∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                (fderiv ℝ
                  (nirenbergTestFunction (d := Module.finrank ℝ E) k h η
                    (uSeq n)) y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        (∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.uChart y *
            nirenbergTestFunction (d := Module.finrank ℝ E) k h η
              (uSeq n) y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.fChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η
            (uSeq n) y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  have h_thick_compact : IsCompact (Metric.cthickening |h| K_0) :=
    cthickening_K_0_isCompact (E := E) hK_0_compact
  intro n
  obtain ⟨h_v_smooth, h_v_cs⟩ :=
    nirenbergTestFunction_smooth_seq hη hη_support k hh hu_seq_smooth n
  have h_v_support : tsupport (nirenbergTestFunction (d := Module.finrank ℝ E)
      k h η (uSeq n)) ⊆ Metric.cthickening |h| K_0 :=
    nirenbergTestFunction_tsupport_in_thickening (E := E) k h
      hη_support_in_K_0 (uSeq n)
  set ψ : EuclN → ℝ := nirenbergTestFunction (d := Module.finrank ℝ E)
    k h η (uSeq n) with hψ_def
  set weak_partial_ψ : Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun j x => (fderiv ℝ ψ x) (EuclideanSpace.single j 1) with hwp_def
  have hψ_lp : _root_.MeasureTheory.MemLp ψ 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0)) :=
    (h_v_smooth.continuous.memLp_of_hasCompactSupport h_v_cs).restrict _
  have hψ_grad_lp : ∀ j : Fin (Module.finrank ℝ E),
      _root_.MeasureTheory.MemLp (weak_partial_ψ j) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0)) := by
    intro j
    have h_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
    have h_cont : Continuous (weak_partial_ψ j) := by
      have h_fderiv_cont : Continuous (fderiv ℝ ψ) :=
        h_v_smooth.continuous_fderiv h_top_ne_zero
      exact h_fderiv_cont.clm_apply continuous_const
    have h_cs : HasCompactSupport (weak_partial_ψ j) :=
      h_v_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
    exact (h_cont.memLp_of_hasCompactSupport h_cs).restrict _
  set ψ_seq : ℕ → EuclN → ℝ := fun _ => ψ with hψseq_def
  have hψ_seq_smooth : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (ψ_seq m) := fun _ => h_v_smooth
  have hψ_seq_cs : ∀ m, HasCompactSupport (ψ_seq m) := fun _ => h_v_cs
  have hψ_seq_support : ∀ m, tsupport (ψ_seq m) ⊆ Metric.cthickening |h| K_0 :=
    fun _ => h_v_support
  have hψ_seq_l2 :
      _root_.Filter.Tendsto (fun m => _root_.MeasureTheory.eLpNorm (fun x => ψ_seq m x - ψ x) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0)))
        atTop (𝓝 0) := by
    have h_eq : (fun m : ℕ => _root_.MeasureTheory.eLpNorm (fun x => ψ_seq m x - ψ x) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0))) =
        (fun _ : ℕ => (0 : ℝ≥0∞)) := by
      funext m
      have h_fun_eq : (fun x => ψ_seq m x - ψ x) = (fun _ : EuclN => (0 : ℝ)) := by
        funext x
        change ψ x - ψ x = 0
        ring
      rw [h_fun_eq]
      simp
    rw [h_eq]
    exact tendsto_const_nhds
  have hψ_seq_grad_l2 : ∀ j : Fin (Module.finrank ℝ E),
      _root_.Filter.Tendsto (fun m => _root_.MeasureTheory.eLpNorm
        (fun x => (fderiv ℝ (ψ_seq m) x) (EuclideanSpace.single j 1) -
          weak_partial_ψ j x) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0)))
        atTop (𝓝 0) := by
    intro j
    have h_eq : (fun m : ℕ => _root_.MeasureTheory.eLpNorm
        (fun x => (fderiv ℝ (ψ_seq m) x) (EuclideanSpace.single j 1) -
          weak_partial_ψ j x) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0))) =
        (fun _ : ℕ => (0 : ℝ≥0∞)) := by
      funext m
      have h_fun_eq : (fun x => (fderiv ℝ (ψ_seq m) x)
          (EuclideanSpace.single j 1) - weak_partial_ψ j x) =
          (fun _ : EuclN => (0 : ℝ)) := by
        funext x
        change (fderiv ℝ ψ x) (EuclideanSpace.single j 1) -
          (fderiv ℝ ψ x) (EuclideanSpace.single j 1) = 0
        ring
      rw [h_fun_eq]
      simp
    rw [h_eq]
    exact tendsto_const_nhds
  exact chart_bilinear_identity_h1_0 (I := I) (M := M) D
    h_thick_compact h_thick ψ weak_partial_ψ hψ_lp hψ_grad_lp ψ_seq
    hψ_seq_smooth hψ_seq_cs hψ_seq_support hψ_seq_l2 hψ_seq_grad_l2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.chart_bilinear_identity_h1_0_smooth_seq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.chart_bilinear_identity_h1_0_smooth_seq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.chart_bilinear_identity_h1_0_smooth_seq ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.chart_bilinear_identity_h1_0_smooth_seq


omit [NeZero (Module.finrank ℝ E)] in
theorem variational_identity_at_v_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ} (hh : h ≠ 0)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (weak_partial_v_h : Fin (Module.finrank ℝ E) → EuclN → ℝ)
    (hv_h_lp : _root_.MeasureTheory.MemLp (nirenbergTestFunction (d := Module.finrank ℝ E)
        k h η D.uChart) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0)))
    (hv_h_grad_lp : ∀ j : Fin (Module.finrank ℝ E),
      _root_.MeasureTheory.MemLp (weak_partial_v_h j) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0)))
    (uSeq : ℕ → EuclN → ℝ)
    (hu_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (uSeq n))
    (h_v_seq_support : ∀ n,
      tsupport (nirenbergTestFunction (d := Module.finrank ℝ E)
        k h η (uSeq n)) ⊆ Metric.cthickening |h| K_0)
    (h_v_seq_l2 :
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
        nirenbergTestFunction (d := Module.finrank ℝ E) k h η (uSeq n) x -
        nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart x) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0)))
        _root_.Filter.atTop (𝓝 0))
    (h_v_seq_grad_l2 : ∀ j : Fin (Module.finrank ℝ E),
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm
        (fun x => (fderiv ℝ
          (nirenbergTestFunction (d := Module.finrank ℝ E) k h η
            (uSeq n)) x) (EuclideanSpace.single j 1) -
          weak_partial_v_h j x) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0)))
        _root_.Filter.atTop (𝓝 0)) :
    (∫ y in Metric.cthickening |h| K_0,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weakPartial i y *
              weak_partial_v_h j y)
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
      (∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.uChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.fChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  have h_thick_compact : IsCompact (Metric.cthickening |h| K_0) :=
    cthickening_K_0_isCompact (E := E) hK_0_compact
  set v_h : EuclN → ℝ := nirenbergTestFunction (d := Module.finrank ℝ E)
    k h η D.uChart with hvh_def
  set v_h_seq : ℕ → EuclN → ℝ := fun n =>
    nirenbergTestFunction (d := Module.finrank ℝ E) k h η (uSeq n)
    with hvhseq_def
  have h_v_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v_h_seq n) := fun n =>
    (nirenbergTestFunction_smooth_seq hη hη_support k hh hu_seq_smooth n).1
  have h_v_seq_cs : ∀ n, HasCompactSupport (v_h_seq n) := fun n =>
    (nirenbergTestFunction_smooth_seq hη hη_support k hh hu_seq_smooth n).2
  exact chart_bilinear_identity_h1_0 (I := I) (M := M) D
    h_thick_compact h_thick v_h weak_partial_v_h hv_h_lp hv_h_grad_lp
    v_h_seq h_v_seq_smooth h_v_seq_cs h_v_seq_support h_v_seq_l2
    h_v_seq_grad_l2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.variational_identity_at_v_h then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.variational_identity_at_v_h"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.variational_identity_at_v_h ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.variational_identity_at_v_h


omit [NeZero (Module.finrank ℝ E)] in
theorem variational_identity_v_h_expanded
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ}
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ}
    (weak_partial_v_h : Fin (Module.finrank ℝ E) → EuclN → ℝ)
    (h_var_id_at_v_h :
      (∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                weak_partial_v_h j y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        (∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.uChart y *
            nirenbergTestFunction (d := Module.finrank ℝ E) k h η
              D.uChart y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        ∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.fChart y *
            nirenbergTestFunction (d := Module.finrank ℝ E) k h η
              D.uChart y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
    (h_weak_partial_eq : ∀ j : Fin (Module.finrank ℝ E), ∀ᵐ y
        ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0)),
      weak_partial_v_h j y =
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun z => (η z) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
            2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart z) y) :
    (∫ y in Metric.cthickening |h| K_0,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weakPartial i y *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k (-h)
                (fun z => (η z) ^ 2 *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
                  2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h D.uChart z) y)
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
      (∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.uChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.fChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  have h_principal_eq :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                weak_partial_v_h j y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k (-h)
                  (fun z => (η z) ^ 2 *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
                    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                      DifferentialGeometry.Analysis.Sobolev.diffQuot
                        (d := Module.finrank ℝ E) k h D.uChart z) y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    refine _root_.MeasureTheory.integral_congr_ae ?_
    have h_all : ∀ j : Fin (Module.finrank ℝ E), ∀ᵐ y
        ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0)),
      weak_partial_v_h j y =
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun z => (η z) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
            2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart z) y :=
      h_weak_partial_eq
    have h_combined : ∀ᵐ y
        ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0)),
      ∀ j : Fin (Module.finrank ℝ E), weak_partial_v_h j y =
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun z => (η z) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
            2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart z) y := by
      rw [_root_.MeasureTheory.ae_all_iff]
      exact h_all
    filter_upwards [h_combined] with y hy
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hy j]
  rw [← h_principal_eq]
  exact h_var_id_at_v_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.variational_identity_v_h_expanded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.variational_identity_v_h_expanded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.variational_identity_v_h_expanded ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.variational_identity_v_h_expanded


omit [NeZero (Module.finrank ℝ E)] in
theorem variational_identity_after_ibp
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ}
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ}
    (h_expanded :
      (∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k (-h)
                  (fun z => (η z) ^ 2 *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
                    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                      DifferentialGeometry.Analysis.Sobolev.diffQuot
                        (d := Module.finrank ℝ E) k h D.uChart z) y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        (∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.uChart y *
            nirenbergTestFunction (d := Module.finrank ℝ E) k h η
              D.uChart y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        ∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.fChart y *
            nirenbergTestFunction (d := Module.finrank ℝ E) k h η
              D.uChart y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
    (h_ibp_per_ij : ∀ i j : Fin (Module.finrank ℝ E),
      ∫ y in Metric.cthickening |h| K_0,
        weightedInvGramOnEuclid (I := I) g α i j y *
          D.weakPartial i y *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun z => (η z) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
              2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.uChart z) y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      - ∫ y in Metric.cthickening |h| K_0,
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
              D.weakPartial i z) y *
          ((η y) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
            2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart y)
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
    (h_principal_integrable : ∀ i j : Fin (Module.finrank ℝ E),
      _root_.MeasureTheory.Integrable (fun y =>
        weightedInvGramOnEuclid (I := I) g α i j y *
          D.weakPartial i y *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun z => (η z) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
              2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.uChart z) y)
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0)))
    (h_principal_integrable_after : ∀ i j : Fin (Module.finrank ℝ E),
      _root_.MeasureTheory.Integrable (fun y =>
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
            D.weakPartial i z) y *
        ((η y) ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.uChart y))
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0))) :
    -(∫ y in Metric.cthickening |h| K_0,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                D.weakPartial i z) y *
            ((η y) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
              2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.uChart y))
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
      (∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.uChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.fChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  have h_int_swap_before :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k (-h)
                  (fun z => (η z) ^ 2 *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
                    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                      DifferentialGeometry.Analysis.Sobolev.diffQuot
                        (d := Module.finrank ℝ E) k h D.uChart z) y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Metric.cthickening |h| K_0,
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weakPartial i y *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k (-h)
                (fun z => (η z) ^ 2 *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
                  2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h D.uChart z) y
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    rw [_root_.MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [_root_.MeasureTheory.integral_finsetSum]
      intro j _
      exact h_principal_integrable i j
    · intro i _
      exact _root_.MeasureTheory.integrable_finsetSum _ (fun j _ => h_principal_integrable i j)
  have h_int_swap_after :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                  D.weakPartial i z) y *
              ((η y) ^ 2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
                2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h D.uChart y))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Metric.cthickening |h| K_0,
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                D.weakPartial i z) y *
            ((η y) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
              2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.uChart y)
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    rw [_root_.MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [_root_.MeasureTheory.integral_finsetSum]
      intro j _
      exact h_principal_integrable_after i j
    · intro i _
      exact _root_.MeasureTheory.integrable_finsetSum _ (fun j _ => h_principal_integrable_after i j)
  have h_per_ij_eq :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Metric.cthickening |h| K_0,
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weakPartial i y *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k (-h)
                (fun z => (η z) ^ 2 *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
                  2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h D.uChart z) y
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
      - ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in Metric.cthickening |h| K_0,
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                  D.weakPartial i z) y *
              ((η y) ^ 2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
                2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h D.uChart y)
              ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact h_ibp_per_ij i j
  rw [h_int_swap_before, h_per_ij_eq, ← h_int_swap_after] at h_expanded
  exact h_expanded

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.variational_identity_after_ibp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.variational_identity_after_ibp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.variational_identity_after_ibp ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.variational_identity_after_ibp


omit [NeZero (Module.finrank ℝ E)] in
theorem variational_identity_after_product_rule
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ}
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ}
    (h_after_ibp :
      -(∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                  D.weakPartial i z) y *
              ((η y) ^ 2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
                2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h D.uChart y))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        (∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.uChart y *
            nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        ∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.fChart y *
            nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
    (h_principal_in_K_0_eq :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                  D.weakPartial i z) y *
              ((η y) ^ 2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
                2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h D.uChart y))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      principalTermChartBilinear (I := I) (M := M) D K_0 η k h
        + cross1TermChartBilinear (I := I) (M := M) D K_0 η k h
        + cross2TermChartBilinear (I := I) (M := M) D K_0 η k h
        + cross3TermChartBilinear (I := I) (M := M) D K_0 η k h)
    (h_c_term_eq :
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.uChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      cTermChartBilinear (I := I) (M := M) D K_0 η k h)
    (h_f_term_eq :
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.fChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      fTermChartBilinear (I := I) (M := M) D K_0 η k h) :
    principalTermChartBilinear (I := I) (M := M) D K_0 η k h
      + cross1TermChartBilinear (I := I) (M := M) D K_0 η k h
      + cross2TermChartBilinear (I := I) (M := M) D K_0 η k h
      + cross3TermChartBilinear (I := I) (M := M) D K_0 η k h
      + fTermChartBilinear (I := I) (M := M) D K_0 η k h
      = cTermChartBilinear (I := I) (M := M) D K_0 η k h := by
  classical
  rw [h_principal_in_K_0_eq, h_c_term_eq, h_f_term_eq] at h_after_ibp
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.variational_identity_after_product_rule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.variational_identity_after_product_rule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.variational_identity_after_product_rule ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand.variational_identity_after_product_rule

end SubstitutionDischargeIBPExpand
end Sobolev
end Analysis
end DifferentialGeometry
