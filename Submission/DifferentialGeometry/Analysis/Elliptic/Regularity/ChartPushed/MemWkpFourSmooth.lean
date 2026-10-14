import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.CanonicalDerivedData
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.DerivedH2Interior
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.MemWkpThreeSmooth
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.MemWkpThree
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Powers.EvenOrderBridge
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.Multiply
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartPushedMemWkpFourSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChosenThirdMixedPartialChartPushed
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartSecondOrderEffectiveSource
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.CanonicalDerivedChartBilinearH1ComplData
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDerivedChartBilinearH2Interior
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpThreeSmooth
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpThree
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartChosenFirstPartial

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem MemWkp_two_extend_via_cutoff_aux
    (k : ℕ)
    {Ω Ω' K : Set EuclN}
    (hΩ_open : IsOpen Ω) (hΩ'_open : IsOpen Ω')
    (hΩ'_in_Ω : Ω' ⊆ Ω)
    (hK_compact : IsCompact K) (hK_in_Ω' : K ⊆ Ω')
    {u : EuclN → ℝ}
    (hu_local : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k 2 u Ω')
    (hu_ae_zero : ∀ᵐ y ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Ω \ K)),
      u y = 0) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k 2 u Ω := by
  classical
  obtain ⟨δ, η, hδ_pos, hδ_in_Ω', hη_smooth, hη_compact_support, hη_range,
    hη_one_on_cthick, hη_tsupp_in_Ω'⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hK_compact hΩ'_open hK_in_Ω'
  obtain ⟨C, hC_nn, hη_bound⟩ :=
    Analysis.Sobolev.Euclidean.exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hη_smooth hη_compact_support k
  have h_eta_u_in_Ω' : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k 2 (fun x => η x * u x) Ω' :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) k (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ'_open hη_smooth
      (fun j _hj x _hx => hη_bound x j _hj) hu_local
  have h_tsupp_prod_in_tsupp_eta : tsupport (fun x => η x * u x) ⊆ tsupport η := by
    refine closure_mono ?_
    intro x hx
    have hx_ne : η x * u x ≠ 0 := hx
    intro hx_eta_zero
    apply hx_ne
    rw [hx_eta_zero]
    ring
  have h_tsupp_prod_in_Ω' : tsupport (fun x => η x * u x) ⊆ Ω' :=
    h_tsupp_prod_in_tsupp_eta.trans hη_tsupp_in_Ω'
  have h_compactSupport_prod : HasCompactSupport (fun x => η x * u x) :=
    hη_compact_support.of_isClosed_subset (isClosed_tsupport _)
      h_tsupp_prod_in_tsupp_eta
  have h_eta_u_in_Ω : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k 2 (fun x => η x * u x) Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.extend_zero
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      hΩ'_open hΩ_open hΩ'_in_Ω h_eta_u_in_Ω' h_tsupp_prod_in_Ω'
      h_compactSupport_prod
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  set U_K : Set EuclN := Metric.cthickening δ K with hU_K_def
  have hU_K_compact : IsCompact U_K := hK_compact.cthickening
  have hU_K_closed : IsClosed U_K := Metric.isClosed_cthickening
  have hU_K_meas : MeasurableSet U_K := hU_K_closed.measurableSet
  have hK_in_U_K : K ⊆ U_K := Metric.self_subset_cthickening _
  have hU_K_in_Ω' : U_K ⊆ Ω' := hδ_in_Ω'
  have hU_K_in_Ω : U_K ⊆ Ω := hU_K_in_Ω'.trans hΩ'_in_Ω
  have h_eta_u_ae_eq_u : (fun x => η x * u x) =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω] u := by
    have h_eq_on_U_K : (fun x => η x * u x) =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict U_K] u := by
      refine (_root_.MeasureTheory.ae_restrict_iff' hU_K_meas).mpr ?_
      refine Filter.Eventually.of_forall fun x hx => ?_
      have hx_eta : η x = 1 := hη_one_on_cthick x hx
      change η x * u x = u x
      rw [hx_eta]; ring
    have h_diff_meas : MeasurableSet (Ω \ U_K) := hΩ_meas.diff hU_K_meas
    have h_K_in_U_K : Ω \ U_K ⊆ Ω \ K := by
      intro x hx
      exact ⟨hx.1, fun hxK => hx.2 (hK_in_U_K hxK)⟩
    have hu_ae_zero_diff : ∀ᵐ y ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Ω \ U_K)),
        u y = 0 := by
      have h_abs : (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Ω \ U_K) ≪
          (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Ω \ K) :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono h_K_in_U_K le_rfl)
      exact h_abs.ae_le hu_ae_zero
    have h_eq_on_diff : (fun x => η x * u x) =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Ω \ U_K)] u := by
      filter_upwards [hu_ae_zero_diff] with x hx
      rw [hx]; ring
    have h_cover : Ω = U_K ∪ (Ω \ U_K) := by
      ext x; constructor
      · intro hx
        by_cases h : x ∈ U_K
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
      · rintro (hx | hx)
        · exact hU_K_in_Ω hx
        · exact hx.1
    have hΩ_restrict_eq : (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω =
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (U_K ∪ (Ω \ U_K)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq]
    rw [MeasureTheory.Measure.restrict_union (Set.disjoint_sdiff_right) h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_U_K, h_eq_on_diff⟩
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open
    h_eta_u_ae_eq_u).mp h_eta_u_in_Ω

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.MemWkp_two_extend_via_cutoff_aux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.MemWkp_two_extend_via_cutoff_aux target :: scope.openDecls } }

theorem chosenSecondPartialChartPushedU_memWkp_two_two_of_twice_diff_identity
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (h_twice_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ l₂ y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
        + (∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
              chosenSecondPartialChartPushedU
                (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chosenSecondPartialChartPushedU
        (I := I) (M := M) g α u_h l₁ l₂)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  obtain ⟨Ω'', hΩ''_open, hK_α_in_Ω'', hΩ''_compact_closure,
    h_closureΩ''_in_chart, h_memWkp22_Ω''⟩ :=
    twiceDerivedChartBilinear_memWkp_two_two_interior
      (I := I) (M := M) g α hu_h l₁ l₂ h_twice_identity
  set K_α : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_α_def
  have hK_α_compact : IsCompact K_α :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_α_in_chart : K_α ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hΩ''_in_chart : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    subset_trans subset_closure h_closureΩ''_in_chart
  have h_ae_zero_off_K_α :
      ∀ᵐ y ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α)),
        chosenSecondPartialChartPushedU
          (I := I) (M := M) g α u_h l₁ l₂ y = 0 :=
    chosenSecondPartialChartPushedU_ae_zero_off_chartImagePOUTsupport
      (I := I) (M := M) g α hu_h l₁ l₂
  exact MemWkp_two_extend_via_cutoff_aux (E := E) 2
    h_chart_open hΩ''_open hΩ''_in_chart hK_α_compact hK_α_in_Ω''
    h_memWkp22_Ω'' h_ae_zero_off_K_α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.chosenSecondPartialChartPushedU_memWkp_two_two_of_twice_diff_identity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.chosenSecondPartialChartPushedU_memWkp_two_two_of_twice_diff_identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.chosenSecondPartialChartPushedU_memWkp_two_two_of_twice_diff_identity ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.chosenSecondPartialChartPushedU_memWkp_two_two_of_twice_diff_identity

theorem chartPushedChosenFirstPartial_memWkp_three_two_of_twice_diff_identities
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_twice_identities :
      ∀ l₁ l₂ : Fin (Module.finrank ℝ E),
        ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
          (∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α i j y *
                  chosenThirdMixedPartialChartPushedU
                    (I := I) (M := M) g α u_h i l₁ l₂ y *
                  (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
          + (∫ y in chartTargetEuclid (I := I) (M := M) α,
              densityOnEuclid (I := I) g α y *
                chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
              ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
              effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
    (l₁ : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 3 2
      (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l₁)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine ⟨chartPushedChosenFirstPartial_memW1p_two
    (I := I) (M := M) g α hu_h l₁, ?_⟩
  intro l₂
  have h_chosenSecond :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂)
        (chartTargetEuclid (I := I) (M := M) α) :=
    chosenSecondPartialChartPushedU_memWkp_two_two_of_twice_diff_identity
      (I := I) (M := M) g α hu_h l₁ l₂ (h_twice_identities l₁ l₂)
  change DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
    (d := Module.finrank ℝ E) 2 2
    (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂)
    (chartTargetEuclid (I := I) (M := M) α)
  exact h_chosenSecond

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.chartPushedChosenFirstPartial_memWkp_three_two_of_twice_diff_identities then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.chartPushedChosenFirstPartial_memWkp_three_two_of_twice_diff_identities"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.chartPushedChosenFirstPartial_memWkp_three_two_of_twice_diff_identities ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.chartPushedChosenFirstPartial_memWkp_three_two_of_twice_diff_identities

theorem chartPushed_memWkp_four_two_of_laplacianDomainPow_two_of_twice_diff_identities
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_twice_identities :
      ∀ l₁ l₂ : Fin (Module.finrank ℝ E),
        ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
          (∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α i j y *
                  chosenThirdMixedPartialChartPushedU
                    (I := I) (M := M) g α u_h i l₁ l₂ y *
                  (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
          + (∫ y in chartTargetEuclid (I := I) (M := M) α,
              densityOnEuclid (I := I) g α y *
                chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
              ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
              effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 4 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  classical
  refine ⟨chartPushed_memW1p_two_of_laplacianDomainPow_two
    (I := I) (M := M) g α hu_h, ?_⟩
  intro l₁
  change DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
    (d := Module.finrank ℝ E) 3 2
    (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l₁)
    (chartTargetEuclid (I := I) (M := M) α)
  exact chartPushedChosenFirstPartial_memWkp_three_two_of_twice_diff_identities
    (I := I) (M := M) g α hu_h h_twice_identities l₁

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.chartPushed_memWkp_four_two_of_laplacianDomainPow_two_of_twice_diff_identities then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.chartPushed_memWkp_four_two_of_laplacianDomainPow_two_of_twice_diff_identities"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.chartPushed_memWkp_four_two_of_laplacianDomainPow_two_of_twice_diff_identities ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.chartPushed_memWkp_four_two_of_laplacianDomainPow_two_of_twice_diff_identities

theorem chartSideH2kBridge_two_of_twice_diff_identities
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_twice_identities :
      ∀ α : M, ∀ l₁ l₂ : Fin (Module.finrank ℝ E),
        ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
          (∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α i j y *
                  chosenThirdMixedPartialChartPushedU
                    (I := I) (M := M) g α u_h i l₁ l₂ y *
                  (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
          + (∫ y in chartTargetEuclid (I := I) (M := M) α,
              densityOnEuclid (I := I) g α y *
                chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
              ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
              effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) :
    ChartSideH2kBridge (I := I) (M := M) 2
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  intro α
  have h_eq : (2 : ℕ) * 2 = 4 := by norm_num
  rw [h_eq]
  exact chartPushed_memWkp_four_two_of_laplacianDomainPow_two_of_twice_diff_identities
    (I := I) (M := M) g α hu_h (h_twice_identities α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.chartSideH2kBridge_two_of_twice_diff_identities then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.chartSideH2kBridge_two_of_twice_diff_identities"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.chartSideH2kBridge_two_of_twice_diff_identities ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.chartSideH2kBridge_two_of_twice_diff_identities

theorem laplacianDomainPow_memWkpChart_four_two_of_twice_diff_identities
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_twice_identities :
      ∀ α : M, ∀ l₁ l₂ : Fin (Module.finrank ℝ E),
        ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
          (∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α i j y *
                  chosenThirdMixedPartialChartPushedU
                    (I := I) (M := M) g α u_h i l₁ l₂ y *
                  (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
          + (∫ y in chartTargetEuclid (I := I) (M := M) α,
              densityOnEuclid (I := I) g α y *
                chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
              ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
              effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  have h_bridge := chartSideH2kBridge_two_of_twice_diff_identities
    (I := I) (M := M) g hu_h h_twice_identities
  have h := laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
    (I := I) (M := M) g 2 h_bridge
  have h_eq : (2 : ℕ) * 2 = 4 := by norm_num
  rw [h_eq] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.laplacianDomainPow_memWkpChart_four_two_of_twice_diff_identities then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.laplacianDomainPow_memWkpChart_four_two_of_twice_diff_identities"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.laplacianDomainPow_memWkpChart_four_two_of_twice_diff_identities ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth.laplacianDomainPow_memWkpChart_four_two_of_twice_diff_identities

end ChartPushedMemWkpFourSmooth
end Laplacian
end Analysis
end DifferentialGeometry

end
