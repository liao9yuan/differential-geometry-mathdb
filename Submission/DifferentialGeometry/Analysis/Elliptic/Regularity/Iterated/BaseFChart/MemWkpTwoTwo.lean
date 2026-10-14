import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothApproxSeq.CauchyW22
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothApproxSeq.IdentificationW22
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBoundW22
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2RegularitySuccessor

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace BaseFChartMemW22

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBoundW22
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchyW22
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqIdentificationW22
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
lemma smoothFChartResidual_memWkp_two_two
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (smoothFChartResidual (I := I) (M := M) g α v)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_ae := smoothFChartResidual_ae_eq_chartPushedRaw_smoothRep
    (I := I) (M := M) g α v
  have h_ptwise : chartPushedRaw (I := I) (M := M) α
        (smoothRep (I := I) (M := M) g α v) =
      fun y => -chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y -
        chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun) y := by
    funext y
    exact chartPushedRaw_smoothRep_eq (I := I) (M := M) g α v y
  have hP_grad : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_smooth := gradInnerPiece_smooth (I := I) (M := M) g α v
    have h_support := tsupport_gradInnerPiece_subset_source
      (I := I) (M := M) g α v.toFun
    have hCP_smooth : ContDiff ℝ ∞
        (chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun)) :=
      chartPushedRaw_contDiff (I := I) (M := M) h_smooth h_support
    have hCP_compact : HasCompactSupport
        (chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun)) :=
      chartPushedRaw_smooth_hasCompactSupport_local (I := I) (M := M) h_support
    have hCP_tsupp : tsupport (chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun)) ⊆
        chartTargetEuclid (I := I) (M := M) α :=
      tsupport_chartPushedRaw_subset_chartTargetEuclid (I := I) (M := M) h_support
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := Module.finrank ℝ E)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      hCP_smooth hCP_compact hCP_tsupp (by norm_num : (1 : ℝ≥0∞) ≤ 2) 2
  have hP_lap : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chartPushedRaw (I := I) (M := M) α
        (lapPiece (I := I) (M := M) g α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_smooth := lapPiece_smooth (I := I) (M := M) g α v
    have h_support := tsupport_lapPiece_subset_source
      (I := I) (M := M) g α v.toFun
    have hCP_smooth : ContDiff ℝ ∞
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun)) :=
      chartPushedRaw_contDiff (I := I) (M := M) h_smooth h_support
    have hCP_compact : HasCompactSupport
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun)) :=
      chartPushedRaw_smooth_hasCompactSupport_local (I := I) (M := M) h_support
    have hCP_tsupp : tsupport (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun)) ⊆
        chartTargetEuclid (I := I) (M := M) α :=
      tsupport_chartPushedRaw_subset_chartTargetEuclid (I := I) (M := M) h_support
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := Module.finrank ℝ E)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      hCP_smooth hCP_compact hCP_tsupp (by norm_num : (1 : ℝ≥0∞) ≤ 2) 2
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hP_negA : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.const_smul
      (d := Module.finrank ℝ E) hp_one hΩ_open hP_grad (-1 : ℝ)
  have hP_negB : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
        (lapPiece (I := I) (M := M) g α v.toFun) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.const_smul
      (d := Module.finrank ℝ E) hp_one hΩ_open hP_lap (-1 : ℝ)
  have hP_sum : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun) y +
        (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.add hp_one hΩ_open
      hP_negA hP_negB
  have h_eq_sum :
      (fun y : EuclN => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y +
        (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun) y) =
      chartPushedRaw (I := I) (M := M) α
        (smoothRep (I := I) (M := M) g α v) := by
    funext y
    rw [h_ptwise]
    ring
  rw [h_eq_sum] at hP_sum
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    hp_one hΩ_open h_ae.symm).mp hP_sum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.smoothFChartResidual_memWkp_two_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.smoothFChartResidual_memWkp_two_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.smoothFChartResidual_memWkp_two_two ``Submission.DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.smoothFChartResidual_memWkp_two_two

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkp_fChartResidual_of_wkpNorm_cauchy_identification_w22
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (v : ℕ → SmoothScalar g)
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 2 2
        (fun y => smoothFChartResidual (I := I) (M := M) g α (v m) y -
          smoothFChartResidual (I := I) (M := M) g α (v n) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε)
    (h_identification : ∀ F_lim : EuclN → ℝ,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2 F_lim
        (chartTargetEuclid (I := I) (M := M) α) →
      _root_.Filter.Tendsto (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 2 2
          (fun y => smoothFChartResidual (I := I) (M := M) g α (v n) y - F_lim y)
          (chartTargetEuclid (I := I) (M := M) α))
        _root_.Filter.atTop (𝓝 0) →
      F_lim =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
        (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_smooth_W2p : ∀ n,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (smoothFChartResidual (I := I) (M := M) g α (v n))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro n
    exact smoothFChartResidual_memWkp_two_two (I := I) (M := M) g α (v n)
  obtain ⟨F_lim, hF_lim_memWkp, hF_lim_tendsto⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.exists_limit_of_wkpNorm_cauchy
      (hΩ_open := chartTargetEuclid_isOpen (I := I) (M := M) α)
      (k := 2) (p := 2) (hp_one := by norm_num)
      (u := fun n => smoothFChartResidual (I := I) (M := M) g α (v n))
      h_smooth_W2p h_cauchy
  have hF_lim_aeEq := h_identification F_lim hF_lim_memWkp hF_lim_tendsto
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    hF_lim_aeEq).mp hF_lim_memWkp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.memWkp_fChartResidual_of_wkpNorm_cauchy_identification_w22 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.memWkp_fChartResidual_of_wkpNorm_cauchy_identification_w22"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.memWkp_fChartResidual_of_wkpNorm_cauchy_identification_w22 ``Submission.DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.memWkp_fChartResidual_of_wkpNorm_cauchy_identification_w22

theorem fChartResidual_memWkp_two_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (fChartResidual (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) :=
  memWkp_fChartResidual_of_wkpNorm_cauchy_identification_w22
    (I := I) (M := M) g α
    (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h)
    (smoothApproxSeq_smoothFChartResidual_wkpNorm_cauchy_w22
      (I := I) (M := M) g α hu_h)
    (smoothApproxSeqWkpThree_smoothFChartResidual_limit_eq_fChartResidual_w22
      (I := I) (M := M) g α hu_h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.fChartResidual_memWkp_two_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.fChartResidual_memWkp_two_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.fChartResidual_memWkp_two_two ``Submission.DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.fChartResidual_memWkp_two_two

theorem base_f_chart_memWkp_two_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).fChart
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_decomp := base_f_chart_ae_eq_piecePreimage_add_residual_chartPulled_on_vol
    (I := I) (M := M) g α hu_h
  have h_piece1_memWkp := fChartPiecePreimage_memWkp_two_two
    (I := I) (M := M) g α hu_h
  have h_residual_memWkp := fChartResidual_memWkp_two_two
    (I := I) (M := M) g α hu_h
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_sum_memWkp :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (fun y => fChartPiecePreimage (I := I) (M := M) g α hu_h y +
          fChartResidual (I := I) (M := M) g α u_h y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.add hp_one hΩ_open
      h_piece1_memWkp h_residual_memWkp
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    hp_one hΩ_open h_decomp.symm).mp h_sum_memWkp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.base_f_chart_memWkp_two_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.base_f_chart_memWkp_two_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.base_f_chart_memWkp_two_two ``Submission.DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22.base_f_chart_memWkp_two_two

end BaseFChartMemW22
end Laplacian
end Analysis
end DifferentialGeometry

end
