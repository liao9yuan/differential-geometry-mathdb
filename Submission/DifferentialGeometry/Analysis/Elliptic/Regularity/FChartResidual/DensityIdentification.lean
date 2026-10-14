import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplResidualMemW1p
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplResidual
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.FChartResidual.MemW1pResidual
import Submission.DifferentialGeometry.Analysis.Sobolev.Approximation.Density.HigherOrder
import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Morrey.HigherOrder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace FChartResidualDensityIdentification

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
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidualMemW1p
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem exists_smoothApprox_chartW22
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : SmoothScalar g, wkpNormChart (I := I) (M := M) 2 2
      (fun x => ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        v.toFun x) ≤ ENNReal.ofReal ε := by
  classical
  set u : M → ℝ := ((H1ComplToLp (I := I) (M := M) g u_h :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) with hu_def
  have h_u_mem : MemWkpChart (I := I) (M := M) 2 2 u :=
    (DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_two_h2_plus_rhs_h2
      (I := I) (M := M) g hu_h).1.1
  obtain ⟨w, hw_smooth, hw_le⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.contMDiff_dense_in_WkpChart_k
      (I := I) (M := M) 2 (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) h_u_mem hε
  refine ⟨⟨w, hw_smooth⟩, ?_⟩
  exact hw_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.exists_smoothApprox_chartW22 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.exists_smoothApprox_chartW22"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.exists_smoothApprox_chartW22 ``Submission.DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.exists_smoothApprox_chartW22

noncomputable def smoothApproxSeq
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (n : ℕ) : SmoothScalar g :=
  (exists_smoothApprox_chartW22 (I := I) (M := M) g hu_h
    (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.smoothApproxSeq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.smoothApproxSeq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.smoothApproxSeq ``Submission.DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.smoothApproxSeq

theorem smoothApproxSeq_wkpNormChart_le
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (n : ℕ) :
    wkpNormChart (I := I) (M := M) 2 2
      (fun x => ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        (smoothApproxSeq (I := I) (M := M) g hu_h n).toFun x) ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
  (exists_smoothApprox_chartW22 (I := I) (M := M) g hu_h
    (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))).choose_spec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.smoothApproxSeq_wkpNormChart_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.smoothApproxSeq_wkpNormChart_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.smoothApproxSeq_wkpNormChart_le ``Submission.DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.smoothApproxSeq_wkpNormChart_le

theorem smoothApproxSeq_wkpNormChart_diff_le
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (m n : ℕ) :
    wkpNormChart (I := I) (M := M) 2 2
      (fun x => (smoothApproxSeq (I := I) (M := M) g hu_h m).toFun x -
        (smoothApproxSeq (I := I) (M := M) g hu_h n).toFun x) ≤
      ENNReal.ofReal (1 / ((m : ℝ) + 1)) + ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  classical
  set u : M → ℝ := ((H1ComplToLp (I := I) (M := M) g u_h :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) with hu_def
  set vm : SmoothScalar g := smoothApproxSeq (I := I) (M := M) g hu_h m
  set vn : SmoothScalar g := smoothApproxSeq (I := I) (M := M) g hu_h n
  have h_decomp : (fun x => vm.toFun x - vn.toFun x) =
      (fun x => (u x - vn.toFun x) - (u x - vm.toFun x)) := by
    funext x; ring
  rw [h_decomp]
  have h_u_mem : MemWkpChart (I := I) (M := M) 2 2 u :=
    (DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_two_h2_plus_rhs_h2
      (I := I) (M := M) g hu_h).1.1
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_smooth_vm : MemWkpChart (I := I) (M := M) 2 2 vm.toFun :=
    DifferentialGeometry.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := I) (M := M) hp_one 2 vm.smooth
  have h_smooth_vn : MemWkpChart (I := I) (M := M) 2 2 vn.toFun :=
    DifferentialGeometry.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := I) (M := M) hp_one 2 vn.smooth
  have h_u_diff_vm : MemWkpChart (I := I) (M := M) 2 2 (fun x => u x - vm.toFun x) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_sub
      (I := I) (M := M) hp_one h_u_mem h_smooth_vm
  have h_u_diff_vn : MemWkpChart (I := I) (M := M) 2 2 (fun x => u x - vn.toFun x) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_sub
      (I := I) (M := M) hp_one h_u_mem h_smooth_vn
  have h_split : (fun x : M => (u x - vn.toFun x) - (u x - vm.toFun x)) =
      (fun x : M => (u x - vn.toFun x) + (-1 : ℝ) * (u x - vm.toFun x)) := by
    funext x; ring
  rw [h_split]
  have h_neg_smul :
      wkpNormChart (I := I) (M := M) 2 2
        (fun x => (-1 : ℝ) * (u x - vm.toFun x)) =
      ‖(-1 : ℝ)‖ₑ * wkpNormChart (I := I) (M := M) 2 2 (fun x => u x - vm.toFun x) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_const_smul
      (I := I) (M := M) hp_one (-1 : ℝ) h_u_diff_vm
  have h_neg_one_norm : ‖(-1 : ℝ)‖ₑ = 1 := by
    simp [_root_.ENorm.enorm]
  rw [h_neg_one_norm, one_mul] at h_neg_smul
  have h_u_diff_vm_neg : MemWkpChart (I := I) (M := M) 2 2
      (fun x => (-1 : ℝ) * (u x - vm.toFun x)) := by
    have h_eq : (fun x : M => (-1 : ℝ) * (u x - vm.toFun x)) =
        (fun x => -(u x - vm.toFun x)) := by funext x; ring
    rw [h_eq]
    exact DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_neg
      (I := I) (M := M) hp_one h_u_diff_vm
  have h_add :=
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_add_le (I := I) (M := M)
      (k := 2) (p := 2) hp_one h_u_diff_vn h_u_diff_vm_neg
  rw [h_neg_smul] at h_add
  have h_bound1 : wkpNormChart (I := I) (M := M) 2 2 (fun x => u x - vn.toFun x) +
        wkpNormChart (I := I) (M := M) 2 2 (fun x => u x - vm.toFun x) ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) + ENNReal.ofReal (1 / ((m : ℝ) + 1)) :=
    add_le_add
      (smoothApproxSeq_wkpNormChart_le (I := I) (M := M) g hu_h n)
      (smoothApproxSeq_wkpNormChart_le (I := I) (M := M) g hu_h m)
  have h_comm : ENNReal.ofReal (1 / ((n : ℝ) + 1)) + ENNReal.ofReal (1 / ((m : ℝ) + 1)) =
      ENNReal.ofReal (1 / ((m : ℝ) + 1)) + ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    rw [add_comm]
  exact le_trans h_add (le_of_le_of_eq h_bound1 h_comm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.smoothApproxSeq_wkpNormChart_diff_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.smoothApproxSeq_wkpNormChart_diff_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.smoothApproxSeq_wkpNormChart_diff_le ``Submission.DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.smoothApproxSeq_wkpNormChart_diff_le

theorem fChartResidual_memW1p_of_cauchy_identification
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y =>
          smoothFChartResidual
            (I := I) (M := M) g α (smoothApproxSeq (I := I) (M := M) g hu_h m) y -
          smoothFChartResidual
            (I := I) (M := M) g α (smoothApproxSeq (I := I) (M := M) g hu_h n) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε)
    (h_identification : ∀ F_lim : EuclN → ℝ,
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 F_lim
        (chartTargetEuclid (I := I) (M := M) α) →
      _root_.Filter.Tendsto (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (fun y =>
            smoothFChartResidual
              (I := I) (M := M) g α (smoothApproxSeq (I := I) (M := M) g hu_h n) y -
            F_lim y)
          (chartTargetEuclid (I := I) (M := M) α))
        _root_.Filter.atTop (𝓝 0) →
      F_lim =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
        (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) :=
  memW1p_fChartResidual_of_wkpNorm_cauchy_identification
    (I := I) (M := M) g α (smoothApproxSeq (I := I) (M := M) g hu_h)
    h_cauchy h_identification

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.fChartResidual_memW1p_of_cauchy_identification then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.fChartResidual_memW1p_of_cauchy_identification"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.fChartResidual_memW1p_of_cauchy_identification ``Submission.DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.fChartResidual_memW1p_of_cauchy_identification

end FChartResidualDensityIdentification
end Laplacian
end Analysis
end DifferentialGeometry

end
