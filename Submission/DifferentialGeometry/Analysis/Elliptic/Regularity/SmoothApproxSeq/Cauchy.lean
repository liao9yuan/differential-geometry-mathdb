import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.FChartResidual.DensityIdentification
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBound
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.Linearity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace SmoothApproxSeqCauchy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualLinearity
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private noncomputable def smoothScalarSub
    {g : SmoothRiemannianMetric I M}
    (v₁ v₂ : SmoothScalar g) : SmoothScalar g :=
  { toFun := fun x => v₁.toFun x - v₂.toFun x
    smooth := v₁.smooth.sub v₂.smooth }

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.smoothScalarSub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.smoothScalarSub target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private lemma smoothScalarSub_toFun
    {g : SmoothRiemannianMetric I M}
    (v₁ v₂ : SmoothScalar g) :
    (smoothScalarSub v₁ v₂).toFun = fun x => v₁.toFun x - v₂.toFun x := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.smoothScalarSub_toFun
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.smoothScalarSub_toFun target :: scope.openDecls } }

theorem smoothApproxSeq_smoothFChartResidual_wkpNorm_cauchy
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y =>
          smoothFChartResidual
            (I := I) (M := M) g α
            (DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.smoothApproxSeq
              (I := I) (M := M) g hu_h m) y -
          smoothFChartResidual
            (I := I) (M := M) g α
            (DifferentialGeometry.Analysis.Laplacian.FChartResidualDensityIdentification.smoothApproxSeq
              (I := I) (M := M) g hu_h n) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε := by
  classical
  intro ε hε
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    wkpNorm_smoothFChartResidual_le_wkpNormChart (I := I) (M := M) g α
  have hε_C_pos : 0 < ε / (2 * C) := by positivity
  obtain ⟨N0, hN0_real⟩ := exists_nat_gt (1 / (ε / (2 * C)) - 1)
  have hN1_pos : (0 : ℝ) < (N0 : ℝ) + 1 := by
    have h_pos : 0 < 1 / (ε / (2 * C)) := by positivity
    linarith
  have hN0_inv_real : (1 : ℝ) / ((N0 : ℝ) + 1) ≤ ε / (2 * C) := by
    rw [div_le_iff₀ hN1_pos]
    have h1 : (1 : ℝ) = (ε / (2 * C)) * (1 / (ε / (2 * C))) := by
      rw [mul_one_div, div_self hε_C_pos.ne']
    rw [h1]
    apply mul_le_mul_of_nonneg_left _ hε_C_pos.le
    linarith
  refine ⟨N0, ?_⟩
  intro m n hm hn
  set vm : SmoothScalar g := smoothApproxSeq (I := I) (M := M) g hu_h m with hvm_def
  set vn : SmoothScalar g := smoothApproxSeq (I := I) (M := M) g hu_h n with hvn_def
  set vdiff : SmoothScalar g := smoothScalarSub vm vn with hvdiff_def
  have hvdiff_toFun :
      vdiff.toFun = fun x => vm.toFun x - vn.toFun x :=
    smoothScalarSub_toFun vm vn
  have h_ae_sub :=
    smoothFChartResidual_ae_sub (I := I) (M := M) g α vm vn vdiff hvdiff_toFun
  have h_wkp_eq :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y =>
          smoothFChartResidual
            (I := I) (M := M) g α vm y -
          smoothFChartResidual
            (I := I) (M := M) g α vn y)
        (chartTargetEuclid (I := I) (M := M) α) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (smoothFChartResidual
          (I := I) (M := M) g α vdiff)
        (chartTargetEuclid (I := I) (M := M) α) := by
    refine DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) ?_
    exact h_ae_sub.symm
  rw [h_wkp_eq]
  have h_bilinear := hC_bound vdiff
  have h_chartW22_cauchy :
      wkpNormChart (I := I) (M := M) 2 2 vdiff.toFun ≤
        ENNReal.ofReal ((1 : ℝ) / ((m : ℝ) + 1)) +
          ENNReal.ofReal ((1 : ℝ) / ((n : ℝ) + 1)) := by
    rw [hvdiff_toFun]
    exact smoothApproxSeq_wkpNormChart_diff_le (I := I) (M := M) g hu_h m n
  have h_step :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (smoothFChartResidual
          (I := I) (M := M) g α vdiff)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C *
        (ENNReal.ofReal ((1 : ℝ) / ((m : ℝ) + 1)) +
          ENNReal.ofReal ((1 : ℝ) / ((n : ℝ) + 1))) := by
    refine h_bilinear.trans ?_
    exact mul_le_mul_of_nonneg_left h_chartW22_cauchy (zero_le)
  refine h_step.trans ?_
  have hN0m : (N0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hN0n : (N0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hm_inv_le : (1 : ℝ) / ((m : ℝ) + 1) ≤ (1 : ℝ) / ((N0 : ℝ) + 1) := by
    apply div_le_div_of_nonneg_left zero_le_one hN1_pos
    linarith
  have hn_inv_le : (1 : ℝ) / ((n : ℝ) + 1) ≤ (1 : ℝ) / ((N0 : ℝ) + 1) := by
    apply div_le_div_of_nonneg_left zero_le_one hN1_pos
    linarith
  have hm_ofReal_le :
      ENNReal.ofReal ((1 : ℝ) / ((m : ℝ) + 1)) ≤
        ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) :=
    ENNReal.ofReal_le_ofReal hm_inv_le
  have hn_ofReal_le :
      ENNReal.ofReal ((1 : ℝ) / ((n : ℝ) + 1)) ≤
        ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) :=
    ENNReal.ofReal_le_ofReal hn_inv_le
  have hsum_le :
      ENNReal.ofReal ((1 : ℝ) / ((m : ℝ) + 1)) +
        ENNReal.ofReal ((1 : ℝ) / ((n : ℝ) + 1)) ≤
      ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) +
        ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) :=
    add_le_add hm_ofReal_le hn_ofReal_le
  have hC_step :
      ENNReal.ofReal C *
        (ENNReal.ofReal ((1 : ℝ) / ((m : ℝ) + 1)) +
          ENNReal.ofReal ((1 : ℝ) / ((n : ℝ) + 1))) ≤
      ENNReal.ofReal C *
        (ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) +
          ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_left hsum_le (zero_le)
  refine hC_step.trans ?_
  have hN0_inv_pos : (0 : ℝ) ≤ (1 : ℝ) / ((N0 : ℝ) + 1) := by positivity
  have h_add :
      ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) +
        ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) =
      ENNReal.ofReal (2 * ((1 : ℝ) / ((N0 : ℝ) + 1))) := by
    rw [show (2 : ℝ) * ((1 : ℝ) / ((N0 : ℝ) + 1)) =
        ((1 : ℝ) / ((N0 : ℝ) + 1)) + ((1 : ℝ) / ((N0 : ℝ) + 1)) by ring,
      ENNReal.ofReal_add hN0_inv_pos hN0_inv_pos]
  rw [h_add]
  have hprod_eq :
      ENNReal.ofReal C * ENNReal.ofReal (2 * ((1 : ℝ) / ((N0 : ℝ) + 1))) =
      ENNReal.ofReal (C * (2 * ((1 : ℝ) / ((N0 : ℝ) + 1)))) := by
    rw [← ENNReal.ofReal_mul hC_pos.le]
  rw [hprod_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have h_step_real :
      C * (2 * ((1 : ℝ) / ((N0 : ℝ) + 1))) ≤
      C * (2 * (ε / (2 * C))) := by
    apply mul_le_mul_of_nonneg_left _ hC_pos.le
    apply mul_le_mul_of_nonneg_left hN0_inv_real (by norm_num : (0 : ℝ) ≤ 2)
  refine h_step_real.trans ?_
  have h_simp : C * (2 * (ε / (2 * C))) = ε := by
    field_simp
  rw [h_simp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.smoothApproxSeq_smoothFChartResidual_wkpNorm_cauchy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.smoothApproxSeq_smoothFChartResidual_wkpNorm_cauchy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.smoothApproxSeq_smoothFChartResidual_wkpNorm_cauchy ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy.smoothApproxSeq_smoothFChartResidual_wkpNorm_cauchy

end SmoothApproxSeqCauchy
end Laplacian
end Analysis
end DifferentialGeometry

end
