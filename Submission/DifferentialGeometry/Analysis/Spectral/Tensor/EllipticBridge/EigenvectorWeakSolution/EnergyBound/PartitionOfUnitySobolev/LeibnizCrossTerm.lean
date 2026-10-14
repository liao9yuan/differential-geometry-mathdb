import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovariantDerivative.PartitionOfUnitySobolevRegularity
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cutoff.ChartComponentSobolevBounds
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.PartitionOfUnitySobolev.ComponentNormComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity

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

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma eigenIdx_val_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val := by
  obtain ⟨u, hu_mem, hu_ne⟩ := i.fst.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ tensorResolventEigenspace
      (I := I) (M := M) g r s i.fst.val := hu_mem
  exact (tensorResolvent_eigenvalue_mem_unit_interval
    (I := I) (M := M) g r s hu_in hu_ne).1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenIdx_val_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenIdx_val_pos target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound

omit [CompleteSpace E] in
lemma covGradPouLeibnizCrossLimit_memWkp_and_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)
    (h_pou_phi : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (covGradPouLeibnizCrossLimit (I := I) (M := M)
          g r s i β P k)
        (chartTargetEuclid (I := I) (M := M) β) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (covGradPouLeibnizCrossLimit (I := I) (M := M)
              g r s i β P k)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal C *
            covGradAggregate (I := I) (M := M) g r s i K β := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have h_eigen_K : ∀ (β' : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β' Q :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β') := by
    intro β' Q
    exact (eigenvectorVec_pou_memWkp_and_wkpNorm_le (I := I) (M := M)
      g r s i K β' Q
      ((h_pou_phi β' Q).le_of_le (Nat.le_succ K))).1
  have hpou_support : tsupport
      ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H β).source :=
    chartAtlasPOU_isSubordinate I M β
  have hpou_pushed_smooth : ContDiff ℝ ∞
      (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
    Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
      (I := I) (M := M)
      (chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯).contMDiff hpou_support
  have hpou_pushed_cs : HasCompactSupport
      (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
    chartPushedRaw_smooth_hasCompactSupport_local
      (I := I) (M := M) hpou_support
  have hmult_smooth : ContDiff ℝ ∞
      (euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ))) :=
    euclidPartial_contDiff (E := E) hpou_pushed_smooth k
  have hmult_smooth' : ContDiff ℝ (⊤ : ℕ∞)
      (euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ))) :=
    hmult_smooth
  have hmult_cs : HasCompactSupport
      (euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ))) := by
    apply HasCompactSupport.of_support_subset_isCompact hpou_pushed_cs
    intro y hy
    by_contra hy_off
    exact hy (by
      have h := euclidPartial_def (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y
      have hopen : IsOpen ((tsupport
          (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)))ᶜ) :=
        (isClosed_tsupport _).isOpen_compl
      have hevt : (chartPushedRaw I β
            ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ))
          =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) :=
        Filter.eventually_of_mem (hopen.mem_nhds hy_off)
          (fun z hz => image_eq_zero_of_notMem_tsupport hz)
      rw [h, hevt.fderiv_eq]
      simp)
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hmult_smooth' hmult_cs K
  have hcutoff_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β P :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    tensorL2ChartComponentCutoff_memWkp_of_pou (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
      β P K (fun β' Q => h_eigen_K β' Q)
  obtain ⟨cutoffConstant, cutoffConstant_nonneg, cutoff_bound⟩ :=
    wkpNorm_tensorL2ChartComponentCutoff_le_of_pou (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
      β P K (fun β' Q => h_eigen_K β' Q)
  obtain ⟨Kmul, hKmul_pos, hKmul_bd⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ_open hmult_smooth'
      hC₀_nn (fun j _hj y _hy => hC₀_bd y j _hj)
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (covGradPouLeibnizCrossLimit (I := I) (M := M)
        g r s i β P k) Ω := by
    have h_prod : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y =>
          euclidPartial (E := E) k
              (chartPushedRaw I β
                ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
      MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hmult_smooth'
        (fun j _hj y _hy => hC₀_bd y j _hj) hcutoff_memWkp
    change MemWkp (d := Module.finrank ℝ E) K 2
        (fun y =>
          euclidPartial (E := E) k
              (chartPushedRaw I β
                ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
    exact h_prod
  have h_transport_le : ∀ β' ∈ transportChartCenters (I := I) (M := M) β,
      ∀ Q : TensorCompIdx (E := E) r s,
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β' Q :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β')
        ≤ ENNReal.ofReal ‖(i.fst.val)⁻¹‖ *
          covGradAggregate (I := I) (M := M) g r s i K β := by
    intro β' hβ' Q
    refine le_trans (eigenvectorVec_pou_memWkp_and_wkpNorm_le
      (I := I) (M := M) g r s i K β' Q
      ((h_pou_phi β' Q).le_of_le (Nat.le_succ K))).2 ?_
    refine mul_le_mul_of_nonneg_left ?_ (zero_le)
    refine le_trans (wkpNorm_mono_order (d := Module.finrank ℝ E)
      (Nat.le_succ K) _ _) ?_
    exact chartCompNorm_transport_le_covGradAggregate (I := I)
      (M := M) g r s i K hβ' Q
  set Saggr : ℝ≥0∞ := covGradAggregate (I := I) (M := M) g r s i K β
    with hSaggr_def
  have h_double_le :
      (∑ β' ∈ transportChartCenters (I := I) (M := M) β,
        ∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i) β' Q :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β'))
        ≤ (∑ _β' ∈ transportChartCenters (I := I) (M := M) β,
            ∑ _Q : TensorCompIdx (E := E) r s,
              ENNReal.ofReal ‖(i.fst.val)⁻¹‖ * Saggr) :=
    Finset.sum_le_sum (fun β' hβ' =>
      Finset.sum_le_sum (fun Q _ => h_transport_le β' hβ' Q))
  have h_double_const :
      (∑ _β' ∈ transportChartCenters (I := I) (M := M) β,
        ∑ _Q : TensorCompIdx (E := E) r s,
          ENNReal.ofReal ‖(i.fst.val)⁻¹‖ * Saggr)
        = ENNReal.ofReal
            (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
              ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
                ‖(i.fst.val)⁻¹‖)) * Saggr := by
    have h_sum : (∑ _β' ∈ transportChartCenters (I := I) (M := M) β,
        ∑ _Q : TensorCompIdx (E := E) r s,
          ENNReal.ofReal ‖(i.fst.val)⁻¹‖ * Saggr)
        = (((transportChartCenters (I := I) (M := M) β).card : ℝ≥0∞) *
            ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ≥0∞) *
              (ENNReal.ofReal ‖(i.fst.val)⁻¹‖ * Saggr))) := by
      rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        nsmul_eq_mul]
    rw [h_sum]
    rw [show ENNReal.ofReal
          (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
            ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
              ‖(i.fst.val)⁻¹‖))
        = ((transportChartCenters (I := I) (M := M) β).card : ℝ≥0∞) *
            ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ≥0∞) *
              ENNReal.ofReal ‖(i.fst.val)⁻¹‖) by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]]
    ring
  have h_cutoff_le : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β P :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
      ≤ ENNReal.ofReal cutoffConstant *
        (ENNReal.ofReal
            (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
              ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
                ‖(i.fst.val)⁻¹‖)) * Saggr) := by
    refine le_trans cutoff_bound ?_
    refine mul_le_mul_of_nonneg_left ?_ (zero_le)
    rw [← h_double_const]
    exact h_double_le
  refine ⟨h_prod_memWkp,
    Kmul * (cutoffConstant *
      (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
        ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
          ‖(i.fst.val)⁻¹‖))),
    by positivity, ?_⟩
  have h_unfold : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (covGradPouLeibnizCrossLimit (I := I) (M := M)
        g r s i β P k) Ω =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y =>
          euclidPartial (E := E) k
              (chartPushedRaw I β
                ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    rfl
  rw [h_unfold]
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y =>
          euclidPartial (E := E) k
              (chartPushedRaw I β
                ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
        ≤ ENNReal.ofReal Kmul *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I)
                      (M := M) g r s) i)
                  β P : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                  EuclN → ℝ) y) Ω :=
      hKmul_bd hcutoff_memWkp
    _ ≤ ENNReal.ofReal Kmul *
          (ENNReal.ofReal cutoffConstant *
            (ENNReal.ofReal
                (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
                  ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
                    ‖(i.fst.val)⁻¹‖)) * Saggr)) :=
      mul_le_mul_of_nonneg_left h_cutoff_le (zero_le)
    _ = ENNReal.ofReal
          (Kmul * (cutoffConstant *
            (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
              ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
                ‖(i.fst.val)⁻¹‖)))) * Saggr := by
      rw [ENNReal.ofReal_mul (le_of_lt hKmul_pos),
        ENNReal.ofReal_mul cutoffConstant_nonneg]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradPouLeibnizCrossLimit_memWkp_and_wkpNorm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradPouLeibnizCrossLimit_memWkp_and_wkpNorm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradPouLeibnizCrossLimit_memWkp_and_wkpNorm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradPouLeibnizCrossLimit_memWkp_and_wkpNorm_le

omit [CompleteSpace E] in
lemma covGradPouLeibnizCrossLimit_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (K : ℕ)
    (h_pou_phi : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (covGradPouLeibnizCrossLimit (I := I) (M := M)
              g r s i β P k)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            covGradAggregate (I := I) (M := M) g r s i K β := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have hpou_support : tsupport
      ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H β).source :=
    chartAtlasPOU_isSubordinate I M β
  have hpou_pushed_smooth : ContDiff ℝ ∞
      (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
    Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
      (I := I) (M := M)
      (chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯).contMDiff hpou_support
  have hpou_pushed_cs : HasCompactSupport
      (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
    chartPushedRaw_smooth_hasCompactSupport_local
      (I := I) (M := M) hpou_support
  have hmult_smooth : ContDiff ℝ ∞
      (euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ))) :=
    euclidPartial_contDiff (E := E) hpou_pushed_smooth k
  have hmult_smooth' : ContDiff ℝ (⊤ : ℕ∞)
      (euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ))) :=
    hmult_smooth
  have hmult_cs : HasCompactSupport
      (euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ))) := by
    apply HasCompactSupport.of_support_subset_isCompact hpou_pushed_cs
    intro y hy
    by_contra hy_off
    exact hy (by
      have h := euclidPartial_def (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y
      have hopen : IsOpen ((tsupport
          (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)))ᶜ) :=
        (isClosed_tsupport _).isOpen_compl
      have hevt : (chartPushedRaw I β
            ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ))
          =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) :=
        Filter.eventually_of_mem (hopen.mem_nhds hy_off)
          (fun z hz => image_eq_zero_of_notMem_tsupport hz)
      rw [h, hevt.fderiv_eq]
      simp)
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hmult_smooth' hmult_cs K
  obtain ⟨Kmul, hKmul_pos, hKmul_bd⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ_open hmult_smooth'
      hC₀_nn (fun j _hj y _hy => hC₀_bd y j _hj)
  obtain ⟨cutoffConstant, cutoffConstant_nonneg, cutoff_bound⟩ :=
    wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform (I := I) (M := M)
      g r s β P K
  refine ⟨Kmul * (cutoffConstant *
      (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
        (Fintype.card (TensorCompIdx (E := E) r s) : ℝ))),
    by positivity, fun i => ?_⟩
  have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_norm : ‖(i.fst.val)⁻¹‖ = (i.fst.val)⁻¹ := Real.norm_of_nonneg hμ_inv_nn
  set Saggr : ℝ≥0∞ := covGradAggregate (I := I) (M := M) g r s i K β
    with hSaggr_def
  have h_eigen_K : ∀ (β' : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β' Q :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β') := by
    intro β' Q
    exact (eigenvectorVec_pou_memWkp_and_wkpNorm_le (I := I) (M := M)
      g r s i K β' Q
      ((h_pou_phi i β' Q).le_of_le (Nat.le_succ K))).1
  have hcutoff_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β P :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    tensorL2ChartComponentCutoff_memWkp_of_pou (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
      β P K (fun β' Q => h_eigen_K β' Q)
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (covGradPouLeibnizCrossLimit (I := I) (M := M)
        g r s i β P k) Ω := by
    have h_prod : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y =>
          euclidPartial (E := E) k
              (chartPushedRaw I β
                ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
      MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hmult_smooth'
        (fun j _hj y _hy => hC₀_bd y j _hj) hcutoff_memWkp
    change MemWkp (d := Module.finrank ℝ E) K 2
        (fun y =>
          euclidPartial (E := E) k
              (chartPushedRaw I β
                ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
    exact h_prod
  have h_transport_le : ∀ β' ∈ transportChartCenters (I := I) (M := M) β,
      ∀ Q : TensorCompIdx (E := E) r s,
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β' Q :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β')
        ≤ ENNReal.ofReal ‖(i.fst.val)⁻¹‖ * Saggr := by
    intro β' hβ' Q
    refine le_trans (eigenvectorVec_pou_memWkp_and_wkpNorm_le
      (I := I) (M := M) g r s i K β' Q
      ((h_pou_phi i β' Q).le_of_le (Nat.le_succ K))).2 ?_
    refine mul_le_mul_of_nonneg_left ?_ (zero_le)
    refine le_trans (wkpNorm_mono_order (d := Module.finrank ℝ E)
      (Nat.le_succ K) _ _) ?_
    exact chartCompNorm_transport_le_covGradAggregate (I := I)
      (M := M) g r s i K hβ' Q
  have h_double_le :
      (∑ β' ∈ transportChartCenters (I := I) (M := M) β,
        ∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i) β' Q :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β'))
        ≤ (∑ _β' ∈ transportChartCenters (I := I) (M := M) β,
            ∑ _Q : TensorCompIdx (E := E) r s,
              ENNReal.ofReal ‖(i.fst.val)⁻¹‖ * Saggr) :=
    Finset.sum_le_sum (fun β' hβ' =>
      Finset.sum_le_sum (fun Q _ => h_transport_le β' hβ' Q))
  have h_double_const :
      (∑ _β' ∈ transportChartCenters (I := I) (M := M) β,
        ∑ _Q : TensorCompIdx (E := E) r s,
          ENNReal.ofReal ‖(i.fst.val)⁻¹‖ * Saggr)
        = ENNReal.ofReal
            (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
              ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
                ‖(i.fst.val)⁻¹‖)) * Saggr := by
    have h_sum : (∑ _β' ∈ transportChartCenters (I := I) (M := M) β,
        ∑ _Q : TensorCompIdx (E := E) r s,
          ENNReal.ofReal ‖(i.fst.val)⁻¹‖ * Saggr)
        = (((transportChartCenters (I := I) (M := M) β).card : ℝ≥0∞) *
            ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ≥0∞) *
              (ENNReal.ofReal ‖(i.fst.val)⁻¹‖ * Saggr))) := by
      rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        nsmul_eq_mul]
    rw [h_sum]
    rw [show ENNReal.ofReal
          (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
            ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
              ‖(i.fst.val)⁻¹‖))
        = ((transportChartCenters (I := I) (M := M) β).card : ℝ≥0∞) *
            ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ≥0∞) *
              ENNReal.ofReal ‖(i.fst.val)⁻¹‖) by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]]
    ring
  have h_cutoff_le : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β P :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
      ≤ ENNReal.ofReal cutoffConstant *
        (ENNReal.ofReal
            (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
              ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
                ‖(i.fst.val)⁻¹‖)) * Saggr) := by
    refine le_trans (cutoff_bound (tensorResolventEigenbasisVec
      (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
      (fun β' Q => h_eigen_K β' Q)) ?_
    refine mul_le_mul_of_nonneg_left ?_ (zero_le)
    rw [← h_double_const]
    exact h_double_le
  have h_unfold : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (covGradPouLeibnizCrossLimit (I := I) (M := M)
        g r s i β P k) Ω =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y =>
          euclidPartial (E := E) k
              (chartPushedRaw I β
                ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    rfl
  rw [h_unfold]
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y =>
          euclidPartial (E := E) k
              (chartPushedRaw I β
                ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
        ≤ ENNReal.ofReal Kmul *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I)
                      (M := M) g r s) i)
                  β P : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                  EuclN → ℝ) y) Ω :=
      hKmul_bd hcutoff_memWkp
    _ ≤ ENNReal.ofReal Kmul *
          (ENNReal.ofReal cutoffConstant *
            (ENNReal.ofReal
                (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
                  ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
                    ‖(i.fst.val)⁻¹‖)) * Saggr)) :=
      mul_le_mul_of_nonneg_left h_cutoff_le (zero_le)
    _ = ENNReal.ofReal ((i.fst.val)⁻¹ *
          (Kmul * (cutoffConstant *
            (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
              (Fintype.card (TensorCompIdx (E := E) r s) : ℝ))))) * Saggr := by
      have h_fold : ENNReal.ofReal Kmul *
            (ENNReal.ofReal cutoffConstant *
              (ENNReal.ofReal
                  (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
                    ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
                      ‖(i.fst.val)⁻¹‖)) * Saggr))
          = ENNReal.ofReal (Kmul * (cutoffConstant *
              (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
                ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
                  ‖(i.fst.val)⁻¹‖)))) * Saggr := by
        rw [ENNReal.ofReal_mul (le_of_lt hKmul_pos),
          ENNReal.ofReal_mul cutoffConstant_nonneg]
        ring
      rw [h_fold]
      congr 2
      rw [hμ_norm]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradPouLeibnizCrossLimit_wkpNorm_le_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradPouLeibnizCrossLimit_wkpNorm_le_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradPouLeibnizCrossLimit_wkpNorm_le_uniform ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradPouLeibnizCrossLimit_wkpNorm_le_uniform

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
