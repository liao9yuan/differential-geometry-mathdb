import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.ArbitraryOrderChartSobolev
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.IteratedRegularity.Support
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Iterated

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart hiding chartTargetEuclid
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.EuclideanIteratedEmbedding

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

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

omit [CompleteSpace E] in
theorem exists_smooth_eigenvectorChartComponent_representative
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ u_smooth : EuclN → ℝ,
      ContDiffOn ℝ (∞ : WithTop ℕ∞) u_smooth
        (chartTargetEuclid (I := I) (M := M) α) ∧
      HasCompactSupport u_smooth ∧
      tsupport u_smooth ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      u_smooth =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s i α P₀ := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set u : EuclN → ℝ :=
    eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀
    with hu_def
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hΩ_open : IsOpen Ω :=
    DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_subset_Ω : K ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have hu_memWkp : ∀ k : ℕ,
      MemWkp (d := Module.finrank ℝ E) k 2 u Ω := fun k =>
    eigenvector_chartComponent_memWkp_arbitrary g r s i k α P₀
  obtain ⟨u₀, hu₀_cdiff, hu_ae_u₀⟩ :=
    exists_contDiffOn_ae_eq_of_forall_memWkp_two (d := Module.finrank ℝ E) hΩ_open hu_memWkp
  obtain ⟨δ, η, hδ_pos, _hδ_subset, hη_cdiff, hη_compact, _hη_range,
      hη_one_cthick, hη_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hK_compact hΩ_open hK_subset_Ω
  have hη_one_K : ∀ y ∈ K, η y = 1 := fun y hy =>
    hη_one_cthick y (Metric.self_subset_cthickening _ hy)
  set u_smooth : EuclN → ℝ := fun y => η y * u₀ y with hu_smooth_def
  have hu_smooth_cdiff : ContDiffOn ℝ (∞ : WithTop ℕ∞) u_smooth Ω :=
    (hη_cdiff.contDiffOn).mul hu₀_cdiff
  have hu_smooth_compact : HasCompactSupport u_smooth :=
    HasCompactSupport.mul_right hη_compact
  have hu_smooth_tsupp : tsupport u_smooth ⊆ Ω :=
    (tsupport_mul_subset_left).trans hη_tsupp
  refine ⟨u_smooth, hu_smooth_cdiff, hu_smooth_compact, hu_smooth_tsupp, ?_⟩
  have hu_ae_zero :
      u =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Ω \ K)]
        (fun _ : EuclN => (0 : ℝ)) :=
    eigenvectorChartComponentFun_ae_zero_off_chartPouKernel
      g r s i α P₀
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hΩK_open : IsOpen (Ω \ K) := hΩ_open.sdiff hK_closed
  have hΩK_subset : Ω \ K ⊆ Ω := Set.sdiff_subset
  have hu₀_ae_u_ΩK : u₀ =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Ω \ K)] u :=
    Filter.EventuallyEq.symm
      (_root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset hΩK_subset hu_ae_u₀)
  have hu_smooth_ae_zero_ΩK :
      u_smooth =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Ω \ K)]
        (fun _ : EuclN => (0 : ℝ)) := by
    have hu₀_ae_zero_ΩK :
        u₀ =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Ω \ K)]
          (fun _ : EuclN => (0 : ℝ)) := hu₀_ae_u_ΩK.trans hu_ae_zero
    filter_upwards [hu₀_ae_zero_ΩK] with y hy
    simp [hu_smooth_def, hy]
  have hu_ae_u_smooth_ΩK :
      u =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Ω \ K)] u_smooth :=
    hu_ae_zero.trans hu_smooth_ae_zero_ΩK.symm
  have hK_meas : MeasurableSet K := hK_closed.measurableSet
  have hu₀_ae_u_K : u₀ =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K] u :=
    Filter.EventuallyEq.symm
      (_root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset hK_subset_Ω hu_ae_u₀)
  have hu_smooth_ae_u₀_K :
      u_smooth =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K] u₀ := by
    refine (_root_.MeasureTheory.ae_restrict_iff' hK_meas).mpr ?_
    exact Filter.Eventually.of_forall fun y hy => by
      simp [hu_smooth_def, hη_one_K y hy]
  have hu_ae_u_smooth_K :
      u =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K] u_smooth :=
    (hu₀_ae_u_K.symm).trans hu_smooth_ae_u₀_K.symm
  have hΩ_eq : Ω = K ∪ (Ω \ K) := by
    rw [Set.union_sdiff_cancel hK_subset_Ω]
  have hu_ae_u_smooth :
      u =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω] u_smooth := by
    rw [hΩ_eq]
    exact (MeasureTheory.ae_restrict_union_iff K (Ω \ K)
      (fun x => u x = u_smooth x)).mpr ⟨hu_ae_u_smooth_K, hu_ae_u_smooth_ΩK⟩
  exact hu_ae_u_smooth.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_smooth_eigenvectorChartComponent_representative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_smooth_eigenvectorChartComponent_representative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_smooth_eigenvectorChartComponent_representative ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_smooth_eigenvectorChartComponent_representative

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
