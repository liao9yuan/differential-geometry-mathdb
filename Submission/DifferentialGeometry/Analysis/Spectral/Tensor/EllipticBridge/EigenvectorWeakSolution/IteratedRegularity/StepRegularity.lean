import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RightHandSide.Differentiated.Sobolev.NumeratorRegularity

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
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean

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
theorem eigenvectorChartIteratedStep_memWkp_K_two
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    {fChartEffectivePrev : EuclN → ℝ}
    (l : Fin (Module.finrank ℝ E))
    (h_comp : MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffectivePrev
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_ae_zero : fChartEffectivePrev =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartIteratedStep (I := I) (M := M)
        g r s i α P₀ m dirs fChartEffectivePrev l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Q : EuclN → ℝ := fun y =>
    eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s i α P₀ m (Fin.snoc dirs l) fChartEffectivePrev y /
    densityOnEuclid (I := I) g α y with hQ_def
  have h_step_eq :
      eigenvectorChartIteratedStep (I := I) (M := M)
        g r s i α P₀ m dirs fChartEffectivePrev l =
      Set.indicator (chartPouKernel (I := I) (M := M) α) Q := by
    unfold eigenvectorChartIteratedStep
    have h_num := eigenvectorChartIteratedStepNumerator_eq_rhsDiffNumerator
      (I := I) (M := M) g r s i α P₀ m dirs fChartEffectivePrev l
    funext y
    simp only [hQ_def]
    rw [h_num]
  have hQ_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 Q
      (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvectorChartRHSDiffNumerator_div_density_memWkp (I := I) (M := M)
      g r s i α P₀ m K (Fin.snoc dirs l)
      h_comp h_prev_memWkp_succ h_prev_ae_zero
  have hQ_ae_zero : Q =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) :=
    eigenvectorChartRHSDiffNumerator_div_density_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ m (Fin.snoc dirs l)
      h_prev_ae_zero
  have h_indicator_ae_eq_Q :
      Set.indicator (chartPouKernel (I := I) (M := M) α) Q =ᵐ[
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)] Q := by
    set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
    set Kα : Set EuclN := chartPouKernel (I := I) (M := M) α with hKα_def
    have hΩ_meas : MeasurableSet Ω :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    have hKα_meas : MeasurableSet Kα :=
      chartPouKernel_measurableSet (I := I) (M := M) α
    have hKα_sub_Ω : Kα ⊆ Ω :=
      chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
    have h_inter_meas : MeasurableSet (Ω ∩ Kα) := hΩ_meas.inter hKα_meas
    have h_eq_on_inter : Set.indicator Kα Q =ᵐ[
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Ω ∩ Kα)] Q := by
      refine (_root_.MeasureTheory.ae_restrict_iff' h_inter_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      exact Set.indicator_of_mem hy.2 _
    have h_diff_meas : MeasurableSet (Ω \ Kα) := hΩ_meas.diff hKα_meas
    have h_indicator_ae_zero : Set.indicator Kα Q =ᵐ[
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Ω \ Kα)]
        (fun _ : EuclN => (0 : ℝ)) := by
      refine (_root_.MeasureTheory.ae_restrict_iff' h_diff_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      exact Set.indicator_of_notMem hy.2 _
    have h_eq_on_diff : Set.indicator Kα Q =ᵐ[
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Ω \ Kα)] Q := by
      filter_upwards [h_indicator_ae_zero, hQ_ae_zero] with y h0 hQ0
      rw [h0, hQ0]
    have h_cover : Ω = (Ω ∩ Kα) ∪ (Ω \ Kα) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Kα
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Kα) (Ω \ Kα) := by
      refine Set.disjoint_left.mpr ?_
      intro y hy hy'; exact hy'.2 hy.2
    have hΩ_restrict_eq : (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω =
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict ((Ω ∩ Kα) ∪ (Ω \ Kα)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  rw [h_step_eq]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    h_indicator_ae_eq_Q).mpr hQ_memWkp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartIteratedStep_memWkp_K_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartIteratedStep_memWkp_K_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartIteratedStep_memWkp_K_two ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartIteratedStep_memWkp_K_two

omit [CompleteSpace E] in
theorem eigenvectorChartIteratedStep_memW1p_two
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    {fChartEffectivePrev : EuclN → ℝ}
    (l : Fin (Module.finrank ℝ E))
    (h_comp : MemWkp (d := Module.finrank ℝ E) (m + 3) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_memWkp_two :
      MemWkp (d := Module.finrank ℝ E) 2 2 fChartEffectivePrev
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_ae_zero : fChartEffectivePrev =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (eigenvectorChartIteratedStep (I := I) (M := M)
        g r s i α P₀ m dirs fChartEffectivePrev l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_prev_memWkp_succ : MemWkp (d := Module.finrank ℝ E) (1 + 1) 2
      fChartEffectivePrev (chartTargetEuclid (I := I) (M := M) α) := by
    have h_eq : (1 + 1 : ℕ) = 2 := by norm_num
    rw [h_eq]; exact h_prev_memWkp_two
  have h_comp' : MemWkp (d := Module.finrank ℝ E) (m + 2 + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_eq : m + 2 + 1 = m + 3 := by ring
    rw [h_eq]; exact h_comp
  have h_mem := eigenvectorChartIteratedStep_memWkp_K_two (I := I) (M := M)
    g r s i α P₀ m 1 dirs (fChartEffectivePrev := fChartEffectivePrev) l
    h_comp' h_prev_memWkp_succ h_prev_ae_zero
  rw [MemWkp.one_iff_memW1p] at h_mem
  exact h_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartIteratedStep_memW1p_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartIteratedStep_memW1p_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartIteratedStep_memW1p_two ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartIteratedStep_memW1p_two

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
