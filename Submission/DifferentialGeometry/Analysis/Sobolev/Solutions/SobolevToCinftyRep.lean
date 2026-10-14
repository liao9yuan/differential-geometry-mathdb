import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Embedding.Iterated

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Integral.Measure

theorem exists_continuous_representative_of_memWkpChart_isRegular
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    {k : ℕ} (hk : Module.finrank ℝ E < 2 * k)
    (hreg : RegularExponent.IsRegular (Module.finrank ℝ E : ℝ) 2 k)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu : MemWkpChart (I := I) (M := M) k 2 u) :
    ∃ ũ : M → ℝ, Continuous ũ ∧
      ũ =ᵐ[riemannianVolumeMeasure I M g] u := by
  obtain ⟨ũ, _C, hũ_cont, _hC_nn, hũ_ae, _hũ_bound⟩ :=
    sobolev_embedding_chart_C0_Hk (I := I) (M := M) g hk hreg
      hu_meas hu
  refine ⟨ũ, hũ_cont, ?_⟩
  have hμ_eq :
      riemannianMeasure (I := I) g (chartAtlasPOU I M) =
        riemannianVolumeMeasure I M g :=
    (riemannianVolumeMeasure_def (I := I) (M := M) g).symm
  rw [hμ_eq] at hũ_ae
  exact hũ_ae

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.exists_continuous_representative_of_memWkpChart_isRegular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.exists_continuous_representative_of_memWkpChart_isRegular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.exists_continuous_representative_of_memWkpChart_isRegular ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.exists_continuous_representative_of_memWkpChart_isRegular

theorem exists_continuous_representative_of_memWkpChart
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    {k : ℕ} (hk : Module.finrank ℝ E < 2 * k)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu : MemWkpChart (I := I) (M := M) k 2 u) :
    ∃ ũ : M → ℝ, Continuous ũ ∧
      ũ =ᵐ[riemannianVolumeMeasure I M g] u := by
  have hd_pos : 0 < Module.finrank ℝ E := NeZero.pos _
  have hk_pos : 1 ≤ k := by
    by_contra h_not
    have hk_zero : k = 0 := by omega
    rw [hk_zero] at hk
    omega
  have hp_one : (1 : ℝ) ≤ 2 := by norm_num
  have hkp_real : (Module.finrank ℝ E : ℝ) < (k : ℝ) * 2 := by
    have h_real : (Module.finrank ℝ E : ℝ) < ((2 * k : ℕ) : ℝ) := by exact_mod_cast hk
    have h2k : ((2 * k : ℕ) : ℝ) = (k : ℝ) * 2 := by push_cast; ring
    rw [h2k] at h_real
    exact h_real
  have h_side : 2 ≤ Module.finrank ℝ E ∨ (1 : ℝ) < 2 := Or.inr (by norm_num)
  have h_two_eq : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by
    rw [show (2 : ℝ) = (2 : ℕ) from by norm_num]
    rw [ENNReal.ofReal_natCast]
    rfl
  have hu' : MemWkpChart (I := I) (M := M) k (ENNReal.ofReal 2) u := by
    rw [← h_two_eq]; exact hu
  obtain ⟨ũ, _C, hũ_cont, _hC_nn, hũ_ae, _hũ_bound⟩ :=
    iterated_sobolev_embedding_chart_C0 (I := I) (M := M) g hk_pos
      hp_one hkp_real h_side hu_meas hu'
  refine ⟨ũ, hũ_cont, ?_⟩
  have hμ_eq :
      riemannianMeasure (I := I) g (chartAtlasPOU I M) =
        riemannianVolumeMeasure I M g :=
    (riemannianVolumeMeasure_def (I := I) (M := M) g).symm
  rw [hμ_eq] at hũ_ae
  exact hũ_ae

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.exists_continuous_representative_of_memWkpChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.exists_continuous_representative_of_memWkpChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.exists_continuous_representative_of_memWkpChart ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.exists_continuous_representative_of_memWkpChart

end Chart
end Sobolev
end Analysis
end DifferentialGeometry

end
