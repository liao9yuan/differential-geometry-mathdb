import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.ChartSobolevDensity
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.ChartPullbackSmooth
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.Transition
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.Basic

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

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
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

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem contMDiff_finsetSum_chartPullback
    [T2Space M]
    {ι : Type*} (S : Finset ι) (α : ι → M)
    (ψ : ι → EuclN → ℝ)
    (hψ_smooth : ∀ i ∈ S, ContDiff ℝ (⊤ : ℕ∞) (ψ i))
    (hψ_compact : ∀ i ∈ S, HasCompactSupport (ψ i))
    (hψ_support : ∀ i ∈ S,
      tsupport (ψ i) ⊆ chartTargetEuclid (I := I) (M := M) (α i)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ∑ i ∈ S, chartPullback I (α i) (ψ i) x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact contMDiff_const
  | insert i S hiS ih =>
      have h_smooth_i : ContMDiff I 𝓘(ℝ, ℝ) ∞ (chartPullback I (α i) (ψ i)) :=
        chartPullback_contMDiff (I := I) (M := M) (α i)
          (hψ_smooth i (Finset.mem_insert_self i S))
          (hψ_compact i (Finset.mem_insert_self i S))
          (hψ_support i (Finset.mem_insert_self i S))
      have ih' : ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun x : M => ∑ j ∈ S, chartPullback I (α j) (ψ j) x) := by
        refine ih ?_ ?_ ?_
        · intro j hj
          exact hψ_smooth j (Finset.mem_insert.mpr (Or.inr hj))
        · intro j hj
          exact hψ_compact j (Finset.mem_insert.mpr (Or.inr hj))
        · intro j hj
          exact hψ_support j (Finset.mem_insert.mpr (Or.inr hj))
      have h_eq : (fun x : M => ∑ j ∈ _root_.Insert.insert i S, chartPullback I (α j) (ψ j) x) =
          (fun x : M => chartPullback I (α i) (ψ i) x +
            ∑ j ∈ S, chartPullback I (α j) (ψ j) x) := by
        funext x
        rw [Finset.sum_insert hiS]
      rw [h_eq]
      exact h_smooth_i.add ih'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.contMDiff_finsetSum_chartPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.contMDiff_finsetSum_chartPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.contMDiff_finsetSum_chartPullback ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.contMDiff_finsetSum_chartPullback

omit [IsManifold I ∞ M] in
lemma chartPushed_finset_sum
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M)
    {ι : Type*} (S : Finset ι) (f : ι → M → ℝ) :
    chartPushed (I := I) (M := M) ρ α (fun x => ∑ i ∈ S, f i x) =
      (fun y => ∑ i ∈ S,
        chartPushed (I := I) (M := M) ρ α (f i) y) := by
  classical
  funext y
  unfold chartPushed
  rw [Finset.mul_sum]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_finset_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_finset_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_finset_sum ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_finset_sum

omit [IsManifold I ∞ M] in
lemma chartPushed_sub
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M)
    (u v : M → ℝ) :
    chartPushed (I := I) (M := M) ρ α (fun x => u x - v x) =
      (fun y =>
        chartPushed (I := I) (M := M) ρ α u y -
          chartPushed (I := I) (M := M) ρ α v y) := by
  funext y
  unfold chartPushed
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_sub ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_sub

theorem MemWkpChart_finset_sum
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {ι : Type*} (S : Finset ι) (f : ι → M → ℝ)
    (hf : ∀ i ∈ S, MemWkpChart (I := I) (M := M) k p (f i)) :
    MemWkpChart (I := I) (M := M) k p (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact MemWkpChart_zero_fun (I := I) (M := M) hp
  | insert i S hiS ih =>
      have hi : MemWkpChart (I := I) (M := M) k p (f i) :=
        hf i (Finset.mem_insert_self i S)
      have ih' : MemWkpChart (I := I) (M := M) k p
          (fun x : M => ∑ j ∈ S, f j x) :=
        ih (fun j hj => hf j (Finset.mem_insert.mpr (Or.inr hj)))
      have h_eq : (fun x : M => ∑ j ∈ _root_.Insert.insert i S, f j x) =
          (fun x : M => f i x + ∑ j ∈ S, f j x) := by
        funext x
        rw [Finset.sum_insert hiS]
      rw [h_eq]
      exact MemWkpChart_add (I := I) (M := M) hp hi ih'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_finset_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_finset_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_finset_sum ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_finset_sum

theorem wkpNormChart_finset_sum_le
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {ι : Type*} (S : Finset ι) (f : ι → M → ℝ)
    (hf : ∀ i ∈ S, MemWkpChart (I := I) (M := M) k p (f i)) :
    wkpNormChart (I := I) (M := M) k p (fun x => ∑ i ∈ S, f i x) ≤
      ∑ i ∈ S, wkpNormChart (I := I) (M := M) k p (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [wkpNormChart_zero_fun (I := I) (M := M) hp]
  | insert i S hiS ih =>
      have hi : MemWkpChart (I := I) (M := M) k p (f i) :=
        hf i (Finset.mem_insert_self i S)
      have hS_mem : ∀ j ∈ S, MemWkpChart (I := I) (M := M) k p (f j) :=
        fun j hj => hf j (Finset.mem_insert.mpr (Or.inr hj))
      have hS_sum_mem : MemWkpChart (I := I) (M := M) k p
          (fun x : M => ∑ j ∈ S, f j x) :=
        MemWkpChart_finset_sum (I := I) (M := M) hp S f hS_mem
      have h_eq : (fun x : M => ∑ j ∈ _root_.Insert.insert i S, f j x) =
          (fun x : M => f i x + ∑ j ∈ S, f j x) := by
        funext x
        rw [Finset.sum_insert hiS]
      rw [h_eq, Finset.sum_insert hiS]
      have h_tri := wkpNormChart_add_le (I := I) (M := M) hp hi hS_sum_mem
      refine h_tri.trans ?_
      gcongr
      exact ih hS_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_finset_sum_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_finset_sum_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_finset_sum_le ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_finset_sum_le

theorem chartPushed_eq_zero_off_compact
    [T2Space M] [SigmaCompactSpace M] (α : M) (u : M → ℝ) {y : EuclN}
    (hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hy_off : y ∉ toEuclidean '' ((extChartAt I α) ''
      (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α) :
        M → ℝ)))) :
    chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y = 0 :=
  DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_support_subset_compact_in_target
    (I := I) (M := M) α u y hy_target hy_off

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_zero_off_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_zero_off_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_zero_off_compact ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_zero_off_compact

theorem wkpNormChart_eq_finset_sum
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) (u : M → ℝ) :
    wkpNormChart (I := I) (M := M) k p u =
      ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOUFinset
              (I := I) (M := M),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold wkpNormChart
  set f : M → ℝ≥0∞ := fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) with hf_def
  have hf_zero_off : ∀ α : M, α ∉
      DifferentialGeometry.Integral.Measure.chartAtlasPOUFinset
        (I := I) (M := M) → f α = 0 := by
    intro α hα
    have hρ_zero : ∀ x : M, (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I M α : M → ℝ) x = 0 := by
      intro x
      exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_weight_zero_of_notMem
        (I := I) (M := M) hα x
    have hChartPushed_zero : chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u =
        (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [hρ_zero]
      ring
    change DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) = 0
    rw [hChartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  rw [tsum_eq_sum hf_zero_off]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_eq_finset_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_eq_finset_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_eq_finset_sum ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_eq_finset_sum

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
