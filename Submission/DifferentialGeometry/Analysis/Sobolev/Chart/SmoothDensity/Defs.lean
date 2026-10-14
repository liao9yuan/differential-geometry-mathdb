import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.AtlasNorm.Atlas
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.Multiply
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.MeasureComparison
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.CompletenessLp
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

variable (I) in
def chartPullback (α : M)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) : M → ℝ := by
  classical
  exact fun x =>
    if x ∈ (chartAt H α).source then
      ψ (toEuclidean (extChartAt I α x))
    else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback

omit [IsManifold I ∞ M] in
lemma chartPullback_apply_of_mem (α : M)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    chartPullback I α ψ x = ψ (toEuclidean (extChartAt I α x)) := by
  classical
  unfold chartPullback
  simp [hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_apply_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_apply_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_apply_of_mem ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_apply_of_mem

omit [IsManifold I ∞ M] in
lemma chartPullback_apply_of_notMem (α : M)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    chartPullback I α ψ x = 0 := by
  classical
  unfold chartPullback
  simp [hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_apply_of_notMem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_apply_of_notMem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_apply_of_notMem ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_apply_of_notMem

omit [IsManifold I ∞ M] in
lemma chartPullback_add (α : M)
    (ψ₁ ψ₂ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    chartPullback I α (fun y => ψ₁ y + ψ₂ y) =
      fun x => chartPullback I α ψ₁ x + chartPullback I α ψ₂ x := by
  classical
  funext x
  by_cases hx : x ∈ (chartAt H α).source
  · simp [chartPullback_apply_of_mem (I := I) (M := M) α _ hx]
  · simp [chartPullback_apply_of_notMem (I := I) (M := M) α _ hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_add ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_add

omit [IsManifold I ∞ M] in
lemma chartPullback_const_smul (α : M) (c : ℝ)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    chartPullback I α (fun y => c * ψ y) =
      fun x => c * chartPullback I α ψ x := by
  classical
  funext x
  by_cases hx : x ∈ (chartAt H α).source
  · simp [chartPullback_apply_of_mem (I := I) (M := M) α _ hx]
  · simp [chartPullback_apply_of_notMem (I := I) (M := M) α _ hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_const_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_const_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_const_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_const_smul

omit [IsManifold I ∞ M] in
lemma chartPullback_zero_fun (α : M) :
    chartPullback I α (fun _ => (0 : ℝ)) = (fun _ : M => (0 : ℝ)) := by
  classical
  funext x
  by_cases hx : x ∈ (chartAt H α).source
  · simp [chartPullback_apply_of_mem (I := I) (M := M) α (fun _ => (0 : ℝ)) hx]
  · simp [chartPullback_apply_of_notMem (I := I) (M := M) α (fun _ => (0 : ℝ)) hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_zero_fun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_zero_fun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_zero_fun ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_zero_fun

omit [IsManifold I ∞ M] in
lemma support_chartPullback_subset_chartAt_source (α : M)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    Function.support (chartPullback I α ψ) ⊆ (chartAt H α).source := by
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx
  by_contra hx_off
  apply hx
  exact chartPullback_apply_of_notMem (I := I) (M := M) α ψ hx_off

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.support_chartPullback_subset_chartAt_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.support_chartPullback_subset_chartAt_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.support_chartPullback_subset_chartAt_source ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.support_chartPullback_subset_chartAt_source

omit [IsManifold I ∞ M] in
omit [FiniteDimensional ℝ E] in
lemma tsupport_pou_mul_subset_tsupport_pou
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    tsupport (fun x : M =>
        (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
      tsupport (ρ α : M → ℝ) := by
  refine closure_mono ?_
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx
  simp only [Function.mem_support, ne_eq]
  intro h_pou_zero
  apply hx
  rw [h_pou_zero, _root_.MulZeroClass.zero_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_pou_mul_subset_tsupport_pou then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_pou_mul_subset_tsupport_pou"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_pou_mul_subset_tsupport_pou ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_pou_mul_subset_tsupport_pou

lemma tsupport_chartAtlasPOU_mul_subset_chartAt_source
    [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) :
    tsupport (fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
          u x) ⊆
      (chartAt H α).source :=
  Set.Subset.trans
    (tsupport_pou_mul_subset_tsupport_pou (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartAtlasPOU_mul_subset_chartAt_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartAtlasPOU_mul_subset_chartAt_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartAtlasPOU_mul_subset_chartAt_source ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartAtlasPOU_mul_subset_chartAt_source

lemma hasCompactSupport_chartAtlasPOU_mul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) :
    HasCompactSupport (fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
          u x) := by
  have h_subset := tsupport_pou_mul_subset_tsupport_pou (I := I) (M := M)
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u
  have h_compact : IsCompact (tsupport
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ)) :=
    (isClosed_tsupport _).isCompact
  exact h_compact.of_isClosed_subset (isClosed_tsupport _) h_subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.hasCompactSupport_chartAtlasPOU_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.hasCompactSupport_chartAtlasPOU_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.hasCompactSupport_chartAtlasPOU_mul ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.hasCompactSupport_chartAtlasPOU_mul

omit [IsManifold I ∞ M] in
lemma chartPushed_chartPullback_apply_of_mem
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushed (I := I) (M := M) ρ α (chartPullback I α ψ) y =
      (ρ α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm (toEuclidean.symm y)) *
      ψ y := by
  classical
  unfold chartPushed
  set z : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hz_def
  have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hz_source : z ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hsymm_target
  have hz_chartAt_source : z ∈ (chartAt H α).source := by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)] at hz_source
    exact hz_source
  rw [chartPullback_apply_of_mem (I := I) (M := M) α ψ hz_chartAt_source]
  have hz_inv : (extChartAt I α) z = (toEuclidean (E := E)).symm y :=
    (extChartAt I α).right_inv hsymm_target
  rw [hz_inv]
  rw [(toEuclidean (E := E)).apply_symm_apply y]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_chartPullback_apply_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_chartPullback_apply_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_chartPullback_apply_of_mem ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_chartPullback_apply_of_mem

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
