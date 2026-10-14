import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.Defs
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.Family
import Submission.DifferentialGeometry.Geometry.Operator.Hessian.Basic
import Submission.DifferentialGeometry.Analysis.Schauder.Elliptic.CompactEllipticity
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Order.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace MetricExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.MetricExtension.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.MetricExtension.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.MetricExtension.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.MetricExtension.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

def chartTargetEuclid (α : M) : Set EuclN :=
  toEuclidean '' (extChartAt I α).target

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
lemma chartTargetEuclid_isOpen [I.Boundaryless] (α : M) :
    IsOpen (chartTargetEuclid (I := I) (M := M) α) := by
  unfold chartTargetEuclid
  have hOpenE : IsOpen ((extChartAt I α).target) :=
    isOpen_extChartAt_target (I := I) α
  exact toEuclidean.toHomeomorph.isOpenMap _ hOpenE

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid_isOpen ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid_isOpen

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
lemma toEuclidean_symm_mem_target {α : M} {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
  rcases hy with ⟨z, hz_target, hz_eq⟩
  have hyz : (toEuclidean (E := E)).symm y = z := by
    rw [← hz_eq]; simp
  rw [hyz]
  exact hz_target

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target

def gramOnEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid

def invGramOnEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  chartInvGramMatrix (I := I) g α
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid

def densityOnEuclid (g : SmoothRiemannianMetric I M) (α : M) (y : EuclN) : ℝ :=
  chartDensity (I := I) g α
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid

def weightedInvGramOnEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  densityOnEuclid (I := I) g α y * invGramOnEuclid (I := I) g α i j y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid

omit [NeZero (Module.finrank ℝ E)] in
lemma contMDiffOn_chart_symm (α : M) :
    ContMDiffOn 𝓘(ℝ, EuclN) I ∞
      (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_inner_contDiff : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
    (toEuclidean (E := E)).symm.contDiff
  have h_inner : ContMDiff 𝓘(ℝ, EuclN) 𝓘(ℝ, E) ∞
      (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
    (contMDiff_iff_contDiff (n := (⊤ : ℕ∞))).mpr h_inner_contDiff
  have h_outer : ContMDiffOn 𝓘(ℝ, E) I ∞
      (extChartAt I α).symm (extChartAt I α).target :=
    contMDiffOn_extChartAt_symm (I := I) α
  have h_maps : _root_.Set.MapsTo (fun y : EuclN => (toEuclidean (E := E)).symm y)
      (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := by
    intro y hy
    exact toEuclidean_symm_mem_target (I := I) hy
  exact h_outer.comp h_inner.contMDiffOn h_maps

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.contMDiffOn_chart_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.contMDiffOn_chart_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.contMDiffOn_chart_symm ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.contMDiffOn_chart_symm

omit [NeZero (Module.finrank ℝ E)] in
private lemma mapsTo_chart_symm_baseSet (α : M) :
    MapsTo (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  intro y hy
  change (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ (chartAt H α).source
  have h_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have h_source : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (extChartAt I α).source :=
    (extChartAt I α).map_target h_target
  rwa [extChartAt_source_eq_chartAt_source (I := I)] at h_source

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.mapsTo_chart_symm_baseSet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.MetricExtension.mapsTo_chart_symm_baseSet target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
lemma gramOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (gramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_chart : ContMDiffOn 𝓘(ℝ, EuclN) I ∞
      (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) :=
    contMDiffOn_chart_symm (I := I) α
  have h_g : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α x i j)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn (I := I) g α i j
  have h_maps := mapsTo_chart_symm_baseSet (I := I) (M := M) α
  have h_comp : ContMDiffOn 𝓘(ℝ, EuclN) 𝓘(ℝ) ∞
      (gramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_g.comp h_chart h_maps
  exact (contMDiffOn_iff_contDiffOn).mp h_comp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid_contDiffOn

omit [NeZero (Module.finrank ℝ E)] in
lemma invGramOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (invGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_chart : ContMDiffOn 𝓘(ℝ, EuclN) I ∞
      (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) :=
    contMDiffOn_chart_symm (I := I) α
  have h_g : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartInvGramMatrix g α x i j)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
  have h_maps := mapsTo_chart_symm_baseSet (I := I) (M := M) α
  have h_comp : ContMDiffOn 𝓘(ℝ, EuclN) 𝓘(ℝ) ∞
      (invGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_g.comp h_chart h_maps
  exact (contMDiffOn_iff_contDiffOn).mp h_comp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_contDiffOn

omit [NeZero (Module.finrank ℝ E)] in
lemma densityOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ ∞ (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_chart : ContMDiffOn 𝓘(ℝ, EuclN) I ∞
      (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) :=
    contMDiffOn_chart_symm (I := I) α
  have h_dens : ContMDiffOn I 𝓘(ℝ) ∞
      (chartDensity g α)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    chartDensity_contMDiffOn (I := I) g α
  have h_maps := mapsTo_chart_symm_baseSet (I := I) (M := M) α
  have h_comp : ContMDiffOn 𝓘(ℝ, EuclN) 𝓘(ℝ) ∞
      (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_dens.comp h_chart h_maps
  exact (contMDiffOn_iff_contDiffOn).mp h_comp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_contDiffOn

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedInvGramOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (weightedInvGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold weightedInvGramOnEuclid
  exact (densityOnEuclid_contDiffOn (I := I) g α).mul
    (invGramOnEuclid_contDiffOn (I := I) g α i j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_contDiffOn

omit [NeZero (Module.finrank ℝ E)] in
lemma invGramOnEuclid_symm_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    invGramOnEuclid (I := I) g α i j y =
      invGramOnEuclid (I := I) g α j i y := by
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have h_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have h_source : x ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target h_target
  have h_base : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    change x ∈ (chartAt H α).source
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at h_source
  have hHerm : (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α x).IsHermitian :=
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_isHermitian (I := I) g α x
  have hHermInv : (chartInvGramMatrix (I := I) g α x).IsHermitian := by
    unfold chartInvGramMatrix
    exact hHerm.inv
  change chartInvGramMatrix (I := I) g α x i j =
    chartInvGramMatrix (I := I) g α x j i
  have h_apply := hHermInv.apply i j
  rw [_root_.TrivialStar.star_trivial] at h_apply
  exact h_apply.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_symm_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_symm_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_symm_of_mem ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_symm_of_mem

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedInvGramOnEuclid_symm_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    weightedInvGramOnEuclid (I := I) g α i j y =
      weightedInvGramOnEuclid (I := I) g α j i y := by
  unfold weightedInvGramOnEuclid
  rw [invGramOnEuclid_symm_of_mem (I := I) g α i j hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_symm_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_symm_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_symm_of_mem ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_symm_of_mem

omit [NeZero (Module.finrank ℝ E)] in
lemma densityOnEuclid_pos
    (g : SmoothRiemannianMetric I M) (α : M)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    0 < densityOnEuclid (I := I) g α y := by
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have h_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have h_source : x ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target h_target
  have h_base : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    change x ∈ (chartAt H α).source
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at h_source
  exact chartDensity_pos (I := I) g α h_base

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_pos ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_pos

omit [NeZero (Module.finrank ℝ E)] in
lemma one_div_densityOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ ∞ (fun y => 1 / densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  contDiffOn_const.div (densityOnEuclid_contDiffOn (I := I) g α)
    (fun _ hy => (densityOnEuclid_pos (I := I) g α hy).ne')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.one_div_densityOnEuclid_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.one_div_densityOnEuclid_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.one_div_densityOnEuclid_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.one_div_densityOnEuclid_contDiffOn

omit [NeZero (Module.finrank ℝ E)] in
lemma invGramOnEuclid_posDef
    (g : SmoothRiemannianMetric I M) (α : M)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        invGramOnEuclid (I := I) g α i j y)).PosDef := by
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have h_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have h_source : x ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target h_target
  have h_base : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    change x ∈ (chartAt H α).source
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at h_source
  have hG : (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α x).PosDef :=
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_posDef (I := I) g α h_base
  have hGinv : (chartInvGramMatrix (I := I) g α x).PosDef := by
    unfold chartInvGramMatrix
    exact hG.inv
  have hmat_eq : (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      invGramOnEuclid (I := I) g α i j y)) =
      chartInvGramMatrix (I := I) g α x := by
    ext i j
    rfl
  rw [hmat_eq]
  exact hGinv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_posDef then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_posDef"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_posDef ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_posDef

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedInvGramOnEuclid_posDef
    (g : SmoothRiemannianMetric I M) (α : M)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      weightedInvGramOnEuclid (I := I) g α i j y)).PosDef := by
  exact (invGramOnEuclid_posDef (I := I) g α hy).smul
    (densityOnEuclid_pos (I := I) g α hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_posDef then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_posDef"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_posDef ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_posDef

omit [NeZero (Module.finrank ℝ E)] in
lemma weighted_quadForm_pos_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (ξ : EuclN) (hξ : ξ ≠ 0) :
    0 < ⟪ξ, DeGiorgi.matMulE
        (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ := by
  have hξ' : ξ.ofLp ≠ 0 := by
    intro h
    exact hξ (WithLp.ofLp_injective 2 h)
  have h := (weightedInvGramOnEuclid_posDef (I := I) g α hy).dotProduct_mulVec_pos hξ'
  change 0 < (DeGiorgi.matMulE _ ξ).ofLp ⬝ᵥ _root_.Star.star ξ.ofLp
  rw [DeGiorgi.matMulE_ofLp, dotProduct_comm]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.weighted_quadForm_pos_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.weighted_quadForm_pos_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.weighted_quadForm_pos_of_mem ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.weighted_quadForm_pos_of_mem

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_uniform_lower_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ lamK : ℝ, 0 < lamK ∧
      ∀ y ∈ K, ∀ ξ : EuclN,
        lamK * ‖ξ‖ ^ 2 ≤
          ⟪ξ, DeGiorgi.matMulE
            (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
              weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ := by
  obtain ⟨c, hc, hbound⟩ := Schauder.exists_uniform_matrix_quadratic_lower_bound hK_compact
    (fun y => Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      weightedInvGramOnEuclid (I := I) g α i j y))
    (fun i j => (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn.mono hK_target)
    (fun _ hy => weightedInvGramOnEuclid_posDef (I := I) g α (hK_target hy))
  refine ⟨c, hc, ?_⟩
  intro y hy ξ
  change c * ‖ξ‖ ^ 2 ≤ (DeGiorgi.matMulE _ ξ).ofLp ⬝ᵥ _root_.Star.star ξ.ofLp
  rw [DeGiorgi.matMulE_ofLp, dotProduct_comm]
  exact hbound y hy ξ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_uniform_lower_bound_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_uniform_lower_bound_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_uniform_lower_bound_on_compact ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_uniform_lower_bound_on_compact

private def kronDelta (i j : Fin (Module.finrank ℝ E)) : ℝ := if i = j then 1 else 0

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.kronDelta
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.MetricExtension.kronDelta target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma kronDelta_self (i : Fin (Module.finrank ℝ E)) :
    kronDelta (E := E) i i = 1 := by
  simp [kronDelta]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.kronDelta_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.MetricExtension.kronDelta_self target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma kronDelta_symm (i j : Fin (Module.finrank ℝ E)) :
    kronDelta (E := E) i j = kronDelta (E := E) j i := by
  by_cases h : i = j
  · subst h; rfl
  · simp [kronDelta, h, Ne.symm h]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.kronDelta_symm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.MetricExtension.kronDelta_symm target :: scope.openDecls } }

def extendedMatrix
    (g : SmoothRiemannianMetric I M) (α : M) (χ : EuclN → ℝ)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  χ y * weightedInvGramOnEuclid (I := I) g α i j y +
    (1 - χ y) * kronDelta (E := E) i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix

omit [NeZero (Module.finrank ℝ E)] in
lemma extendedMatrix_symm_of_mem
    (g : SmoothRiemannianMetric I M) (α : M) (χ : EuclN → ℝ)
    (i j : Fin (Module.finrank ℝ E)) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    extendedMatrix (I := I) g α χ i j y =
      extendedMatrix (I := I) g α χ j i y := by
  unfold extendedMatrix
  rw [weightedInvGramOnEuclid_symm_of_mem (I := I) g α i j hy]
  rw [kronDelta_symm (E := E) i j]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_symm_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_symm_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_symm_of_mem ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_symm_of_mem

omit [NeZero (Module.finrank ℝ E)] in
lemma extendedMatrix_symm_off_tsupport
    (g : SmoothRiemannianMetric I M) (α : M) {χ : EuclN → ℝ}
    (i j : Fin (Module.finrank ℝ E)) {y : EuclN} (hy : y ∉ tsupport χ) :
    extendedMatrix (I := I) g α χ i j y =
      extendedMatrix (I := I) g α χ j i y := by
  have hχ_zero : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
  have h_lhs : extendedMatrix (I := I) g α χ i j y = kronDelta (E := E) i j := by
    unfold extendedMatrix
    rw [hχ_zero]; ring
  have h_rhs : extendedMatrix (I := I) g α χ j i y = kronDelta (E := E) j i := by
    unfold extendedMatrix
    rw [hχ_zero]; ring
  rw [h_lhs, h_rhs, kronDelta_symm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_symm_off_tsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_symm_off_tsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_symm_off_tsupport ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_symm_off_tsupport

omit [NeZero (Module.finrank ℝ E)] in
lemma extendedMatrix_symm
    (g : SmoothRiemannianMetric I M) (α : M) {χ : EuclN → ℝ}
    (hχ_support : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) :
    extendedMatrix (I := I) g α χ i j y =
      extendedMatrix (I := I) g α χ j i y := by
  by_cases hy : y ∈ tsupport χ
  · exact extendedMatrix_symm_of_mem (I := I) g α χ i j (hχ_support hy)
  · exact extendedMatrix_symm_off_tsupport (I := I) g α i j hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_symm ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_symm

omit [NeZero (Module.finrank ℝ E)] in
lemma extendedMatrix_contDiff
    (g : SmoothRiemannianMetric I M) (α : M) [I.Boundaryless]
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_support : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (extendedMatrix (I := I) g α χ i j) := by
  set f : EuclN → ℝ := extendedMatrix (I := I) g α χ i j with hf_def
  set s : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hs_def
  set t : Set EuclN := (tsupport χ)ᶜ with ht_def
  have hs_open : IsOpen s := chartTargetEuclid_isOpen (I := I) (M := M) α
  have ht_open : IsOpen t := isClosed_tsupport _ |>.isOpen_compl
  have hcov : s ∪ t = Set.univ := by
    refine Set.eq_univ_of_forall ?_
    intro y
    by_cases hy : y ∈ tsupport χ
    · exact Or.inl (hχ_support hy)
    · exact Or.inr hy
  have hf_on_s : ContDiffOn ℝ (⊤ : ℕ∞) f s := by
    change ContDiffOn ℝ (⊤ : ℕ∞) (fun y =>
      χ y * weightedInvGramOnEuclid (I := I) g α i j y +
        (1 - χ y) * kronDelta (E := E) i j) s
    refine ContDiffOn.add ?_ ?_
    · exact (hχ_smooth.contDiffOn).mul
        (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j)
    · have h_one_minus_chi : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclN => 1 - χ y) s :=
        (contDiffOn_const.sub hχ_smooth.contDiffOn)
      exact h_one_minus_chi.mul contDiffOn_const
  have hf_on_t : ContDiffOn ℝ (⊤ : ℕ∞) f t := by
    have hf_eq_const : ∀ y ∈ t, f y = kronDelta (E := E) i j := by
      intro y hy
      have hy_compl : y ∉ tsupport χ := hy
      have hχ_zero : χ y = 0 := image_eq_zero_of_notMem_tsupport hy_compl
      change extendedMatrix (I := I) g α χ i j y = kronDelta (E := E) i j
      unfold extendedMatrix
      rw [hχ_zero]
      ring
    have h_const_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : EuclN => kronDelta (E := E) i j) t :=
      contDiffOn_const
    exact h_const_smooth.congr (fun y hy => hf_eq_const y hy)
  exact contDiff_of_contDiffOn_union_of_isOpen hf_on_s hf_on_t hcov hs_open ht_open

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_contDiff ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_contDiff

omit [NeZero (Module.finrank ℝ E)] in
lemma extendedMatrix_quad_decomp
    (g : SmoothRiemannianMetric I M) (α : M)
    (χ : EuclN → ℝ) (y : EuclN) (ξ : EuclN) :
    ⟪ξ, DeGiorgi.matMulE
      (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        extendedMatrix (I := I) g α χ i j y)) ξ⟫_ℝ =
      χ y * ⟪ξ, DeGiorgi.matMulE
        (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ +
      (1 - χ y) * ‖ξ‖ ^ 2 := by
  classical
  have h_ext : ⟪ξ, DeGiorgi.matMulE
      (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        extendedMatrix (I := I) g α χ i j y)) ξ⟫_ℝ =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        extendedMatrix (I := I) g α χ i j y * ξ.ofLp i * ξ.ofLp j := by
    change (DeGiorgi.matMulE _ ξ).ofLp ⬝ᵥ _root_.Star.star ξ.ofLp = _
    rw [DeGiorgi.matMulE_ofLp]
    have hstar : _root_.Star.star ξ.ofLp = ξ.ofLp := by funext i; exact _root_.TrivialStar.star_trivial _
    rw [hstar]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  have h_w : ⟪ξ, DeGiorgi.matMulE
      (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i j y * ξ.ofLp i * ξ.ofLp j := by
    change (DeGiorgi.matMulE _ ξ).ofLp ⬝ᵥ _root_.Star.star ξ.ofLp = _
    rw [DeGiorgi.matMulE_ofLp]
    have hstar : _root_.Star.star ξ.ofLp = ξ.ofLp := by funext i; exact _root_.TrivialStar.star_trivial _
    rw [hstar]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  have h_norm_sq : ‖ξ‖ ^ 2 =
      ∑ i : Fin (Module.finrank ℝ E), (ξ.ofLp i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Real.norm_eq_abs, sq_abs]
  rw [h_ext, h_w, h_norm_sq]
  rw [Finset.mul_sum]
  rw [show (1 - χ y) * ∑ i : Fin (Module.finrank ℝ E), (ξ.ofLp i) ^ 2 =
      ∑ i : Fin (Module.finrank ℝ E), (1 - χ y) * (ξ.ofLp i) ^ 2 from
        (Finset.mul_sum _ _ _)]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        χ y * ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y * ξ.ofLp i * ξ.ofLp j) +
      ∑ i : Fin (Module.finrank ℝ E), (1 - χ y) * (ξ.ofLp i) ^ 2 =
      ∑ i : Fin (Module.finrank ℝ E),
        (χ y * ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y * ξ.ofLp i * ξ.ofLp j +
          (1 - χ y) * (ξ.ofLp i) ^ 2) from
        (Finset.sum_add_distrib).symm]
  refine Finset.sum_congr rfl ?_
  intro i _
  unfold extendedMatrix
  rw [show ∑ j : Fin (Module.finrank ℝ E),
        (χ y * weightedInvGramOnEuclid (I := I) g α i j y +
            (1 - χ y) * kronDelta (E := E) i j) * ξ.ofLp i * ξ.ofLp j =
      ∑ j : Fin (Module.finrank ℝ E),
        ((χ y * weightedInvGramOnEuclid (I := I) g α i j y *
            ξ.ofLp i * ξ.ofLp j) +
          (1 - χ y) * kronDelta (E := E) i j * ξ.ofLp i * ξ.ofLp j) from by
    refine Finset.sum_congr rfl ?_
    intro j _
    ring]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  · rw [Finset.sum_eq_single i]
    · rw [kronDelta_self]
      ring
    · intro j _ hji
      have : kronDelta (E := E) i j = 0 := by
        unfold kronDelta
        rw [if_neg (Ne.symm hji)]
      rw [this]
      ring
    · intro h_not_mem
      exact absurd (Finset.mem_univ i) h_not_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_quad_decomp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_quad_decomp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_quad_decomp ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_quad_decomp

omit [NeZero (Module.finrank ℝ E)] in
lemma extendedMatrix_coercive_on_chart
    (g : SmoothRiemannianMetric I M) (α : M)
    {χ : EuclN → ℝ}
    (hχ_range : Set.range χ ⊆ Set.Icc (0 : ℝ) 1)
    {y : EuclN}
    {lamK : ℝ}
    (h_uniform : ∀ ξ : EuclN,
        lamK * ‖ξ‖ ^ 2 ≤
          ⟪ξ, DeGiorgi.matMulE
            (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
              weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ)
    (ξ : EuclN) :
    _root_.Min.min (1 : ℝ) lamK * ‖ξ‖ ^ 2 ≤
      ⟪ξ, DeGiorgi.matMulE
        (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          extendedMatrix (I := I) g α χ i j y)) ξ⟫_ℝ := by
  classical
  have hχ_in_Icc : χ y ∈ Set.Icc (0 : ℝ) 1 :=
    hχ_range (Set.mem_range_self y)
  have hχ_nn : 0 ≤ χ y := hχ_in_Icc.1
  have hχ_le_one : χ y ≤ 1 := hχ_in_Icc.2
  have h_one_minus_chi_nn : 0 ≤ 1 - χ y := by linarith
  have h_decomp := extendedMatrix_quad_decomp (I := I) g α χ y ξ
  rw [h_decomp]
  have h_uniform_ξ := h_uniform ξ
  have h_first : χ y * (lamK * ‖ξ‖ ^ 2) ≤
      χ y * ⟪ξ, DeGiorgi.matMulE
        (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ :=
    mul_le_mul_of_nonneg_left h_uniform_ξ hχ_nn
  have h_norm_sq_nn : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
  have h_min_le : _root_.Min.min (1 : ℝ) lamK ≤ χ y * lamK + (1 - χ y) := by
    have h_min_le_lamK : _root_.Min.min (1 : ℝ) lamK ≤ lamK := min_le_right _ _
    have h_min_le_one : _root_.Min.min (1 : ℝ) lamK ≤ 1 := min_le_left _ _
    have h1 : χ y * _root_.Min.min (1 : ℝ) lamK ≤ χ y * lamK :=
      mul_le_mul_of_nonneg_left h_min_le_lamK hχ_nn
    have h2 : (1 - χ y) * _root_.Min.min (1 : ℝ) lamK ≤ (1 - χ y) * 1 :=
      mul_le_mul_of_nonneg_left h_min_le_one h_one_minus_chi_nn
    have h_factor : (χ y) * _root_.Min.min (1 : ℝ) lamK + (1 - χ y) * _root_.Min.min (1 : ℝ) lamK =
        min (1 : ℝ) lamK := by ring
    linarith
  have h_first_step : _root_.Min.min (1 : ℝ) lamK * ‖ξ‖ ^ 2 ≤
      (χ y * lamK + (1 - χ y)) * ‖ξ‖ ^ 2 :=
    mul_le_mul_of_nonneg_right h_min_le h_norm_sq_nn
  have h_alg : (χ y * lamK + (1 - χ y)) * ‖ξ‖ ^ 2 =
      χ y * (lamK * ‖ξ‖ ^ 2) + (1 - χ y) * ‖ξ‖ ^ 2 := by ring
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_coercive_on_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_coercive_on_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_coercive_on_chart ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_coercive_on_chart

omit [NeZero (Module.finrank ℝ E)] in
lemma extendedMatrix_eq_kronDelta_off_tsupport
    (g : SmoothRiemannianMetric I M) (α : M)
    {χ : EuclN → ℝ}
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) (hy : y ∉ tsupport χ) :
    extendedMatrix (I := I) g α χ i j y = kronDelta (E := E) i j := by
  have hχ_zero : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
  unfold extendedMatrix
  rw [hχ_zero]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_eq_kronDelta_off_tsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_eq_kronDelta_off_tsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_eq_kronDelta_off_tsupport ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_eq_kronDelta_off_tsupport

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma kronDelta_quad_eq_norm_sq (ξ : EuclN) :
    ⟪ξ, DeGiorgi.matMulE
      (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        kronDelta (E := E) i j)) ξ⟫_ℝ = ‖ξ‖ ^ 2 := by
  classical
  have h_eq : (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      kronDelta (E := E) i j)) =
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [kronDelta]
    · simp [kronDelta, h]
  rw [h_eq]
  have hmul1 : DeGiorgi.matMulE
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) ξ = ξ := by
    apply WithLp.ofLp_injective 2
    rw [DeGiorgi.matMulE_ofLp]
    exact Matrix.one_mulVec _
  rw [hmul1]
  rw [real_inner_self_eq_norm_sq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.kronDelta_quad_eq_norm_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.kronDelta_quad_eq_norm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.kronDelta_quad_eq_norm_sq ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.kronDelta_quad_eq_norm_sq

omit [NeZero (Module.finrank ℝ E)] in
lemma extendedMatrix_coercive
    (g : SmoothRiemannianMetric I M) (α : M)
    {χ : EuclN → ℝ}
    (hχ_range : Set.range χ ⊆ Set.Icc (0 : ℝ) 1)
    (hχ_support : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {lamK : ℝ} (hlamK_le : lamK ≤ 1)
    (h_uniform : ∀ y ∈ tsupport χ, ∀ ξ : EuclN,
        lamK * ‖ξ‖ ^ 2 ≤
          ⟪ξ, DeGiorgi.matMulE
            (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
              weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ)
    (y : EuclN) (ξ : EuclN) :
    lamK * ‖ξ‖ ^ 2 ≤
      ⟪ξ, DeGiorgi.matMulE
        (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          extendedMatrix (I := I) g α χ i j y)) ξ⟫_ℝ := by
  classical
  by_cases hy : y ∈ tsupport χ
  · have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := hχ_support hy
    have h_uniform_y : ∀ ξ : EuclN, lamK * ‖ξ‖ ^ 2 ≤
        ⟪ξ, DeGiorgi.matMulE
          (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
            weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ :=
      fun ξ => h_uniform y hy ξ
    have h_min_eq : _root_.Min.min (1 : ℝ) lamK = lamK := min_eq_right hlamK_le
    have h := extendedMatrix_coercive_on_chart (I := I) g α
      (χ := χ) hχ_range (y := y) h_uniform_y ξ
    rw [h_min_eq] at h
    exact h
  · have h_eq : ⟪ξ, DeGiorgi.matMulE
        (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          extendedMatrix (I := I) g α χ i j y)) ξ⟫_ℝ = ‖ξ‖ ^ 2 := by
      have h_mat_eq : (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
            extendedMatrix (I := I) g α χ i j y)) =
          Matrix.of (fun i j : Fin (Module.finrank ℝ E) => kronDelta (E := E) i j) := by
        ext i j
        exact extendedMatrix_eq_kronDelta_off_tsupport (I := I) g α i j y hy
      rw [h_mat_eq]
      exact kronDelta_quad_eq_norm_sq ξ
    rw [h_eq]
    have h_norm_sq_nn : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
    have : lamK * ‖ξ‖ ^ 2 ≤ 1 * ‖ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hlamK_le h_norm_sq_nn
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_coercive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_coercive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_coercive ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.extendedMatrix_coercive

theorem exists_smooth_metric_extension
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN}
    (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ Ω' : Set EuclN,
      IsOpen Ω' ∧ K ⊆ Ω' ∧ IsCompact (closure Ω') ∧
      closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α ∧
    ∃ B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN),
      (∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        B.a y i j = weightedInvGramOnEuclid (I := I) g α i j y) ∧
      B.c = (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have hO : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨δ, δ_pos, hδ_subset⟩ := hK.exists_cthickening_subset_open hO hK_target
  set Ω' : Set EuclN := Metric.thickening δ K with hΩ'_def
  set K' : Set EuclN := Metric.cthickening δ K with hK'_def
  have hΩ'_open : IsOpen Ω' := Metric.isOpen_thickening
  have hK'_compact : IsCompact K' := hK.cthickening (r := δ)
  have h_K_in_Ω' : K ⊆ Ω' := Metric.self_subset_thickening δ_pos K
  have h_Ω'_in_K' : Ω' ⊆ K' := Metric.thickening_subset_cthickening δ K
  have h_K'_in_chart : K' ⊆ chartTargetEuclid (I := I) (M := M) α := hδ_subset
  have h_closure_Ω'_in_K' : closure Ω' ⊆ K' :=
    Metric.closure_thickening_subset_cthickening δ K
  have h_closure_compact : IsCompact (closure Ω') :=
    hK'_compact.of_isClosed_subset isClosed_closure h_closure_Ω'_in_K'
  have h_closure_in_chart : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closure_Ω'_in_K'.trans h_K'_in_chart
  obtain ⟨χ, hχ_smooth, hχ_support, hχ_one_nhds, hχ_tsupp, hχ_range⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact
      (K := K) (U := Ω') hK hΩ'_open h_K_in_Ω'
  have hχ_one : ∀ x ∈ K, χ x = 1 := fun _ hx =>
    hχ_one_nhds.self_of_nhdsSet hx
  have hχ_tsupp_chart : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro y hy
    have h1 : y ∈ Ω' := hχ_tsupp hy
    exact (h_Ω'_in_K'.trans h_K'_in_chart) h1
  have hχ_tsupp_compact : IsCompact (tsupport χ) := hχ_support
  obtain ⟨lamK0, hlamK0_pos, hlamK0_bound⟩ :=
    exists_uniform_lower_bound_on_compact (I := I) g α hχ_tsupp_compact hχ_tsupp_chart
  set lamK : ℝ := _root_.Min.min 1 lamK0 with hlamK_def
  have hlamK_pos : 0 < lamK := lt_min one_pos hlamK0_pos
  have hlamK_le_one : lamK ≤ 1 := min_le_left _ _
  have hlamK_le_lamK0 : lamK ≤ lamK0 := min_le_right _ _
  have hlamK0_bound_for_lamK : ∀ y ∈ tsupport χ, ∀ ξ : EuclN,
      lamK * ‖ξ‖ ^ 2 ≤
        ⟪ξ, DeGiorgi.matMulE
          (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
            weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ := by
    intro y hy ξ
    have h0 := hlamK0_bound y hy ξ
    have h_norm_sq_nn : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
    have h_le : lamK * ‖ξ‖ ^ 2 ≤ lamK0 * ‖ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hlamK_le_lamK0 h_norm_sq_nn
    linarith
  let aFun : EuclN → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun y => Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      extendedMatrix (I := I) g α χ i j y)
  have h_a_smooth : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN => aFun y i j) := by
    intro i j
    change ContDiff ℝ (⊤ : ℕ∞) (extendedMatrix (I := I) g α χ i j)
    exact extendedMatrix_contDiff (I := I) g α
      (χ := χ) hχ_smooth hχ_tsupp_chart i j
  have h_a_symm : ∀ y i j, aFun y i j = aFun y j i := by
    intro y i j
    change extendedMatrix (I := I) g α χ i j y =
      extendedMatrix (I := I) g α χ j i y
    exact extendedMatrix_symm (I := I) g α
      (χ := χ) hχ_tsupp_chart i j y
  have h_a_coercive : ∀ y ∈ (Set.univ : Set EuclN), ∀ ξ : EuclN,
      lamK * ‖ξ‖ ^ 2 ≤ ⟪ξ, DeGiorgi.matMulE (aFun y) ξ⟫_ℝ := by
    intro y _ ξ
    change lamK * ‖ξ‖ ^ 2 ≤
      ⟪ξ, DeGiorgi.matMulE
        (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          extendedMatrix (I := I) g α χ i j y)) ξ⟫_ℝ
    exact extendedMatrix_coercive (I := I) g α
      (χ := χ) hχ_range hχ_tsupp_chart hlamK_le_one
      hlamK0_bound_for_lamK y ξ
  let B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN) :=
    { a := aFun
      c := fun _ => 0
      symm := h_a_symm
      smooth_a := h_a_smooth
      smooth_c := contDiff_const
      lam := lamK
      capLam := _root_.Max.max lamK 1
      ellipticity_pos := hlamK_pos
      ellipticity_le_upper := le_max_left _ _
      coercive := h_a_coercive }
  have h_agree : ∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
      B.a y i j = weightedInvGramOnEuclid (I := I) g α i j y := by
    intro y hy i j
    change extendedMatrix (I := I) g α χ i j y =
      weightedInvGramOnEuclid (I := I) g α i j y
    have hχ_y : χ y = 1 := hχ_one y hy
    unfold extendedMatrix
    rw [hχ_y]
    ring
  refine ⟨Ω', hΩ'_open, h_K_in_Ω', h_closure_compact, h_closure_in_chart, B, h_agree, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_smooth_metric_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_smooth_metric_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_smooth_metric_extension ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_smooth_metric_extension

end MetricExtension
end Laplacian
end Analysis
end DifferentialGeometry

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

lemma chartCoeffOnE_comp_toEuclidean_symm_contDiffOn
    (α : M) {Ω : Set EuclN} (hΩs : Ω ⊆ chartTargetEuclid (I := I) α)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => chartCoeffOnE (I := I) α X i
      ((toEuclidean (E := E)).symm z)) Ω := by
  apply (chartCoeffOnE_contDiffOn (I := I) α X i).comp
    (toEuclidean (E := E)).symm.contDiff.contDiffOn
  intro z hz
  exact toEuclidean_symm_mem_target (hΩs hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_contDiffOn


end DifferentialGeometry.Analysis.Laplacian.MetricExtension

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclF" => EuclideanSpace ℝ (Fin (Module.finrank ℝ F))

lemma exists_uniform_inv_gram_lower_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M) {K : Set EuclF}
    (hK : IsCompact K) (hKs : K ⊆ chartTargetEuclid (I := I) α) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ y ∈ K, ∀ ξ : Fin (Module.finrank ℝ F) → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j, invGramOnEuclid g α i j y * ξ i * ξ j := by
  obtain ⟨lam, hlam, hbound⟩ := Schauder.exists_uniform_matrix_quadratic_lower_bound hK
    (fun y => Matrix.of (fun i j : Fin (Module.finrank ℝ F) => invGramOnEuclid g α i j y))
    (fun i j => (invGramOnEuclid_contDiffOn g α i j).continuousOn.mono hKs)
    (fun y hy => invGramOnEuclid_posDef g α (hKs hy))
  refine ⟨lam, hlam, ?_⟩
  intro y hy ξ
  have hb := hbound y hy (WithLp.toLp 2 ξ)
  have hnorm : ‖(WithLp.toLp 2 ξ : EuclF)‖ ^ 2 = ∑ i, (ξ i)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    change ‖ξ i‖^2 = (ξ i)^2
    simp only [Real.norm_eq_abs, sq_abs]
  have hquad : dotProduct (_root_.Star.star (WithLp.toLp 2 ξ : EuclF))
      ((Matrix.of (fun i j => invGramOnEuclid g α i j y)).mulVec (WithLp.toLp 2 ξ)) =
      ∑ i, ∑ j, invGramOnEuclid g α i j y * ξ i * ξ j := by
    simp only [Matrix.mulVec, dotProduct, Pi.star_apply, _root_.TrivialStar.star_trivial, Matrix.of_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change ξ i * (invGramOnEuclid g α i j y * ξ j) = _
    ring
  rwa [hnorm, hquad] at hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_uniform_inv_gram_lower_bound_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_uniform_inv_gram_lower_bound_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_uniform_inv_gram_lower_bound_on_compact ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_uniform_inv_gram_lower_bound_on_compact

end DifferentialGeometry.Analysis.Laplacian.MetricExtension

end

noncomputable section

open _root_.Manifold _root_.Set
open scoped _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_smooth_metric_extension_of_subset_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target) :
    ∃ B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN),
      (∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        B.a y i j = weightedInvGramOnEuclid (I := I) g α i j y) ∧
      B.c = (fun _ : EuclN => (0 : ℝ)) := by
  classical
  let U : Set EuclN := toEuclidean (E := E) '' interior (extChartAt I α).target
  have hU : IsOpen U :=
    (toEuclidean (E := E)).toHomeomorph.isOpenMap _ isOpen_interior
  have hU_target : U ⊆ chartTargetEuclid (I := I) (M := M) α :=
    _root_.Set.image_mono interior_subset
  obtain ⟨χ, hχ_smooth, hχ_compact, hχ_one_nhds, hχ_support, hχ_range⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact hK hU hK_target
  have hχ_one : ∀ y ∈ K, χ y = 1 := fun _ hy =>
    hχ_one_nhds.self_of_nhdsSet hy
  have hχ_target : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α :=
    hχ_support.trans hU_target
  obtain ⟨lamK, hlamK_pos, hlamK_bound⟩ :=
    exists_uniform_lower_bound_on_compact (I := I) g α hχ_compact hχ_target
  have hbound : ∀ y ∈ tsupport χ, ∀ ξ : EuclN,
      _root_.Min.min 1 lamK * ‖ξ‖ ^ 2 ≤
        _root_.Inner.inner ℝ ξ (DeGiorgi.matMulE
          (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
            weightedInvGramOnEuclid (I := I) g α i j y)) ξ) := by
    intro y hy ξ
    exact (mul_le_mul_of_nonneg_right (min_le_right 1 lamK)
      (sq_nonneg ‖ξ‖)).trans (hlamK_bound y hy ξ)
  let aFun : EuclN → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun y => Matrix.of (fun i j => extendedMatrix (I := I) g α χ i j y)
  have h_a_smooth : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN => aFun y i j) := by
    intro i j
    have hproduct : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : EuclN => χ y * weightedInvGramOnEuclid (I := I) g α i j y) := by
      simpa only [smul_eq_mul] using DifferentialGeometry.Analysis.contDiff_cutoff_smul
        hU hχ_smooth hχ_support
        ((weightedInvGramOnEuclid_contDiffOn (I := I) g α i j).mono hU_target)
    change ContDiff ℝ (⊤ : ℕ∞) (extendedMatrix (I := I) g α χ i j)
    unfold extendedMatrix
    exact hproduct.add ((contDiff_const.sub hχ_smooth).mul contDiff_const)
  let B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN) :=
    { a := aFun
      c := fun _ => 0
      symm := fun y i j => extendedMatrix_symm (I := I) g α hχ_target i j y
      smooth_a := h_a_smooth
      smooth_c := contDiff_const
      lam := _root_.Min.min 1 lamK
      capLam := 1
      ellipticity_pos := lt_min one_pos hlamK_pos
      ellipticity_le_upper := min_le_left _ _
      coercive := fun y _ ξ => extendedMatrix_coercive (I := I) g α
        hχ_range hχ_target (min_le_left 1 lamK) hbound y ξ }
  refine ⟨B, ?_, rfl⟩
  intro y hy i j
  change extendedMatrix (I := I) g α χ i j y =
    weightedInvGramOnEuclid (I := I) g α i j y
  unfold extendedMatrix
  simp only [hχ_one y hy, one_mul, sub_self, _root_.MulZeroClass.zero_mul, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_smooth_metric_extension_of_subset_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_smooth_metric_extension_of_subset_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_smooth_metric_extension_of_subset_interior ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_smooth_metric_extension_of_subset_interior

end DifferentialGeometry.Analysis.Laplacian.MetricExtension

end
