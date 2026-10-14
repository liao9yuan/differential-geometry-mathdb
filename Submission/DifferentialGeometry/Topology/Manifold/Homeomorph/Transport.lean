import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Manifold _root_.Topology
open scoped _root_.ContDiff
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.Homeomorph
variable {H M X : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace X]

@[instance_reducible] def pullbackChartedSpace (h : X ≃ₜ M) : ChartedSpace H X where
  atlas := {h.toOpenPartialHomeomorph.trans e | e ∈ atlas H M}
  chartAt x := h.toOpenPartialHomeomorph.trans (chartAt H (h x))
  mem_chart_source x := by simp
  chart_mem_atlas x := ⟨chartAt H (h x), chart_mem_atlas H (h x), rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace ``Submission.DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace


@[simp] theorem chartAt_pullback (h : X ≃ₜ M) (x : X) :
    let _ := pullbackChartedSpace (H := H) h
    chartAt H x = h.toOpenPartialHomeomorph.trans (chartAt H (h x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Homeomorph.chartAt_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Homeomorph.chartAt_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Homeomorph.chartAt_pullback ``Submission.DifferentialGeometry.Manifold.Homeomorph.chartAt_pullback

omit [ChartedSpace H M] in
private theorem trans_cancel (h : X ≃ₜ M) (e e' : OpenPartialHomeomorph M H) :
    (h.toOpenPartialHomeomorph.trans e).symm.trans
      (h.toOpenPartialHomeomorph.trans e') = e.symm.trans e' := by
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_assoc, ← OpenPartialHomeomorph.trans_assoc h.toOpenPartialHomeomorph.symm,
    ← Homeomorph.symm_toOpenPartialHomeomorph, ← Homeomorph.trans_toOpenPartialHomeomorph,
    Homeomorph.symm_trans_self]
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Manifold.Homeomorph.trans_cancel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Manifold.Homeomorph.trans_cancel target :: scope.openDecls } }

instance instHasGroupoidPullback (h : X ≃ₜ M) (G : StructureGroupoid H) [HasGroupoid M G] :
    let _ := pullbackChartedSpace (H := H) h
    HasGroupoid X G := by
  let _ := pullbackChartedSpace (H := H) h
  change HasGroupoid X G
  constructor
  rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
  rw [trans_cancel]
  exact G.compatible he he'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Homeomorph.instHasGroupoidPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Homeomorph.instHasGroupoidPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Homeomorph.instHasGroupoidPullback ``Submission.DifferentialGeometry.Manifold.Homeomorph.instHasGroupoidPullback

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} [IsManifold I n M]


instance instIsManifoldPullback (h : X ≃ₜ M) :
    let _ := pullbackChartedSpace (H := H) h
    IsManifold I n X := by
  let _ := pullbackChartedSpace (H := H) h
  exact IsManifold.mk' I n X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback ``Submission.DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback


theorem contMDiff_pullback (h : X ≃ₜ M) :
    let _ := pullbackChartedSpace (H := H) h
    ContMDiff I I n h := by
  let _ := pullbackChartedSpace (H := H) h
  apply contMDiff_iff.mpr
  refine ⟨h.continuous, ?_⟩
  intro x y
  have hh := (contMDiff_iff.mp (contMDiff_id (I := I) (M := M) (n := n))).2 (h x) y
  convert hh using 1
  · ext z
    simp [extChartAt, OpenPartialHomeomorph.extend, Function.comp_def]
  · ext z
    simp [extChartAt, OpenPartialHomeomorph.extend, Function.comp_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Homeomorph.contMDiff_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Homeomorph.contMDiff_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Homeomorph.contMDiff_pullback ``Submission.DifferentialGeometry.Manifold.Homeomorph.contMDiff_pullback


theorem contMDiff_symm_pullback (h : X ≃ₜ M) :
    let _ := pullbackChartedSpace (H := H) h
    ContMDiff I I n h.symm := by
  let _ := pullbackChartedSpace (H := H) h
  apply contMDiff_iff.mpr
  refine ⟨h.symm.continuous, ?_⟩
  intro x y
  have hh := (contMDiff_iff.mp (contMDiff_id (I := I) (M := M) (n := n))).2 x (h y)
  convert hh using 1
  · ext z
    simp [extChartAt, OpenPartialHomeomorph.extend, Function.comp_def]
  · ext z
    simp [extChartAt, OpenPartialHomeomorph.extend, Function.comp_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Homeomorph.contMDiff_symm_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Homeomorph.contMDiff_symm_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Homeomorph.contMDiff_symm_pullback ``Submission.DifferentialGeometry.Manifold.Homeomorph.contMDiff_symm_pullback

def pullbackDiffeomorph (h : X ≃ₜ M) :
    let _ := pullbackChartedSpace (H := H) h
    Diffeomorph I I X M n := by
  let _ := pullbackChartedSpace (H := H) h
  exact ⟨h.toEquiv, contMDiff_pullback h, contMDiff_symm_pullback h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph ``Submission.DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph

theorem boundaryless_manifold_pullback
    [BoundarylessManifold I M] (h : X ≃ₜ M) (hn : n ≠ 0) :
    let _ := pullbackChartedSpace (H := H) h
    BoundarylessManifold I X := by
  let _ := pullbackChartedSpace (H := H) h
  refine ⟨fun x ↦ ?_⟩
  exact ((pullbackDiffeomorph (I := I) (n := n) h).isLocalDiffeomorph x).isInteriorPoint_iff
    hn |>.mpr BoundarylessManifold.isInteriorPoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Homeomorph.boundaryless_manifold_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Homeomorph.boundaryless_manifold_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Homeomorph.boundaryless_manifold_pullback ``Submission.DifferentialGeometry.Manifold.Homeomorph.boundaryless_manifold_pullback

@[simp] theorem pullbackDiffeomorph_apply (h : X ≃ₜ M) (x : X) :
    let _ := pullbackChartedSpace (H := H) h
    pullbackDiffeomorph (I := I) (n := n) h x = h x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph_apply ``Submission.DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph_apply

theorem pullbackDiffeomorph_symm_apply (h : X ≃ₜ M) (x : M) :
    let _ := pullbackChartedSpace (H := H) h
    (pullbackDiffeomorph (I := I) (n := n) h).symm x = h.symm x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph_symm_apply

end DifferentialGeometry.Manifold.Homeomorph
