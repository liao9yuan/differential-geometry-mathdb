import Submission.DifferentialGeometry.Topology.PuncturedConnected
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.LocallyConvex.WithSeminorms

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Filter _root_.Set
open scoped _root_.Topology

open _root_.ChartedSpace in
theorem ChartedSpace.isPathConnected_compl_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [PreconnectedSpace M]
    (hdim : 1 < Module.rank ℝ E) (p : M) :
    IsPathConnected ({p}ᶜ : Set M) := by
  let _ : T1Space M := ChartedSpace.t1Space E M
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  let e : OpenPartialHomeomorph M E := chartAt E p
  have hp : p ∈ e.source := mem_chart_source E p
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (e.open_target.mem_nhds (e.map_source hp))
  let U : Set M := e.symm '' Metric.ball (e p) r
  have hopen : IsOpen U := e.isOpen_image_symm_of_subset_target Metric.isOpen_ball hball
  have hpU : p ∈ U := ⟨e p, Metric.mem_ball_self hr, e.left_inv hp⟩
  have himage : e.symm '' (Metric.ball (e p) r \ {e p}) = U \ {p} := by
    apply Set.Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      refine ⟨⟨z, hz.1, rfl⟩, ?_⟩
      intro heq
      apply hz.2
      exact (e.right_inv (hball hz.1)).symm.trans (congrArg e heq)
    · rintro y ⟨⟨z, hz, rfl⟩, hne⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      intro heq
      apply hne
      exact (congrArg e.symm heq).trans (e.left_inv hp)
  apply isPathConnected_compl_singleton_of_punctured_neighborhood p (hopen.mem_nhds hpU)
  rw [← himage]
  exact ((Metric.isPathConnected_ball_sdiff_singleton hdim (e p) hr).image'
    (e.continuousOn_symm.mono (fun z hz => hball hz.1))).isConnected

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ChartedSpace
  let env ← Lean.getEnv
  if env.contains `ChartedSpace.isPathConnected_compl_singleton then
    throwError "Refusing to shadow existing declaration ChartedSpace.isPathConnected_compl_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `ChartedSpace.isPathConnected_compl_singleton ``Submission.ChartedSpace.isPathConnected_compl_singleton


open _root_.ModelWithCorners in
theorem ModelWithCorners.isPathConnected_compl_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [PreconnectedSpace M]
    (hdim : 1 < Module.rank ℝ E) (p : M) :
    IsPathConnected ({p}ᶜ : Set M) := by
  let _ : ChartedSpace E H := I.toHomeomorph.symm.chartedSpace
  let _ : ChartedSpace E M := ChartedSpace.comp E H M
  exact ChartedSpace.isPathConnected_compl_singleton hdim p

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ModelWithCorners
  let env ← Lean.getEnv
  if env.contains `ModelWithCorners.isPathConnected_compl_singleton then
    throwError "Refusing to shadow existing declaration ModelWithCorners.isPathConnected_compl_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `ModelWithCorners.isPathConnected_compl_singleton ``Submission.ModelWithCorners.isPathConnected_compl_singleton
