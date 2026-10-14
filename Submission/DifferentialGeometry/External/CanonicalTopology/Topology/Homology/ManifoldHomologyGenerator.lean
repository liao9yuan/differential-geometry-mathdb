import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ManifoldFundamentalClass
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.EuclideanLocalTop

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
noncomputable section

open _root_.CategoryTheory _root_.Module _root_.Set
open scoped _root_.Manifold

universe u

namespace DifferentialGeometry.Topology

private theorem exists_manifold_local_generator
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T1Space M] [ChartedSpace E M] (p : M) :
    ∃ c : integralLocalHomology (_root_.Module.finrank ℝ E) p,
      Function.Bijective (fun k : ℤ => k • c) := by
  obtain ⟨c, hc⟩ := exists_integralLocalHomology_generator (chartAt E p p)
  let e := (integralLocalHomologyChartIso (Y := E) (_root_.Module.finrank ℝ E) p).toLinearEquiv
  refine ⟨e.symm c, ?_⟩
  simpa only [Function.comp_def, map_zsmul] using e.symm.bijective.comp hc

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.exists_manifold_local_generator
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.exists_manifold_local_generator target :: scope.openDecls } }

theorem exists_integralSingularHomology_generator_of_simplyConnected
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    [CompactSpace M] [SimplyConnectedSpace M] :
    ∃ a : integralSingularHomology (_root_.Module.finrank ℝ E) M,
      Function.Bijective (fun k : ℤ => k • a) ∧
      ∀ x : M, Function.Bijective (fun k : ℤ =>
        k • integralAbsoluteToRelative (_root_.Module.finrank ℝ E) ({x}ᶜ : Set M) a) := by
  let p := Classical.arbitrary M
  obtain ⟨c, hc⟩ := exists_manifold_local_generator (E := E) p
  let e := LinearEquiv.ofBijective
    (integralAbsoluteToRelative (_root_.Module.finrank ℝ E) ({p}ᶜ : Set M))
    (integralAbsoluteToRelative_bijective_of_simplyConnected (E := E) p)
  have ha : Function.Bijective (fun k : ℤ => k • e.symm c) := by
    simpa only [Function.comp_def, map_zsmul] using e.symm.bijective.comp hc
  refine ⟨e.symm c, ha, ?_⟩
  intro x
  simpa only [Function.comp_def, map_zsmul] using
    (integralAbsoluteToRelative_bijective_of_simplyConnected (E := E) x).comp ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_integralSingularHomology_generator_of_simplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_integralSingularHomology_generator_of_simplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_integralSingularHomology_generator_of_simplyConnected ``Submission.DifferentialGeometry.Topology.exists_integralSingularHomology_generator_of_simplyConnected

end DifferentialGeometry.Topology
