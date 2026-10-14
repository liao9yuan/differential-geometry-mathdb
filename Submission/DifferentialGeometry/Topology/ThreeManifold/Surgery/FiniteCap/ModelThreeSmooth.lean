import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapAtlas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.E3 target :: scope.openDecls } }
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]

def modelThreeDiffeomorph (hdim : Module.finrank ℝ E = 3) : H ≃ₘ⟮I, 𝓡 3⟯ E3 where
  toEquiv := (modelThreeHomeomorph I hdim).toEquiv
  contMDiff_toFun := by
    exact ((LinearEquiv.ofFinrankEq (R := ℝ) E E3 (by simpa using hdim)).toContinuousLinearEquiv.contDiff.contMDiff).comp I.contMDiff
  contMDiff_invFun := by
    have hs : ContMDiff 𝓘(ℝ, E) I ∞ I.symm := by
      rw [← contMDiffOn_univ, ← I.range_eq_univ]
      exact I.contMDiffOn_symm
    exact hs.comp ((LinearEquiv.ofFinrankEq (R := ℝ) E E3 (by simpa using hdim)).toContinuousLinearEquiv.symm.contDiff.contMDiff)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.modelThreeDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.modelThreeDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.modelThreeDiffeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.modelThreeDiffeomorph

theorem modelThreeDiffeomorph_apply (hdim : Module.finrank ℝ E = 3) (x : H) :
    modelThreeDiffeomorph I hdim x = modelThreeHomeomorph I hdim x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.modelThreeDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.modelThreeDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.modelThreeDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.modelThreeDiffeomorph_apply

theorem modelThreeDiffeomorph_symm_apply (hdim : Module.finrank ℝ E = 3) (x : E3) :
    (modelThreeDiffeomorph I hdim).symm x = (modelThreeHomeomorph I hdim).symm x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.modelThreeDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.modelThreeDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.modelThreeDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.modelThreeDiffeomorph_symm_apply
end DifferentialGeometry.Topology.ThreeManifold.Surgery
