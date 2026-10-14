import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CoreInteriorCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.IsManifold
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev NormalE2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.NormalE2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.NormalE2 target :: scope.openDecls } }
private abbrev NormalC := NormalE2 × ℝ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.NormalC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.NormalC target :: scope.openDecls } }
private abbrev NormalIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.NormalIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.NormalIC target :: scope.openDecls } }
private abbrev NormalH := ModelProd NormalE2 ℝ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.NormalH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.NormalH target :: scope.openDecls } }
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable (hdim : Module.finrank ℝ E = 3)

def coreAmbientLinearEquiv : E ≃L[ℝ] NormalC :=
  (LinearEquiv.ofFinrankEq (R := ℝ) E NormalC (by simpa using hdim)).toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientLinearEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientLinearEquiv

def coreBoundaryAmbientLinearEquiv : (NormalE2 × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] E :=
  ((ContinuousLinearEquiv.refl ℝ NormalE2).prodCongr
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ))).trans (coreAmbientLinearEquiv hdim).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.coreBoundaryAmbientLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.coreBoundaryAmbientLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.coreBoundaryAmbientLinearEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.coreBoundaryAmbientLinearEquiv

def coreAmbientCoordinateDiffeomorph : H ≃ₘ⟮I, 𝓘(ℝ, NormalC)⟯ NormalC where
  toEquiv := (I.toHomeomorph.trans (coreAmbientLinearEquiv hdim).toHomeomorph).toEquiv
  contMDiff_toFun := (coreAmbientLinearEquiv hdim).contDiff.contMDiff.comp I.contMDiff
  contMDiff_invFun := by
    have hI : ContMDiff 𝓘(ℝ, E) I ∞ I.symm := by
      rw [← contMDiffOn_univ, ← I.range_eq_univ]
      exact I.contMDiffOn_symm
    exact hI.comp (coreAmbientLinearEquiv hdim).symm.contDiff.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientCoordinateDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientCoordinateDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientCoordinateDiffeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientCoordinateDiffeomorph

def coreAmbientNormalizingHomeomorph (a σ : ℝ) (hσ : σ ^ 2 = 1) : NormalH ≃ₜ H :=
  (NormalIC.toHomeomorph.trans
    (cylinderAxialDiffeomorph (I := 𝓡 2) (M := NormalE2) a σ hσ).toHomeomorph).trans
      (coreAmbientCoordinateDiffeomorph I hdim).symm.toHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientNormalizingHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientNormalizingHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientNormalizingHomeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientNormalizingHomeomorph

theorem coreAmbientNormalizingHomeomorph_contMDiff (a σ : ℝ) (hσ : σ ^ 2 = 1) :
    ContMDiff NormalIC I ∞ (coreAmbientNormalizingHomeomorph I hdim a σ hσ) := by
  have hA : ContDiff ℝ ∞ (fun z : NormalC => (z.1, a + σ * z.2)) := by fun_prop
  exact (coreAmbientCoordinateDiffeomorph I hdim).symm.contMDiff.comp
    (hA.contMDiff.comp NormalIC.contMDiff)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientNormalizingHomeomorph_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientNormalizingHomeomorph_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientNormalizingHomeomorph_contMDiff ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientNormalizingHomeomorph_contMDiff

theorem coreAmbientNormalizingHomeomorph_symm_contMDiff (a σ : ℝ) (hσ : σ ^ 2 = 1) :
    ContMDiff I NormalIC ∞ (coreAmbientNormalizingHomeomorph I hdim a σ hσ).symm := by
  have hA : ContDiff ℝ ∞ (fun z : NormalC => (z.1, σ * (z.2 - a))) := by fun_prop
  have hIC : ContMDiff 𝓘(ℝ, NormalC) NormalIC ∞ NormalIC.symm := by
    rw [← contMDiffOn_univ, ← NormalIC.range_eq_univ]
    exact NormalIC.contMDiffOn_symm
  exact hIC.comp (hA.contMDiff.comp (coreAmbientCoordinateDiffeomorph I hdim).contMDiff)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientNormalizingHomeomorph_symm_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientNormalizingHomeomorph_symm_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientNormalizingHomeomorph_symm_contMDiff ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientNormalizingHomeomorph_symm_contMDiff

theorem coreAmbientNormalizingHomeomorph_extend (a σ : ℝ) (hσ : σ ^ 2 = 1) (z : NormalH) :
    I (coreAmbientNormalizingHomeomorph I hdim a σ hσ z) =
      (coreAmbientLinearEquiv hdim).symm (z.1, a + σ * z.2) := by
  exact I.right_inv (by rw [I.range_eq_univ]; trivial)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientNormalizingHomeomorph_extend then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientNormalizingHomeomorph_extend"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientNormalizingHomeomorph_extend ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.coreAmbientNormalizingHomeomorph_extend
end DifferentialGeometry.Topology.ThreeManifold.Surgery
