import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import Submission.DifferentialGeometry.Geometry.Metric.PolarCoordinates
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

def positiveCylinderReparametrization : S2 × ℝ → S2 × ℝ := Prod.map id Real.exp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.positiveCylinderReparametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.positiveCylinderReparametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.positiveCylinderReparametrization ``Submission.DifferentialGeometry.Topology.Manifold.positiveCylinderReparametrization

theorem positiveCylinderReparametrization_contMDiff :
    ContMDiff IC IC ∞ positiveCylinderReparametrization :=
  contMDiff_id.prodMap Real.contDiff_exp.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.positiveCylinderReparametrization_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.positiveCylinderReparametrization_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.positiveCylinderReparametrization_contMDiff ``Submission.DifferentialGeometry.Topology.Manifold.positiveCylinderReparametrization_contMDiff

private theorem exp_mfderiv_bijective (t : ℝ) :
    Bijective (mfderiv 𝓘(ℝ) 𝓘(ℝ) Real.exp t) := by
  let A : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 (Real.exp t) (Real.exp_ne_zero t))
  have h : mfderiv 𝓘(ℝ) 𝓘(ℝ) Real.exp t = (A : ℝ →L[ℝ] ℝ) := by
    rw [mfderiv_eq_fderiv, (Real.hasDerivAt_exp t).hasFDerivAt.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    change v * Real.exp t = Real.exp t * v
    exact mul_comm _ _
  rw [h]
  exact A.bijective

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.exp_mfderiv_bijective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.exp_mfderiv_bijective target :: scope.openDecls } }

theorem positiveCylinderReparametrization_mfderiv_bijective (q : S2 × ℝ) :
    Bijective (mfderiv IC IC positiveCylinderReparametrization q) := by
  have hexp : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ Real.exp := Real.contDiff_exp.contMDiff
  change _root_.Function.Bijective (mfderiv IC IC (Prod.map (id : S2 → S2) Real.exp) q)
  rw [mfderiv_prodMap mdifferentiableAt_id (hexp.mdifferentiableAt (by simp)), mfderiv_id]
  exact Function.bijective_id.prodMap (exp_mfderiv_bijective q.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.positiveCylinderReparametrization_mfderiv_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.positiveCylinderReparametrization_mfderiv_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.positiveCylinderReparametrization_mfderiv_bijective ``Submission.DifferentialGeometry.Topology.Manifold.positiveCylinderReparametrization_mfderiv_bijective

def exponentialPolarMap (q : S2 × ℝ) : E3 := euclideanPolarMap (positiveCylinderReparametrization q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exponentialPolarMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exponentialPolarMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exponentialPolarMap ``Submission.DifferentialGeometry.Topology.Manifold.exponentialPolarMap

theorem exponentialPolarMap_contMDiff : ContMDiff IC (𝓡 3) ∞ exponentialPolarMap :=
  (euclideanPolarMap_smooth (n := 2)).comp positiveCylinderReparametrization_contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exponentialPolarMap_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exponentialPolarMap_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exponentialPolarMap_contMDiff ``Submission.DifferentialGeometry.Topology.Manifold.exponentialPolarMap_contMDiff

theorem exponentialPolarMap_mfderiv_bijective (q : S2 × ℝ) :
    Bijective (mfderiv IC (𝓡 3) exponentialPolarMap q) := by
  have hP : IsLocalDiffeomorphAt IC (𝓡 3) ∞ euclideanPolarMap
      (positiveCylinderReparametrization q) :=
    PartialDiffeomorph.isLocalDiffeomorphAt IC (𝓡 3) ∞
      (euclideanPolarDiffeomorph (E := E3) (n := 2)) (Real.exp_pos q.2)
  have h := mfderiv_comp q (hP.contMDiffAt.mdifferentiableAt (by simp))
    (positiveCylinderReparametrization_contMDiff.mdifferentiableAt (by simp))
  change _root_.Function.Bijective (mfderiv IC (𝓡 3) (euclideanPolarMap ∘ positiveCylinderReparametrization) q)
  rw [h]
  exact (hP.mfderivToContinuousLinearEquiv (by simp)).bijective.comp (positiveCylinderReparametrization_mfderiv_bijective q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exponentialPolarMap_mfderiv_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exponentialPolarMap_mfderiv_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exponentialPolarMap_mfderiv_bijective ``Submission.DifferentialGeometry.Topology.Manifold.exponentialPolarMap_mfderiv_bijective

def roundCylinderSmoothOrientation (o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) :
    SmoothOrientation IC (S2 × ℝ) :=
  pullbackSmoothOrientation IC (𝓡 3) exponentialPolarMap exponentialPolarMap_contMDiff
    exponentialPolarMap_mfderiv_bijective (euclideanSmoothOrientation E3 o)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.roundCylinderSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.roundCylinderSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.roundCylinderSmoothOrientation ``Submission.DifferentialGeometry.Topology.Manifold.roundCylinderSmoothOrientation

theorem roundCylinderSmoothOrientation_pushforward
    (o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) (q : S2 × ℝ) :
    tangentOrientationEquiv (differentialEquivOfBijective IC (𝓡 3) exponentialPolarMap
      exponentialPolarMap_mfderiv_bijective q).toLinearEquiv ((roundCylinderSmoothOrientation o).val q) = o :=
  tangentOrientationEquiv_symm
    (differentialEquivOfBijective IC (𝓡 3) exponentialPolarMap
      exponentialPolarMap_mfderiv_bijective q).symm.toLinearEquiv o

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.roundCylinderSmoothOrientation_pushforward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.roundCylinderSmoothOrientation_pushforward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.roundCylinderSmoothOrientation_pushforward ``Submission.DifferentialGeometry.Topology.Manifold.roundCylinderSmoothOrientation_pushforward
end DifferentialGeometry.Topology.Manifold
