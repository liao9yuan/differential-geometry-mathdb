import Submission.DifferentialGeometry.Topology.ProjectiveSpace.SphereHalfTurnFrame
import Mathlib.LinearAlgebra.Basis.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Module _root_.Submission.Module
open scoped _root_.Manifold _root_.ContDiff

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private local instance cylinderHalfTurnDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnDimension target :: scope.openDecls } }

def cylinderAntipodalProductDiffeomorph : (S × ℝ) ≃ₘ⟮CI, CI⟯ (S × ℝ) :=
  sphereAntipodalDiffeomorph.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAntipodalProductDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAntipodalProductDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAntipodalProductDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAntipodalProductDiffeomorph

theorem cylinderAntipodalProduct_mfderiv (p : S × ℝ) (v : TangentSpace CI p) :
    mfderiv CI CI cylinderAntipodalProductDiffeomorph p v =
      (mfderiv (𝓡 2) (𝓡 2) sphereAntipodalDiffeomorph p.1 v.1, v.2) := by
  change mfderiv CI CI (Prod.map sphereAntipodalDiffeomorph id) p v = _
  rw [mfderiv_prodMap
    (sphereAntipodalDiffeomorph.contMDiff.mdifferentiableAt (by simp))
    mdifferentiableAt_id, mfderiv_id]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAntipodalProduct_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAntipodalProduct_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAntipodalProduct_mfderiv ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAntipodalProduct_mfderiv

def cylinderHalfTurnBasis (t : ℝ) :
    Basis (Fin 3) ℝ (TangentSpace CI (sphereEquator t, (0 : ℝ))) :=
  ((sphereHalfTurnBasis t).prod (Basis.singleton (Fin 1) ℝ)).reindex finSumFinEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis

private theorem cylinderHalfTurnBasis_zero (t : ℝ) :
    cylinderHalfTurnBasis t 0 = (sphereHalfTurnBasis t 0, 0) := by
  have h : (((sphereHalfTurnBasis t).prod (Basis.singleton (Fin 1) ℝ)).reindex
      finSumFinEquiv) (Fin.castSucc (0 : Fin 2)) = (sphereHalfTurnBasis t 0, 0) := by
    rw [Basis.reindex_apply, finSumFinEquiv_symm_apply_castSucc]
    exact Prod.ext ((sphereHalfTurnBasis t).prod_apply_inl_fst _ _)
      ((sphereHalfTurnBasis t).prod_apply_inl_snd _ _)
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_zero target :: scope.openDecls } }

private theorem cylinderHalfTurnBasis_one (t : ℝ) :
    cylinderHalfTurnBasis t 1 = (sphereHalfTurnBasis t 1, 0) := by
  have h : (((sphereHalfTurnBasis t).prod (Basis.singleton (Fin 1) ℝ)).reindex
      finSumFinEquiv) (Fin.castSucc (1 : Fin 2)) = (sphereHalfTurnBasis t 1, 0) := by
    rw [Basis.reindex_apply, finSumFinEquiv_symm_apply_castSucc]
    exact Prod.ext ((sphereHalfTurnBasis t).prod_apply_inl_fst _ _)
      ((sphereHalfTurnBasis t).prod_apply_inl_snd _ _)
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_one target :: scope.openDecls } }

private theorem cylinderHalfTurnBasis_two (t : ℝ) :
    cylinderHalfTurnBasis t 2 = (0, 1) := by
  have h : (((sphereHalfTurnBasis t).prod (Basis.singleton (Fin 1) ℝ)).reindex
      finSumFinEquiv) (Fin.last 2) = (0, 1) := by
    rw [Basis.reindex_apply, finSumFinEquiv_symm_last]
    exact Prod.ext ((sphereHalfTurnBasis t).prod_apply_inr_fst _ _)
      (((sphereHalfTurnBasis t).prod_apply_inr_snd _ _).trans
        (Basis.singleton_apply (Fin 1) ℝ 0))
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_two
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_two target :: scope.openDecls } }

theorem cylinderHalfTurnBasis_continuous (i : Fin 3) :
    Continuous (fun t : ℝ =>
      (⟨(sphereEquator t, 0), cylinderHalfTurnBasis t i⟩ : TangentBundle CI (S × ℝ))) := by
  have hprod : Continuous (equivTangentBundleProd (𝓡 2) S 𝓘(ℝ, ℝ) ℝ).symm :=
    (contMDiff_equivTangentBundleProd_symm (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ))
      (M := S) (M' := ℝ) (n := ∞)).continuous
  have hzero : Continuous (fun t : ℝ =>
      TotalSpace.mk' V (E := TangentSpace (𝓡 2)) (sphereEquator t) 0) :=
    (continuous_zeroSection ℝ (F := V) (E := TangentSpace (𝓡 2))).comp
      sphereEquator_smooth.continuous
  fin_cases i
  · change Continuous (fun t : ℝ =>
      (⟨(sphereEquator t, 0), cylinderHalfTurnBasis t 0⟩ : TangentBundle CI (S × ℝ)))
    convert hprod.comp ((sphereHalfTurnBasis_continuous 0).prodMk
      (continuous_const (y := TotalSpace.mk' ℝ (E := TangentSpace 𝓘(ℝ, ℝ)) 0 0))) using 1
    funext t
    exact congrArg (fun v => (⟨(sphereEquator t, 0), v⟩ : TangentBundle CI (S × ℝ)))
      (cylinderHalfTurnBasis_zero t)
  · change Continuous (fun t : ℝ =>
      (⟨(sphereEquator t, 0), cylinderHalfTurnBasis t 1⟩ : TangentBundle CI (S × ℝ)))
    convert hprod.comp ((sphereHalfTurnBasis_continuous 1).prodMk
      (continuous_const (y := TotalSpace.mk' ℝ (E := TangentSpace 𝓘(ℝ, ℝ)) 0 0))) using 1
    funext t
    exact congrArg (fun v => (⟨(sphereEquator t, 0), v⟩ : TangentBundle CI (S × ℝ)))
      (cylinderHalfTurnBasis_one t)
  · change Continuous (fun t : ℝ =>
      (⟨(sphereEquator t, 0), cylinderHalfTurnBasis t 2⟩ : TangentBundle CI (S × ℝ)))
    convert hprod.comp (hzero.prodMk
      (continuous_const (y := TotalSpace.mk' ℝ (E := TangentSpace 𝓘(ℝ, ℝ)) 0 1))) using 1
    funext t
    exact congrArg (fun v => (⟨(sphereEquator t, 0), v⟩ : TangentBundle CI (S × ℝ)))
      (cylinderHalfTurnBasis_two t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_continuous ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_continuous

theorem cylinderHalfTurnBasis_pi_zero :
    cylinderHalfTurnBasis Real.pi 0 =
      mfderiv CI CI cylinderAntipodalProductDiffeomorph (sphereEquator 0, (0 : ℝ))
        (cylinderHalfTurnBasis 0 0) := by
  rw [cylinderAntipodalProduct_mfderiv, cylinderHalfTurnBasis_zero,
    cylinderHalfTurnBasis_zero]
  exact congrArg (fun v : V => (v, (0 : ℝ))) sphereHalfTurnBasis_pi_first

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_pi_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_pi_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_pi_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_pi_zero

theorem cylinderHalfTurnBasis_pi_one :
    cylinderHalfTurnBasis Real.pi 1 =
      -(mfderiv CI CI cylinderAntipodalProductDiffeomorph (sphereEquator 0, (0 : ℝ))
        (cylinderHalfTurnBasis 0 1)) := by
  rw [cylinderAntipodalProduct_mfderiv, cylinderHalfTurnBasis_one,
    cylinderHalfTurnBasis_one]
  apply Prod.ext
  · exact sphereHalfTurnBasis_pi_second
  · exact (neg_zero : -(0 : ℝ) = 0).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_pi_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_pi_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_pi_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_pi_one

theorem cylinderHalfTurnBasis_pi_two :
    cylinderHalfTurnBasis Real.pi 2 =
      mfderiv CI CI cylinderAntipodalProductDiffeomorph (sphereEquator 0, (0 : ℝ))
        (cylinderHalfTurnBasis 0 2) := by
  rw [cylinderAntipodalProduct_mfderiv, cylinderHalfTurnBasis_two,
    cylinderHalfTurnBasis_two]
  apply Prod.ext
  · exact (map_zero (mfderiv (𝓡 2) (𝓡 2) sphereAntipodalDiffeomorph
      (sphereEquator 0))).symm
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_pi_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_pi_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_pi_two ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderHalfTurnBasis_pi_two

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
