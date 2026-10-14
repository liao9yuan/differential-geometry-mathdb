import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ConformalFactor
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Polar
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder
import Submission.DifferentialGeometry.Geometry.Metric.PolarCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.TopologicalSpace _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.InnerProductSpace _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.S2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

def puncturedSpace : _root_.TopologicalSpace.Opens E3 := ⟨{0}ᶜ, isOpen_compl_singleton⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.puncturedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.puncturedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.puncturedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.puncturedSpace

@[simp] theorem mem_puncturedSpace (x : E3) : x ∈ puncturedSpace ↔ x ≠ 0 := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.mem_puncturedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.mem_puncturedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.mem_puncturedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.mem_puncturedSpace

def conformalMap (q : S2 × ℝ) : E3 := conformalRadius q.2 • (q.1 : E3)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap

theorem conformalMap_smooth : ContMDiff ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) ∞ conformalMap :=
  (contDiff_conformalRadius.contMDiff.comp contMDiff_snd).smul
    ((contMDiff_coe_sphere (n := 2)).comp contMDiff_fst)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap_smooth ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap_smooth

@[simp] theorem conformalMap_norm (q : S2 × ℝ) : ‖conformalMap q‖ = conformalRadius q.2 := by
  simp only [conformalMap, norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere,
    mul_one, abs_of_pos (conformalRadius_pos q.2)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap_norm ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap_norm

theorem conformalMap_ne_zero (q : S2 × ℝ) : conformalMap q ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [conformalMap_norm]
  exact (conformalRadius_pos q.2).ne'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap_ne_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap_ne_zero

private def conformalInverse (x : puncturedSpace) : S2 × ℝ :=
  (((euclideanPolarDiffeomorph (n := 2)).symm (x : E3)).1, conformalCoordinate ‖(x : E3)‖)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalInverse
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalInverse target :: scope.openDecls } }

private theorem conformalInverse_smooth :
    ContMDiff (𝓡 3) ((𝓡 2).prod 𝓘(ℝ)) ∞ conformalInverse := by
  have hp : ContMDiff (𝓡 3) ((𝓡 2).prod 𝓘(ℝ)) ∞
      (fun x : puncturedSpace => (euclideanPolarDiffeomorph (n := 2)).symm (x : E3)) := by
    intro x
    apply (contMDiffAt_subtype_iff (U := puncturedSpace)).mpr
    exact (euclideanPolarDiffeomorph (n := 2)).symm.contMDiffOn_toFun.contMDiffAt
      (isOpen_compl_singleton.mem_nhds x.property)
  have hn : ContMDiff (𝓡 3) 𝓘(ℝ) ∞ (fun x : puncturedSpace => ‖(x : E3)‖) := by
    intro x
    apply (contMDiffAt_subtype_iff (U := puncturedSpace)).mpr
    exact (contDiffAt_norm ℝ x.property).contMDiffAt
  have hz : ContMDiff (𝓡 3) 𝓘(ℝ) ∞
      (fun x : puncturedSpace => conformalCoordinate ‖(x : E3)‖) := by
    intro x
    have hzAt : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ conformalCoordinate ‖(x : E3)‖ :=
      (contDiffOn_conformalCoordinate.contDiffAt
        (isOpen_Ioi.mem_nhds (norm_pos_iff.mpr x.property))).contMDiffAt
    have hcomp := hzAt.comp (f := fun y : puncturedSpace => ‖(y : E3)‖)
      (g := conformalCoordinate) x (hn x)
    exact hcomp
  exact hp.fst.prodMk hz

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalInverse_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalInverse_smooth target :: scope.openDecls } }

private theorem conformalInverse_left (q : S2 × ℝ) :
    conformalInverse ⟨conformalMap q, conformalMap_ne_zero q⟩ = q := by
  have hp := (euclideanPolarDiffeomorph (n := 2)).left_inv'
    (show (q.1, conformalRadius q.2) ∈ (euclideanPolarDiffeomorph (n := 2)).source
      from conformalRadius_pos q.2)
  apply Prod.ext
  · change (((euclideanPolarDiffeomorph (n := 2)).symm (conformalMap q)).1) = q.1
    have hfst := congrArg (fun p : S2 × ℝ => p.1) hp
    exact hfst
  · change conformalCoordinate ‖conformalMap q‖ = q.2
    rw [conformalMap_norm, conformalCoordinate_conformalRadius]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalInverse_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalInverse_left target :: scope.openDecls } }

private theorem conformalInverse_right (x : puncturedSpace) :
    conformalMap (conformalInverse x) = (x : E3) := by
  change conformalRadius (conformalCoordinate ‖(x : E3)‖) •
    (((euclideanPolarDiffeomorph (n := 2)).symm (x : E3)).1 : E3) = (x : E3)
  rw [conformalRadius_conformalCoordinate (norm_pos_iff.mpr x.property)]
  have hp := (euclideanPolarDiffeomorph (n := 2)).right_inv' x.property
  change euclideanPolarMap ((euclideanPolarDiffeomorph (n := 2)).symm (x : E3)) = (x : E3) at hp
  simpa only [euclideanPolarMap, euclideanPolarDiffeomorph_symm_snd x.property] using hp

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalInverse_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalInverse_right target :: scope.openDecls } }

def conformalChart : (S2 × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), 𝓡 3⟯ puncturedSpace where
  toFun q := ⟨conformalMap q, conformalMap_ne_zero q⟩
  invFun := conformalInverse
  left_inv := conformalInverse_left
  right_inv x := Subtype.ext (conformalInverse_right x)
  contMDiff_toFun _ := codRestr_contMDiffAt
    (fun y => conformalMap_ne_zero y) conformalMap_smooth.contMDiffAt
  contMDiff_invFun := conformalInverse_smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart

@[simp] theorem conformalChart_apply (q : S2 × ℝ) :
    (conformalChart q : E3) = conformalMap q := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_apply

theorem conformalChart_symm_fst_val (x : puncturedSpace) :
    ((conformalChart.symm x).1 : E3) = ‖(x : E3)‖⁻¹ • (x : E3) :=
  euclideanPolarDiffeomorph_symm_fst_val x.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_symm_fst_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_symm_fst_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_symm_fst_val ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_symm_fst_val

@[simp] theorem conformalChart_symm_snd (x : puncturedSpace) :
    (conformalChart.symm x).2 = conformalCoordinate ‖(x : E3)‖ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_symm_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_symm_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_symm_snd ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_symm_snd

theorem conformalChart_norm (q : S2 × ℝ) : ‖(conformalChart q : E3)‖ = conformalRadius q.2 :=
  conformalMap_norm q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_norm ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_norm

theorem conformalChart_cylindrical (q : S2 × ℝ) (hq : 0 ≤ q.2) :
    (conformalChart q : E3) = (transitionEnd + q.2) • (q.1 : E3) := by
  rw [conformalChart_apply, conformalMap, conformalRadius_cylindrical hq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_cylindrical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_cylindrical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_cylindrical ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_cylindrical

private theorem mfderiv_conformalRadius (z t : ℝ) :
    mfderiv 𝓘(ℝ) 𝓘(ℝ) conformalRadius z t =
      (warpingFunction (conformalRadius z) / Real.sqrt 2) * t := by
  rw [mfderiv_eq_fderiv]
  change fderiv ℝ conformalRadius z t = _
  rw [(hasDerivAt_conformalRadius z).hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.mfderiv_conformalRadius
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.mfderiv_conformalRadius target :: scope.openDecls } }

private theorem mfderiv_sphere_projection (q : S2 × ℝ)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    mvfderiv ((𝓡 2).prod 𝓘(ℝ)) (fun p : S2 × ℝ => (p.1 : E3)) q v =
      dIncl q.1 v.1 := by
  have hcomp := mfderiv_comp (I := ((𝓡 2).prod 𝓘(ℝ))) (I' := 𝓡 2)
    (I'' := 𝓡 3) q
    ((contMDiff_coe_sphere (n := 2)).contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)) mdifferentiableAt_fst
  have h := congrArg (fun D => D v) hcomp
  rw [mfderiv_fst] at h
  with_unfolding_all exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.mfderiv_sphere_projection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.mfderiv_sphere_projection target :: scope.openDecls } }

private theorem mfderiv_conformal_radius_projection (q : S2 × ℝ)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    mvfderiv ((𝓡 2).prod 𝓘(ℝ)) (fun p : S2 × ℝ => conformalRadius p.2) q v =
      (warpingFunction (conformalRadius q.2) / Real.sqrt 2) * v.2 := by
  have hcomp := mfderiv_comp (I := ((𝓡 2).prod 𝓘(ℝ))) (I' := 𝓘(ℝ))
    (I'' := 𝓘(ℝ)) q
    (contDiff_conformalRadius.contMDiff.contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)) mdifferentiableAt_snd
  have h := congrArg (fun D => D v) hcomp
  rw [mfderiv_snd] at h
  have h' :
      mfderiv ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) (fun p : S2 × ℝ => conformalRadius p.2) q v =
        mfderiv 𝓘(ℝ) 𝓘(ℝ) conformalRadius q.2 v.2 := by
    with_unfolding_all exact h
  exact h'.trans (mfderiv_conformalRadius q.2 v.2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.mfderiv_conformal_radius_projection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.mfderiv_conformal_radius_projection target :: scope.openDecls } }

private theorem mfderiv_conformalMap_decomposition (q : S2 × ℝ)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    mvfderiv ((𝓡 2).prod 𝓘(ℝ)) conformalMap q v =
      mvfderiv ((𝓡 2).prod 𝓘(ℝ))
          (fun p : S2 × ℝ => conformalRadius p.2) q v • (q.1 : E3) +
        conformalRadius q.2 •
          mvfderiv ((𝓡 2).prod 𝓘(ℝ))
            (fun p : S2 × ℝ => (p.1 : E3)) q v := by
  let f : S2 × ℝ → ℝ := fun q => conformalRadius q.2
  let g : S2 × ℝ → E3 := fun q => (q.1 : E3)
  have hf : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) f q :=
    (contDiff_conformalRadius.contMDiff.comp contMDiff_snd).contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hg : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) g q :=
    ((contMDiff_coe_sphere (n := 2)).comp contMDiff_fst).contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  calc
    mvfderiv ((𝓡 2).prod 𝓘(ℝ)) conformalMap q v =
        mvfderiv ((𝓡 2).prod 𝓘(ℝ)) (f • g) q v := by
      rw [show conformalMap = f • g by rfl]
    _ = f q • mvfderiv ((𝓡 2).prod 𝓘(ℝ)) g q v +
        mvfderiv ((𝓡 2).prod 𝓘(ℝ)) f q v • g q := by
      rw [mvfderiv_smul hf hg]
      simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    _ = _ := by
      simp only [f, g, add_comm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.mfderiv_conformalMap_decomposition
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.mfderiv_conformalMap_decomposition target :: scope.openDecls } }

theorem conformalMap_mfderiv (q : S2 × ℝ)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalMap q v =
      ((warpingFunction (conformalRadius q.2) / Real.sqrt 2) * v.2) • (q.1 : E3) +
        conformalRadius q.2 • dIncl q.1 v.1 := by
  change mvfderiv ((𝓡 2).prod 𝓘(ℝ)) conformalMap q v = _
  rw [mfderiv_conformalMap_decomposition,
    mfderiv_conformal_radius_projection, mfderiv_sphere_projection]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap_mfderiv ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalMap_mfderiv

theorem conformalChart_mfderiv_eq_ambient (q : S2 × ℝ)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalChart q v =
      mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalMap q v := by
  have h := congrArg (fun D => D v) (mfderiv_comp q
    ((contMDiff_subtype_val (I := 𝓡 3) (U := puncturedSpace)).mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0)
      (conformalChart q)) (conformalChart.contMDiff.mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0) q))
  change mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalMap q v =
    mfderiv (𝓡 3) (𝓡 3) (Subtype.val : puncturedSpace → E3) (conformalChart q)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalChart q v) at h
  rw [mfderiv_subtype_val_apply] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_mfderiv_eq_ambient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_mfderiv_eq_ambient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_mfderiv_eq_ambient ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_mfderiv_eq_ambient

theorem conformalChart_mfderiv (q : S2 × ℝ)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalChart q v =
      ((warpingFunction (conformalRadius q.2) / Real.sqrt 2) * v.2) • (q.1 : E3) +
        conformalRadius q.2 • dIncl q.1 v.1 :=
  (conformalChart_mfderiv_eq_ambient q v).trans (conformalMap_mfderiv q v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_mfderiv ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_mfderiv

theorem conformalChart_metric_inner (q : S2 × ℝ)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    metric.inner (conformalChart q : E3)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalChart q v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalChart q w) =
      (warpingFunction (conformalRadius q.2) / Real.sqrt 2) ^ 2 *
        (roundCylinderMetric (E := E3) (n := 2)).inner q v w := by
  rw [conformalChart_apply, conformalMap, conformalChart_mfderiv, conformalChart_mfderiv,
    metric_inner_polar (norm_eq_of_mem_sphere q.1)
      (dIncl_orth q.1 v.1) (dIncl_orth q.1 w.1) (conformalRadius_pos q.2),
    roundCylinderMetric_inner]
  have hscale : 2 * (warpingFunction (conformalRadius q.2) / Real.sqrt 2) ^ 2 =
      warpingFunction (conformalRadius q.2) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [← hscale]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_metric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_metric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_metric_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_metric_inner

theorem conformalChart_metric_inner_exp (q : S2 × ℝ)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    metric.inner (conformalChart q : E3)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalChart q v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalChart q w) =
      Real.exp (2 * conformalFactor q.2) *
        (roundCylinderMetric (E := E3) (n := 2)).inner q v w := by
  rw [conformalChart_metric_inner, exp_two_conformalFactor]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_metric_inner_exp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_metric_inner_exp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_metric_inner_exp ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_metric_inner_exp

theorem conformalChart_metric_inner_cylindrical (q : S2 × ℝ) (hq : 0 ≤ q.2)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    metric.inner (conformalChart q : E3)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalChart q v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalChart q w) =
      (roundCylinderMetric (E := E3) (n := 2)).inner q v w := by
  rw [conformalChart_metric_inner, conformalRadius_cylindrical hq,
    warpingFunction_eq_sqrt_two (by linarith)]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  simp only [div_self hs, one_pow, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_metric_inner_cylindrical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_metric_inner_cylindrical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_metric_inner_cylindrical ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_metric_inner_cylindrical

theorem conformalChart_linearIsometryEquiv (f : E3 ≃ₗᵢ[ℝ] E3) (q : S2 × ℝ) :
    (conformalChart (⟨f (q.1 : E3), by
      simpa only [Metric.mem_sphere, dist_zero_right] using
        (f.norm_map (q.1 : E3)).trans (norm_eq_of_mem_sphere q.1)⟩, q.2) : E3) =
      f (conformalChart q : E3) :=
  (f.map_smul (conformalRadius q.2) (q.1 : E3)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_linearIsometryEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_linearIsometryEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_linearIsometryEquiv ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalChart_linearIsometryEquiv

end DifferentialGeometry.PDE.RicciFlow.StandardCap
