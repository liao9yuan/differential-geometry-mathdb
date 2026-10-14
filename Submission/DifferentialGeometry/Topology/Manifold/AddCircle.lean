import Submission.DifferentialGeometry.Topology.Manifold.SmoothModelTransport
import Submission.DifferentialGeometry.Topology.Manifold.ChartedSpaceHomeomorph
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Manifold.Instances.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open scoped _root_.Manifold _root_.ContDiff

namespace AddCircle
open _root_.AddCircle

open _root_.AddCircle in
instance instChartedSpaceUnitAddCircle :
    ChartedSpace (EuclideanSpace ℝ (Fin 1)) (AddCircle (1 : ℝ)) :=
  (_root_.AddCircle.homeomorphCircle (T := (1 : ℝ)) (by norm_num)).symm.chartedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.instChartedSpaceUnitAddCircle then
    throwError "Refusing to shadow existing declaration AddCircle.instChartedSpaceUnitAddCircle"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.instChartedSpaceUnitAddCircle ``Submission.AddCircle.instChartedSpaceUnitAddCircle

open _root_.AddCircle in
instance instIsManifoldUnitAddCircle : IsManifold (𝓡 1) ∞ (AddCircle (1 : ℝ)) := by
  have hcirc : IsManifold (𝓡 1) ∞ Circle := IsManifold.of_le (le_top : (∞ : ℕ∞ω) ≤ ω)
  exact DifferentialGeometry.Manifold.isManifold_homeomorphChartedSpace (I := 𝓡 1) (n := ∞)
    (M := Circle) (f := (_root_.AddCircle.homeomorphCircle (T := (1 : ℝ)) (by norm_num)).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.instIsManifoldUnitAddCircle then
    throwError "Refusing to shadow existing declaration AddCircle.instIsManifoldUnitAddCircle"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.instIsManifoldUnitAddCircle ``Submission.AddCircle.instIsManifoldUnitAddCircle

open _root_.AddCircle in
noncomputable def euclideanSpaceFinOneContinuousLinearEquivReal :
    EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.euclideanSpaceFinOneContinuousLinearEquivReal then
    throwError "Refusing to shadow existing declaration AddCircle.euclideanSpaceFinOneContinuousLinearEquivReal"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.euclideanSpaceFinOneContinuousLinearEquivReal ``Submission.AddCircle.euclideanSpaceFinOneContinuousLinearEquivReal

open _root_.AddCircle in
noncomputable def euclideanSpaceFinOneHomeomorphReal : EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ :=
  euclideanSpaceFinOneContinuousLinearEquivReal.toHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.euclideanSpaceFinOneHomeomorphReal then
    throwError "Refusing to shadow existing declaration AddCircle.euclideanSpaceFinOneHomeomorphReal"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.euclideanSpaceFinOneHomeomorphReal ``Submission.AddCircle.euclideanSpaceFinOneHomeomorphReal

open _root_.AddCircle in
instance instChartedSpaceRealUnitAddCircle : ChartedSpace ℝ (AddCircle (1 : ℝ)) :=
  DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph (M := AddCircle (1 : ℝ))
    euclideanSpaceFinOneHomeomorphReal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.instChartedSpaceRealUnitAddCircle then
    throwError "Refusing to shadow existing declaration AddCircle.instChartedSpaceRealUnitAddCircle"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.instChartedSpaceRealUnitAddCircle ``Submission.AddCircle.instChartedSpaceRealUnitAddCircle

open _root_.AddCircle in
instance instIsManifoldRealUnitAddCircle : IsManifold 𝓘(ℝ, ℝ) ∞ (AddCircle (1 : ℝ)) :=
  DifferentialGeometry.Manifold.isManifold_transHomeomorph (I := 𝓡 1) (J := 𝓘(ℝ, ℝ))
    euclideanSpaceFinOneHomeomorphReal euclideanSpaceFinOneContinuousLinearEquivReal
    (fun _ => rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.instIsManifoldRealUnitAddCircle then
    throwError "Refusing to shadow existing declaration AddCircle.instIsManifoldRealUnitAddCircle"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.instIsManifoldRealUnitAddCircle ``Submission.AddCircle.instIsManifoldRealUnitAddCircle


open _root_.AddCircle in
private lemma homeomorphCircle_coe (t : ℝ) :
    homeomorphCircle (T := (1 : ℝ)) one_ne_zero (t : AddCircle (1 : ℝ))
      = Circle.exp (2 * Real.pi * t) := by
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  congr 1
  ring

run_cmd do
  let target := ``Submission.AddCircle.homeomorphCircle_coe
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.homeomorphCircle_coe target :: scope.openDecls } }

open _root_.AddCircle in
theorem contMDiff_coe :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => (t : AddCircle (1 : ℝ))) := by
  have hGt : ∀ t : ℝ,
      homeomorphCircle (T := (1 : ℝ)) one_ne_zero (t : AddCircle (1 : ℝ))
        = Circle.exp (2 * Real.pi * t) := fun t => homeomorphCircle_coe t
  have hf : ContMDiff (𝓡 1) (𝓡 1) ∞
      ((_root_.AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm : Circle → AddCircle (1 : ℝ)) :=
    DifferentialGeometry.Manifold.contMDiff_homeomorphChartedSpace (𝓡 1)
      (_root_.AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
  have hcomp : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞
      ((_root_.AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
        ∘ fun t : ℝ => Circle.exp (2 * Real.pi * t)) :=
    hf.comp (contMDiff_circleExp.comp (contDiff_const.mul contDiff_id).contMDiff)
  have heq : ((_root_.AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
        ∘ fun t : ℝ => Circle.exp (2 * Real.pi * t))
      = fun t : ℝ => (t : AddCircle (1 : ℝ)) := by
    funext t
    rw [Function.comp_apply, ← hGt t, Homeomorph.symm_apply_apply]
  have hsphere : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ (fun t : ℝ => (t : AddCircle (1 : ℝ))) :=
    hcomp.congr fun t => (congrFun heq t).symm
  exact (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_iff
    (I := 𝓡 1) (J := 𝓘(ℝ, ℝ)) euclideanSpaceFinOneHomeomorphReal
    euclideanSpaceFinOneContinuousLinearEquivReal (fun _ => rfl) (I₀ := 𝓘(ℝ, ℝ))).mpr hsphere

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.contMDiff_coe then
    throwError "Refusing to shadow existing declaration AddCircle.contMDiff_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.contMDiff_coe ``Submission.AddCircle.contMDiff_coe

open _root_.AddCircle in
private lemma bijective_mfderiv_circleExp [Fact (Module.finrank ℝ ℂ = 1 + 1)] (t : ℝ) :
    Function.Bijective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1)
      (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1)) t) := by
  set w : Metric.sphere (0 : ℂ) 1 := Circle.exp (2 * Real.pi * t) with hw
  set A := mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Metric.sphere (0 : ℂ) 1 => (z : ℂ)) w with hA
  set B := mfderiv 𝓘(ℝ, ℝ) (𝓡 1)
    (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1)) t with hB
  set c : ℂ := Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) * (((2 * Real.pi : ℝ) : ℂ) * Complex.I) with hcdef
  have hderiv : HasDerivAt (fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)) c t := by
    rw [hcdef]
    have hR : HasDerivAt (fun s : ℝ => 2 * Real.pi * s) (2 * Real.pi) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)
    exact ((hR.ofReal_comp).mul_const Complex.I).cexp
  have hc : c ≠ 0 := by
    rw [hcdef]
    exact mul_ne_zero (Complex.exp_ne_zero _)
      (mul_ne_zero (by exact_mod_cast (by positivity : (2 : ℝ) * Real.pi ≠ 0)) Complex.I_ne_zero)
  have hCval : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      (fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)) t
      = ContinuousLinearMap.toSpanSingleton ℝ c := by
    rw [mfderiv_eq_fderiv, hderiv.hasFDerivAt.fderiv]
  have hspan : Function.Injective (ContinuousLinearMap.toSpanSingleton ℝ c) := by
    intro x y hxy
    rw [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.toSpanSingleton_apply] at hxy
    have h : (x - y) • c = 0 := by rw [sub_smul, hxy, sub_self]
    rcases smul_eq_zero.mp h with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hc
  have hCwide : Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      (fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)) t) := by
    intro x y hxy
    exact hspan (by rw [← hCval]; exact hxy)
  have hclosure : (fun z : Metric.sphere (0 : ℂ) 1 => (z : ℂ)) ∘
      (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1))
      = fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I) := by
    funext s
    rfl
  have hgw : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Metric.sphere (0 : ℂ) 1 => (z : ℂ)) w :=
    (contMDiff_coe_sphere (E := ℂ) (n := 1) (m := ∞)).mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hft : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1)
      (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1)) t :=
    ((contMDiff_circleExp.comp ((contDiff_const.mul contDiff_id).contMDiff) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞
        (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1)))).mdifferentiableAt
      (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hchain : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      (fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)) t = A.comp B := by
    rw [← hclosure, hA, hB]
    exact mfderiv_comp t hgw hft
  have hBinj : Function.Injective B := fun x y hxy => by
    apply hCwide
    rw [hchain]
    exact congrArg A hxy
  have hfin : Module.finrank ℝ (TangentSpace 𝓘(ℝ, ℝ) t)
      = Module.finrank ℝ (TangentSpace (𝓡 1) w) :=
    (Module.finrank_self ℝ).trans
      ((finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin 1)).trans (Fintype.card_fin 1)).symm
  exact ⟨hBinj, (@LinearMap.injective_iff_surjective_of_finrank_eq_finrank ℝ
    (TangentSpace 𝓘(ℝ, ℝ) t) _ _ _ (TangentSpace (𝓡 1) w) _ _
    (inferInstanceAs (FiniteDimensional ℝ ℝ))
    (inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 1))))
    hfin (f := B.toLinearMap)).mp hBinj⟩

run_cmd do
  let target := ``Submission.AddCircle.bijective_mfderiv_circleExp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.bijective_mfderiv_circleExp target :: scope.openDecls } }

open _root_.AddCircle in
theorem bijective_mfderiv_coe (t : ℝ) :
    Function.Bijective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun s : ℝ => (s : AddCircle (1 : ℝ))) t) := by
  let _ := (Complex.finrank_real_complex_fact : Fact (Module.finrank ℝ ℂ = 1 + 1))
  let G : AddCircle (1 : ℝ) ≃ₜ Circle := _root_.AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have hGt : ∀ s : ℝ, G (s : AddCircle (1 : ℝ)) = Circle.exp (2 * Real.pi * s) :=
    fun s => homeomorphCircle_coe s
  have hB : Function.Bijective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1)
      (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1)) t) :=
    bijective_mfderiv_circleExp t
  have hGs : Function.Bijective (mfderiv (𝓡 1) (𝓡 1)
      (G.symm : Circle → AddCircle (1 : ℝ)) (Circle.exp (2 * Real.pi * t))) :=
    DifferentialGeometry.Manifold.bijective_mfderiv_homeomorphChartedSpace (𝓡 1) G.symm _
  have hfun : (G.symm : Circle → AddCircle (1 : ℝ)) ∘
      (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1))
      = fun s : ℝ => (s : AddCircle (1 : ℝ)) := by
    funext s
    rw [Function.comp_apply, ← hGt s]
    exact Homeomorph.symm_apply_apply G (s : AddCircle (1 : ℝ))
  have hg : MDifferentiableAt (𝓡 1) (𝓡 1)
      (G.symm : Circle → AddCircle (1 : ℝ)) (Circle.exp (2 * Real.pi * t)) :=
    (DifferentialGeometry.Manifold.contMDiff_homeomorphChartedSpace (𝓡 1) G.symm).mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1)
      (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1)) t :=
    ((contMDiff_circleExp.comp ((contDiff_const.mul contDiff_id).contMDiff) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞
        (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1)))).mdifferentiableAt
      (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hX : Function.Bijective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1)
      (fun s : ℝ => (s : AddCircle (1 : ℝ))) t) := by
    rw [← hfun, mfderiv_comp t hg hf]
    exact hGs.comp hB
  exact (DifferentialGeometry.Manifold.bijective_mfderiv_chartedSpaceTransHomeomorph_iff
    (I := 𝓡 1) (J := 𝓘(ℝ, ℝ)) euclideanSpaceFinOneHomeomorphReal
    euclideanSpaceFinOneContinuousLinearEquivReal (fun _ => rfl) (I₀ := 𝓘(ℝ, ℝ))
    (f := fun s : ℝ => (s : AddCircle (1 : ℝ))) (x := t)).mpr hX

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.bijective_mfderiv_coe then
    throwError "Refusing to shadow existing declaration AddCircle.bijective_mfderiv_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.bijective_mfderiv_coe ``Submission.AddCircle.bijective_mfderiv_coe

end AddCircle

end
