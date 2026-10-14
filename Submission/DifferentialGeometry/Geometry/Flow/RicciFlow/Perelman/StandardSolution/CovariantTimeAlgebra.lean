import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MetricCompatibleTimeDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

theorem ricciTimeCorrection_add {s : ℕ} {x : M} (g : SmoothRiemannianMetric I M)
    (A B : Tensor0SSpace s I x) :
    ricciTimeCorrection g (A + B) = ricciTimeCorrection g A + ricciTimeCorrection g B := by
  apply tensor0SSpace_ext s x
  intro v
  simp only [ricciTimeCorrection_apply, Tensor0SSpace.add_apply, Finset.sum_add_distrib]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciTimeCorrection_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciTimeCorrection_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciTimeCorrection_add ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciTimeCorrection_add

theorem covariantTimeDerivWithin_zero {s : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (t : ℝ) :
    covariantTimeDerivWithin g (fun _ => (0 : Tensor0SSpace s I x)) J t = 0 := by
  have hc : ricciTimeCorrection (g t) (0 : Tensor0SSpace s I x) = 0 := by
    simpa only [zero_smul] using ricciTimeCorrection_smul (g t) (0 : ℝ) (0 : Tensor0SSpace s I x)
  have hd : derivWithin (fun _ => (0 : Tensor0SSpace s I x)) J t = 0 :=
    congrFun (derivWithin_fun_const J (0 : Tensor0SSpace s I x)) t
  exact (congrArg₂ (fun U V : Tensor0SSpace s I x => U + V) hd hc).trans (zero_add _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_zero

theorem covariantTimeDerivWithin_add {s : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M) (A B : ℝ → Tensor0SSpace s I x)
    (J : Set ℝ) (t : ℝ) (hJ : UniqueDiffWithinAt ℝ J t)
    (hA : DifferentiableWithinAt ℝ A J t) (hB : DifferentiableWithinAt ℝ B J t) :
    covariantTimeDerivWithin g (fun r => A r + B r) J t =
      covariantTimeDerivWithin g A J t + covariantTimeDerivWithin g B J t := by
  have hd : derivWithin (fun r => A r + B r) J t = derivWithin A J t + derivWithin B J t :=
    (hA.hasDerivWithinAt.add hB.hasDerivWithinAt).derivWithin hJ
  simp only [covariantTimeDerivWithin, hd, ricciTimeCorrection_add]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_add ``Submission.DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_add

theorem covariantTimeDerivWithin_const_smul {s : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M) (T : ℝ → Tensor0SSpace s I x) (c : ℝ)
    (J : Set ℝ) (t : ℝ) (hJ : UniqueDiffWithinAt ℝ J t)
    (hT : DifferentiableWithinAt ℝ T J t) :
    covariantTimeDerivWithin g (fun r => c • T r) J t =
      c • covariantTimeDerivWithin g T J t := by
  simpa only [zero_smul, zero_add] using
    covariantTimeDerivWithin_smul g T (derivWithin T J t) (fun _ => c) 0 J t hJ
      hT.hasDerivWithinAt (hasDerivWithinAt_const t J c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_const_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_const_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_const_smul ``Submission.DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_const_smul

omit [T2Space M] [BoundarylessManifold I M] in
theorem hasDerivWithinAt_tensor0S_domDomCongr {s s' : ℕ} {x : M}
    (T : ℝ → Tensor0SSpace s I x) (Tdot : Tensor0SSpace s I x)
    (e : Fin s ≃ Fin s') (J : Set ℝ) (t : ℝ)
    (hT : ∀ v : Fin s → TangentSpace I x,
      HasDerivWithinAt (fun r => T r v) (Tdot v) J t) :
    HasDerivWithinAt (fun r => (T r).domDomCongr e) (Tdot.domDomCongr e) J t := by
  apply hasDerivWithinAt_tensor0S_of_eval
  intro v
  simpa only [Tensor0SSpace.domDomCongr_apply] using hT (fun i => v (e i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hasDerivWithinAt_tensor0S_domDomCongr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hasDerivWithinAt_tensor0S_domDomCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hasDerivWithinAt_tensor0S_domDomCongr ``Submission.DifferentialGeometry.PDE.RicciFlow.hasDerivWithinAt_tensor0S_domDomCongr

theorem ricciTimeCorrection_domDomCongr {s s' : ℕ} {x : M}
    (g : SmoothRiemannianMetric I M) (T : Tensor0SSpace s I x) (e : Fin s ≃ Fin s') :
    ricciTimeCorrection g (T.domDomCongr e) = (ricciTimeCorrection g T).domDomCongr e := by
  classical
  apply tensor0SSpace_ext s' x
  intro v
  simp only [ricciTimeCorrection_apply, Tensor0SSpace.domDomCongr_apply]
  calc (∑ b : Fin s', T (fun i => Function.update v b (ricciSharp g x (v b)) (e i)))
      = ∑ a : Fin s, T (fun i => Function.update v (e a) (ricciSharp g x (v (e a))) (e i)) :=
        (e.sum_comp (fun b => T (fun i => Function.update v b (ricciSharp g x (v b)) (e i)))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      exact congrArg T (Function.update_comp_eq_of_injective v e.injective a (ricciSharp g x (v (e a))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciTimeCorrection_domDomCongr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciTimeCorrection_domDomCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciTimeCorrection_domDomCongr ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciTimeCorrection_domDomCongr

theorem covariantTimeDerivWithin_domDomCongr {s s' : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M) (T : ℝ → Tensor0SSpace s I x)
    (Tdot : Tensor0SSpace s I x) (e : Fin s ≃ Fin s')
    (J : Set ℝ) (t : ℝ) (hJ : UniqueDiffWithinAt ℝ J t)
    (hT : ∀ v : Fin s → TangentSpace I x,
      HasDerivWithinAt (fun r => T r v) (Tdot v) J t) :
    covariantTimeDerivWithin g (fun r => (T r).domDomCongr e) J t =
      (covariantTimeDerivWithin g T J t).domDomCongr e := by
  have hd := (hasDerivWithinAt_tensor0S_domDomCongr T Tdot e J t hT).derivWithin hJ
  have he := (hasDerivWithinAt_tensor0S_of_eval T Tdot J t hT).derivWithin hJ
  calc covariantTimeDerivWithin g (fun r => (T r).domDomCongr e) J t
      = Tdot.domDomCongr e + (ricciTimeCorrection (g t) (T t)).domDomCongr e :=
        congrArg₂ (fun U V : Tensor0SSpace s' I x => U + V) hd
          (ricciTimeCorrection_domDomCongr (g t) (T t) e)
    _ = (Tdot + ricciTimeCorrection (g t) (T t)).domDomCongr e := by
      apply tensor0SSpace_ext s' x
      intro v
      simp only [Tensor0SSpace.add_apply, Tensor0SSpace.domDomCongr_apply]
    _ = _ := congrArg (fun U : Tensor0SSpace s I x =>
      (U + ricciTimeCorrection (g t) (T t)).domDomCongr e) he.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_domDomCongr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_domDomCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_domDomCongr ``Submission.DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_domDomCongr
end DifferentialGeometry.PDE.RicciFlow
