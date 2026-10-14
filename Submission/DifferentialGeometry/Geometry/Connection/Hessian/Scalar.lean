import Submission.DifferentialGeometry.Geometry.Connection.Trivial.AlongCurve
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.AlongCurve
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Differentiability.Tensor
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace CovariantDerivative
open _root_.CovariantDerivative

open _root_.Submission.DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

open _root_.CovariantDerivative in
theorem hessian_trivial_eq_cotangentCov
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x) :
    (trivial I M ℝ).hessian cov f x = cotangentCov cov (mvfderiv I f) x := by
  have hσ : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) 2 (T% f) x :=
    (_root_.Bundle.contMDiffAt_section (F := ℝ) (E := Bundle.Trivial M ℝ) x).mpr hf
  have hcov : _root_.CovariantDerivative.ContMDiffCovariantDerivative (trivial I M ℝ) ∞ := inferInstance
  have hD := (hcov.contMDiffAt (m := 1) hσ (by norm_num)).mdifferentiableAt (by simp)
  ext v w
  let W := FiberBundle.extend E w
  have hW : MDiffAt (T% W) x := FiberBundle.mdifferentiableAt_extend ..
  have hWx : W x = w := by simp [W]
  have h := (trivial I M ℝ).hessian_apply cov hD hW v
  have hp := cotangentCov_dualPairing cov hD hW v
  simp only [trivial_apply, hWx] at h hp
  exact h.trans (sub_eq_of_eq_add hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.hessian_trivial_eq_cotangentCov then
    throwError "Refusing to shadow existing declaration CovariantDerivative.hessian_trivial_eq_cotangentCov"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.hessian_trivial_eq_cotangentCov ``Submission.CovariantDerivative.hessian_trivial_eq_cotangentCov

end CovariantDerivative

namespace DifferentialGeometry.Geometry.Connection

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem abstractHessian_apply_velocity_of_hasGeodesicEquationAt
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {γ : ℝ → M} {t : ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f (γ t))
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t)
    (hint : I.IsInteriorPoint (γ t)) (hgeo : HasGeodesicEquationAt g γ t) :
    let v := mfderiv 𝓘(ℝ, ℝ) I γ t ((NormedSpace.fromTangentSpace t).symm 1)
    abstractHessian g f (γ t) v v = iteratedDeriv 2 (f ∘ γ) t := by
  have hσ : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) 2 (T% f) (γ t) :=
    (_root_.Bundle.contMDiffAt_section (F := ℝ) (E := Bundle.Trivial M ℝ) (γ t)).mpr hf
  have hcov : CovariantDerivative.ContMDiffCovariantDerivative (CovariantDerivative.trivial I M ℝ) ∞ := inferInstance
  have h := (CovariantDerivative.trivial I M ℝ).hessian_apply_velocity_of_hasGeodesicEquationAt
    hcov g (J := Set.univ) Filter.univ_mem hγ hσ hint hgeo
  dsimp only at h ⊢
  rw [mfderivWithin_univ, CovariantDerivative.hessian_trivial_eq_cotangentCov _ hf,
    CovariantDerivative.derivAlongWithin_trivial] at h
  simp only [CovariantDerivative.derivAlongWithin_trivial, derivWithin_univ] at h
  exact h.trans (by rw [iteratedDeriv_succ, iteratedDeriv_one]; rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.abstractHessian_apply_velocity_of_hasGeodesicEquationAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.abstractHessian_apply_velocity_of_hasGeodesicEquationAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.abstractHessian_apply_velocity_of_hasGeodesicEquationAt ``Submission.DifferentialGeometry.Geometry.Connection.abstractHessian_apply_velocity_of_hasGeodesicEquationAt

omit [T2Space M] in
theorem abstractHessian_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) {f h : M → ℝ} {x : M}
    (heq : f =ᶠ[𝓝 x] h) :
    abstractHessian g f x = abstractHessian g h x := by
  have hdeq : ∀ᶠ y in 𝓝 x, mvfderiv I f y = mvfderiv I h y := by
    filter_upwards [heq.eventuallyEq_nhds] with y hy
    unfold mvfderiv
    rw [hy.mfderiv_eq, hy.eq_of_nhds]
  have htotal : (fun y => (⟨y, mvfderiv I f y⟩ : _root_.Bundle.TotalSpace (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ))) =ᶠ[𝓝 x]
      (fun y => (⟨y, mvfderiv I h y⟩ : _root_.Bundle.TotalSpace (E →L[ℝ] ℝ)
        (fun y => TangentSpace I y →L[ℝ] ℝ))) := by
    filter_upwards [hdeq] with y hy
    rw [hy]
  by_cases hdf : MDiffAtCotangent (mvfderiv I f) x
  · have hdh : MDiffAtCotangent (mvfderiv I h) x :=
      hdf.congr_of_eventuallyEq htotal.symm
    exact (cotangentCov (LeviCivita g)).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hdf hdh Filter.univ_mem hdeq
  · have hdh : ¬MDiffAtCotangent (mvfderiv I h) x :=
      fun hh => hdf (hh.congr_of_eventuallyEq htotal)
    change cotangentCovAt (LeviCivita g) (mvfderiv I f) x =
      cotangentCovAt (LeviCivita g) (mvfderiv I h) x
    rw [cotangentCovAt_of_not_diff _ hdf, cotangentCovAt_of_not_diff _ hdh]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.abstractHessian_congr_of_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.abstractHessian_congr_of_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.abstractHessian_congr_of_eventuallyEq ``Submission.DifferentialGeometry.Geometry.Connection.abstractHessian_congr_of_eventuallyEq

end DifferentialGeometry.Geometry.Connection
