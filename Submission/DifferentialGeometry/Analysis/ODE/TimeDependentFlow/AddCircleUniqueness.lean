import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.ForwardIntegralCurveUniqueness
import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import Submission.DifferentialGeometry.Topology.Manifold.AddCircle.PeriodicExtension
import Submission.DifferentialGeometry.Topology.Manifold.AddCircle.VectorField
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace AddCircle
open _root_.AddCircle

open _root_.AddCircle in
private theorem hasMFDerivWithinAt_of_local_lift
    {J : Set ℝ} {t b : ℝ} {l : ℝ → ℝ} {γ : ℝ → AddCircle (1 : ℝ)}
    (ht : t ∈ J) (hl : HasDerivWithinAt l b J t)
    (heq : (fun s => (l s : AddCircle (1 : ℝ))) =ᶠ[𝓝[J] t] γ) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) γ J t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (b • parameterTangent (γ t))) := by
  have heqt := heq.eq_of_nhdsWithin ht
  have hq := (contMDiff_coe.mdifferentiableAt (x := l t)
    (by decide : (∞ : ℕ∞ω) ≠ 0)).hasMFDerivAt
  have hcomp := hq.comp_hasMFDerivWithinAt t hl.hasFDerivWithinAt.hasMFDerivWithinAt
  have hval : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun x : ℝ => (x : AddCircle (1 : ℝ))) (l t) b =
      b • parameterTangent (γ t) := by
    rw [← heqt, parameterTangent_coe]
    let L : ℝ →L[ℝ] ℝ := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun x : ℝ => (x : AddCircle (1 : ℝ))) (l t)
    change L b = b • L 1
    simpa only [smul_eq_mul, mul_one] using L.map_smul b (1 : ℝ)
  have hcomp' : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun s => (l s : AddCircle (1 : ℝ))) J t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (b • parameterTangent (γ t))) := by
    refine hcomp.congr_mfderiv ?_
    apply ContinuousLinearMap.ext
    intro r
    change ℝ at r
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun x : ℝ => (x : AddCircle (1 : ℝ))) (l t) (r • b) =
      r • (b • parameterTangent (γ t))
    erw [map_smul, hval]
    rfl
  exact hcomp'.congr_of_eventuallyEq heq.symm heqt.symm

run_cmd do
  let target := ``Submission.AddCircle.hasMFDerivWithinAt_of_local_lift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.hasMFDerivWithinAt_of_local_lift target :: scope.openDecls } }

open _root_.AddCircle in
theorem eqOn_of_periodic_ode {a b : ℝ} {β : ℝ → ℝ → ℝ}
    (hβ : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => β p.1 p.2)
      (_root_.Set.Icc a b ×ˢ (_root_.Set.univ : Set ℝ)))
    (hper : ∀ t ∈ _root_.Set.Icc a b, Function.Periodic (β t) 1)
    {γ η : ℝ → AddCircle (1 : ℝ)}
    (hγ : ∀ t ∈ _root_.Set.Icc a b, ∃ l : ℝ → ℝ,
      (fun s => (l s : AddCircle (1 : ℝ))) =ᶠ[𝓝[_root_.Set.Icc a b] t] γ ∧
      HasDerivWithinAt l (β t (l t)) (_root_.Set.Icc a b) t)
    (hη : ∀ t ∈ _root_.Set.Icc a b, ∃ l : ℝ → ℝ,
      (fun s => (l s : AddCircle (1 : ℝ))) =ᶠ[𝓝[_root_.Set.Icc a b] t] η ∧
      HasDerivWithinAt l (β t (l t)) (_root_.Set.Icc a b) t)
    (hstart : γ a = η a) : _root_.Set.EqOn γ η (_root_.Set.Icc a b) := by
  obtain ⟨f, hf, hfeq⟩ := exists_contMDiff_extension_of_periodic hβ hper
  let X : ℝ → ∀ z : AddCircle (1 : ℝ), TangentSpace 𝓘(ℝ, ℝ) z :=
    fun t z => f (t, z) • parameterTangent z
  have hX := DifferentialGeometry.Analysis.ODE.autonomizedFieldJointC1_of_contMDiff
    X (contMDiff_parameterTangent_smul hf)
  have hcurve (σ : ℝ → AddCircle (1 : ℝ))
      (hσ : ∀ t ∈ _root_.Set.Icc a b, ∃ l : ℝ → ℝ,
        (fun s => (l s : AddCircle (1 : ℝ))) =ᶠ[𝓝[_root_.Set.Icc a b] t] σ ∧
        HasDerivWithinAt l (β t (l t)) (_root_.Set.Icc a b) t) :
      ∀ t ∈ _root_.Set.Icc a b,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) σ (_root_.Set.Icc a b) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (σ t))) := by
    intro t ht
    obtain ⟨l, hleq, hld⟩ := hσ t ht
    have hval : f (t, σ t) = β t (l t) := by
      rw [← hleq.eq_of_nhdsWithin ht, hfeq t ht]
    simpa only [X, hval] using hasMFDerivWithinAt_of_local_lift ht hld hleq
  exact DifferentialGeometry.Analysis.ODE.forward_integral_curves_eqOn_of_jointC1
    X hX (fun t _ => γ t) (fun t _ => η t) 0 0
    (hcurve γ hγ) (hcurve η hη) hstart

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.eqOn_of_periodic_ode then
    throwError "Refusing to shadow existing declaration AddCircle.eqOn_of_periodic_ode"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.eqOn_of_periodic_ode ``Submission.AddCircle.eqOn_of_periodic_ode

end AddCircle

end
