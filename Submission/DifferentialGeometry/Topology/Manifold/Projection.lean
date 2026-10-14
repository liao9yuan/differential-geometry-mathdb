import Submission.DifferentialGeometry.Topology.Manifold.InverseFunction
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Function
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E F V H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]

theorem isLocalDiffeomorphAt_fst_of_mfderiv_snd_eq_zero
    {f : M → F × V} (hf : ContMDiff I 𝓘(ℝ, F × V) ∞ f) {x : M}
    (hinj : _root_.Function.Injective (mfderiv I 𝓘(ℝ, F × V) f x))
    (hzero : mfderiv I 𝓘(ℝ, V) (fun y => (f y).2) x = 0)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    IsLocalDiffeomorphAt I 𝓘(ℝ, F) ∞ (fun y => (f y).1) x := by
  let p : M → F := fun y => (f y).1
  have hp : ContMDiff I 𝓘(ℝ, F) ∞ p := contDiff_fst.contMDiff.comp hf
  let D : E →L[ℝ] F × V := mfderiv I 𝓘(ℝ, F × V) f x
  have hfst : mfderiv I 𝓘(ℝ, F) p x = (ContinuousLinearMap.fst ℝ F V).comp D := by
    change mfderiv I 𝓘(ℝ, F) ((ContinuousLinearMap.fst ℝ F V) ∘ f) x = _
    rw [mfderiv_comp x (ContinuousLinearMap.fst ℝ F V).mdifferentiableAt
      (hf.mdifferentiableAt (by simp))]
    have hproj : mfderiv 𝓘(ℝ, F × V) 𝓘(ℝ, F) (ContinuousLinearMap.fst ℝ F V) (f x) =
        ContinuousLinearMap.fst ℝ F V :=
      (ContinuousLinearMap.fst ℝ F V).hasMFDerivAt.mfderiv
    rw [hproj]
    rfl
  have hsnd : (ContinuousLinearMap.snd ℝ F V).comp D = 0 := by
    have hh : mfderiv I 𝓘(ℝ, V) (fun y => (f y).2) x =
        (ContinuousLinearMap.snd ℝ F V).comp D := by
      change mfderiv I 𝓘(ℝ, V) ((ContinuousLinearMap.snd ℝ F V) ∘ f) x = _
      rw [mfderiv_comp x (ContinuousLinearMap.snd ℝ F V).mdifferentiableAt
        (hf.mdifferentiableAt (by simp))]
      have hproj : mfderiv 𝓘(ℝ, F × V) 𝓘(ℝ, V) (ContinuousLinearMap.snd ℝ F V) (f x) =
          ContinuousLinearMap.snd ℝ F V :=
        (ContinuousLinearMap.snd ℝ F V).hasMFDerivAt.mfderiv
      rw [hproj]
      rfl
    exact hh.symm.trans hzero
  have hp_inj : _root_.Function.Injective (mfderiv I 𝓘(ℝ, F) p x) := by
    intro u v huv
    apply hinj
    apply Prod.ext
    · have hh := huv
      rw [hfst] at hh
      exact hh
    · have h := congrArg (fun A : E →L[ℝ] V => A u) hsnd
      have h' := congrArg (fun A : E →L[ℝ] V => A v) hsnd
      exact h.trans h'.symm
  let P : E →L[ℝ] F := mfderiv I 𝓘(ℝ, F) p x
  let A : E ≃L[ℝ] F :=
    (P.toLinearMap.linearEquivOfInjective hp_inj hdim).toContinuousLinearEquiv
  exact isLocalDiffeomorphAt_of_hasMFDerivAt_equiv p hp x A
    ((hp.mdifferentiableAt (by simp)).hasMFDerivAt)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_fst_of_mfderiv_snd_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_fst_of_mfderiv_snd_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_fst_of_mfderiv_snd_eq_zero ``Submission.DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_fst_of_mfderiv_snd_eq_zero

end DifferentialGeometry.Topology.Manifold
