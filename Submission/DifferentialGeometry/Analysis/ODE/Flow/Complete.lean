import Submission.DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.CompactTrajectory

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Filter _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

noncomputable def curveAtDiffeomorph [FiniteDimensional ℝ E] [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I I.tangent ∞
      (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (t : ℝ) : Diffeomorph I I M M ∞ := by
  have hv1 : CMDiff 1 (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have hsmooth (s : ℝ) :
      ContMDiff I I ∞ (fun x : M ↦ curveAt v hcomplete x s) := by
    have hpair : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞
        (fun x : M ↦ (s, x)) :=
      contMDiff_const.prodMk contMDiff_id
    simpa [Function.comp_def] using
      (contMDiff_curveAt v hv hcomplete).comp hpair
  exact
    { toEquiv :=
        { toFun := fun x ↦ curveAt v hcomplete x t
          invFun := fun x ↦ curveAt v hcomplete x (-t)
          left_inv := by
            intro x
            have h := curveAt_add v hv1 hcomplete x t (-t)
            simpa only [add_neg_cancel, curveAt_zero] using h.symm
          right_inv := by
            intro x
            have h := curveAt_add v hv1 hcomplete x (-t) t
            simpa only [neg_add_cancel, curveAt_zero] using h.symm }
      contMDiff_toFun := hsmooth t
      contMDiff_invFun := hsmooth (-t) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph ``Submission.DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph

section Diffeomorph

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  (v : (x : M) → TangentSpace I x)
  (hv : ContMDiff I I.tangent ∞
    (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)))
  (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)

@[simp]
theorem curveAtDiffeomorph_apply (t : ℝ) (x : M) :
    curveAtDiffeomorph v hv hcomplete t x = curveAt v hcomplete x t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph_apply ``Submission.DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph_apply

@[simp]
theorem curveAtDiffeomorph_symm (t : ℝ) :
    (curveAtDiffeomorph v hv hcomplete t).symm =
      curveAtDiffeomorph v hv hcomplete (-t) := by
  ext x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph_symm ``Submission.DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph_symm

@[simp]
theorem curveAtDiffeomorph_zero :
    curveAtDiffeomorph v hv hcomplete 0 = Diffeomorph.refl I M ∞ := by
  ext x
  exact curveAt_zero v hcomplete x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph_zero ``Submission.DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph_zero

theorem curveAtDiffeomorph_add (s t : ℝ) :
    curveAtDiffeomorph v hv hcomplete (s + t) =
      (curveAtDiffeomorph v hv hcomplete s).trans
        (curveAtDiffeomorph v hv hcomplete t) := by
  ext x
  exact curveAt_add v (hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞))
    hcomplete x s t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph_add ``Submission.DifferentialGeometry.Analysis.ODE.curveAtDiffeomorph_add

end Diffeomorph

end DifferentialGeometry.Analysis.ODE
