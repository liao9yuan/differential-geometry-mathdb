import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.Function
open scoped _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Morse
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


theorem fderiv_fderiv_comp_at_critical {f : F → ℝ} {c : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (c x)) (hc : ContDiffAt ℝ 2 c x)
    (hcrit : fderiv ℝ f (c x) = 0) :
    fderiv ℝ (fderiv ℝ (f ∘ c)) x =
      ((ContinuousLinearMap.compL ℝ E F ℝ).flip (fderiv ℝ c x)).comp
        ((fderiv ℝ (fderiv ℝ f) (c x)).comp (fderiv ℝ c x)) := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdc := (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hd := (hdf.hasFDerivAt.comp x (hc.differentiableAt (by norm_num)).hasFDerivAt).clm_comp hdc.hasFDerivAt
  have heq : fderiv ℝ (f ∘ c) =ᶠ[𝓝 x] fun y => (fderiv ℝ f (c y)).comp (fderiv ℝ c y) := by
    filter_upwards [hc.eventually (by norm_num), hc.continuousAt.preimage_mem_nhds
      (hf.eventually (by norm_num))] with y hcy hfy
    have hfy' : ContDiffAt ℝ 2 f (c y) := hfy
    exact fderiv_comp y (hfy'.differentiableAt (by norm_num)) (hcy.differentiableAt (by norm_num))
  rw [heq.fderiv_eq]
  simpa only [_root_.Function.comp_apply,hcrit,map_zero,ContinuousLinearMap.zero_comp,zero_add] using hd.fderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.fderiv_fderiv_comp_at_critical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.fderiv_fderiv_comp_at_critical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.fderiv_fderiv_comp_at_critical ``Submission.DifferentialGeometry.Morse.fderiv_fderiv_comp_at_critical


theorem bijective_dual_precomp (e : E ≃L[ℝ] F) :
    Bijective ((ContinuousLinearMap.compL ℝ E F ℝ).flip e.toContinuousLinearMap) := by
  constructor
  · intro L T h
    apply ContinuousLinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    exact congrArg (fun K : E →L[ℝ] ℝ => K v) h
  · intro L
    refine ⟨L.comp e.symm.toContinuousLinearMap,?_⟩
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg L (e.symm_apply_apply v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.bijective_dual_precomp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.bijective_dual_precomp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.bijective_dual_precomp ``Submission.DifferentialGeometry.Morse.bijective_dual_precomp


theorem bijective_fderiv_fderiv_comp_at_critical_iff {f : F → ℝ} {c : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (c x)) (hc : ContDiffAt ℝ 2 c x)
    (hcrit : fderiv ℝ f (c x) = 0) (hcinv : (fderiv ℝ c x).IsInvertible) :
    _root_.Function.Bijective (fderiv ℝ (fderiv ℝ (f ∘ c)) x) ↔
      Bijective (fderiv ℝ (fderiv ℝ f) (c x)) := by
  obtain ⟨e,he⟩ := hcinv
  have hce : e.toContinuousLinearMap = fderiv ℝ c x := he
  rw [fderiv_fderiv_comp_at_critical hf hc hcrit,← hce]
  change _root_.Function.Bijective (((ContinuousLinearMap.compL ℝ E F ℝ).flip e.toContinuousLinearMap) ∘
    ((fderiv ℝ (fderiv ℝ f) (c x)) ∘ e)) ↔ _
  rw [(bijective_dual_precomp e).of_comp_iff',Bijective.of_comp_iff _ e.bijective]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.bijective_fderiv_fderiv_comp_at_critical_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.bijective_fderiv_fderiv_comp_at_critical_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.bijective_fderiv_fderiv_comp_at_critical_iff ``Submission.DifferentialGeometry.Morse.bijective_fderiv_fderiv_comp_at_critical_iff

end DifferentialGeometry.Morse
