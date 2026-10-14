import Submission.DifferentialGeometry.Topology.Morse.RelativePerturbationMorse
import Submission.DifferentialGeometry.Topology.Manifold.MFDeriv.Affine

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Topology.Morse
namespace DifferentialGeometry.Morse
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]


private theorem fderiv_fderiv_const_sub (f : E → ℝ) (b : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (fun y => b - f y)) x = -fderiv ℝ (fderiv ℝ f) x := by
  have heq : fderiv ℝ (fun y => b - f y) = -fderiv ℝ f := funext fun y => fderiv_const_sub b
  rw [heq,fderiv_neg]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Morse.fderiv_fderiv_const_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Morse.fderiv_fderiv_const_sub target :: scope.openDecls } }

theorem chartHessianAt_const_sub (f : E → ℝ) (b : ℝ) (x : E) :
    chartHessianAt (fun y => b - f y) x = -chartHessianAt f x := by
  ext v
  change (fderiv ℝ (fderiv ℝ (fun y => b - f y)) x v) v =
    -((fderiv ℝ (fderiv ℝ f) x v) v)
  rw [fderiv_fderiv_const_sub]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.chartHessianAt_const_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.chartHessianAt_const_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.chartHessianAt_const_sub ``Submission.DifferentialGeometry.Morse.chartHessianAt_const_sub

theorem chartHessianAt_neg (f : E → ℝ) (x : E) :
    chartHessianAt (fun y => -f y) x = -chartHessianAt f x := by
  simpa only [zero_sub] using chartHessianAt_const_sub f 0 x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.chartHessianAt_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.chartHessianAt_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.chartHessianAt_neg ``Submission.DifferentialGeometry.Morse.chartHessianAt_neg

variable {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}


theorem isCriticalPointAt_const_sub_iff {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (b : ℝ) :
    IsCriticalPointAt I (fun y => b - f y) x ↔ IsCriticalPointAt I f x := by
  change (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y => b - f y) x) = 0 ↔
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x) = 0
  rw [DifferentialGeometry.Manifold.mfderiv_const_sub_real hf b,neg_eq_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.isCriticalPointAt_const_sub_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.isCriticalPointAt_const_sub_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.isCriticalPointAt_const_sub_iff ``Submission.DifferentialGeometry.Morse.isCriticalPointAt_const_sub_iff

variable [IsManifold I ∞ M]


theorem isNondegenerateCriticalPointAt_const_sub_iff {f : M → ℝ} {x : M}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hx : I.IsInteriorPoint x) (b : ℝ) :
    IsNondegenerateCriticalPointAt I (fun y => b - f y) x ↔
      IsNondegenerateCriticalPointAt I f x := by
  let c := DifferentialGeometry.Manifold.interiorChart I ∞ x
  let g : E → ℝ := fun z => f (c.symm z)
  have hxc : x ∈ c.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hx
  have hg : ContDiffAt ℝ 2 g (c x) :=
    (((hf.comp_contMDiffOn c.symm.contMDiffOn).contMDiffAt
      (c.open_target.mem_nhds (c.map_source hxc))).contDiffAt).of_le
      (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hbg : ContDiffAt ℝ 2 (fun z => b - g z) (c x) := contDiffAt_const.sub hg
  change (IsCriticalPointAt I (fun y => b - f y) x ∧
      (QuadraticMap.associated (R := ℝ) (chartHessianAt (fun z => b - g z) (c x))).SeparatingLeft) ↔
    (IsCriticalPointAt I f x ∧
      (QuadraticMap.associated (R := ℝ) (chartHessianAt g (c x))).SeparatingLeft)
  rw [isCriticalPointAt_const_sub_iff (hf.mdifferentiableAt (by simp)) b,
    separatingLeft_chartHessianAt_iff hbg, separatingLeft_chartHessianAt_iff hg,
    fderiv_fderiv_const_sub]
  constructor
  · rintro ⟨hc,h⟩
    refine ⟨hc,fun v w hvw => ?_⟩
    exact h (congrArg Neg.neg hvw)
  · rintro ⟨hc,h⟩
    refine ⟨hc,fun v w hvw => ?_⟩
    exact h (neg_injective hvw)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_const_sub_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_const_sub_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_const_sub_iff ``Submission.DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_const_sub_iff

end DifferentialGeometry.Morse
