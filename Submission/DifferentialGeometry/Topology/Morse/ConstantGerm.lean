import Submission.DifferentialGeometry.Topology.Manifold.InteriorChart
import Submission.DifferentialGeometry.Topology.Morse.Defs
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Topology.Morse
namespace DifferentialGeometry.Morse
variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

private theorem mfderiv_add_const_real {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (b : ℝ) :
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y => f y + b) x) =
      (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x) := by
  change (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (f + (fun _ : M => b)) x) = _
  erw [mfderiv_add hf mdifferentiableAt_const,mfderiv_const,add_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Morse.mfderiv_add_const_real
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Morse.mfderiv_add_const_real target :: scope.openDecls } }


theorem isCriticalPointAt_iff_of_eventuallyEq_add_const {f g : M → ℝ} {x : M} {b : ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (h : g =ᶠ[𝓝 x] (fun y => f y + b)) :
    IsCriticalPointAt I g x ↔ IsCriticalPointAt I f x := by
  exact Iff.of_eq (congrArg (fun L : E →L[ℝ] ℝ => L = 0)
    (h.mfderiv_eq.trans (mfderiv_add_const_real hf b)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.isCriticalPointAt_iff_of_eventuallyEq_add_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.isCriticalPointAt_iff_of_eventuallyEq_add_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.isCriticalPointAt_iff_of_eventuallyEq_add_const ``Submission.DifferentialGeometry.Morse.isCriticalPointAt_iff_of_eventuallyEq_add_const

variable [IsManifold I ∞ M]


theorem chartHessianAt_eq_of_eventuallyEq_add_const {f g : M → ℝ} {x : M} {b : ℝ}
    (hx : I.IsInteriorPoint x) (h : g =ᶠ[𝓝 x] (fun y => f y + b)) :
    chartHessianAt (fun z => g ((extChartAt I x).symm z)) (extChartAt I x x) =
      chartHessianAt (fun z => f ((extChartAt I x).symm z)) (extChartAt I x x) := by
  let c := DifferentialGeometry.Manifold.interiorChart I ∞ x
  have hxc : x ∈ c.source := (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hx
  have hc : ContinuousAt c.symm (c x) :=
    c.symm.toOpenPartialHomeomorph.continuousOn.continuousAt
      (c.open_target.mem_nhds (c.map_source hxc))
  have hct : _root_.Filter.Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
    have hh : _root_.Filter.Tendsto c.symm (𝓝 (c x)) (𝓝 (c.symm (c x))) := hc
    exact (congrArg (fun y : M => _root_.Filter.Tendsto c.symm (𝓝 (c x)) (𝓝 y)) (c.left_inv hxc)).mp hh
  have hgerm : (fun z => g (c.symm z)) =ᶠ[𝓝 (c x)] (fun z => f (c.symm z) + b) :=
    h.comp_tendsto hct
  have hD := (hgerm.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  have hconst : fderiv ℝ (fun z => f (c.symm z) + b) = fderiv ℝ (fun z => f (c.symm z)) :=
    funext fun z => fderiv_add_const b
  rw [hconst] at hD
  unfold chartHessianAt chartHessianBilinAt
  congr 1
  ext v w
  exact congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L v w) hD

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.chartHessianAt_eq_of_eventuallyEq_add_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.chartHessianAt_eq_of_eventuallyEq_add_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.chartHessianAt_eq_of_eventuallyEq_add_const ``Submission.DifferentialGeometry.Morse.chartHessianAt_eq_of_eventuallyEq_add_const


theorem isNondegenerateCriticalPointAt_iff_of_eventuallyEq_add_const
    {f g : M → ℝ} {x : M} {b : ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hx : I.IsInteriorPoint x)
    (h : g =ᶠ[𝓝 x] (fun y => f y + b)) :
    IsNondegenerateCriticalPointAt I g x ↔ IsNondegenerateCriticalPointAt I f x := by
  unfold IsNondegenerateCriticalPointAt
  rw [isCriticalPointAt_iff_of_eventuallyEq_add_const hf h,
    chartHessianAt_eq_of_eventuallyEq_add_const hx h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_iff_of_eventuallyEq_add_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_iff_of_eventuallyEq_add_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_iff_of_eventuallyEq_add_const ``Submission.DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_iff_of_eventuallyEq_add_const

end DifferentialGeometry.Morse
