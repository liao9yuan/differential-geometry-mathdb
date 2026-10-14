import Submission.DifferentialGeometry.Topology.Manifold.MFDeriv.Interior
import Submission.DifferentialGeometry.Topology.Morse.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Topology.Morse
namespace DifferentialGeometry.Morse
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H)


theorem isCriticalPointAt_openRestriction {U : TopologicalSpace.Opens M} {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : U) (hx : I.IsInteriorPoint (x : M)) :
    IsCriticalPointAt I (fun y : U => f y) x ↔ IsCriticalPointAt I f (x : M) := by
  change (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y : U => f y) x) = 0 ↔
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f (x : M)) = 0
  erw [DifferentialGeometry.Manifold.mfderiv_openRestriction I hf x hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.isCriticalPointAt_openRestriction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.isCriticalPointAt_openRestriction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.isCriticalPointAt_openRestriction ``Submission.DifferentialGeometry.Morse.isCriticalPointAt_openRestriction


theorem chartHessianAt_openRestriction (U : TopologicalSpace.Opens M) (f : M → ℝ) (x : U) :
    chartHessianAt (fun y => f (((extChartAt I x).symm y : U) : M)) (extChartAt I x x) =
      chartHessianAt (fun y => f ((extChartAt I (x : M)).symm y)) (extChartAt I (x : M) x) := by
  have h : fderiv ℝ (fderiv ℝ (fun y => f ((extChartAt I (x : M)).symm y)))
      (extChartAt I (x : M) x) =
      fderiv ℝ (fderiv ℝ (fun y => f (((extChartAt I x).symm y : U) : M)))
        (extChartAt I (x : M) x) :=
    ((DifferentialGeometry.Manifold.extChartAt_subtype_val_symm_eventuallyEq I U x).fun_comp f).fderiv.fderiv_eq
  ext v
  change (fderiv ℝ (fderiv ℝ (fun y => f (((extChartAt I x).symm y : U) : M)))
    (extChartAt I (x : M) x)) v v = _
  rw [← h]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.chartHessianAt_openRestriction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.chartHessianAt_openRestriction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.chartHessianAt_openRestriction ``Submission.DifferentialGeometry.Morse.chartHessianAt_openRestriction


theorem isNondegenerateCriticalPointAt_openRestriction
    {U : TopologicalSpace.Opens M} {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : U) (hx : I.IsInteriorPoint (x : M)) :
    IsNondegenerateCriticalPointAt I (fun y : U => f y) x ↔
      IsNondegenerateCriticalPointAt I f (x : M) := by
  unfold IsNondegenerateCriticalPointAt
  rw [isCriticalPointAt_openRestriction I hf x hx, chartHessianAt_openRestriction I U f x]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_openRestriction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_openRestriction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_openRestriction ``Submission.DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_openRestriction

variable [IsManifold I ∞ M] [BoundarylessManifold I M]


theorem isCriticalPointAt_interiorAtlas {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    let _ := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := M)
    IsCriticalPointAt 𝓘(ℝ, E) f x ↔ IsCriticalPointAt I f x := by
  let _ := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := M)
  change (show E →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) = 0 ↔
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x) = 0
  erw [DifferentialGeometry.Manifold.mfderiv_interiorAtlas I hf x]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.isCriticalPointAt_interiorAtlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.isCriticalPointAt_interiorAtlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.isCriticalPointAt_interiorAtlas ``Submission.DifferentialGeometry.Morse.isCriticalPointAt_interiorAtlas


theorem chartHessianAt_interiorAtlas (f : M → ℝ) (x : M) :
    let _ := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := M)
    chartHessianAt (fun y => f ((extChartAt 𝓘(ℝ, E) x).symm y))
      (extChartAt 𝓘(ℝ, E) x x) =
      chartHessianAt (fun y => f ((extChartAt I x).symm y)) (extChartAt I x x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.chartHessianAt_interiorAtlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.chartHessianAt_interiorAtlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.chartHessianAt_interiorAtlas ``Submission.DifferentialGeometry.Morse.chartHessianAt_interiorAtlas


theorem isNondegenerateCriticalPointAt_interiorAtlas {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    let _ := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := M)
    IsNondegenerateCriticalPointAt 𝓘(ℝ, E) f x ↔ IsNondegenerateCriticalPointAt I f x := by
  let _ := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := M)
  change (IsCriticalPointAt 𝓘(ℝ, E) f x ∧ _) ↔ (IsCriticalPointAt I f x ∧ _)
  have hc : IsCriticalPointAt 𝓘(ℝ, E) f x ↔ IsCriticalPointAt I f x :=
    isCriticalPointAt_interiorAtlas I hf x
  rw [hc]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_interiorAtlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_interiorAtlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_interiorAtlas ``Submission.DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_interiorAtlas
end DifferentialGeometry.Morse
