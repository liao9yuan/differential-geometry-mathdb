import Submission.DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityContinuity
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Mathlib.MeasureTheory.Integral.Bochner.Set

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Integral.Measure

open _root_.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
variable {P : Type*} [TopologicalSpace P]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem continuousOn_integral_riemannianVolumeMeasure_of_compact_support
    (g : P → SmoothRiemannianMetric I M) {J : Set P}
    (hg : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : P × M => chartGramMatrix (I := I) (g p.1) α p.2 i j)
        (J ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet))
    (f : P → M → F)
    (hf : ContinuousOn (fun p : P × M => f p.1 p.2) (J ×ˢ (_root_.Set.univ : Set M)))
    {K : Set M} (hK : IsCompact K)
    (hzero : ∀ s ∈ J, ∀ x ∉ K, f s x = 0) :
    ContinuousOn (fun s => ∫ x, f s x ∂riemannianVolumeMeasure (I := I) (M := M) (g s)) J := by
  intro t ht
  let μ := riemannianVolumeMeasure (I := I) (M := M) (g t)
  let : _root_.MeasureTheory.IsFiniteMeasureOnCompacts μ :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (g t)
  let u : P → M → F := fun s x => riemannianVolumeDensity (g t) (g s) x • f s x
  have hu : ContinuousOn (fun p : P × M => u p.1 p.2) (J ×ˢ (_root_.Set.univ : Set M)) :=
    (riemannianVolumeDensity_family_continuousOn (g t) g hg).smul hf
  have hcont := _root_.continuousOn_integral_of_compact_support (μ := μ) (f := u) (s := J) hK hu
    (fun s x hs hx => by simp only [u, hzero s hs x hx, smul_zero])
  have heq (s : P) : (∫ x, f s x ∂riemannianVolumeMeasure (I := I) (M := M) (g s)) =
      ∫ x, u s x ∂μ :=
    integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul (g t) (g s) (f s)
  exact (hcont.congr fun s _ => heq s) t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.continuousOn_integral_riemannianVolumeMeasure_of_compact_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.continuousOn_integral_riemannianVolumeMeasure_of_compact_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.continuousOn_integral_riemannianVolumeMeasure_of_compact_support ``Submission.DifferentialGeometry.Integral.Measure.continuousOn_integral_riemannianVolumeMeasure_of_compact_support

end DifferentialGeometry.Integral.Measure
