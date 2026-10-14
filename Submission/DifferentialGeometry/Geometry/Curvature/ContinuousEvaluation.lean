import Submission.DifferentialGeometry.Geometry.Curvature.PositiveSectional
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem continuous_sectional_contraction {P : Type*} [TopologicalSpace P]
    (g : SmoothRiemannianMetric I M) (b : P → M) (hb : Continuous b)
    (v w : ∀ p, TangentSpace I (b p))
    (hv : Continuous (fun p => (⟨b p, v p⟩ : TangentBundle I M)))
    (hw : Continuous (fun p => (⟨b p, w p⟩ : TangentBundle I M))) :
    Continuous (fun p => metricRm04StandardAt g (b p) (v p) (w p) (w p) (v p)) := by
  let V : Fin 4 → ∀ p, TangentSpace I (b p) := ![v, w, w, v]
  have hV : ∀ i : Fin 4, Continuous (fun p => (⟨b p, V i p⟩ : TangentBundle I M)) := by
    intro i
    fin_cases i <;> assumption
  have hR : Continuous (fun p => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
      (E := fun x : M => Tensor0SSpace 4 I x) (b p) ((metricRm04 g) (b p))) :=
    (metricRm04 g).contMDiff.continuous.comp hb
  have he := TensorMultilinear.continuous_section_apply_base b hb
    (fun p => (metricRm04 g) (b p)) hR V hV
  apply he.congr
  intro p
  rw [metricRm04_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.continuous_sectional_contraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.continuous_sectional_contraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.continuous_sectional_contraction ``Submission.DifferentialGeometry.Geometry.continuous_sectional_contraction

end DifferentialGeometry.Geometry
