import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.Relowering
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.TraceBound
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Estimates.TensorProductNorm
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [T2Space M]
variable [CompactSpace M] [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem reLowerPairSq_le (g : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (K : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3)
    (x : M) :
    normSq0S (I := I) g x (s + 2) (reLowerPair (I := I) g T K x) ≤
      (Module.finrank Real E : Real) ^ (s + 4) *
        (normSq0S (I := I) g x (s + 1) (T x) * normSq0S (I := I) g x 3 (K x)) := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis hON
  have hprod : normSq0S (I := I) g x (s + 1 + 3)
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K x) =
      normSq0S (I := I) g x (s + 1) (T x) * normSq0S (I := I) g x 3 (K x) :=
    normSq0S_product (I := I) g x basis hinv T K
  have hcongr : normSq0S (I := I) g x (s + 1 + 3)
      (ContinuousMultilinearMap.domDomCongr (reLowerPermutationWithThreeInputs s)
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K x)) =
      normSq0S (I := I) g x (s + 1 + 3)
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K x) :=
    normSq0S_domDomCongr (I := I) g x basis hinv (reLowerPermutationWithThreeInputs s) _
  have htr := traceNormSq_le (I := I) (s := s + 2) g x
    (ContinuousMultilinearMap.domDomCongr (reLowerPermutationWithThreeInputs s)
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K x))
  rw [hcongr, hprod] at htr
  exact htr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLowerPairSq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLowerPairSq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLowerPairSq_le ``Submission.DifferentialGeometry.PDE.RicciFlow.reLowerPairSq_le


end DifferentialGeometry.PDE.RicciFlow
