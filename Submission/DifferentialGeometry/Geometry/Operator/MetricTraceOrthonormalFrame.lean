import Submission.DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Rough

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem metricTraceFirstTwo0SAt_eq_sum_smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) {s : ℕ} {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (I := I) (M := M) (s + 2) x)
    (tail : Fin s → TangentSpace I x) :
    metricTraceFirstTwo0SAt g T tail =
      ∑ i : Fin (Module.finrank ℝ E),
        T (Fin.cons (smoothOrthoFrame g x i x)
          (Fin.cons (smoothOrthoFrame g x i x) tail)) := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : IsEmpty (Fin (Module.finrank ℝ E)) := by
      simpa [hdim] using (Fin.isEmpty : IsEmpty (Fin 0))
    let basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
      Module.finBasis ℝ (TangentSpace I x)
    have horth : ∀ i j, g.inner x (basis i) (basis j) = if i = j then 1 else 0 := by
      intro i
      exact isEmptyElim i
    rw [metricTraceFirstTwo0SAt_eq_sum_basis g basis identityInvMetric
      (metricInverseInBasis_identity_of_orthonormal g basis horth)]
    simp [metricTrace0S2InBasis]
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let basis := (smoothOrtho_isLocal g x).toBasisAt (mem_smoothOrthoFrameNeighborhood_self x)
  have horth : ∀ i j, g.inner x (basis i) (basis j) = if i = j then 1 else 0 := by
    intro i j
    simpa only [basis, IsLocalFrameOn.toBasisAt_coe] using
      smoothOrthoFrame_orthonormal_at_center g x i j
  rw [metricTraceFirstTwo0SAt_eq_sum_basis g basis identityInvMetric
    (metricInverseInBasis_identity_of_orthonormal g basis horth)]
  simp only [metricTrace0S2InBasis, identityInvMetric, diagonalInvMetric,
    ite_mul, one_mul, _root_.MulZeroClass.zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    basis, IsLocalFrameOn.toBasisAt_coe]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_eq_sum_smoothOrthoFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_eq_sum_smoothOrthoFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_eq_sum_smoothOrthoFrame ``Submission.DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_eq_sum_smoothOrthoFrame

end DifferentialGeometry.Geometry.Operator
