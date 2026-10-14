import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.Topology _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

def RicciBoundedBelow (g : SmoothRiemannianMetric I M) (κ : ℝ) : Prop :=
  ∀ (x : M) (v : TangentSpace I x), κ * (g.inner x v v : ℝ) ≤ ricciTensor (I := I) g x v v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow ``Submission.DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciLower_of_rm
    (g : SmoothRiemannianMetric I M) {Rm : ℝ}
    (hRm : ∀ x : M,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 4
        (metricRm04At (I := I) (M := M) g x)) ≤ Rm) :
    RicciBoundedBelow (I := I) g
      (-((Module.finrank ℝ E : ℝ) ^ 2 * Rm)) := by
  classical
  intro x v
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  let A : ℝ := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 4
    (metricRm04At (I := I) (M := M) g x))
  have hfinrank : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := by
    have hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact mem_chart_source H x
    exact ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x).linearEquivAt ℝ x hx).finrank_eq
  have hcomp : ∀ i j,
      |metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j))| ≤
        (Module.finrank ℝ E : ℝ) * A := by
    intro i j
    simpa [A, hfinrank] using metricRicciComp_le (I := I) g basis hON i j
  have hunit : ∀ u : TangentSpace I x, g.inner x u u = 1 →
      |metricRicciAt (I := I) (M := M) g x (vec2 (I := I) u u)| ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * A := by
    intro u hu
    have h := ricci_unitSphere_le_of_componentBound
      (I := I) g (metricRicciAt (I := I) (M := M) g x) basis hON
      (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) hcomp u hu
    simpa [A, hfinrank, pow_two, mul_assoc] using h
  have hquad := tensor02_quadForm_abs_le_of_unit_bound
    (I := I) g (metricRicciAt (I := I) (M := M) g x) hunit v
  rw [metricRicciAt_apply_eq_ricciTensor (I := I) g x v v] at hquad
  have hinner : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with hv | hv
    · subst v
      simp
    · exact (g.pos x v hv).le
  have hcoef :
      (Module.finrank ℝ E : ℝ) ^ 2 * A ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * Rm :=
    mul_le_mul_of_nonneg_left (hRm x) (sq_nonneg _)
  have habs : |ricciTensor (I := I) g x v v| ≤
      ((Module.finrank ℝ E : ℝ) ^ 2 * Rm) * g.inner x v v :=
    hquad.trans (mul_le_mul_of_nonneg_right hcoef hinner)
  simpa only [neg_mul] using (abs_le.mp habs).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.BonnetMyers.ricciLower_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.BonnetMyers.ricciLower_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.BonnetMyers.ricciLower_of_rm ``Submission.DifferentialGeometry.Geometry.Riemannian.BonnetMyers.ricciLower_of_rm

end BonnetMyers
end Riemannian
end Geometry
end DifferentialGeometry

end
