import Submission.DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciLowerAt_of_rm
    (g : SmoothRiemannianMetric I M) {x : M} {Rm : ℝ}
    (hRm :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 4
        (metricRm04At (I := I) (M := M) g x)) ≤ Rm)
    (v : TangentSpace I x) :
    -((Module.finrank ℝ E : ℝ) ^ 2 * Rm) * g.inner x v v ≤
      ricciTensor (I := I) g x v v := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hxbase : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H x
  have hrank : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E :=
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x).linearEquivAt ℝ x hxbase).finrank_eq
  let A : ℝ := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 4
    (metricRm04At (I := I) (M := M) g x))
  have hcomp : ∀ i j,
      |metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j))| ≤
        (Module.finrank ℝ E : ℝ) * A := by
    intro i j
    calc
      |metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j))| ≤
          (Module.finrank ℝ (TangentSpace I x) : ℝ) * A := by
        simpa [A] using metricRicciComp_le (I := I) g basis hON i j
      _ = (Module.finrank ℝ E : ℝ) * A := by rw [hrank]
  have hunit : ∀ u : TangentSpace I x, g.inner x u u = 1 →
      |metricRicciAt (I := I) (M := M) g x (vec2 (I := I) u u)| ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * A := by
    intro u hu
    have h := ricci_unitSphere_le_of_componentBound
      (I := I) g (metricRicciAt (I := I) (M := M) g x) basis hON
      (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) hcomp u hu
    calc
      |metricRicciAt (I := I) (M := M) g x (vec2 (I := I) u u)| ≤
          (Module.finrank ℝ (TangentSpace I x) : ℝ) *
            ((Module.finrank ℝ E : ℝ) * A) := by
        simpa [A, mul_assoc] using h
      _ = (Module.finrank ℝ E : ℝ) ^ 2 * A := by
        rw [hrank]
        ring
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
    mul_le_mul_of_nonneg_left hRm (sq_nonneg _)
  have habs : |ricciTensor (I := I) g x v v| ≤
      ((Module.finrank ℝ E : ℝ) ^ 2 * Rm) * g.inner x v v :=
    hquad.trans (mul_le_mul_of_nonneg_right hcoef hinner)
  simpa only [neg_mul] using (abs_le.mp habs).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.BonnetMyers.ricciLowerAt_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.BonnetMyers.ricciLowerAt_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.BonnetMyers.ricciLowerAt_of_rm ``Submission.DifferentialGeometry.Geometry.Riemannian.BonnetMyers.ricciLowerAt_of_rm

end BonnetMyers
end Riemannian
end Geometry
end DifferentialGeometry

end
