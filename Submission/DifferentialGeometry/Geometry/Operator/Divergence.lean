import Submission.DifferentialGeometry.Bundle.ContinuousLinearMapSection.Basic
import Submission.DifferentialGeometry.Bundle.Hom.Trace
import Submission.DifferentialGeometry.Geometry.Connection.ConnectionForm
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.CovariantDerivative
import Submission.DifferentialGeometry.Geometry.Operator.Scalar.Calculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [CompleteSpace E] in
theorem divergence_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (divergence (I := I) cov X) := by
  apply contMDiff_linearMap_trace (F := E) (V := TangentSpace I)
  rw [← contMDiffOn_univ]
  exact hcov.contMDiff.contMDiff X.contMDiff.contMDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.divergence_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.divergence_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.divergence_contMDiff ``Submission.DifferentialGeometry.Geometry.Operator.divergence_contMDiff

omit [CompleteSpace E] in
theorem divergence_contMDiffAt_partial [T2Space M]
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
    {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP 1 P]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    {X : P → ∀ x : M, TangentSpace I x} {p : P × M} {m : ℕ∞} {n : ℕ∞ω}
    (hX : ContMDiffAt (IP.prod I) I.tangent n
      (fun q => (⟨q.2, X q.1 q.2⟩ : TangentBundle I M)) p)
    (hmn : (m : ℕ∞ω) + 1 ≤ n) :
    ContMDiffAt (IP.prod I) 𝓘(ℝ) m (fun q => divergence cov (X q.1) q.2) p :=
  (hcov.contMDiffAt_partial hX hmn).trace_bundle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.divergence_contMDiffAt_partial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.divergence_contMDiffAt_partial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.divergence_contMDiffAt_partial ``Submission.DifferentialGeometry.Geometry.Operator.divergence_contMDiffAt_partial

theorem leviCivita_divergence_contMDiff
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ) ∞
      (divergence (I := I)
        (Geometry.Connection.leviCivitaConnectionOfMetric (I := I) g) X) :=
  divergence_contMDiff
    (Geometry.Connection.leviCivitaConnectionOfMetric (I := I) g)
    (Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
      (I := I) g) X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.leviCivita_divergence_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.leviCivita_divergence_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.leviCivita_divergence_contMDiff ``Submission.DifferentialGeometry.Geometry.Operator.leviCivita_divergence_contMDiff

end Operator
end Geometry
end DifferentialGeometry
