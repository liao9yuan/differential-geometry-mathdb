import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
variable [IsManifold I 1 N]
variable [T2Space N] [SigmaCompactSpace N]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace N] in
theorem metricRm04StandardAt_pullback_localDiffeo
    (g : SmoothRiemannianMetric I N)
    (V : TopologicalSpace.Opens N) [T2Space V]
      [IsManifold I 1 V]
    (W : TopologicalSpace.Opens M) [T2Space W]
      [IsManifold I 1 W]
    (Ψ : W ≃ₘ⟮I, I⟯ V) (x : W) (X Y Z W' : TangentSpace I x) :
    metricRm04StandardAt (I := I) (M := W)
        (Diffeomorph.pullbackMetric (I := I) (g.restrictOpen (I := I) V) Ψ) x X Y Z W' =
      metricRm04StandardAt (I := I) (M := N) g ((Ψ x : V) : N)
        (mfderiv I I (Ψ : W → V) x X) (mfderiv I I (Ψ : W → V) x Y)
        (mfderiv I I (Ψ : W → V) x Z) (mfderiv I I (Ψ : W → V) x W') := by
  rw [metricRm04Standard_pullback (I := I) (g.restrictOpen (I := I) V) Ψ x X Y Z W',
    metricRm04StandardAt_restrictOpen (I := I) g V (Ψ x)
      (mfderiv I I (Ψ : W → V) x X) (mfderiv I I (Ψ : W → V) x Y)
      (mfderiv I I (Ψ : W → V) x Z) (mfderiv I I (Ψ : W → V) x W')]
  simp only [mfderiv_subtype_val_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt_pullback_localDiffeo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt_pullback_localDiffeo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt_pullback_localDiffeo ``Submission.DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt_pullback_localDiffeo

end DifferentialGeometry.Geometry.Curvature
