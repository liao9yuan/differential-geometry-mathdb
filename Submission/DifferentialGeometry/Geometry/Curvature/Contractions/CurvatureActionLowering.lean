import Submission.DifferentialGeometry.Geometry.Connection.RicciIdentity.Tensor0S.CurvatureAction
import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.Contractions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}

theorem curvatureAction0SAt_eq_rm04 {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : Rm04LowersRm13At (I := I) g x (Rm13 x) Rm04)
    (S : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (X Y : TangentSpace I x) (slots : Fin s -> TangentSpace I x) :
    curvatureAction0SAt (I := I) Rm13 S X Y slots =
      -∑ q : Fin s, ∑ p : Idx,
        (∑ r : Idx, gInv p r * S (Function.update slots q (basis r))) *
          Rm04 (vec4 (I := I) X Y (slots q) (basis p)) := by
  unfold curvatureAction0SAt
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [rm13_oneForm_apply_eq_sum_inv_flat (I := I) g basis gInv hinv (Rm13 x)
    (oneFormAtSlot0S (I := I) S slots q) X Y (slots q)]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [oneFormAtSlot0S_apply]
  rw [(hLower X Y (slots q) (basis p)).symm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureAction0SAt_eq_rm04 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureAction0SAt_eq_rm04"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureAction0SAt_eq_rm04 ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureAction0SAt_eq_rm04

end DifferentialGeometry.Geometry.Curvature
