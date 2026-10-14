import Submission.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Components

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem iterRmComp_joint
    {Idx : Type*} [Fintype Idx]
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {J : Set Real} {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {t : Real} {x : M} (ht : t ∈ J) (hx : x ∈ u)
    (chr : Real -> M -> Idx -> Idx -> Idx -> Real)
    (base : Real -> M -> (Fin 4 -> Idx) -> Real)
    (hchr : ∀ i j k : Idx,
      ContMDiffWithinAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M => chr q.1 q.2 i j k) (J ×ˢ u) (t, x))
    (hbase : ∀ m : Fin 4 -> Idx,
      ContMDiffWithinAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M => base q.1 q.2 m) (J ×ˢ u) (t, x)) :
    ∀ k : Nat, ∀ m : Fin (4 + k) -> Idx,
      ContMDiffWithinAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M =>
          iteratedRmComp (I := I) frame chr base k q.1 q.2 m)
        (J ×ˢ u) (t, x) := by
  classical
  intro k
  induction k with
  | zero =>
      intro m
      simpa [iteratedRmComp_zero] using hbase m
  | succ k ih =>
      intro n
      have hext := prodExtDeriv_joint (I := I) hu ht hx
        (hF := ih (Fin.tail n))
        (hX := hframe.contMDiffAt hu hx (n 0))
      have hsum :
          ContMDiffWithinAt ((modelWithCornersSelf Real Real).prod I)
            (modelWithCornersSelf Real Real) (∞ : WithTop ℕ∞)
            (fun q : Real × M =>
              ∑ s : Fin (4 + k), ∑ p : Idx,
                chr q.1 q.2 (n 0) (Fin.tail n s) p *
                  iteratedRmComp (I := I) frame chr base k q.1 q.2
                    (Function.update (Fin.tail n) s p))
            (J ×ˢ u) (t, x) := by
        refine ContMDiffWithinAt.sum fun s _ =>
          ContMDiffWithinAt.sum fun p _ => ?_
        exact (hchr (n 0) (Fin.tail n s) p).mul
          (ih (Function.update (Fin.tail n) s p))
      have hstep := hext.sub hsum
      simpa [iteratedRmComp_succ, covDerivStepComp, frameDirectionalDerivatives] using hstep

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.iterRmComp_joint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.iterRmComp_joint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.iterRmComp_joint ``Submission.DifferentialGeometry.PDE.RicciFlow.iterRmComp_joint

end DifferentialGeometry.PDE.RicciFlow
