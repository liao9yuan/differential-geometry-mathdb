import Submission.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Components

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

attribute [local instance] Fintype.ofFinite Classical.propDecidable

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem iterRmComp_smoothAt
    {Idx : Type*} [Fintype Idx]
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {t : Real} {x : M} (hx : x ∈ u)
    (chr : Real -> M -> Idx -> Idx -> Idx -> Real)
    (base : Real -> M -> (Fin 4 -> Idx) -> Real)
    (hchr : forall i j k : Idx,
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M => chr q.1 q.2 i j k) (t, x))
    (hbase : forall m : Fin 4 -> Idx,
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M => base q.1 q.2 m) (t, x)) :
    forall k : Nat, forall m : Fin (4 + k) -> Idx,
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M =>
          iteratedRmComp (I := I) frame chr base k q.1 q.2 m) (t, x) := by
  intro k
  induction k with
  | zero =>
      intro m
      simpa [iteratedRmComp_zero] using hbase m
  | succ k ih =>
      intro n
      have hext := prodExtDerivAt_smooth (I := I)
        (hF := ih (Fin.tail n))
        (hX := hframe.contMDiffAt hu hx (n 0))
      have hsum :
          ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
            (modelWithCornersSelf Real Real) (∞ : WithTop ℕ∞)
            (fun q : Real × M =>
              ∑ s : Fin (4 + k), ∑ p : Idx,
                chr q.1 q.2 (n 0) (Fin.tail n s) p *
                  iteratedRmComp (I := I) frame chr base k q.1 q.2
                    (Function.update (Fin.tail n) s p)) (t, x) := by
        refine ContMDiffAt.sum fun s _ => ContMDiffAt.sum fun p _ => ?_
        exact (hchr (n 0) (Fin.tail n s) p).mul
          (ih (Function.update (Fin.tail n) s p))
      have hstep := hext.sub hsum
      simpa [iteratedRmComp_succ, covDerivStepComp, frameDirectionalDerivatives] using hstep

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.iterRmComp_smoothAt with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.iterRmComp_smoothAt"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.iterRmComp_smoothAt ``Submission.DifferentialGeometry.PDE.RicciFlow.iterRmComp_smoothAt

end DifferentialGeometry.PDE.RicciFlow
