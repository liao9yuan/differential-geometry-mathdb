import Submission.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle
open scoped _root_.BigOperators
open scoped _root_.Manifold _root_.ContDiff

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

def covDerivStepComp {r : ℕ}
    (ext : (Fin r → Idx) → Idx → Real)
    (chr : Idx → Idx → Idx → Real)
    (A : (Fin r → Idx) → Real) : (Fin (r + 1) → Idx) → Real :=
  fun n =>
    ext (Fin.tail n) (n 0) -
      ∑ s : Fin r, ∑ p : Idx,
        chr (n 0) (Fin.tail n s) p * A (Function.update (Fin.tail n) s p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covDerivStepComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covDerivStepComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covDerivStepComp ``Submission.DifferentialGeometry.PDE.RicciFlow.covDerivStepComp

def frameDirectionalDerivatives {r : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (frame : Idx → (x : M) → TangentSpace I x)
    (A : M → (Fin r → Idx) → Real) (x : M) :
    (Fin r → Idx) → Idx → Real :=
  fun m d => mvfderiv (I := I) (fun y : M => A y m) x (frame d x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.frameDirectionalDerivatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.frameDirectionalDerivatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.frameDirectionalDerivatives ``Submission.DifferentialGeometry.PDE.RicciFlow.frameDirectionalDerivatives

omit [DecidableEq Idx] in
theorem covDerivComp_joint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    {J : Set Real} {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {t : Real} {x : M} (ht : t ∈ J) (hx : x ∈ u)
    (chr : Real → M → Idx → Idx → Idx → Real)
    (A : Real → M → (Fin r → Idx) → Real)
    (hchr : ∀ i j k : Idx,
      ContMDiffWithinAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M ↦ chr q.1 q.2 i j k) (J ×ˢ u) (t, x))
    (hA : ∀ m : Fin r → Idx,
      ContMDiffWithinAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M ↦ A q.1 q.2 m) (J ×ˢ u) (t, x)) :
    ∀ n : Fin (r + 1) → Idx,
      ContMDiffWithinAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M ↦
          covDerivStepComp
            (frameDirectionalDerivatives (I := I) frame (fun y ↦ A q.1 y) q.2)
            (chr q.1 q.2) (A q.1 q.2) n)
        (J ×ˢ u) (t, x) := by
  classical
  intro n
  have hext := prodExtDeriv_joint (I := I) hu ht hx
    (hF := hA (Fin.tail n))
    (hX := hframe.contMDiffAt hu hx (n 0))
  have hsum :
      ContMDiffWithinAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M ↦
          ∑ s : Fin r, ∑ p : Idx,
            chr q.1 q.2 (n 0) (Fin.tail n s) p *
              A q.1 q.2 (Function.update (Fin.tail n) s p))
        (J ×ˢ u) (t, x) := by
    refine ContMDiffWithinAt.sum fun s _ ↦
      ContMDiffWithinAt.sum fun p _ ↦ ?_
    exact (hchr (n 0) (Fin.tail n s) p).mul
      (hA (Function.update (Fin.tail n) s p))
  simpa [covDerivStepComp, frameDirectionalDerivatives] using hext.sub hsum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covDerivComp_joint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covDerivComp_joint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covDerivComp_joint ``Submission.DifferentialGeometry.PDE.RicciFlow.covDerivComp_joint

end DifferentialGeometry.PDE.RicciFlow
