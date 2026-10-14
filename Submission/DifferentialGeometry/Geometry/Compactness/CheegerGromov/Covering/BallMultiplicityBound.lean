import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped _root_.Manifold

variable {E : Type uE} [NormedAddCommGroup E]
variable [NormedSpace Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

structure BallMultiplicityBound
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  dist : PointedRiemannianSeq.Distance (I := I) X
  r0 : Real
  r0_pos : 0 < r0
  multiplicity : Real → Nat
  card_le :
    ∀ (m : Real) (k : Nat) {α : Type u}, [Fintype α] → [DecidableEq α] →
      ∀ centers : α → (X.obj k).M, ∀ r : Real, 0 < r → m * r ≤ r0 →
        (∀ i j : α, i ≠ j → r ≤ dist k (centers i) (centers j)) →
        ∀ z : (X.obj k).M, ∀ J : Finset α,
          (∀ j : α, j ∈ J → dist k (centers j) z ≤ m * r) →
          J.card ≤ multiplicity m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.BallMultiplicityBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.BallMultiplicityBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.BallMultiplicityBound ``Submission.DifferentialGeometry.CheegerGromovCompactness.BallMultiplicityBound

namespace BallMultiplicityBound

def subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : BallMultiplicityBound (I := I) X) (f : Nat → Nat) :
    BallMultiplicityBound (I := I) (X.subseq f) where
  dist := fun k x y => h.dist (f k) x y
  r0 := h.r0
  r0_pos := h.r0_pos
  multiplicity := h.multiplicity
  card_le := by
    intro m k α _ _ centers r hr hcap hsep z J hJz
    exact h.card_le m (f k) centers r hr hcap hsep z J hJz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.BallMultiplicityBound.subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.BallMultiplicityBound.subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.BallMultiplicityBound.subseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.BallMultiplicityBound.subseq

end BallMultiplicityBound

end CheegerGromovCompactness
end DifferentialGeometry
