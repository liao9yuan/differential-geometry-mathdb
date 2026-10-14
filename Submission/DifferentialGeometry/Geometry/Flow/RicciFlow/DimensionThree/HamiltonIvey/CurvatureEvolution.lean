import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIvey.Reaction
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.Algebra.UhlenbeckReaction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorHeatReaction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Curvature.NormHeatEquation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry.Analysis.Convex
open _root_.Submission.DifferentialGeometry.Analysis.InnerProductSpace
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree
open _root_.Submission.DifferentialGeometry.Dim3Reaction
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.RealInnerProductSpace _root_.BigOperators _root_.Matrix _root_.NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private lemma bTensorDown_eq_Bt (R : Fin 3 → Fin 3 → ℝ) (a b c d : Fin 3) :
    bTensorDown (fun a' b' c' d' => rm R a' b' c' d') a b c d = Bt R a b c d := by
  unfold bTensorDown Bt
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.bTensorDown_eq_Bt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.bTensorDown_eq_Bt target :: scope.openDecls } }

omit [TopologicalSpace M] in
private lemma uhlenbeckCurvatureOperatorReaction_eq_reactionState
    (pulledRm : FourComp M (Fin 3)) (t : Real) (x : M)
    (R : Fin 3 → Fin 3 → ℝ) (hR : ∀ i j, R i j = R j i)
    (hrm : ∀ a b c d, pulledRm t x a b c d = rm R a b c d) :
    uhlenbeckCurvatureOperatorReaction
        (fun _ _ a b c d => bTensorDown (fun a' b' c' d' => pulledRm t x a' b' c' d') a b c d)
        t x =
      hamiltonIveyMatrixReactionEuclidean (uhlenbeckCurvatureOperatorMatrix pulledRm t x) := by
  unfold uhlenbeckCurvatureOperatorReaction hamiltonIveyMatrixReactionEuclidean
    uhlenbeckCurvatureOperatorMatrix
  apply congrArg (WithLp.toLp 2)
  funext ij
  let i : Fin 3 := ij.1
  let j : Fin 3 := ij.2
  let a : Fin 3 := (bivectorIndex3 i).1
  let b : Fin 3 := (bivectorIndex3 i).2
  let c : Fin 3 := (bivectorIndex3 j).2
  let d : Fin 3 := (bivectorIndex3 j).1
  have hB : ∀ p q r s : Fin 3,
      bTensorDown (fun a' b' c' d' => pulledRm t x a' b' c' d') p q r s = Bt R p q r s := by
    intro p q r s
    have h := bTensorDown_eq_Bt R p q r s
    convert h using 1
    · congr 1
      funext a' b' c' d'
      exact hrm a' b' c' d'
  change -2 * (bTensorDown (fun a' b' c' d' => pulledRm t x a' b' c' d') a b c d -
        bTensorDown (fun a' b' c' d' => pulledRm t x a' b' c' d') a b d c +
        bTensorDown (fun a' b' c' d' => pulledRm t x a' b' c' d') a c b d -
        bTensorDown (fun a' b' c' d' => pulledRm t x a' b' c' d') a d b c) =
    (hamiltonIveyMatrixReaction (euclideanToMatrix (uhlenbeckCurvatureOperatorMatrix pulledRm t x))) i j
  rw [hB a b c d, hB a b d c, hB a c b d, hB a d b c]
  have hmain := curvatureOperatorReactionMatrix_eq_hamiltonIveyMatrixReaction R hR
  have hentry : -2 * Bsharp R a b c d =
      (hamiltonIveyMatrixReaction (curvatureOperatorMatrixOfRicci R)) i j := by
    have h := congrFun (congrFun hmain i) j
    simpa [a, b, c, d, bivectorIndex3] using h
  have hA : euclideanToMatrix (uhlenbeckCurvatureOperatorMatrix pulledRm t x) =
      curvatureOperatorMatrixOfRicci R := by
    ext p q
    dsimp [euclideanToMatrix, uhlenbeckCurvatureOperatorMatrix, curvatureOperatorMatrixOfRicci]
    rw [hrm (bivectorIndex3 p).1 (bivectorIndex3 p).2 (bivectorIndex3 q).2 (bivectorIndex3 q).1]
  have hrhs : (hamiltonIveyMatrixReaction
      (euclideanToMatrix (uhlenbeckCurvatureOperatorMatrix pulledRm t x))) i j =
      (hamiltonIveyMatrixReaction (curvatureOperatorMatrixOfRicci R)) i j := by
    rw [hA]
  have hlhs : -2 * (Bt R a b c d - Bt R a b d c + Bt R a c b d - Bt R a d b c) =
      -2 * Bsharp R a b c d := by
    unfold Bsharp
    ring
  rw [hlhs]
  calc
    -2 * Bsharp R a b c d =
      (hamiltonIveyMatrixReaction (curvatureOperatorMatrixOfRicci R)) i j := hentry
    _ = (hamiltonIveyMatrixReaction
        (euclideanToMatrix (uhlenbeckCurvatureOperatorMatrix pulledRm t x))) i j := hrhs.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorReaction_eq_reactionState
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorReaction_eq_reactionState target :: scope.openDecls } }

omit [TopologicalSpace M] in
lemma uhlenbeckReaction_eq_reactionState_at
    {pulledRm B : FourComp M (Fin 3)} (t : Real) (x : M)
    (R : Fin 3 → Fin 3 → ℝ) (hR : ∀ i j, R i j = R j i)
    (hrm : ∀ a b c d, pulledRm t x a b c d = rm R a b c d)
    (hB : ∀ a b c d, B t x a b c d = bTensorDown (fun a' b' c' d' => pulledRm t x a' b' c' d') a b c d) :
    uhlenbeckCurvatureOperatorReaction B t x =
      hamiltonIveyMatrixReactionEuclidean (uhlenbeckCurvatureOperatorMatrix pulledRm t x) := by
  have h := uhlenbeckCurvatureOperatorReaction_eq_reactionState pulledRm t x R hR hrm
  have hB' : uhlenbeckCurvatureOperatorReaction B t x =
      uhlenbeckCurvatureOperatorReaction
        (fun _ _ a b c d => bTensorDown (fun a' b' c' d' => pulledRm t x a' b' c' d') a b c d)
        t x := by
    unfold uhlenbeckCurvatureOperatorReaction
    apply congrArg (WithLp.toLp 2)
    funext ij
    let a : Fin 3 := (bivectorIndex3 ij.1).1
    let b : Fin 3 := (bivectorIndex3 ij.1).2
    let c : Fin 3 := (bivectorIndex3 ij.2).2
    let d : Fin 3 := (bivectorIndex3 ij.2).1
    change -2 * (B t x a b c d - B t x a b d c + B t x a c b d - B t x a d b c) =
      -2 * (bTensorDown (fun a' b' c' d' => pulledRm t x a' b' c' d') a b c d -
            bTensorDown (fun a' b' c' d' => pulledRm t x a' b' c' d') a b d c +
            bTensorDown (fun a' b' c' d' => pulledRm t x a' b' c' d') a c b d -
            bTensorDown (fun a' b' c' d' => pulledRm t x a' b' c' d') a d b c)
    rw [hB a b c d, hB a b d c, hB a c b d, hB a d b c]
  exact hB'.trans h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeckReaction_eq_reactionState_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeckReaction_eq_reactionState_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeckReaction_eq_reactionState_at ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeckReaction_eq_reactionState_at

omit [CompleteSpace E] in
theorem innerProductHeatReactionOn_of_uhlenbeckCurvatureOperator_quadratic
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (pulledRm roughLapD B : FourComp M (Fin 3))
    (hU : UhlenbeckCurvatureEvolutionInFrameOn (D := D) pulledRm roughLapD B)
    (hlap : ∀ t : Real, t ∈ D.carrier → ∀ x : M, ∀ ij : Fin 3 × Fin 3,
      roughLapD t x (bivectorIndex3 ij.1).1 (bivectorIndex3 ij.1).2
          (bivectorIndex3 ij.2).2 (bivectorIndex3 ij.2).1 =
        laplacianAt (I := I) G t
          (fun y : M => uhlenbeckCurvatureOperatorMatrix pulledRm t y ij) x)
    (hjoint : ContinuousOn (fun q : Real × M => uhlenbeckCurvatureOperatorMatrix pulledRm q.1 q.2)
      (D.carrier ×ˢ (Set.univ : Set M)))
    (hsmooth : ∀ ij : Fin 3 × Fin 3, ∀ t : Real, t ∈ D.carrier →
      ContMDiff I 𝓘(Real, Real) ∞
        (fun x : M => uhlenbeckCurvatureOperatorMatrix pulledRm t x ij))
    (R : Real → M → Fin 3 → Fin 3 → ℝ)
    (hR : ∀ t x i j, R t x i j = R t x j i)
    (hrm : ∀ t x a b c d, pulledRm t x a b c d = rm (R t x) a b c d)
    (hB : ∀ t x a b c d, B t x a b c d = bTensorDown (fun a' b' c' d' => pulledRm t x a' b' c' d') a b c d) :
    IsInnerProductHeatReactionOn (D := D) (G := G)
      (F := EuclideanSpace ℝ (Fin 3 × Fin 3))
      (fun _t _x A => hamiltonIveyMatrixReactionEuclidean A)
      (uhlenbeckCurvatureOperatorMatrix pulledRm) := by
  have hsolB : IsInnerProductHeatReactionOn (D := D) (G := G)
      (F := EuclideanSpace ℝ (Fin 3 × Fin 3))
      (fun t x _ => uhlenbeckCurvatureOperatorReaction B t x)
      (uhlenbeckCurvatureOperatorMatrix pulledRm) :=
    innerProductHeatReactionOn_of_uhlenbeckCurvatureOperator (I := I) (M := M)
      G pulledRm roughLapD B hU hlap hjoint hsmooth
  refine ⟨hsolB.jointCont, ?_, ?_⟩
  · intro y t ht
    exact hsolB.scalarSliceSmooth y t ht
  · intro y t ht x
    have hderiv := hsolB.equation y t ht x
    have hre := uhlenbeckReaction_eq_reactionState_at (pulledRm := pulledRm) (B := B)
      t x (R t x) (hR t x) (hrm t x) (hB t x)
    have hinner : _root_.Inner.inner ℝ (uhlenbeckCurvatureOperatorReaction B t x) y =
        _root_.Inner.inner ℝ (hamiltonIveyMatrixReactionEuclidean
          (uhlenbeckCurvatureOperatorMatrix pulledRm t x)) y := by
      rw [hre]
    have hderiv' : HasDerivAt (fun s : Real => innerScalarization
        (uhlenbeckCurvatureOperatorMatrix pulledRm) y s x)
        (laplacianAt (I := I) G t (innerScalarization
          (uhlenbeckCurvatureOperatorMatrix pulledRm) y t) x +
          _root_.Inner.inner ℝ (hamiltonIveyMatrixReactionEuclidean
            (uhlenbeckCurvatureOperatorMatrix pulledRm t x)) y) t := by
      exact hderiv.congr_deriv (by rw [hinner])
    simpa using hderiv'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.innerProductHeatReactionOn_of_uhlenbeckCurvatureOperator_quadratic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.innerProductHeatReactionOn_of_uhlenbeckCurvatureOperator_quadratic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.innerProductHeatReactionOn_of_uhlenbeckCurvatureOperator_quadratic ``Submission.DifferentialGeometry.PDE.RicciFlow.innerProductHeatReactionOn_of_uhlenbeckCurvatureOperator_quadratic

end DifferentialGeometry.PDE.RicciFlow

end
