import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.CovariantDerivativeFields

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates

open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

def nabla3InnerSlots
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x) (x : M)
    (d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    Fin 5 → TangentSpace I x :=
  Fin.cons (frame d₂ x) (frameTuple (I := I) frame x m)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nabla3InnerSlots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nabla3InnerSlots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nabla3InnerSlots ``Submission.DifferentialGeometry.PDE.RicciFlow.nabla3InnerSlots

def nabla3FrameTuple
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x) (x : M)
    (d₀ d₁ d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    Fin 7 → TangentSpace I x :=
  metricTraceInput (I := I) (frame d₀ x) (frame d₁ x)
    (nabla3InnerSlots (I := I) frame x d₂ m)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nabla3FrameTuple then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nabla3FrameTuple"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nabla3FrameTuple ``Submission.DifferentialGeometry.PDE.RicciFlow.nabla3FrameTuple

omit [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E]
    [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem nabla3FrameTuple_eq_metricTraceInput
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x) (x : M)
    (d₀ d₁ d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3FrameTuple (I := I) frame x d₀ d₁ d₂ m =
      metricTraceInput (I := I) (frame d₀ x) (frame d₁ x)
        (nabla3InnerSlots (I := I) frame x d₂ m) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nabla3FrameTuple_eq_metricTraceInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nabla3FrameTuple_eq_metricTraceInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nabla3FrameTuple_eq_metricTraceInput ``Submission.DifferentialGeometry.PDE.RicciFlow.nabla3FrameTuple_eq_metricTraceInput

def nablaLapCommReactionTerm
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    Real :=
  (nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a b c m) -
      nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a c b m)) +
    curvatureAction0SAt (I := I) (S.base.rm13 t) (nablaRm04Field (I := I) S t x₀)
      (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
      (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nablaLapCommReactionTerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nablaLapCommReactionTerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nablaLapCommReactionTerm ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaLapCommReactionTerm

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaLapComm_pointwise
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a b c m) -
      nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ c a b m) =
      nablaLapCommReactionTerm (I := I) S (t : Real) x₀ a b c m := by
  classical
  have hR2 :=
    nablaRm04_ricciIdentityAt (I := I) S t x₀
      (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
      (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m)
  rw [nablaLapCommReactionTerm]
  simp only [nabla3FrameTuple, nabla3InnerSlots] at hR2 ⊢
  linarith [hR2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nablaLapComm_pointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nablaLapComm_pointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nablaLapComm_pointwise ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaLapComm_pointwise

def roughLapNablaRmComp
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    Real :=
  ∑ a : CoordinateIdx (𝕜 := Real) E, ∑ b : CoordinateIdx (𝕜 := Real) E,
    gInv a b *
      nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a b c m)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.roughLapNablaRmComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.roughLapNablaRmComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.roughLapNablaRmComp ``Submission.DifferentialGeometry.PDE.RicciFlow.roughLapNablaRmComp

def nablaRoughLapRmComp
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    Real :=
  ∑ a : CoordinateIdx (𝕜 := Real) E, ∑ b : CoordinateIdx (𝕜 := Real) E,
    gInv a b *
      nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ c a b m)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nablaRoughLapRmComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nablaRoughLapRmComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nablaRoughLapRmComp ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaRoughLapRmComp

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaLapComm_trace
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    roughLapNablaRmComp (I := I) S (t : Real) x₀ gInv c m -
        nablaRoughLapRmComp (I := I) S (t : Real) x₀ gInv c m =
      ∑ a : CoordinateIdx (𝕜 := Real) E, ∑ b : CoordinateIdx (𝕜 := Real) E,
        gInv a b * nablaLapCommReactionTerm (I := I) S (t : Real) x₀ a b c m := by
  classical
  rw [roughLapNablaRmComp, nablaRoughLapRmComp]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← mul_sub, nablaLapComm_pointwise (I := I) S t x₀ a b c m]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nablaLapComm_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nablaLapComm_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nablaLapComm_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaLapComm_trace

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaLapComm_orthonormalTrace
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (horth : ∀ i j : CoordinateIdx (𝕜 := Real) E, gInv i j = if i = j then 1 else 0)
    (c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    roughLapNablaRmComp (I := I) S (t : Real) x₀ gInv c m -
        nablaRoughLapRmComp (I := I) S (t : Real) x₀ gInv c m =
      ∑ a : CoordinateIdx (𝕜 := Real) E,
        nablaLapCommReactionTerm (I := I) S (t : Real) x₀ a a c m := by
  classical
  rw [nablaLapComm_trace (I := I) S t x₀ gInv c m]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, one_mul]
  · intro b _ hb
    rw [horth a b, if_neg (fun h => hb h.symm), _root_.MulZeroClass.zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nablaLapComm_orthonormalTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nablaLapComm_orthonormalTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nablaLapComm_orthonormalTrace ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaLapComm_orthonormalTrace

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaLapComm_secondTerm_eq
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
        (nablaRm04Field (I := I) S (t : Real) x₀)
        (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
        (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m) =
      nabla3Rm04Field (I := I) S (t : Real) x₀
          (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a c b m) -
        nabla3Rm04Field (I := I) S (t : Real) x₀
          (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ c a b m) := by
  have hR2 :=
    nablaRm04_ricciIdentityAt (I := I) S t x₀
      (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
      (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m)
  simp only [nabla3FrameTuple, nabla3InnerSlots] at hR2 ⊢
  exact hR2.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nablaLapComm_secondTerm_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nablaLapComm_secondTerm_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nablaLapComm_secondTerm_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaLapComm_secondTerm_eq

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaLapCommReactionTerm_eq_nabla3
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nablaLapCommReactionTerm (I := I) S (t : Real) x₀ a b c m =
      nabla3Rm04Field (I := I) S (t : Real) x₀
          (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a b c m) -
        nabla3Rm04Field (I := I) S (t : Real) x₀
          (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ c a b m) :=
  (nablaLapComm_pointwise (I := I) S t x₀ a b c m).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nablaLapCommReactionTerm_eq_nabla3 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nablaLapCommReactionTerm_eq_nabla3"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nablaLapCommReactionTerm_eq_nabla3 ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaLapCommReactionTerm_eq_nabla3

end DifferentialGeometry.PDE.RicciFlow
