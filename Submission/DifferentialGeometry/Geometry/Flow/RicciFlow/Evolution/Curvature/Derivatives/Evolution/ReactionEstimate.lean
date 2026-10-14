import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.HeatEquation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Frame.Invariant
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Metric.OrthonormalComponents
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import Submission.DifferentialGeometry.Geometry.Metric.QuadraticBounds.FiniteArrayNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
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


section ReactionBridge

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

def combinedStarArray {s : ℕ}
    (ric : Idx → Idx → Real)
    (rmComp residualComp : (Fin s → Idx) → Real) :
    (Fin s → Idx) → Real :=
  fun m => ricStarArray ric rmComp m + residualComp m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.combinedStarArray then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.combinedStarArray"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.combinedStarArray ``Submission.DifferentialGeometry.PDE.RicciFlow.combinedStarArray

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaKRm04Reaction_orthoBasis_eq_compContract
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ)
    (basis : (x : M) → Module.Basis Idx Real (TangentSpace I x))
    (gInv : Real → M → Idx → Idx → Real)
    (ric : Real → M → Idx → Idx → Real)
    (Tdot : Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (4 + k) x)
    (t : Real) (x : M)
    (horth : ∀ i j : Idx,
      (S.base.metric t).inner x (basis x i) (basis x j) =
        if i = j then (1 : Real) else 0)
    (hgInv : gInv t x = identityInvMetric (Idx := Idx)) :
    nablaKRm04ReactionIntrinsic (I := I) S k basis gInv ric Tdot t x =
      2 * ∑ m : Fin (4 + k) → Idx,
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
            (fun i => basis x i) m *
          combinedStarArray (ric t x)
            (fun I0 : Fin (4 + k) → Idx =>
              tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
                (fun i => basis x i) I0)
            (fun m : Fin (4 + k) → Idx =>
              tensor0SComponent (I := I)
                (Tdot t x -
                  metricTrace0S2TensorInBasis (I := I) (basis x) (gInv t x)
                    (nablaKRm04Field (I := I) S t (k + 2) x))
                (fun i => basis x i) m)
            m := by
  classical
  rw [nablaKRm04ReactionIntrinsic]
  set rmC : (Fin (4 + k) → Idx) → Real :=
    fun I0 => tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
      (fun i => basis x i) I0 with hrmC
  set resid : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (4 + k) x :=
    Tdot t x -
      metricTrace0S2TensorInBasis (I := I) (basis x) (gInv t x)
        (nablaKRm04Field (I := I) S t (k + 2) x) with hresid
  set residC : (Fin (4 + k) → Idx) → Real :=
    fun m => tensor0SComponent (I := I) resid (fun i => basis x i) m with hresidC
  rw [hgInv]
  rw [ricReactionContract_delta_eq_compContract (Idx := Idx) (ric t x) rmC rmC]
  rw [inner0S_orthoBasis_eq_compContract (I := I) (S.base.metric t) (basis x) horth
    resid (nablaKRm04Field (I := I) S t k x)]
  have hcombine :
      (∑ I0 : Fin (4 + k) → Idx, rmC I0 * ricStarArray (ric t x) rmC I0) +
          (∑ m : Fin (4 + k) → Idx, residC m * rmC m) =
        ∑ m : Fin (4 + k) → Idx,
          rmC m * combinedStarArray (ric t x) rmC residC m := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold combinedStarArray
    ring
  rw [show
      2 * (∑ I0 : Fin (4 + k) → Idx, rmC I0 * ricStarArray (ric t x) rmC I0) +
          2 * (∑ m : Fin (4 + k) → Idx, residC m * rmC m) =
        2 * ((∑ I0 : Fin (4 + k) → Idx, rmC I0 * ricStarArray (ric t x) rmC I0) +
              (∑ m : Fin (4 + k) → Idx, residC m * rmC m)) from by ring]
  rw [hcombine]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nablaKRm04Reaction_orthoBasis_eq_compContract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nablaKRm04Reaction_orthoBasis_eq_compContract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nablaKRm04Reaction_orthoBasis_eq_compContract ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaKRm04Reaction_orthoBasis_eq_compContract

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaKReactionAt_eq
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ) (t : Real) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv ric : Idx → Idx → Real)
    (Tdot : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (4 + k) x)
    (horth : ∀ i j : Idx,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (hgInv : gInv = identityInvMetric (Idx := Idx)) :
    nablaKReactionAt (I := I) S k t x basis gInv ric Tdot =
      2 * ∑ m : Fin (4 + k) → Idx,
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
            (fun i => basis i) m *
          combinedStarArray ric
            (fun I0 : Fin (4 + k) → Idx =>
              tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
                (fun i => basis i) I0)
            (fun m : Fin (4 + k) → Idx =>
              tensor0SComponent (I := I)
                (Tdot - metricTrace0S2TensorInBasis (I := I) basis gInv
                    (nablaKRm04Field (I := I) S t (k + 2) x))
                (fun i => basis i) m)
            m := by
  classical
  rw [nablaKReactionAt]
  set rmC : (Fin (4 + k) → Idx) → Real :=
    fun I0 => tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
      (fun i => basis i) I0 with hrmC
  set resid : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (4 + k) x :=
    Tdot - metricTrace0S2TensorInBasis (I := I) basis gInv
      (nablaKRm04Field (I := I) S t (k + 2) x) with hresid
  set residC : (Fin (4 + k) → Idx) → Real :=
    fun m => tensor0SComponent (I := I) resid (fun i => basis i) m with hresidC
  rw [hgInv]
  rw [ricReactionContract_delta_eq_compContract (Idx := Idx) ric rmC rmC]
  rw [inner0S_orthoBasis_eq_compContract (I := I) (S.base.metric t) basis horth
    resid (nablaKRm04Field (I := I) S t k x)]
  have hcombine :
      (∑ I0 : Fin (4 + k) → Idx, rmC I0 * ricStarArray ric rmC I0) +
          (∑ m : Fin (4 + k) → Idx, residC m * rmC m) =
        ∑ m : Fin (4 + k) → Idx,
          rmC m * combinedStarArray ric rmC residC m := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold combinedStarArray
    ring
  rw [show
      2 * (∑ I0 : Fin (4 + k) → Idx, rmC I0 * ricStarArray ric rmC I0) +
          2 * (∑ m : Fin (4 + k) → Idx, residC m * rmC m) =
        2 * ((∑ I0 : Fin (4 + k) → Idx, rmC I0 * ricStarArray ric rmC I0) +
              (∑ m : Fin (4 + k) → Idx, residC m * rmC m)) from by ring]
  rw [hcombine]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nablaKReactionAt_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nablaKReactionAt_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nablaKReactionAt_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaKReactionAt_eq

end ReactionBridge

end DifferentialGeometry.PDE.RicciFlow
