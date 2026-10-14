import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.PositiveRicciReaction
import Submission.DifferentialGeometry.Geometry.Operator.Heat.Tensor
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Equation.Lichnerowicz
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricVariation
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.Basic
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.Barrier.Basic
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.Reaction.Realization
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.FirstNull.Basic
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.FirstNull.Compactness
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.FirstNull.Signs
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.Regularity
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.Barrier.Certification
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.Weak
import Submission.DifferentialGeometry.Geometry.Curvature.Sections.Connection
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.RicciNorm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity
import Submission.DifferentialGeometry.Geometry.Coordinates.NablaComponents.TwoTensor
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Formula
import Submission.DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit
import Submission.DifferentialGeometry.Geometry.Metric.QuadraticBounds.TimeSlab
import Submission.DifferentialGeometry.Tensor.RSTensor.Algebra.Product
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Algebra.ContractionLeibniz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Tensor.RicciIdentity
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow


open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.BigOperators _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
private theorem real_smul0S_apply {s : ℕ} {x : M} (c : Real)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (v : Fin s → TangentSpace I x) :
    (c • A) v = c * A v := by
  rw [Tensor0SSpace.smul_apply, smul_eq_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.real_smul0S_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.real_smul0S_apply target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem tensor02_zero_apply {x : M}
    (A : Tensor02At (I := I) (M := M) x) :
    A (0 : Fin 2 → TangentSpace I x) = 0 := by
  with_unfolding_all exact A.map_coord_zero (0 : Fin 2) rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.tensor02_zero_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.tensor02_zero_apply target :: scope.openDecls } }

def ShiftBlockReactRealizes
    (G : Real -> SmoothRiemannianMetric I M)
    (N : TwoTensorReaction (I := I) (M := M))
    (delta t : Real)
    (A : RawTwoTensorField (I := I) (M := M)) {x : M}
    (v : TangentSpace I x) (a b c : Real) : Prop :=
  (N t (G t) A) x v v = shiftReactBlock3 delta a b c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ShiftBlockReactRealizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ShiftBlockReactRealizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ShiftBlockReactRealizes ``Submission.DifferentialGeometry.PDE.RicciFlow.ShiftBlockReactRealizes

omit [FiniteDimensional ℝ E] in
theorem shiftNullSymm_of_block
    {G : Real -> SmoothRiemannianMetric I M}
    {N : TwoTensorReaction (I := I) (M := M)}
    {U : Set Real} {delta : Real}
    (hdelta13 : delta < (1 : Real) / 3)
    (hreal :
      ∀ t, t ∈ U -> ∀ A : RawTwoTensorField (I := I) (M := M), ∀ x,
        TwoTensorSymmetricAt (I := I) (M := M) A x ->
        TwoTensorBilinearAt (I := I) (M := M) A x ->
        TwoTensorNonnegativeAt (I := I) (M := M) A x ->
        ∀ v : TangentSpace I x,
          A x v v = 0 ->
          ∃ a b c : Real,
            ShiftBlockReactRealizes (I := I) (M := M) G N delta t A v a b c) :
    TensorNullEigenvectorConditionSymm (I := I) (M := M) G N U := by
  intro t ht A x hsym hbilin hA v hv
  rcases hreal t ht A x hsym hbilin hA v hv with ⟨a, b, c, hreact⟩
  rw [hreact]
  exact shiftReactBlock3_nonneg delta a b c hdelta13

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shiftNullSymm_of_block then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shiftNullSymm_of_block"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shiftNullSymm_of_block ``Submission.DifferentialGeometry.PDE.RicciFlow.shiftNullSymm_of_block

def ShiftBlockReactRealizesScaled
    (G : Real -> SmoothRiemannianMetric I M)
    (N : TwoTensorReaction (I := I) (M := M))
    (delta t : Real)
    (A : RawTwoTensorField (I := I) (M := M)) {x : M}
    (v : TangentSpace I x) (r a b c : Real) : Prop :=
  (N t (G t) A) x v v = r ^ 2 * shiftReactBlock3 delta a b c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ShiftBlockReactRealizesScaled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ShiftBlockReactRealizesScaled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ShiftBlockReactRealizesScaled ``Submission.DifferentialGeometry.PDE.RicciFlow.ShiftBlockReactRealizesScaled

omit [FiniteDimensional ℝ E] in
theorem shiftNullSymm_of_block_scaled
    {G : Real -> SmoothRiemannianMetric I M}
    {N : TwoTensorReaction (I := I) (M := M)}
    {U : Set Real} {delta : Real}
    (hdelta13 : delta < (1 : Real) / 3)
    (hreal :
      ∀ t, t ∈ U -> ∀ A : RawTwoTensorField (I := I) (M := M), ∀ x,
        TwoTensorSymmetricAt (I := I) (M := M) A x ->
        TwoTensorBilinearAt (I := I) (M := M) A x ->
        TwoTensorNonnegativeAt (I := I) (M := M) A x ->
        ∀ v : TangentSpace I x,
          A x v v = 0 ->
          ∃ r a b c : Real,
            ShiftBlockReactRealizesScaled
              (I := I) (M := M) G N delta t A v r a b c) :
    TensorNullEigenvectorConditionSymm (I := I) (M := M) G N U := by
  intro t ht A x hsym hbilin hA v hv
  rcases hreal t ht A x hsym hbilin hA v hv with ⟨r, a, b, c, hreact⟩
  rw [hreact]
  exact mul_nonneg (sq_nonneg r)
    (shiftReactBlock3_nonneg delta a b c hdelta13)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shiftNullSymm_of_block_scaled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shiftNullSymm_of_block_scaled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shiftNullSymm_of_block_scaled ``Submission.DifferentialGeometry.PDE.RicciFlow.shiftNullSymm_of_block_scaled

def pinchTensor
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) (delta : Real) :
    TwoTensorFamily (I := I) (M := M) :=
  fun t x v w => Ric t x v w - delta * scalar t x * (G t).inner x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchTensor ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchTensor

def RicciPosInitial
    (Ric : TwoTensorFamily (I := I) (M := M)) : Prop :=
  ∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M) (Ric 0) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.RicciPosInitial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.RicciPosInitial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.RicciPosInitial ``Submission.DifferentialGeometry.PDE.RicciFlow.RicciPosInitial

def PinchInitial
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) : Prop :=
  ∃ delta : Real,
    0 < delta ∧ delta <= (1 : Real) / 3 ∧
      TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
        (pinchTensor (I := I) (M := M) G Ric scalar delta) 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PinchInitial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PinchInitial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PinchInitial ``Submission.DifferentialGeometry.PDE.RicciFlow.PinchInitial

def PinchInitialLt
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) : Prop :=
  ∃ delta : Real,
    0 < delta ∧ delta < (1 : Real) / 3 ∧
      TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
        (pinchTensor (I := I) (M := M) G Ric scalar delta) 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PinchInitialLt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PinchInitialLt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PinchInitialLt ``Submission.DifferentialGeometry.PDE.RicciFlow.PinchInitialLt

omit [FiniteDimensional ℝ E] in
theorem pinchInitial_of_lt
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (hinit : PinchInitialLt (I := I) (M := M) G Ric scalar) :
    PinchInitial (I := I) (M := M) G Ric scalar := by
  rcases hinit with ⟨delta, hdelta0, hdelta13, hpinch⟩
  exact ⟨delta, hdelta0, le_of_lt hdelta13, hpinch⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchInitial_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchInitial_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchInitial_of_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchInitial_of_lt

def InitialBounds
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) : Prop :=
  ∃ c C : Real,
    0 < c ∧ 0 < C ∧
      (∀ x v, c * (G 0).inner x v v <= Ric 0 x v v) ∧
      (∀ x, scalar 0 x <= C)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.InitialBounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.InitialBounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.InitialBounds ``Submission.DifferentialGeometry.PDE.RicciFlow.InitialBounds

def HasPositiveRicciLowerBound
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (ricMin : M -> Real) : Prop :=
  Continuous ricMin ∧
    (∀ x, 0 < ricMin x) ∧
    (∀ x v, ricMin x * (G 0).inner x v v <= Ric 0 x v v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HasPositiveRicciLowerBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HasPositiveRicciLowerBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HasPositiveRicciLowerBound ``Submission.DifferentialGeometry.PDE.RicciFlow.HasPositiveRicciLowerBound

structure MetricRicciData
    [SigmaCompactSpace M] [T2Space M]
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M)) where
  K : ConnectionCurvatureSections
    (I := I) (M := M)
    (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) (G 0)) (G 0)
  ricci_eq :
    ∀ x v w, Ric 0 x v w = K.ricci x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.MetricRicciData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.MetricRicciData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.MetricRicciData ``Submission.DifferentialGeometry.PDE.RicciFlow.MetricRicciData

def MetricRicciPos
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric) : Prop :=
  ∀ x v, v ≠ 0 -> 0 < D.K.ricci x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.MetricRicciPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.MetricRicciPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.MetricRicciPos ``Submission.DifferentialGeometry.PDE.RicciFlow.MetricRicciPos

def MetricRicciMin
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (ricMin : M -> Real) : Prop :=
  Continuous ricMin ∧
    (∀ x, 0 < ricMin x) ∧
    (∀ x v,
      ricMin x * (G 0).inner x v v <=
        D.K.ricci x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.MetricRicciMin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.MetricRicciMin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.MetricRicciMin ``Submission.DifferentialGeometry.PDE.RicciFlow.MetricRicciMin

abbrev UnitTangent (g : SmoothRiemannianMetric I M) : Type _ :=
  MetricUnitTangent (I := I) (M := M) g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.UnitTangent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.UnitTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.UnitTangent ``Submission.DifferentialGeometry.PDE.RicciFlow.UnitTangent

namespace UnitTangent

def base {g : SmoothRiemannianMetric I M}
    (p : UnitTangent (I := I) (M := M) g) : M :=
  p.1.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.UnitTangent.base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.UnitTangent.base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.UnitTangent.base ``Submission.DifferentialGeometry.PDE.RicciFlow.UnitTangent.base

def vec {g : SmoothRiemannianMetric I M}
    (p : UnitTangent (I := I) (M := M) g) :
    TangentSpace I (base (I := I) (M := M) p) :=
  p.1.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.UnitTangent.vec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.UnitTangent.vec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.UnitTangent.vec ``Submission.DifferentialGeometry.PDE.RicciFlow.UnitTangent.vec

omit [FiniteDimensional ℝ E] in
@[simp]
theorem unit {g : SmoothRiemannianMetric I M}
    (p : UnitTangent (I := I) (M := M) g) :
    g.inner (base (I := I) (M := M) p)
      (vec (I := I) (M := M) p) (vec (I := I) (M := M) p) = 1 :=
  p.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.UnitTangent.unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.UnitTangent.unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.UnitTangent.unit ``Submission.DifferentialGeometry.PDE.RicciFlow.UnitTangent.unit

omit [FiniteDimensional ℝ E] in
@[simp]
theorem base_mk {g : SmoothRiemannianMetric I M} {x : M}
    {v : TangentSpace I x} {hunit : g.inner x v v = 1} :
    base (I := I) (M := M)
      (⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩ :
        UnitTangent (I := I) (M := M) g) = x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.UnitTangent.base_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.UnitTangent.base_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.UnitTangent.base_mk ``Submission.DifferentialGeometry.PDE.RicciFlow.UnitTangent.base_mk

omit [FiniteDimensional ℝ E] in
@[simp]
theorem vec_mk {g : SmoothRiemannianMetric I M} {x : M}
    {v : TangentSpace I x} {hunit : g.inner x v v = 1} :
    vec (I := I) (M := M)
      (⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩ :
        UnitTangent (I := I) (M := M) g) = v :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.UnitTangent.vec_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.UnitTangent.vec_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.UnitTangent.vec_mk ``Submission.DifferentialGeometry.PDE.RicciFlow.UnitTangent.vec_mk

end UnitTangent

def UnitRicciLower
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric) (c : Real) : Prop :=
  0 < c ∧
    ∀ x (v : TangentSpace I x), (G 0).inner x v v = 1 ->
      c <= D.K.ricci x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.UnitRicciLower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.UnitRicciLower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.UnitRicciLower ``Submission.DifferentialGeometry.PDE.RicciFlow.UnitRicciLower

def unitRicEval
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (p : UnitTangent (I := I) (M := M) (G 0)) : Real :=
  D.K.ricci (UnitTangent.base (I := I) (M := M) p)
    (DifferentialGeometry.Geometry.Curvature.vec2 (I := I)
      (UnitTangent.vec (I := I) (M := M) p)
      (UnitTangent.vec (I := I) (M := M) p))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.unitRicEval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.unitRicEval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.unitRicEval ``Submission.DifferentialGeometry.PDE.RicciFlow.unitRicEval

theorem metricMin_unit
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {c : Real}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hlower : UnitRicciLower (I := I) (M := M) D c) :
    MetricRicciMin (I := I) (M := M) D (fun _ : M => c) := by
  rcases hlower with ⟨hc, hlower⟩
  refine ⟨continuous_const, fun _ => hc, ?_⟩
  intro x v
  by_cases hv : v = 0
  · subst v
    have hzero :
        D.K.ricci x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I)
          (0 : TangentSpace I x) (0 : TangentSpace I x)) = 0 := by
      have hzero' :
          D.K.ricci x (fun _ : Fin 2 => (0 : TangentSpace I x)) = 0 := by
        simpa [quad02] using
          DifferentialGeometry.tensor02_smul2 (I := I) (M := M) (D.K.ricci x)
            0 (0 : TangentSpace I x)
      have hvec :
          DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (0 : TangentSpace I x)
            (0 : TangentSpace I x) =
            (fun _ : Fin 2 => (0 : TangentSpace I x)) := by
        funext i
        simp [DifferentialGeometry.Geometry.Curvature.vec2]
      simpa [hvec] using hzero'
    simp [hzero]
  let r : Real := (G 0).inner x v v
  have hrpos : 0 < r := by
    exact (G 0).pos x v hv
  let s : Real := Real.sqrt r
  have hspos : 0 < s := Real.sqrt_pos.mpr hrpos
  have hsne : s ≠ 0 := ne_of_gt hspos
  let a : Real := s⁻¹
  let u : TangentSpace I x := a • v
  have hss : s * s = r := by
    simpa [sq] using (Real.sq_sqrt (le_of_lt hrpos))
  have haa : a * a * r = 1 := by
    have hmul : (s * s) * (s⁻¹ * s⁻¹) = 1 := by
      field_simp [hsne]
    calc
      a * a * r = (s⁻¹ * s⁻¹) * (s * s) := by
        rw [hss]
      _ = (s * s) * (s⁻¹ * s⁻¹) := by ring
      _ = 1 := hmul
  have hunit : (G 0).inner x u u = 1 := by
    calc
      (G 0).inner x u u = a * a * r := by
        simpa [u, r] using DifferentialGeometry.metric_smul2 (I := I) (M := M) (G 0) a v
      _ = 1 := haa
  have hRic_unit := hlower x u hunit
  have hRic_scale :
      D.K.ricci x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) u u) =
        a * a * D.K.ricci x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) := by
    have hscale' :
        D.K.ricci x (fun _ : Fin 2 => a • v) =
          a * a * D.K.ricci x (fun _ : Fin 2 => v) := by
      simpa [quad02] using
        DifferentialGeometry.tensor02_smul2 (I := I) (M := M)
          (D.K.ricci x) a v
    have hvecu :
        DifferentialGeometry.Geometry.Curvature.vec2 (I := I) u u = (fun _ : Fin 2 => u) := by
      funext i
      simp [DifferentialGeometry.Geometry.Curvature.vec2]
    have hvecv :
        DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v = (fun _ : Fin 2 => v) := by
      funext i
      simp [DifferentialGeometry.Geometry.Curvature.vec2]
    simpa [hvecu, hvecv, u] using hscale'
  have hineq :
      c <= a * a * D.K.ricci x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) := by
    simpa [hRic_scale] using hRic_unit
  have hs2_nonneg : 0 <= s * s := mul_nonneg (le_of_lt hspos) (le_of_lt hspos)
  have hmul := mul_le_mul_of_nonneg_left hineq hs2_nonneg
  have hcancel : (s * s) * (a * a *
        D.K.ricci x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)) =
      D.K.ricci x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) := by
    have hmul : (s * s) * (a * a) = 1 := by
      have hsa : s * a = 1 := by
        simp [a, hsne]
      calc
        (s * s) * (a * a) = (s * a) * (s * a) := by ring
        _ = 1 := by rw [hsa]; ring
    calc
      (s * s) * (a * a *
          D.K.ricci x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)) =
          ((s * s) * (a * a)) *
            D.K.ricci x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) := by ring
      _ = D.K.ricci x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) := by
        rw [hmul]
        ring
  have hleft : (s * s) * c = c * (G 0).inner x v v := by
    rw [hss]
    ring
  rwa [hcancel, hleft] at hmul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricMin_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricMin_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricMin_unit ``Submission.DifferentialGeometry.PDE.RicciFlow.metricMin_unit

theorem unitLower_of_compact_continuous
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D)
    (hcompact : IsCompact (Set.univ : Set (UnitTangent (I := I) (M := M) (G 0))))
    (hcont : Continuous (unitRicEval (I := I) (M := M) D)) :
    ∃ c : Real, UnitRicciLower (I := I) (M := M) D c := by
  classical
  by_cases hne : (Set.univ : Set (UnitTangent (I := I) (M := M) (G 0))).Nonempty
  · obtain ⟨p0, _hp0, hmin⟩ :=
      hcompact.exists_isMinOn hne hcont.continuousOn
    let c : Real :=
      unitRicEval (I := I) (M := M) D p0
    have hc : 0 < c := by
      let x0 := UnitTangent.base (I := I) (M := M) p0
      let v0 := UnitTangent.vec (I := I) (M := M) p0
      have hunit0 : (G 0).inner x0 v0 v0 = 1 := by
        simp [x0, v0, UnitTangent.unit]
      have hv0 : v0 ≠ 0 := by
        intro hz
        have hbad : (0 : Real) = 1 := by
          simp [hz] at hunit0
        norm_num at hbad
      exact hpos x0 v0 hv0
    refine ⟨c, hc, ?_⟩
    intro x v hunit
    let p : UnitTangent (I := I) (M := M) (G 0) :=
      ⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩
    exact (isMinOn_iff.mp hmin) p (Set.mem_univ p)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x v hunit
    exfalso
    exact hne ⟨⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩, Set.mem_univ _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.unitLower_of_compact_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.unitLower_of_compact_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.unitLower_of_compact_continuous ``Submission.DifferentialGeometry.PDE.RicciFlow.unitLower_of_compact_continuous

theorem unitTan_compact
    [CompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    IsCompact (Set.univ : Set (UnitTangent (I := I) (M := M) g)) := by
  exact metricUnit_compact (I := I) (M := M) g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.unitTan_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.unitTan_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.unitTan_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.unitTan_compact

theorem unitRic_cont
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric) :
    Continuous (unitRicEval (I := I) (M := M) D) := by
  refine (metricUnit_quadCont (I := I) (M := M) (G 0) D.K.ricci).congr ?_
  intro p
  dsimp [unitRicEval, quad02, UnitTangent.base, UnitTangent.vec,
    MetricUnitTangent.base, MetricUnitTangent.vec]
  congr 1
  funext i
  fin_cases i <;> simp [DifferentialGeometry.Geometry.Curvature.vec2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.unitRic_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.unitRic_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.unitRic_cont ``Submission.DifferentialGeometry.PDE.RicciFlow.unitRic_cont

theorem unitLower_pos
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D) :
    ∃ c : Real, UnitRicciLower (I := I) (M := M) D c := by
  exact unitLower_of_compact_continuous (I := I) (M := M) D hpos
    (unitTan_compact (I := I) (M := M) (G 0))
    (unitRic_cont (I := I) (M := M) D)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.unitLower_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.unitLower_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.unitLower_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.unitLower_pos

theorem metricMin_pos
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D) :
    ∃ ricMin : M -> Real,
      MetricRicciMin (I := I) (M := M) D ricMin := by
  rcases unitLower_pos (I := I) (M := M) D hpos with ⟨c, hc⟩
  exact ⟨fun _ : M => c, metricMin_unit (I := I) (M := M) D hc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricMin_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricMin_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricMin_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.metricMin_pos

theorem ricciPos_metric
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D) :
    RicciPosInitial (I := I) (M := M) Ric := by
  intro x v hv
  rw [D.ricci_eq x v v]
  exact hpos x v hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciPos_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciPos_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciPos_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciPos_metric

theorem ricMin_of_metric
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {ricMin : M -> Real}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hmin : MetricRicciMin (I := I) (M := M) D ricMin) :
    HasPositiveRicciLowerBound (I := I) (M := M) G Ric ricMin := by
  rcases hmin with ⟨hcont, hpos, hlower⟩
  refine ⟨hcont, hpos, ?_⟩
  intro x v
  rw [D.ricci_eq x v v]
  exact hlower x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricMin_of_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricMin_of_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricMin_of_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.ricMin_of_metric

def BoundsOfPosRic
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) : Prop :=
  RicciPosInitial (I := I) (M := M) Ric ->
    InitialBounds (I := I) (M := M) G Ric scalar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.BoundsOfPosRic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.BoundsOfPosRic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.BoundsOfPosRic ``Submission.DifferentialGeometry.PDE.RicciFlow.BoundsOfPosRic

omit [FiniteDimensional ℝ E] in
theorem ricPos_ricMin
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {ricMin : M -> Real}
    (hmin : HasPositiveRicciLowerBound (I := I) (M := M) G Ric ricMin) :
    RicciPosInitial (I := I) (M := M) Ric := by
  rcases hmin with ⟨_hcont, hpos, hlower⟩
  intro x v hv
  have hgpos : 0 < (G 0).inner x v v := (G 0).pos x v hv
  exact lt_of_lt_of_le (mul_pos (hpos x) hgpos) (hlower x v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricPos_ricMin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricPos_ricMin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricPos_ricMin ``Submission.DifferentialGeometry.PDE.RicciFlow.ricPos_ricMin

theorem scalarUpper_cont
    [CompactSpace M] [Nonempty M]
    {scalar : Real -> M -> Real}
    (hcont : Continuous (fun x : M => scalar 0 x)) :
    ∃ C : Real, 0 < C ∧ ∀ x, scalar 0 x <= C := by
  have hcompact : IsCompact (Set.univ : Set M) := isCompact_univ
  have hnonempty : (Set.univ : Set M).Nonempty := Set.univ_nonempty
  obtain ⟨x0, _hx0, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty hcont.continuousOn
  refine ⟨max 1 (scalar 0 x0), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left 1 (scalar 0 x0))
  · intro x
    exact le_trans (hmax (by simp : x ∈ (Set.univ : Set M)))
      (le_max_right 1 (scalar 0 x0))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalarUpper_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarUpper_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarUpper_cont ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarUpper_cont

omit [FiniteDimensional ℝ E] in
theorem bounds_ricMin
    [CompactSpace M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    (hmin : HasPositiveRicciLowerBound (I := I) (M := M) G Ric ricMin)
    (hscalar : ∃ C : Real, 0 < C ∧ ∀ x, scalar 0 x <= C) :
    InitialBounds (I := I) (M := M) G Ric scalar := by
  rcases hmin with ⟨hcont, hpos, hRicLower⟩
  rcases hscalar with ⟨C, hC, hScalarUpper⟩
  have hcompact : IsCompact (Set.univ : Set M) := isCompact_univ
  have hnonempty : (Set.univ : Set M).Nonempty := Set.univ_nonempty
  obtain ⟨x0, _hx0, hminOn⟩ :=
    hcompact.exists_isMinOn hnonempty hcont.continuousOn
  let c : Real := ricMin x0
  have hc : 0 < c := by
    dsimp [c]
    exact hpos x0
  have hc_le : ∀ x : M, c <= ricMin x := by
    intro x
    exact hminOn (by simp : x ∈ (Set.univ : Set M))
  refine ⟨c, C, hc, hC, ?_, hScalarUpper⟩
  intro x v
  have hg_nonneg : 0 <= (G 0).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact le_of_lt ((G 0).pos x v hv)
  exact le_trans (mul_le_mul_of_nonneg_right (hc_le x) hg_nonneg)
    (hRicLower x v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.bounds_ricMin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.bounds_ricMin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.bounds_ricMin ``Submission.DifferentialGeometry.PDE.RicciFlow.bounds_ricMin

omit [FiniteDimensional ℝ E] in
theorem boundsPos_ricMin
    [CompactSpace M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    (hmin : HasPositiveRicciLowerBound (I := I) (M := M) G Ric ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    BoundsOfPosRic (I := I) (M := M) G Ric scalar := by
  intro _hpos
  exact bounds_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (ricMin := ricMin) hmin
    (scalarUpper_cont (M := M) hscalar)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.boundsPos_ricMin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.boundsPos_ricMin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.boundsPos_ricMin ``Submission.DifferentialGeometry.PDE.RicciFlow.boundsPos_ricMin

omit [FiniteDimensional ℝ E] in
theorem pinchInitialLt_bounds
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (hbounds : InitialBounds (I := I) (M := M) G Ric scalar) :
    PinchInitialLt (I := I) (M := M) G Ric scalar := by
  rcases hbounds with ⟨c, C, hc, hC, hRicLower, hScalarUpper⟩
  let delta : Real := _root_.Min.min ((1 : Real) / 6) (c / C)
  have hsix_pos : 0 < (1 : Real) / 6 := by norm_num
  have hdiv_pos : 0 < c / C := div_pos hc hC
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact lt_min hsix_pos hdiv_pos
  have hdelta_le_six : delta <= (1 : Real) / 6 := by
    dsimp [delta]
    exact min_le_left _ _
  have hdelta_lt_third : delta < (1 : Real) / 3 := by
    nlinarith
  have hdelta_nonneg : 0 <= delta := le_of_lt hdelta_pos
  have hdelta_le_div : delta <= c / C := by
    dsimp [delta]
    exact min_le_right _ _
  have hdeltaC_le_c : delta * C <= c := by
    have hmul := mul_le_mul_of_nonneg_right hdelta_le_div (le_of_lt hC)
    have hcancel : c / C * C = c := div_mul_cancel₀ c (ne_of_gt hC)
    nlinarith
  refine ⟨delta, hdelta_pos, hdelta_lt_third, ?_⟩
  intro x v
  have hg_nonneg : 0 <= (G 0).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact le_of_lt ((G 0).pos x v hv)
  have hscalar_le : delta * scalar 0 x <= delta * C :=
    mul_le_mul_of_nonneg_left (hScalarUpper x) hdelta_nonneg
  have hscaled_le :
      delta * scalar 0 x * (G 0).inner x v v <= c * (G 0).inner x v v := by
    calc
      delta * scalar 0 x * (G 0).inner x v v
          = (delta * scalar 0 x) * (G 0).inner x v v := by ring
      _ <= (delta * C) * (G 0).inner x v v :=
          mul_le_mul_of_nonneg_right hscalar_le hg_nonneg
      _ <= c * (G 0).inner x v v :=
          mul_le_mul_of_nonneg_right hdeltaC_le_c hg_nonneg
  have hpinch_le : delta * scalar 0 x * (G 0).inner x v v <= Ric 0 x v v :=
    le_trans hscaled_le (hRicLower x v)
  simpa [pinchTensor, sub_nonneg] using hpinch_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_bounds

omit [FiniteDimensional ℝ E] in
theorem pinchInitial_of_bounds
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (hbounds : InitialBounds (I := I) (M := M) G Ric scalar) :
    PinchInitial (I := I) (M := M) G Ric scalar := by
  exact pinchInitial_of_lt (I := I) (M := M)
    (pinchInitialLt_bounds (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) hbounds)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchInitial_of_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchInitial_of_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchInitial_of_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchInitial_of_bounds

omit [FiniteDimensional ℝ E] in
theorem pinchInitialLt_of_pos
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (hpos : RicciPosInitial (I := I) (M := M) Ric)
    (hbounds : BoundsOfPosRic (I := I) (M := M) G Ric scalar) :
    PinchInitialLt (I := I) (M := M) G Ric scalar := by
  exact pinchInitialLt_bounds (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (hbounds hpos)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_of_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_of_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_of_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_of_pos

omit [FiniteDimensional ℝ E] in
theorem pinchInitial_of_pos
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (hpos : RicciPosInitial (I := I) (M := M) Ric)
    (hbounds : BoundsOfPosRic (I := I) (M := M) G Ric scalar) :
    PinchInitial (I := I) (M := M) G Ric scalar := by
  exact pinchInitial_of_lt (I := I) (M := M)
    (pinchInitialLt_of_pos (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) hpos hbounds)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchInitial_of_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchInitial_of_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchInitial_of_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchInitial_of_pos

omit [FiniteDimensional ℝ E] in
theorem pinchInitialLt_ricMin
    [CompactSpace M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    (hmin : HasPositiveRicciLowerBound (I := I) (M := M) G Ric ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    PinchInitialLt (I := I) (M := M) G Ric scalar :=
  pinchInitialLt_bounds (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar)
    (bounds_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) hmin
      (scalarUpper_cont (M := M) hscalar))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_ricMin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_ricMin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_ricMin ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_ricMin

omit [FiniteDimensional ℝ E] in
theorem pinchInitial_ricMin
    [CompactSpace M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    (hmin : HasPositiveRicciLowerBound (I := I) (M := M) G Ric ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    PinchInitial (I := I) (M := M) G Ric scalar :=
  pinchInitial_of_lt (I := I) (M := M)
    (pinchInitialLt_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) hmin hscalar)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchInitial_ricMin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchInitial_ricMin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchInitial_ricMin ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchInitial_ricMin

theorem pinchInitialLt_metric
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hmin : MetricRicciMin (I := I) (M := M) D ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    PinchInitialLt (I := I) (M := M) G Ric scalar :=
  pinchInitialLt_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (ricMin := ricMin)
    (ricMin_of_metric (I := I) (M := M) D hmin) hscalar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_metric

theorem pinchInitial_metric
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hmin : MetricRicciMin (I := I) (M := M) D ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    PinchInitial (I := I) (M := M) G Ric scalar :=
  pinchInitial_of_lt (I := I) (M := M)
    (pinchInitialLt_metric (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) D hmin hscalar)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchInitial_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchInitial_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchInitial_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchInitial_metric

theorem pinchInitialLt_pos
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    PinchInitialLt (I := I) (M := M) G Ric scalar := by
  rcases metricMin_pos (I := I) (M := M) D hpos with ⟨ricMin, hmin⟩
  exact pinchInitialLt_metric (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (ricMin := ricMin) D hmin hscalar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchInitialLt_pos

theorem pinchInitial_pos
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    PinchInitial (I := I) (M := M) G Ric scalar := by
  exact pinchInitial_of_lt (I := I) (M := M)
    (pinchInitialLt_pos (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) D hpos hscalar)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchInitial_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchInitial_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchInitial_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchInitial_pos

noncomputable def initialMetricRicciDataOfSolution
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    MetricRicciData (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) where
  K := metricCurvatureSections (I := I) (M := M) (S.base.metric 0)
  ricci_eq := by
    intro x v w
    simp [twoTensorSecToFamily, SolutionOn.ricci, SolutionFamily.ricci,
      metricCurvatureSections, DifferentialGeometry.Geometry.Curvature.metricCurvatureSections]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.initialMetricRicciDataOfSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.initialMetricRicciDataOfSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.initialMetricRicciDataOfSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.initialMetricRicciDataOfSolution

theorem initialMetricRicciDataOfSolution_positive
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hpos : RicciPosInitial (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci)) :
    MetricRicciPos (I := I) (M := M)
      (initialMetricRicciDataOfSolution (I := I) (M := M) S) := by
  intro x v hv
  have h := hpos x v hv
  rw [← (initialMetricRicciDataOfSolution (I := I) (M := M) S).ricci_eq x v v]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.initialMetricRicciDataOfSolution_positive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.initialMetricRicciDataOfSolution_positive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.initialMetricRicciDataOfSolution_positive ``Submission.DifferentialGeometry.PDE.RicciFlow.initialMetricRicciDataOfSolution_positive

theorem initial_scalar_curvature_continuous_of_solution
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (h0 : (0 : Real) ∈ D.carrier) :
    Continuous (fun x : M => S.scalar 0 x) := by
  have hmap : Continuous (fun y : M => ((0 : Real), y)) :=
    continuous_const.prodMk continuous_id
  have hmem : ∀ y : M, ((0 : Real), y) ∈ D.carrier ×ˢ (Set.univ : Set M) := by
    intro y
    exact ⟨h0, trivial⟩
  have hcomp := hS.scalarCont.comp_continuous hmap hmem
  simpa [Function.comp_def] using hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.initial_scalar_curvature_continuous_of_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.initial_scalar_curvature_continuous_of_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.initial_scalar_curvature_continuous_of_solution ``Submission.DifferentialGeometry.PDE.RicciFlow.initial_scalar_curvature_continuous_of_solution

def PinchPres
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) (T delta : Real) : Prop :=
  TwoTensorFamilyNonnegativeOn (I := I) (M := M)
    (pinchTensor (I := I) (M := M) G Ric scalar delta) (Set.Icc 0 T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PinchPres then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PinchPres"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PinchPres ``Submission.DifferentialGeometry.PDE.RicciFlow.PinchPres

theorem ricciCov1
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (S.base.connection t)
      (1 : WithTop ℕ∞) := by
  simpa [SolutionFamily.connection] using
    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) (S.base.metric t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciCov1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciCov1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciCov1 ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciCov1

theorem ricciCovInf
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (S.base.connection t)
      (∞ : WithTop ℕ∞) := by
  simpa [SolutionFamily.connection, metricCov] using
    metricCov_smooth (I := I) (M := M) (S.base.metric t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciCovInf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciCovInf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciCovInf ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciCovInf

theorem ricciMetricComp
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible
      (I := I) (S.base.connection t) (S.base.metric t) := by
  simpa [SolutionFamily.connection] using
    (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) (S.base.metric t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciMetricComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciMetricComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciMetricComp ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciMetricComp

noncomputable def ricciDerivsWeakMaximumPrinciple
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    CanonicalSpatialDerivs0S (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (S.base.connection t) (S.ricci t) :=
  CanonicalSpatialDerivs0S.ofSmoothConnection
    (E := E) (H := H) (I := I) (M := M)
    (S.base.connection t) (ricciCovInf (I := I) S t) (S.ricci t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciDerivsWeakMaximumPrinciple then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciDerivsWeakMaximumPrinciple"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciDerivsWeakMaximumPrinciple ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciDerivsWeakMaximumPrinciple

noncomputable def ricciNablaWeakMaximumPrinciple
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    TensorNabla1SecFamily (I := I) (M := M) :=
  fun t => (ricciDerivsWeakMaximumPrinciple (I := I) S t).nablaA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciNablaWeakMaximumPrinciple then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciNablaWeakMaximumPrinciple"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciNablaWeakMaximumPrinciple ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciNablaWeakMaximumPrinciple

noncomputable def ricciNabla2WeakMaximumPrinciple
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    TensorNabla2SecFamily (I := I) (M := M) :=
  fun t => (ricciDerivsWeakMaximumPrinciple (I := I) S t).nabla2A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciNabla2WeakMaximumPrinciple then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciNabla2WeakMaximumPrinciple"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciNabla2WeakMaximumPrinciple ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciNabla2WeakMaximumPrinciple

theorem ricciSpatialWeakMaximumPrinciple
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    TensorSpatialDerivs (I := I) (M := M)
      (fun t : Real => S.base.connection t) S.ricci
      (ricciNablaWeakMaximumPrinciple (I := I) S) (ricciNabla2WeakMaximumPrinciple (I := I) S) := by
  constructor
  · intro t
    simpa [ricciNablaWeakMaximumPrinciple, ricciDerivsWeakMaximumPrinciple] using
      (ricciDerivsWeakMaximumPrinciple (I := I) S t).first
  · intro t
    simpa [ricciNablaWeakMaximumPrinciple, ricciNabla2WeakMaximumPrinciple, ricciDerivsWeakMaximumPrinciple] using
      (ricciDerivsWeakMaximumPrinciple (I := I) S t).second

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciSpatialWeakMaximumPrinciple then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciSpatialWeakMaximumPrinciple"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciSpatialWeakMaximumPrinciple ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciSpatialWeakMaximumPrinciple

noncomputable def pinchSec
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) :
    TwoTensorSecFamily (I := I) (M := M) :=
  fun t =>
    letI := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2
    let hscalar :
        ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun x : M => delta * S.scalar t x) := by
      have hR :
          ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
            (fun x : M => S.scalar t x) := by
        simpa [SolutionOn.scalar, SolutionFamily.scalar] using
          metricScalar_smooth (I := I) (M := M) (S.base.metric t)
      have hmul : ((fun _ : M => delta) * fun x : M => S.scalar t x) =
          fun x : M => delta * S.scalar t x := by
        rfl
      rw [← hmul]
      exact contMDiff_const.mul hR
    let Ric : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2 := S.ricci t
    Ric + (-1 : Real) •
      tensor0SFieldSmulByFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
        (fun x : M => delta * S.scalar t x) hscalar
        (metricTensorField (I := I) (S.base.metric t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchSec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchSec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchSec ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchSec

noncomputable def pinchLipSec
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    TwoTensorSecFamily (I := I) (M := M) :=
  fun t =>
    letI := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2
    let hscalar :
        ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun x : M => S.scalar t x) := by
      simpa [SolutionOn.scalar, SolutionFamily.scalar] using
        metricScalar_smooth (I := I) (M := M) (S.base.metric t)
    (3 : Real) • S.ricci t + (-1 : Real) •
      tensor0SFieldSmulByFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
        (fun x : M => S.scalar t x) hscalar
        (metricTensorField (I := I) (S.base.metric t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchLipSec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchLipSec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchLipSec ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchLipSec

@[simp]
theorem pinchLipSec_apply
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v w : TangentSpace I x) :
    (pinchLipSec (I := I) S t x) (vec2 (I := I) v w) =
      3 * S.ricciAt t x (vec2 (I := I) v w) -
        S.scalar t x * (S.base.metric t).inner x v w := by
  simp only [pinchLipSec, tensor0SField_smulByFun_apply,
    ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_smul,
    Pi.smul_apply, Tensor0SSpace.add_apply,
    Tensor0SSpace.smul_apply, smul_eq_mul]
  rw [metricTensorField_apply]
  have h0 : vec2 (I := I) v w 0 = v := by
    unfold DifferentialGeometry.Geometry.Curvature.vec2
    simp
  have h1 : vec2 (I := I) v w 1 = w := by
    unfold DifferentialGeometry.Geometry.Curvature.vec2
    norm_num
  rw [h0, h1]
  simp [SolutionOn.ricciAt, SolutionFamily.ricciAt]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchLipSec_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchLipSec_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchLipSec_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchLipSec_apply

@[simp]
theorem pinchSec_eq
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) :
    twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta) =
      pinchTensor (I := I) (M := M) (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar delta := by
  funext t x v w
  simp only [pinchSec, pinchTensor, twoTensorSecToFamily,
    ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_smul,
    Pi.smul_apply, tensor0SField_smulByFun_apply,
    Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply,
    smul_eq_mul]
  change
    ((S.ricci t) x) (vec2 (I := I) v w) +
        (-1 : Real) * (delta * S.scalar t x *
          (metricTensorField (I := I) (S.base.metric t) x)
            (vec2 (I := I) v w)) =
      ((S.ricci t) x) (vec2 (I := I) v w) -
        delta * S.scalar t x * (S.base.metric t).inner x v w
  rw [metricTensorField_apply]
  have h0 : vec2 (I := I) v w 0 = v := by
    unfold DifferentialGeometry.Geometry.Curvature.vec2
    simp
  have h1 : vec2 (I := I) v w 1 = w := by
    unfold DifferentialGeometry.Geometry.Curvature.vec2
    norm_num
  rw [h0, h1]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchSec_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchSec_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchSec_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchSec_eq

theorem pinchSec_at_trace
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (delta t : Real) (x : M) :
    (pinchSec (I := I) S delta) t x =
      S.ricci t x -
        (delta *
          metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x)) •
          metricTensorField (I := I) (S.base.metric t) x := by
  have hscalar :
      S.scalar t x =
        metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) := by
    simp [SolutionOn.scalar_eq_metricTrace, SolutionOn.ricci,
      SolutionFamily.ricci, SolutionOn.ricciAt, SolutionFamily.ricciAt]
  apply ContinuousMultilinearMap.ext
  intro slots
  simp only [pinchSec, tensor0SField_smulByFun_apply,
    ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_smul,
    Pi.smul_apply]
  rw [hscalar]
  simp [sub_eq_add_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchSec_at_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchSec_at_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchSec_at_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchSec_at_trace

theorem ricciAt_symm
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) :
    DifferentialGeometry.Geometry.Curvature.RicciSymAt (I := I) (S.ricciAt t x) := by
  classical
  let basis : Module.Basis (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E)
      Real (TangentSpace I x) :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x
  let gInv :
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real := fun k l =>
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent
      (I := I) (S.base.metric t) x k l (extChartAt I x x)
  have hinv :
      MetricInverseInBasis (I := I) (S.base.metric t) x basis gInv := by
    simpa [basis, gInv] using
      Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) (S.base.metric t) x
  exact DifferentialGeometry.Geometry.Curvature.ricciSym_of_basis
    (I := I) basis (S.ricciAt t x)
    (fun i j => by
      simpa [SolutionOn.ricciAt, SolutionFamily.ricciAt, basis, gInv] using
        DifferentialGeometry.Geometry.Curvature.metricRicciSymm (I := I) (M := M) (S.base.metric t)
          basis gInv hinv i j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciAt_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciAt_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciAt_symm ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciAt_symm

theorem ricciSec_symm
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (U : Set Real) :
    TwoTensorFamilySymmetricOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) U := by
  intro t _ht x v w
  simpa [twoTensorSecToFamily, SolutionOn.ricci, SolutionFamily.ricci,
    SolutionOn.ricciAt, SolutionFamily.ricciAt] using
    ricciAt_symm (I := I) S t x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciSec_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciSec_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciSec_symm ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciSec_symm

theorem pinchSec_symm
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) (U : Set Real) :
    TwoTensorFamilySymmetricOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta)) U := by
  intro t _ht x v w
  rw [pinchSec_eq (I := I) S delta]
  simp only [pinchTensor]
  have hRic := ricciAt_symm (I := I) S t x v w
  have hg := (S.base.metric t).symm x v w
  simpa [twoTensorSecToFamily, SolutionOn.ricci, SolutionFamily.ricci,
    SolutionOn.ricciAt, SolutionFamily.ricciAt, hg] using congrArg
      (fun z => z - delta * S.scalar t x * (S.base.metric t).inner x w v)
      hRic

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchSec_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchSec_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchSec_symm ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchSec_symm

theorem shiftNRaw_pinch
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta t : Real)
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    (shiftNRaw (I := I) (M := M) delta t g
        (twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta) t)) x v w =
      shiftNAt (I := I) (M := M) delta t g x
        ((pinchSec (I := I) S delta) t x)
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w) := by
  let Araw : RawTwoTensorField (I := I) (M := M) :=
    twoTensorSecToFamily (I := I) (M := M)
      (pinchSec (I := I) S delta) t
  have hbilin : TwoTensorBilinearAt (I := I) (M := M) Araw x := by
    simpa [Araw] using
      twoTensorSecToFamily_bilin (I := I) (M := M)
        (pinchSec (I := I) S delta) t x
  have hsym : TwoTensorSymmetricAt (I := I) (M := M) Araw x := by
    simpa [Araw] using
      (pinchSec_symm (I := I) S delta Set.univ) t (by simp) x
  rw [show
      twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta) t = Araw by rfl]
  rw [shiftNRaw, Tensor02ReactionAt.toRawSymm_eval_of_bilin
    (I := I) (M := M) (shiftNAt (I := I) (M := M) delta)
    t g Araw x hbilin]
  have hrealSec :
      Tensor02RealizesRawAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) Araw) x
        ((pinchSec (I := I) S delta) t x) := by
    intro X Y
    rw [rawSym2_eq_of_symm (I := I) (M := M) hsym X Y]
    rfl
  have hrealBundled :
      Tensor02RealizesRawAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) Araw) x
        (tensor02OfRawAt (I := I) (M := M)
          (rawSym2 (I := I) (M := M) Araw) x
          (rawSym2_bilin (I := I) (M := M) hbilin)) :=
    tensor02OfRawAt_realizes (I := I) (M := M)
      (rawSym2 (I := I) (M := M) Araw) x
      (rawSym2_bilin (I := I) (M := M) hbilin)
  have hT :
      tensor02OfRawAt (I := I) (M := M)
          (rawSym2 (I := I) (M := M) Araw) x
          (rawSym2_bilin (I := I) (M := M) hbilin) =
        (pinchSec (I := I) S delta) t x :=
    tensor02_realizes_ext (I := I) (M := M) hrealBundled hrealSec
  rw [hT]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shiftNRaw_pinch then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shiftNRaw_pinch"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shiftNRaw_pinch ``Submission.DifferentialGeometry.PDE.RicciFlow.shiftNRaw_pinch

theorem shiftNRaw_barrier
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (G : Real -> SmoothRiemannianMetric I M)
    (delta epsilon d t0 t : Real) (x : M)
    (v w : TangentSpace I x) :
    (shiftNRaw (I := I) (M := M) delta t (G t)
        (tensorBarrierFamily (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M)
            (pinchSec (I := I) S delta))
          epsilon d t0 t)) x v w =
      shiftNAt (I := I) (M := M) delta t (G t) x
        (((pinchSec (I := I) S delta) t x) +
          (epsilon * (d + t - t0)) •
            metricTensorField (I := I) (G t) x)
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w) := by
  let Araw : RawTwoTensorField (I := I) (M := M) :=
    tensorBarrierFamily (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M)
        (pinchSec (I := I) S delta))
      epsilon d t0 t
  have hbaseBilin :
      TwoTensorBilinearAt (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta) t) x := by
    exact twoTensorSecToFamily_bilin (I := I) (M := M)
      (pinchSec (I := I) S delta) t x
  have hbilin : TwoTensorBilinearAt (I := I) (M := M) Araw x := by
    simpa [Araw] using
      barrierBilinearAt (I := I) (M := M)
        (G := G)
        (S := twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta))
        (epsilon := epsilon) (delta := d) (t0 := t0) (t := t)
        (x := x) hbaseBilin
  have hbaseSymm :
      TwoTensorSymmetricAt (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta) t) x := by
    exact (pinchSec_symm (I := I) S delta Set.univ) t (by simp) x
  have hsym : TwoTensorSymmetricAt (I := I) (M := M) Araw x := by
    simpa [Araw] using
      barrierSymmAt (I := I) (M := M)
        (G := G)
        (S := twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta))
        (epsilon := epsilon) (delta := d) (t0 := t0) (t := t)
        (x := x) hbaseSymm
  rw [show
      tensorBarrierFamily (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M)
            (pinchSec (I := I) S delta))
          epsilon d t0 t = Araw by rfl]
  rw [shiftNRaw, Tensor02ReactionAt.toRawSymm_eval_of_bilin
    (I := I) (M := M) (shiftNAt (I := I) (M := M) delta)
    t (G t) Araw x hbilin]
  let Bsec : TwoTensorSecFamily (I := I) (M := M) :=
    tensorBarrierSecFamily (I := I) (M := M) G
      (pinchSec (I := I) S delta) epsilon d t0
  have hrealSec :
      Tensor02RealizesRawAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) Araw) x (Bsec t x) := by
    intro X Y
    rw [rawSym2_eq_of_symm (I := I) (M := M) hsym X Y]
    change Bsec t x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) X Y) = Araw x X Y
    rw [show Bsec t x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) X Y) =
        twoTensorSecToFamily (I := I) (M := M) Bsec t x X Y by rfl]
    simpa [Araw, Bsec] using
      tensorBarrierSec_apply (I := I) (M := M) G
        (pinchSec (I := I) S delta) epsilon d t0 t x X Y
  have hrealBundled :
      Tensor02RealizesRawAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) Araw) x
        (tensor02OfRawAt (I := I) (M := M)
          (rawSym2 (I := I) (M := M) Araw) x
          (rawSym2_bilin (I := I) (M := M) hbilin)) :=
    tensor02OfRawAt_realizes (I := I) (M := M)
      (rawSym2 (I := I) (M := M) Araw) x
      (rawSym2_bilin (I := I) (M := M) hbilin)
  have hT :
      tensor02OfRawAt (I := I) (M := M)
          (rawSym2 (I := I) (M := M) Araw) x
          (rawSym2_bilin (I := I) (M := M) hbilin) =
        Bsec t x :=
    tensor02_realizes_ext (I := I) (M := M) hrealBundled hrealSec
  rw [hT]
  simp [Bsec, tensorBarrierSecFamily]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shiftNRaw_barrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shiftNRaw_barrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shiftNRaw_barrier ``Submission.DifferentialGeometry.PDE.RicciFlow.shiftNRaw_barrier

theorem shiftNRaw_barrier_diff
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {delta epsilon d t0 t : Real} {x : M}
    (hdelta : delta < (1 : Real) / 3)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (v : TangentSpace I x) :
    (shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
        (tensorBarrierFamily (I := I) (M := M)
          (fun s : Real => S.base.metric s)
          (twoTensorSecToFamily (I := I) (M := M)
            (pinchSec (I := I) S delta))
          epsilon d t0 t)) x v v -
      (shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta) t)) x v v =
        ((epsilon * (d + t - t0)) / (1 - 3 * delta)) *
          (2 * delta - 1) *
          (pinchLipSec (I := I) S t x) (vec2 (I := I) v v) := by
  let _ := (inferInstance : (SigmaCompactSpace M))
  let c : Real := epsilon * (d + t - t0)
  have hden : (1 : Real) - 3 * delta ≠ 0 := by nlinarith
  rw [shiftNRaw_barrier (I := I) (M := M) S
      (fun s : Real => S.base.metric s) delta epsilon d t0 t x v v]
  rw [shiftNRaw_pinch (I := I) (M := M) S delta t
      (S.base.metric t) x v v]
  have hdiff :=
    shiftNAt_add_g_quad (I := I) (M := M)
      (delta := delta) (c := c) (t := t) (g := S.base.metric t)
      (x := x) hden hdim ((pinchSec (I := I) S delta) t x) v
  have hcoeff :
      ((3 : Real) •
          shiftRic3At (I := I) (M := M) delta (S.base.metric t)
            ((pinchSec (I := I) S delta) t x) -
          metricTracePair0SAt (I := I) (S.base.metric t)
              (shiftRic3At (I := I) (M := M) delta (S.base.metric t)
                ((pinchSec (I := I) S delta) t x)) •
            metricTensorField (I := I) (S.base.metric t) x)
        (vec2 (I := I) v v) =
        (pinchLipSec (I := I) S t x) (vec2 (I := I) v v) := by
    have tensor_zero
        (T : Tensor02At (I := I) (M := M) x) :
        T (vec2 (I := I) (0 : TangentSpace I x) 0) = 0 := by
      have h := tensor02_smul2 (I := I) (M := M) T
        (0 : Real) (0 : TangentSpace I x)
      simpa [quad02, vec2_self_eq_const] using h
    by_cases hv : v = 0
    · subst v
      simp [tensor_zero]
    · obtain ⟨nb⟩ :=
        exists_nullOrthonormalBasis3At (I := I) (M := M)
          (S.base.metric t) (x := x) (v := v) hdim hv
      have hpinch := pinchSec_at_trace (I := I) (M := M) S delta t x
      have hshift :=
        shiftRic3At_pinch (I := I) (M := M) nb.basis nb.orthonormal
          hden (S.ricci t x)
      rw [← hpinch] at hshift
      have htrace :
          metricTracePair0SAt (I := I) (S.base.metric t)
              (shiftRic3At (I := I) (M := M) delta (S.base.metric t)
                ((pinchSec (I := I) S delta) t x)) =
            S.scalar t x := by
        rw [hshift]
        simp [SolutionOn.scalar_eq_metricTrace, SolutionOn.ricci,
          SolutionFamily.ricci, SolutionOn.ricciAt, SolutionFamily.ricciAt]
      rw [hshift]
      rw [pinchLipSec_apply]
      simp only [Tensor0SSpace.sub_apply,
        Tensor0SSpace.smul_apply, smul_eq_mul]
      rw [metricTensorField_apply]
      have h0 : vec2 (I := I) v v 0 = v := by
        unfold DifferentialGeometry.Geometry.Curvature.vec2
        simp
      have h1 : vec2 (I := I) v v 1 = v := by
        unfold DifferentialGeometry.Geometry.Curvature.vec2
        norm_num
      rw [h0, h1]
      have hscalar :
          S.scalar t x =
            metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) := by
        simp [SolutionOn.scalar_eq_metricTrace, SolutionOn.ricci,
          SolutionFamily.ricci, SolutionOn.ricciAt, SolutionFamily.ricciAt]
      rw [hscalar]
      simp [SolutionOn.ricciAt, SolutionFamily.ricciAt]
  rw [hcoeff] at hdiff
  simpa [c] using hdiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shiftNRaw_barrier_diff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shiftNRaw_barrier_diff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shiftNRaw_barrier_diff ``Submission.DifferentialGeometry.PDE.RicciFlow.shiftNRaw_barrier_diff

private theorem ricciEnd_repr_basis
    {g : SmoothRiemannianMetric I M} {x : M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Ric : Tensor02At (I := I) (M := M) x)
    (i k : Idx) :
    basis.repr (DifferentialGeometry.Geometry.Curvature.ricciEndAt (I := I) g Ric (basis i)) k =
      ∑ a : Idx, gInv k a * Ric (vec2 (I := I) (basis i) (basis a)) := by
  rw [basis_repr_eq_sum_inv_inner (I := I) g x basis gInv hinv]
  simp [DifferentialGeometry.Geometry.Curvature.ricciEnd_inner]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciEnd_repr_basis
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.ricciEnd_repr_basis target :: scope.openDecls } }

private theorem ricciQuadAt_comp_basis
    {g : SmoothRiemannianMetric I M} {x : M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Ric : Tensor02At (I := I) (M := M) x)
    (i j : Idx) :
    ricciQuadAt (I := I) (M := M) g Ric
        (vec2 (I := I) (basis i) (basis j)) =
      DifferentialGeometry.Geometry.Curvature.ricciQuadraticAt (I := I) basis gInv Ric i j := by
  rw [ricciQuadAt_apply]
  have hEnd :
      DifferentialGeometry.Geometry.Curvature.ricciEndAt (I := I) g Ric (basis i) =
        ∑ k : Idx,
          basis.repr (DifferentialGeometry.Geometry.Curvature.ricciEndAt (I := I) g Ric (basis i))
            k •
            basis k := by
    exact (basis.sum_repr
      (DifferentialGeometry.Geometry.Curvature.ricciEndAt (I := I) g Ric (basis i))).symm
  rw [hEnd]
  rw [show
      vec2 (I := I)
          (∑ k : Idx,
            basis.repr (DifferentialGeometry.Geometry.Curvature.ricciEndAt (I := I) g Ric
              (basis i)) k •
              basis k)
          (basis j) =
        Fin.cons
          (∑ k : Idx,
            basis.repr (DifferentialGeometry.Geometry.Curvature.ricciEndAt (I := I) g Ric
              (basis i)) k •
              basis k)
          (fun _ : Fin 1 => basis j) by
    funext q
    fin_cases q <;> rfl]
  rw [← DifferentialGeometry.Tensor.RSTensor.metricTrace_tensor0S_curry_apply_cons
    (I := I) (M := M) (s := 1) Ric
      (∑ k : Idx,
        basis.repr (DifferentialGeometry.Geometry.Curvature.ricciEndAt (I := I) g Ric (basis i)) k
          •
          basis k)
      (fun _ : Fin 1 => basis j)]
  change
    ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x Ric)
        (∑ k : Idx,
          basis.repr (DifferentialGeometry.Geometry.Curvature.ricciEndAt (I := I) g Ric (basis i))
            k •
            basis k))
        (fun _ : Fin 1 => basis j) =
      DifferentialGeometry.Geometry.Curvature.ricciQuadraticAt (I := I) basis gInv Ric i j
  rw [map_sum]
  simp [DifferentialGeometry.Tensor.RSTensor.metricTrace_tensor0S_curry_apply_cons,
    finCons1_eq_vec2,
    ricciEnd_repr_basis (I := I) (M := M) basis gInv hinv Ric,
    DifferentialGeometry.Geometry.Curvature.ricciQuadraticAt,
      DifferentialGeometry.Geometry.Curvature.oneUp02CompAt, smul_eq_mul, mul_comm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciQuadAt_comp_basis
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.ricciQuadAt_comp_basis target :: scope.openDecls } }

private theorem rm04ContrAt_comp_basis
    {g : SmoothRiemannianMetric I M} {x : M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (Ric : Tensor02At (I := I) (M := M) x)
    (i j : Idx) :
    rm04RicciContrAt (I := I) (M := M) g Rm04 Ric
        (vec2 (I := I) (basis i) (basis j)) =
      DifferentialGeometry.Geometry.Curvature.rm04RicciContractionAt (I := I) basis Rm04 gInv Ric i
        j := by
  have hInv : ∀ a b : Idx, gInv a b = gInv b a :=
    Tensor0SBundle.MetricInverseInBasis.symmetric (I := I) (M := M) g x basis gInv hinv
  rw [rm04RicciContrAt_apply]
  rw [inner0S_two_eq_coord (I := I) g x basis gInv hinv]
  unfold DifferentialGeometry.Geometry.Curvature.rm04RicciContractionAt
    DifferentialGeometry.Geometry.Curvature.raised02CompAt
  change
    (∑ a : Idx, ∑ b : Idx, ∑ k : Idx, ∑ l : Idx,
        (gInv a k * gInv b l *
          Ric (vec2 (I := I) (basis a) (basis b))) *
            rm04Mid02At (I := I) (M := M) Rm04 (basis i) (basis j)
              (vec2 (I := I) (basis k) (basis l))) =
      ∑ k : Idx, ∑ l : Idx,
        Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          (∑ a : Idx, ∑ b : Idx,
            gInv k a * gInv l b *
              Ric (vec2 (I := I) (basis a) (basis b)))
  have hmid : ∀ k l : Idx,
      rm04Mid02At (I := I) (M := M) Rm04 (basis i) (basis j)
          (vec2 (I := I) (basis k) (basis l)) =
        Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) := by
    intro k l
    exact rm04Mid02At_apply (I := I) (M := M) Rm04
      (basis i) (basis j) (basis k) (basis l)
  calc
    (∑ a : Idx, ∑ b : Idx, ∑ k : Idx, ∑ l : Idx,
        (gInv a k * gInv b l *
          Ric (vec2 (I := I) (basis a) (basis b))) *
            rm04Mid02At (I := I) (M := M) Rm04 (basis i) (basis j)
              (vec2 (I := I) (basis k) (basis l))) =
      ∑ a : Idx, ∑ b : Idx, ∑ k : Idx, ∑ l : Idx,
        (gInv a k * gInv b l *
          Ric (vec2 (I := I) (basis a) (basis b))) *
            Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hmid k l]
    _ =
      ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, ∑ b : Idx,
        (gInv a k * gInv b l *
          Ric (vec2 (I := I) (basis a) (basis b))) *
            Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) := by
        calc
          (∑ a : Idx, ∑ b : Idx, ∑ k : Idx, ∑ l : Idx,
              (gInv a k * gInv b l *
                Ric (vec2 (I := I) (basis a) (basis b))) *
                  Rm04 (vec4 (I := I) (basis i) (basis k) (basis j)
                    (basis l))) =
            ∑ a : Idx, ∑ k : Idx, ∑ b : Idx, ∑ l : Idx,
              (gInv a k * gInv b l *
                Ric (vec2 (I := I) (basis a) (basis b))) *
                  Rm04 (vec4 (I := I) (basis i) (basis k) (basis j)
                    (basis l)) := by
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.sum_comm]
          _ = ∑ k : Idx, ∑ a : Idx, ∑ b : Idx, ∑ l : Idx,
              (gInv a k * gInv b l *
                Ric (vec2 (I := I) (basis a) (basis b))) *
                  Rm04 (vec4 (I := I) (basis i) (basis k) (basis j)
                    (basis l)) := by
              rw [Finset.sum_comm]
          _ = ∑ k : Idx, ∑ a : Idx, ∑ l : Idx, ∑ b : Idx,
              (gInv a k * gInv b l *
                Ric (vec2 (I := I) (basis a) (basis b))) *
                  Rm04 (vec4 (I := I) (basis i) (basis k) (basis j)
                    (basis l)) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.sum_comm]
          _ = ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, ∑ b : Idx,
              (gInv a k * gInv b l *
                Ric (vec2 (I := I) (basis a) (basis b))) *
                  Rm04 (vec4 (I := I) (basis i) (basis k) (basis j)
                    (basis l)) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.sum_comm]
    _ = ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, ∑ b : Idx,
        Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          (gInv k a * gInv l b *
            Ric (vec2 (I := I) (basis a) (basis b))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun l _ => ?_
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hInv a k, hInv b l]
        ring
    _ = ∑ k : Idx, ∑ l : Idx,
        Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          (∑ a : Idx, ∑ b : Idx,
            gInv k a * gInv l b *
              Ric (vec2 (I := I) (basis a) (basis b))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.rm04ContrAt_comp_basis
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.rm04ContrAt_comp_basis target :: scope.openDecls } }

private theorem sum_coord_react_cancel
    {Idx : Type*} [Fintype Idx]
    (c L R Q : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx,
        c i j * ((-2 : Real) * R i j - 2 * Q i j)) =
      (∑ i : Idx, ∑ j : Idx,
        c i j * (L i j - 2 * R i j - 2 * Q i j)) -
        ∑ i : Idx, ∑ j : Idx, c i j * L i j := by
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  ring_nf
  simp_rw [Finset.sum_neg_distrib]
  abel

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.sum_coord_react_cancel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.sum_coord_react_cancel target :: scope.openDecls } }

private theorem standardRmOfRic3_signed_contr
    (Ric : Fin 3 -> Fin 3 -> Real)
    (i j : Fin 3) :
    (∑ k : Fin 3, ∑ l : Fin 3,
        standardRmOfRic3 (fun a b : Fin 3 => -Ric a b) i k j l * Ric k l) =
      -∑ k : Fin 3, ∑ l : Fin 3,
        standardRmOfRic3 Ric i k j l * Ric k l := by
  fin_cases i <;> fin_cases j <;>
    simp [standardRmOfRic3, ricciScal3, DifferentialGeometry.Geometry.Curvature.delta3,
      Fin.sum_univ_three] <;>
    ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.standardRmOfRic3_signed_contr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.standardRmOfRic3_signed_contr target :: scope.openDecls } }

private theorem actualRm04_comp_signed
    {g : SmoothRiemannianMetric I M} {x : M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt (I := I) g x basis)
    (htrace :
      DifferentialGeometry.Geometry.Curvature.RiemannFromRicci3DTraceDataAt
        (I := I) g (-Ric) (-(metricTracePair0SAt (I := I) g Ric))
        Rm04 basis)
    (i k j l : Fin 3) :
    Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) =
      standardRmOfRic3
        (fun a b : Fin 3 =>
          -Ric (vec2 (I := I) (basis a) (basis b))) i k j l := by
  have hformula :=
    DifferentialGeometry.Geometry.Curvature.rm04Comp_displayedRiemannFromRicci3D_at
      (I := I) htrace i k l j
  have htraceRic :
      metricTracePair0SAt (I := I) g Ric =
        ricciScal3
          (fun a b : Fin 3 =>
            Ric (vec2 (I := I) (basis a) (basis b))) :=
    metricTrace_comp_orthonormal (I := I) (M := M) basis horth Ric
  rw [rm04CompAt_apply] at hformula
  rw [hformula, htraceRic]
  simp only [ricciCompAt_apply, Tensor0SSpace.neg_apply,
    standardRmOfRic3, ricciScal3, Finset.sum_neg_distrib]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.actualRm04_comp_signed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.actualRm04_comp_signed target :: scope.openDecls } }

private theorem actualRm04Contr_eq_canonical
    {g : SmoothRiemannianMetric I M} {x : M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt (I := I) g x basis)
    (htrace :
      DifferentialGeometry.Geometry.Curvature.RiemannFromRicci3DTraceDataAt
        (I := I) g (-Ric) (-(metricTracePair0SAt (I := I) g Ric))
        Rm04 basis)
    (i j : Fin 3) :
    (∑ k : Fin 3, ∑ l : Fin 3,
        Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          Ric (vec2 (I := I) (basis k) (basis l))) =
      -∑ k : Fin 3, ∑ l : Fin 3,
        rm04OfRic3At (I := I) (M := M) g Ric
            (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          Ric (vec2 (I := I) (basis k) (basis l)) := by
  let RicC : Fin 3 -> Fin 3 -> Real :=
    fun a b => Ric (vec2 (I := I) (basis a) (basis b))
  calc
    (∑ k : Fin 3, ∑ l : Fin 3,
        Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          Ric (vec2 (I := I) (basis k) (basis l))) =
      ∑ k : Fin 3, ∑ l : Fin 3,
        standardRmOfRic3 (fun a b : Fin 3 => -RicC a b) i k j l *
          RicC k l := by
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun l _ => ?_
        exact congrArg (fun z : Real => z * RicC k l)
          (actualRm04_comp_signed (I := I) (M := M) horth htrace i k j l)
    _ =
      -∑ k : Fin 3, ∑ l : Fin 3,
        standardRmOfRic3 RicC i k j l * RicC k l := by
        exact standardRmOfRic3_signed_contr RicC i j
    _ =
      -∑ k : Fin 3, ∑ l : Fin 3,
        rm04OfRic3At (I := I) (M := M) g Ric
            (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          Ric (vec2 (I := I) (basis k) (basis l)) := by
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun l _ => ?_
        exact congrArg
          (fun z : Real => z * Ric (vec2 (I := I) (basis k) (basis l)))
          (rm04OfRic3At_comp_orthonormal
            (I := I) (M := M) basis horth Ric i k j l).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.actualRm04Contr_eq_canonical
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.actualRm04Contr_eq_canonical target :: scope.openDecls } }

theorem traceData_metricTrace
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt
      (I := I) (S.base.metric t) x basis) :
    DifferentialGeometry.Geometry.Curvature.RiemannFromRicci3DTraceDataAt
      (I := I) (S.base.metric t) (-(S.ricci t x))
      (-(metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x)))
      (S.base.rm04 t x) basis := by
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M)
        (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (1 : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) (S.base.metric t)
  have hRm13 :
      DifferentialGeometry.Geometry.Curvature.rm13RealizesConnection (I := I)
        (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm13 t) := by
    change DifferentialGeometry.Geometry.Curvature.rm13RealizesConnection (I := I)
      (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
        (S.base.metric t))
      (metricCurvatureSections (I := I) (M := M) (S.base.metric t)).rm13
    exact (metricCurvatureSections (I := I) (M := M) (S.base.metric t)).rm13Realizes
  have hRm04 :
      DifferentialGeometry.Geometry.Curvature.rm04RealizesConnection (I := I) (S.base.metric t)
        (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm04 t) := by
    change DifferentialGeometry.Geometry.Curvature.rm04RealizesConnection (I := I)
      (S.base.metric t)
      (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
        (S.base.metric t))
      (metricCurvatureSections (I := I) (M := M) (S.base.metric t)).rm04
    exact (metricCurvatureSections (I := I) (M := M) (S.base.metric t)).rm04Realizes
  have hRic13 :
      S.ricci t x =
        DifferentialGeometry.Geometry.Curvature.ricciFromRm13At (I := I) (M := M)
          (S.base.rm13 t x) := by
    change (metricCurvatureSections (I := I) (M := M) (S.base.metric t)).ricci x =
      DifferentialGeometry.Geometry.Curvature.ricciFromRm13At (I := I) (M := M)
        ((metricCurvatureSections (I := I) (M := M) (S.base.metric t)).rm13 x)
    exact (metricCurvatureSections (I := I) (M := M) (S.base.metric t)).ricciRealizes x
  have hLowerAt :
      DifferentialGeometry.Geometry.Curvature.Rm04LowersRm13At (I := I) (S.base.metric t) x
        (S.base.rm13 t x) (S.base.rm04 t x) :=
    DifferentialGeometry.Geometry.Curvature.rm04LowersRm13At_of_realizes
      (I := I) (g := S.base.metric t)
      (cov := DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
        (S.base.metric t))
      (Rm13 := S.base.rm13 t) (Rm04 := S.base.rm04 t)
      hRm13 hRm04 x
  have hcurv :
      DifferentialGeometry.Geometry.Curvature.AlgebraicCurvatureSymmetries3
        (DifferentialGeometry.Geometry.Curvature.standardRmCompAt
          (I := I) basis (S.base.rm04 t x)) :=
    algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes
      (I := I) (g := S.base.metric t)
      (Rm04 := S.base.rm04 t) (hRm04 := hRm04) basis
  have hRicFirst :
      DifferentialGeometry.Geometry.Curvature.RicciRealizesRm04FirstTraceAt (I := I) (S.ricci t x)
        (S.base.rm04 t x) DifferentialGeometry.Geometry.Curvature.delta3 basis := by
    have hinv :
        MetricInverseInBasis (I := I) (S.base.metric t) x basis
          DifferentialGeometry.Geometry.Curvature.delta3 :=
      DifferentialGeometry.Geometry.Curvature.orthonormal_invBasis3 (I := I) (S.base.metric t)
        basis horth
    exact DifferentialGeometry.Geometry.Curvature.ricciFirstTraceAt_of_rm13
      (I := I) (S.base.metric t) basis DifferentialGeometry.Geometry.Curvature.delta3 hinv
      (S.ricci t x) (S.base.rm13 t x) (S.base.rm04 t x)
      hRic13 hLowerAt
  have hScalarTrace :
      DifferentialGeometry.Geometry.Curvature.ScalarRealizesRicciTraceAt (I := I)
        (metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x))
        (S.ricci t x) DifferentialGeometry.Geometry.Curvature.delta3 basis := by
    have hinv :
        MetricInverseInBasis (I := I) (S.base.metric t) x basis
          DifferentialGeometry.Geometry.Curvature.delta3 :=
      DifferentialGeometry.Geometry.Curvature.orthonormal_invBasis3 (I := I) (S.base.metric t)
        basis horth
    unfold DifferentialGeometry.Geometry.Curvature.ScalarRealizesRicciTraceAt
    rw [metricTracePair0SAt_eq_sum_basis
      (I := I) (S.base.metric t) basis DifferentialGeometry.Geometry.Curvature.delta3 hinv
      (S.ricci t x)]
  exact DifferentialGeometry.Geometry.Curvature.traceDataOfFirst
    (I := I) (M := M) horth hcurv hRicFirst hScalarTrace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.traceData_metricTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.traceData_metricTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.traceData_metricTrace ``Submission.DifferentialGeometry.PDE.RicciFlow.traceData_metricTrace

@[simp]
theorem pinchSec_quad
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta t : Real)
    (x : M) (v : TangentSpace I x) :
    (pinchSec (I := I) S delta t x) (vec2 (I := I) v v) =
      S.ricci t x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) -
        delta * S.scalar t x * (S.family.metric t).inner x v v := by
  change twoTensorSecToFamily (I := I) (M := M)
    (pinchSec (I := I) S delta) t x v v = _
  rw [pinchSec_eq (I := I) S delta]
  simp [pinchTensor]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchSec_quad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchSec_quad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchSec_quad ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchSec_quad

theorem pinchSec_quad_deriv
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) {K : Set Real}
    {delta t ricDt scalarDt metricDt : Real}
    {x : M} {v : TangentSpace I x}
    (hRic :
      HasDerivWithinAt
        (fun s : Real => S.ricci s x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v))
        ricDt K t)
    (hScalar :
      HasDerivWithinAt (fun s : Real => S.scalar s x) scalarDt K t)
    (hMetric :
      HasDerivWithinAt
        (fun s : Real => (S.family.metric s).inner x v v) metricDt K t) :
    HasDerivWithinAt
      (fun s : Real =>
        twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta) s x v v)
      (ricDt -
        delta * (scalarDt * (S.family.metric t).inner x v v +
          S.scalar t x * metricDt))
      K t := by
  have hprod :
      HasDerivWithinAt
        (fun s : Real => S.scalar s x * (S.family.metric s).inner x v v)
        (scalarDt * (S.family.metric t).inner x v v +
          S.scalar t x * metricDt) K t :=
    hScalar.mul hMetric
  have hscaled :
      HasDerivWithinAt
        (fun s : Real =>
          delta * (S.scalar s x * (S.family.metric s).inner x v v))
        (delta * (scalarDt * (S.family.metric t).inner x v v +
          S.scalar t x * metricDt)) K t :=
    hprod.const_mul delta
  have hsub :
      HasDerivWithinAt
        (fun s : Real =>
          S.ricci s x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) -
            delta * (S.scalar s x * (S.family.metric s).inner x v v))
        (ricDt -
          delta * (scalarDt * (S.family.metric t).inner x v v +
            S.scalar t x * metricDt)) K t :=
    hRic.sub hscaled
  refine hsub.congr_of_eventuallyEq ?_ ?_
  · filter_upwards with s
    simp [twoTensorSecToFamily, SolutionOn.ricci, SolutionOn.scalar,
      SolutionOn.family, mul_assoc]
  · simp [twoTensorSecToFamily, SolutionOn.ricci, SolutionOn.scalar,
      SolutionOn.family, mul_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchSec_quad_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchSec_quad_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchSec_quad_deriv ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchSec_quad_deriv

theorem ricciQuadDeriv_coord
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (v : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real => S.ricci s x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v))
      (∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord i v *
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord j v
              *
              ricciEvolutionRHSInFrame
                (I := I) S S.base.rm04 (coordInv (I := I) S x)
                (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
                (coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x))
                (t : Real) x i j)
      D.carrier (t : Real) := by
  classical
  let b := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x
  let frame := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
  let rhs : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      ricciEvolutionRHSInFrame
        (I := I) S S.base.rm04 (coordInv (I := I) S x)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
        (coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x))
        (t : Real) x i j
  have hsum_eval : ∀ s : Real,
      S.ricci s x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) =
        ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            b.coord i v * b.coord j v *
              ricciCompInFrame (I := I) S frame s x i j := by
    intro s
    have h :=
      DifferentialGeometry.Tensor.Coordinates.tensor0S_two_eval_coordFrame_sum (I := I)
        (M := M) (x₀ := x) (Ax := S.ricci s x) v v
    rw [vec2_self_eq_const (I := I) (M := M) v]
    have hvec (i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
        (fun q : Fin 2 => if q = 0 then
          DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i x else
          DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j x) =
          DifferentialGeometry.Geometry.Curvature.vec2 (I := I)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i x)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j x) := by
      rfl
    simp_rw [hvec] at h
    have hself : (fun q : Fin 2 => if q = 0 then v else v) = fun _ : Fin 2 => v := by
      funext q
      by_cases hq : q = 0
      · rw [if_pos hq]
      · rw [if_neg hq]
    rw [hself] at h
    simpa only [b, frame, ricciCompInFrame,
      SolutionOn.ricci, SolutionOn.ricciAt, SolutionFamily.ricci_apply] using h
  have hsum_deriv :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
              b.coord i v * b.coord j v *
                ricciCompInFrame (I := I) S frame s x i j)
        (∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            b.coord i v * b.coord j v * rhs i j)
        D.carrier (t : Real) := by
    simpa [rhs, b, frame, mul_assoc] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ :
          Finset (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E)))
        (A := fun i s =>
          ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            b.coord i v * b.coord j v *
              ricciCompInFrame (I := I) S frame s x i j)
        (A' := fun i =>
          ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            b.coord i v * b.coord j v * rhs i j)
        (s := D.carrier) (x := (t : Real))
        (fun i _hi => by
          simpa [rhs, b, frame, mul_assoc] using
            (HasDerivWithinAt.fun_sum
              (u := (Finset.univ :
                Finset (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E)))
              (A := fun j s =>
                b.coord i v * b.coord j v *
                  ricciCompInFrame (I := I) S frame s x i j)
              (A' := fun j => b.coord i v * b.coord j v * rhs i j)
              (s := D.carrier) (x := (t : Real))
              (fun j _hj => by
                simpa [rhs, b, frame, mul_assoc] using
                  ((hS.ricciEvolution x t i j).const_mul
                    (b.coord i v * b.coord j v))))))
  refine hsum_deriv.congr_of_eventuallyEq ?_ ?_
  · filter_upwards with s
    exact hsum_eval s
  · exact hsum_eval (t : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciQuadDeriv_coord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciQuadDeriv_coord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciQuadDeriv_coord ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciQuadDeriv_coord

theorem pinchQuadDeriv_coord
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {delta : Real}
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (v : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real =>
        twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta) s x v v)
      ((∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord i v
              *
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord j
                v *
                ricciEvolutionRHSInFrame
                  (I := I) S S.base.rm04 (coordInv (I := I) S x)
                  (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
                  (coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x))
                  (t : Real) x i j) -
        delta *
          ((DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S)
            (t : Real)
                (S.scalar (t : Real)) x +
              2 * normSq0S (I := I) (S.family.metric (t : Real)) x 2
                (S.ricci (t : Real) x)) *
              (S.family.metric (t : Real)).inner x v v +
            S.scalar (t : Real) x *
              ((-2 : Real) * S.ricciAt (t : Real) x
                (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v))))
      D.carrier (t : Real) := by
  have hRic := ricciQuadDeriv_coord (I := I) (M := M) S hS t x v
  have hScalar :
      HasDerivWithinAt (fun s : Real => S.scalar s x)
        (DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S) (t : Real)
            (S.scalar (t : Real)) x +
          2 * normSq0S (I := I) (S.family.metric (t : Real)) x 2
            (S.ricci (t : Real) x))
        D.carrier (t : Real) := by
    exact hS.scalarEvolution (flowG (I := I) S)
      (by intro τ; rfl) (by intro τ; rfl) t x
  have hMetric :
      HasDerivWithinAt
        (fun s : Real => (S.family.metric s).inner x v v)
        ((-2 : Real) * S.ricciAt (t : Real) x
          (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v))
        D.carrier (t : Real) := by
    exact metric_derivWithin_eq_neg_two_ricci (I := I) S hS.isSolution t x v v
  exact pinchSec_quad_deriv (I := I) (M := M) S
    (delta := delta) hRic hScalar hMetric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchQuadDeriv_coord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchQuadDeriv_coord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchQuadDeriv_coord ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchQuadDeriv_coord

noncomputable def pinchMetricDerivs
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    CanonicalSpatialDerivs0S (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (S.base.connection t)
      (metricTensorField (I := I) (S.base.metric t)) := by
  simpa [SolutionFamily.connection] using
    metricDerivsZero (I := I)
      (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
        (S.base.metric t))
      (S.base.metric t)
      (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
        (I := I) (S.base.metric t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchMetricDerivs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchMetricDerivs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchMetricDerivs ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchMetricDerivs

@[simp]
theorem pinchMetric_nabla
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (x : M) (slots : Fin 3 -> TangentSpace I x) :
    (pinchMetricDerivs (I := I) S t).nablaA x slots = 0 := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchMetric_nabla then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchMetric_nabla"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchMetric_nabla ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchMetric_nabla

@[simp]
theorem pinchMetric_nabla2
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (x : M) (slots : Fin 4 -> TangentSpace I x) :
    (pinchMetricDerivs (I := I) S t).nabla2A x slots = 0 := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchMetric_nabla2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchMetric_nabla2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchMetric_nabla2 ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchMetric_nabla2

theorem pinchRough_smulMetric
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (S.base.metric t) x basis gInv)
    (f : Real)
    (df : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hessF : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (nabla2fG :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (tail : Fin 2 -> TangentSpace I x)
    (hleib :
      ∀ X Y : TangentSpace I x, ∀ tail : Fin 2 -> TangentSpace I x,
        nabla2fG (metricTraceInput (I := I) X Y tail) =
          hessF (metricTraceInput (I := I) X Y Fin.elim0) *
              metricTensorField (I := I) (S.base.metric t) x tail +
            df (fun _ : Fin 1 => X) *
              (pinchMetricDerivs (I := I) S t).nablaA x (Fin.cons Y tail) +
            df (fun _ : Fin 1 => Y) *
              (pinchMetricDerivs (I := I) S t).nablaA x (Fin.cons X tail) +
            f * (pinchMetricDerivs (I := I) S t).nabla2A x
              (metricTraceInput (I := I) X Y tail)) :
    roughLap0STensor (I := I) (S.base.metric t) nabla2fG tail =
      metricTraceFirstTwo0SAt (I := I) (S.base.metric t) hessF Fin.elim0 *
        metricTensorField (I := I) (S.base.metric t) x tail := by
  exact roughLap_smul_par (I := I) (S.base.metric t) basis gInv hinv
    f df hessF (metricTensorField (I := I) (S.base.metric t) x)
    ((pinchMetricDerivs (I := I) S t).nablaA x)
    ((pinchMetricDerivs (I := I) S t).nabla2A x)
    nabla2fG tail
    (by intro X tail; simp)
    (by intro X Y tail; simp)
    hleib

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchRough_smulMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchRough_smulMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchRough_smulMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchRough_smulMetric

theorem pinchRough_hessMetric
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (S.base.metric t) x basis gInv)
    (hessF : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (tail : Fin 2 -> TangentSpace I x) :
    roughLap0STensor (I := I) (S.base.metric t)
        (Tensor0SSpace.product hessF
          (metricTensorField (I := I) (S.base.metric t) x))
        tail =
      metricTraceFirstTwo0SAt (I := I) (S.base.metric t) hessF Fin.elim0 *
        metricTensorField (I := I) (S.base.metric t) x tail := by
  refine pinchRough_smulMetric (I := I) S t basis gInv hinv
    (0 : Real)
    (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    hessF
    (Tensor0SSpace.product hessF
      (metricTensorField (I := I) (S.base.metric t) x))
    tail ?_
  intro X Y tail
  rw [Tensor0SSpace.product_apply]
  have hleft :
      metricTraceInput (I := I) X Y tail ∘ Fin.castAdd 2 =
        metricTraceInput (I := I) X Y Fin.elim0 := by
    funext a
    fin_cases a <;> rfl
  have hright :
      metricTraceInput (I := I) X Y tail ∘ Fin.natAdd 2 = tail := by
    funext a
    fin_cases a <;> rfl
  rw [hleft, hright]
  rw [metricTensorField_apply]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchRough_hessMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchRough_hessMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchRough_hessMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchRough_hessMetric

theorem scalarSmoothSec
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun x : M => S.scalar t x) := by
  simpa [SolutionOn.scalar, SolutionFamily.scalar] using
    metricScalar_smooth (I := I) (M := M) (S.base.metric t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalarSmoothSec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarSmoothSec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarSmoothSec ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarSmoothSec

noncomputable def scalarDuSec
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    OneFormSection (I := I) (M := M) :=
  duSec (I := I) (fun x : M => S.scalar t x)
    (scalarSmoothSec (I := I) S t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalarDuSec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarDuSec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarDuSec ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarDuSec

noncomputable def scalarHessSec
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TwoTensorSection (I := I) (M := M) :=
  hessianSec (I := I) (S.base.connection t) (ricciCovInf (I := I) S t)
    (fun x : M => S.scalar t x) (scalarSmoothSec (I := I) S t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalarHessSec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarHessSec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarHessSec ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarHessSec

noncomputable def scalarMetric1Sec
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
    (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
    (scalarDuSec (I := I) S t)
    (metricTensorField (I := I) (S.base.metric t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalarMetric1Sec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarMetric1Sec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarMetric1Sec ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarMetric1Sec

noncomputable def scalarMetric2Sec
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
    (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2)
    (scalarHessSec (I := I) S t)
    (metricTensorField (I := I) (S.base.metric t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalarMetric2Sec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarMetric2Sec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarMetric2Sec ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarMetric2Sec

@[simp]
theorem scalarMetric1Sec_apply
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    scalarMetric1Sec (I := I) S t x =
      Tensor0SSpace.product (scalarDuSec (I := I) S t x)
        (metricTensorField (I := I) (S.base.metric t) x) := by
  apply tensor0SSpace_ext (I := I) 3 x
  intro v
  change Bundle.continuousMultilinearMap.productFun
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 1 x (scalarDuSec (I := I) S t x))
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x
        (metricTensorField (I := I) (S.base.metric t) x)) v = _
  rw [Bundle.continuousMultilinearMap.product_fun_apply, Tensor0SSpace.product_apply]
  simp only [tensor0SSpaceFiberContinuousLinearEquiv_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalarMetric1Sec_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarMetric1Sec_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarMetric1Sec_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarMetric1Sec_apply

@[simp]
theorem scalarMetric2Sec_apply
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    scalarMetric2Sec (I := I) S t x =
      Tensor0SSpace.product (scalarHessSec (I := I) S t x)
        (metricTensorField (I := I) (S.base.metric t) x) := by
  apply tensor0SSpace_ext (I := I) 4 x
  intro v
  change Bundle.continuousMultilinearMap.productFun
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x (scalarHessSec (I := I) S t x))
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x
        (metricTensorField (I := I) (S.base.metric t) x)) v = _
  rw [Bundle.continuousMultilinearMap.product_fun_apply, Tensor0SSpace.product_apply]
  simp only [tensor0SSpaceFiberContinuousLinearEquiv_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalarMetric2Sec_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarMetric2Sec_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarMetric2Sec_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarMetric2Sec_apply

theorem scalarHessTrace_eq_lap
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
        (scalarHessSec (I := I) S t x) Fin.elim0 =
      DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S) t
        (S.scalar t) x := by
  have hlap :
      ScalarLaplacianRealizesTraceAt (I := I)
        (S.base.connection t) (S.base.metric t)
        (fun y : M => S.scalar t y)
        (scalarHessSec (I := I) S t x) := by
    simpa [scalarHessSec] using
      (scalarLap_smooth (I := I) (M := M)
        (cov := S.base.connection t) (ricciCovInf (I := I) S t)
        (g := S.base.metric t) (ricciMetricComp (I := I) S t)
        (f := fun y : M => S.scalar t y) (scalarSmoothSec (I := I) S t)
        (x := x))
  have htrace :=
    ScalarLaplacianRealizesTraceAt.eq_trace (I := I)
      (S.base.connection t) (S.base.metric t)
      (fun y : M => S.scalar t y) (scalarHessSec (I := I) S t x) hlap
  rw [traceFirstTwo_elim0]
  change scalarLapTraceAt (I := I) (S.base.metric t) (scalarHessSec (I := I) S t x) =
    laplacian (I := I) (S.base.connection t) (S.base.metric t)
      (fun y : M => S.scalar t y) x
  exact htrace.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalarHessTrace_eq_lap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarHessTrace_eq_lap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarHessTrace_eq_lap ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarHessTrace_eq_lap

theorem ricciRoughTrace_coord
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (x : M) (v : TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
        (ricciNabla2WeakMaximumPrinciple (I := I) S t x)
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) =
      ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord i v *
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord j v
              *
              coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x)
                t x i j := by
  classical
  let b := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x
  let frame := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
  let roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 x :=
    roughLap0STensor (I := I) (S.base.metric t)
      (ricciNabla2WeakMaximumPrinciple (I := I) S t x)
  have hnabla : ∀ y a i j,
      ricciNablaWeakMaximumPrinciple (I := I) S t y
          (DifferentialGeometry.Geometry.Curvature.vec3 (I := I)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x a y)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i y)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j y)) =
        nablaRicComp (I := I) S
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x) t y a i j := by
    intro y a i j
    simp [ricciNablaWeakMaximumPrinciple, ricciDerivsWeakMaximumPrinciple, nablaRicComp,
      CanonicalSpatialDerivs0S.ofSmoothConnection]
  have hnab2 :=
    coordinate_second_ricci_covariant_derivative_of_realization (I := I) S t x
      (ricciNablaWeakMaximumPrinciple (I := I) S t)
      (ricciNabla2WeakMaximumPrinciple (I := I) S t)
      (by
        simpa [SolutionOn.family, ricciNablaWeakMaximumPrinciple, ricciNabla2WeakMaximumPrinciple] using
          (ricciSpatialWeakMaximumPrinciple (I := I) S).second t)
      hnabla
  have hcomp :
      ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        roughA
            (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (frame i x) (frame j x)) =
          coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x)
            t x i j := by
    intro i j
    simpa [roughA, frame, SolutionOn.family] using
      rough_laplacian_ricci_component_of_coordinate_realization (I := I) S t x
        (ricciNabla2WeakMaximumPrinciple (I := I) S t) hnab2 i j
  have hcomp_if :
      ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        roughA
            (fun q : Fin 2 => if q = 0 then frame i x else frame j x) =
          coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x)
            t x i j := by
    intro i j
    rw [show (fun q : Fin 2 => if q = 0 then frame i x else frame j x) =
      DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (frame i x) (frame j x) by rfl]
    exact hcomp i j
  have hsum :=
    DifferentialGeometry.Tensor.Coordinates.tensor0S_two_eval_coordFrame_sum (I := I)
      (M := M) (x₀ := x) (Ax := roughA) v v
  rw [← roughLap0STensor_apply (I := I) (S.base.metric t)
      (ricciNabla2WeakMaximumPrinciple (I := I) S t x) (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)]
  rw [vec2_self_eq_const (I := I) (M := M) v]
  change roughA (fun _ : Fin 2 => v) =
    ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
      ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        b.coord i v * b.coord j v *
          coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x) t x i j
  simpa [b, frame, hcomp_if] using hsum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciRoughTrace_coord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciRoughTrace_coord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciRoughTrace_coord ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciRoughTrace_coord

theorem ricciRoughPair
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (x : M) (v w : TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
        (ricciNabla2WeakMaximumPrinciple (I := I) S t x)
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w) =
      ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord i v *
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord j w
              *
              coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x)
                t x i j := by
  classical
  let b := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x
  let frame := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
  let roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 x :=
    roughLap0STensor (I := I) (S.base.metric t)
      (ricciNabla2WeakMaximumPrinciple (I := I) S t x)
  have hnabla : ∀ y a i j,
      ricciNablaWeakMaximumPrinciple (I := I) S t y
          (DifferentialGeometry.Geometry.Curvature.vec3 (I := I)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x a y)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i y)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j y)) =
        nablaRicComp (I := I) S
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x) t y a i j := by
    intro y a i j
    simp [ricciNablaWeakMaximumPrinciple, ricciDerivsWeakMaximumPrinciple, nablaRicComp,
      CanonicalSpatialDerivs0S.ofSmoothConnection]
  have hnab2 :=
    coordinate_second_ricci_covariant_derivative_of_realization (I := I) S t x
      (ricciNablaWeakMaximumPrinciple (I := I) S t)
      (ricciNabla2WeakMaximumPrinciple (I := I) S t)
      (by
        simpa [SolutionOn.family, ricciNablaWeakMaximumPrinciple, ricciNabla2WeakMaximumPrinciple] using
          (ricciSpatialWeakMaximumPrinciple (I := I) S).second t)
      hnabla
  have hcomp :
      ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        roughA
            (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (frame i x) (frame j x)) =
          coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x)
            t x i j := by
    intro i j
    simpa [roughA, frame, SolutionOn.family] using
      rough_laplacian_ricci_component_of_coordinate_realization (I := I) S t x
        (ricciNabla2WeakMaximumPrinciple (I := I) S t) hnab2 i j
  have hcomp_if :
      ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        roughA
            (fun q : Fin 2 => if q = 0 then frame i x else frame j x) =
          coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x)
            t x i j := by
    intro i j
    rw [show (fun q : Fin 2 => if q = 0 then frame i x else frame j x) =
      DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (frame i x) (frame j x) by rfl]
    exact hcomp i j
  have hsum :=
    DifferentialGeometry.Tensor.Coordinates.tensor0S_two_eval_coordFrame_sum (I := I)
      (M := M) (x₀ := x) (Ax := roughA) v w
  rw [← roughLap0STensor_apply (I := I) (S.base.metric t)
      (ricciNabla2WeakMaximumPrinciple (I := I) S t x)
      (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w)]
  change roughA (fun q : Fin 2 => if q = 0 then v else w) = _
  simpa [b, frame, hcomp_if] using hsum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciRoughPair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciRoughPair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciRoughPair ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciRoughPair

theorem scalarMetric_trace
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (S.base.metric t) x basis gInv)
    (v : TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
        (scalarMetric2Sec (I := I) S t x)
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) =
      metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
          (scalarHessSec (I := I) S t x) Fin.elim0 *
        (S.base.metric t).inner x v v := by
  have h := pinchRough_hessMetric (I := I) S t basis gInv hinv
    (scalarHessSec (I := I) S t x) (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)
  rw [roughLap0STensor_apply] at h
  rw [scalarMetric2Sec_apply]
  simpa [metricTensorField_apply,
    DifferentialGeometry.Geometry.Curvature.vec2, DifferentialGeometry.Geometry.Curvature.vec2]
      using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalarMetric_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarMetric_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarMetric_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarMetric_trace

private theorem trace_sub_smul
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    {s : ℕ}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (c : Real) (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g (A - c • B) tail =
      metricTraceFirstTwo0SAt (I := I) g A tail -
        c * metricTraceFirstTwo0SAt (I := I) g B tail := by
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv
      (A - c • B) tail,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv A tail,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv B tail]
  simp only [metricTrace0S2InBasis, Tensor0SSpace.sub_apply,
    Tensor0SSpace.smul_apply, smul_eq_mul]
  simp_rw [mul_sub]
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.trace_sub_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.trace_sub_smul target :: scope.openDecls } }

def pinchNab2Model
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta t : Real) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  ricciNabla2WeakMaximumPrinciple (I := I) S t x -
    delta • scalarMetric2Sec (I := I) S t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchNab2Model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchNab2Model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchNab2Model ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchNab2Model

theorem pinchNab2Model_trace
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta t : Real)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (S.base.metric t) x basis gInv)
    (v : TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
        (pinchNab2Model (I := I) S delta t x)
          (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) =
      metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
          (ricciNabla2WeakMaximumPrinciple (I := I) S t x)
            (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) -
        delta *
          (metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
              (scalarHessSec (I := I) S t x) Fin.elim0 *
            (S.base.metric t).inner x v v) := by
  rw [pinchNab2Model]
  rw [trace_sub_smul (I := I) (M := M) (S.base.metric t) basis gInv hinv
    (ricciNabla2WeakMaximumPrinciple (I := I) S t x)
    (scalarMetric2Sec (I := I) S t x)
    delta (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)]
  rw [scalarMetric_trace (I := I) S t basis gInv hinv v]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchNab2Model_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchNab2Model_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchNab2Model_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchNab2Model_trace

theorem scalarHessSec_realizes
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 (S.base.connection t) (scalarDuSec (I := I) S t)
      (scalarHessSec (I := I) S t) := by
  unfold scalarHessSec hessianSec
  exact totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    1 (S.base.connection t) (scalarDuSec (I := I) S t)
    (totalNabla0S_regularity (E := E) (H := H) (I := I) (M := M)
      1 (S.base.connection t) (ricciCovInf (I := I) S t)
      (scalarDuSec (I := I) S t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalarHessSec_realizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarHessSec_realizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarHessSec_realizes ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarHessSec_realizes

theorem scalarMetric1Sec_realizes
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (S.base.connection t)
      (tensor0SFieldSmulByFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
        (fun x : M => S.scalar t x) (scalarSmoothSec (I := I) S t)
        (metricTensorField (I := I) (S.base.metric t)))
      (scalarMetric1Sec (I := I) S t) := by
  intro X x slots
  classical
  let V : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (slots a)).choose
  have hV : ∀ a : Fin 2, V a x = slots a := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (slots a)).choose_spec
  let metricSec : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
    metricTensorField (I := I) (S.base.metric t)
  let f : M -> Real := fun y : M => S.scalar t y
  let mfun : M -> Real := fun y : M => metricSec y (fun a : Fin 2 => V a y)
  have hf : MDifferentiableAt I 𝓘(Real, Real) f x :=
    (scalarSmoothSec (I := I) S t).contMDiffAt.mdifferentiableAt (by simp)
  have hm : MDifferentiableAt I 𝓘(Real, Real) mfun x := by
    exact (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      metricSec V x).mdifferentiableAt (by simp)
  have hprod :
      mvfderiv (I := I) (fun y : M => f y * mfun y) x (X x) =
        f x * mvfderiv (I := I) mfun x (X x) +
          mvfderiv (I := I) f x (X x) * mfun x := by
    exact mvfderiv_mul (I := I) (f := f) (h := mfun) (X x) hf hm
  have hmetricReal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.base.connection t) metricSec
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) 3) := by
    simpa [metricSec, SolutionFamily.connection] using
      zero_realizes_metric (I := I) (S.base.connection t) (S.base.metric t)
        (ricciMetricComp (I := I) S t)
  have hmetricEval :=
    TotalNabla0SRealizes.eval_smooth_slots (I := I) hmetricReal X V x
  have hnabla :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (S.base.connection t) X V
      (tensor0SFieldSmulByFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
        f (scalarSmoothSec (I := I) S t) metricSec) x
  have hdu :
      scalarDuSec (I := I) S t x (fun _ : Fin 1 => X x) =
        mvfderiv (I := I) f x (X x) := by
    simp [scalarDuSec, f, differential1FormFun_apply_eq_mvfderiv]
  have hslots :
      (fun a : Fin 2 => V a x) = slots := by
    funext a
    exact hV a
  have hmetric_zero :
      mvfderiv (I := I) mfun x (X x) -
          ∑ a : Fin 2,
            metricSec x
              (Function.update (fun b : Fin 2 => V b x) a
                (((S.base.connection t) (fun p : M => V a p) x) (X x))) =
        0 := by
    simpa [metricSec, mfun] using hmetricEval.symm
  calc
    scalarMetric1Sec (I := I) S t x (Fin.cons (X x) slots)
        =
          mvfderiv (I := I) f x (X x) * metricSec x slots := by
          rw [scalarMetric1Sec_apply, Tensor0SSpace.product_apply]
          have hleft :
              Fin.cons (X x) slots ∘ Fin.castAdd 2 =
                fun _ : Fin 1 => X x := by
            funext a
            fin_cases a
            rfl
          have hright :
              Fin.cons (X x) slots ∘ Fin.natAdd 1 = slots := by
            funext a
            fin_cases a <;> rfl
          rw [hleft, hright, hdu]
      _ =
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 (S.base.connection t) X
            (tensor0SFieldSmulByFun (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
              f (scalarSmoothSec (I := I) S t) metricSec) x slots := by
          rw [← hslots]
          rw [hnabla]
          simp only [tensor0SField_smulByFun_apply,
            Tensor0SSpace.smul_apply, smul_eq_mul]
          rw [hprod]
          have hsum :
              (∑ a : Fin 2,
                f x *
                  metricSec x
                    (Function.update (fun b : Fin 2 => V b x) a
                      (((S.base.connection t) (fun p : M => V a p) x) (X x)))) =
                f x *
                  ∑ a : Fin 2,
                    metricSec x
                      (Function.update (fun b : Fin 2 => V b x) a
                        (((S.base.connection t) (fun p : M => V a p) x)
                          (X x))) := by
            rw [Finset.mul_sum]
          rw [hsum]
          have hm0 := hmetric_zero
          have hmfunx : mfun x = metricSec x (fun a : Fin 2 => V a x) := rfl
          have hdm :
              (mvfderiv (I := I) mfun x) (X x) =
                ∑ a : Fin 2,
                  metricSec x
                    (Function.update (fun b : Fin 2 => V b x) a
                      (((S.base.connection t) (fun p : M => V a p) x)
                        (X x))) := by
            linarith [hm0]
          rw [hmfunx, hdm]
          ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalarMetric1Sec_realizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarMetric1Sec_realizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarMetric1Sec_realizes ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarMetric1Sec_realizes

theorem scalarMetric2Sec_realizes
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 (S.base.connection t) (scalarMetric1Sec (I := I) S t)
      (scalarMetric2Sec (I := I) S t) := by
  intro X x slots
  classical
  let V : Fin 3 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (slots a)).choose
  have hV : ∀ a : Fin 3, V a x = slots a := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (slots a)).choose_spec
  let alphaSec : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 :=
    scalarDuSec (I := I) S t
  let hessSec : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
    scalarHessSec (I := I) S t
  let metricSec : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
    metricTensorField (I := I) (S.base.metric t)
  let V0 : Fin 1 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := fun _ => V 0
  let W : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := fun a => V (Fin.natAdd 1 a)
  let afun : M -> Real := fun y : M => alphaSec y (fun _ : Fin 1 => V 0 y)
  let mfun : M -> Real := fun y : M => metricSec y (fun a : Fin 2 => W a y)
  have ha : MDifferentiableAt I 𝓘(Real, Real) afun x := by
    exact (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      alphaSec V0 x).mdifferentiableAt (by simp)
  have hm : MDifferentiableAt I 𝓘(Real, Real) mfun x := by
    exact (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      metricSec W x).mdifferentiableAt (by simp)
  have hprod :
      mvfderiv (I := I) (fun y : M => afun y * mfun y) x (X x) =
        afun x * mvfderiv (I := I) mfun x (X x) +
          mvfderiv (I := I) afun x (X x) * mfun x := by
    exact mvfderiv_mul (I := I) (f := afun) (h := mfun) (X x) ha hm
  have hmetricReal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.base.connection t) metricSec
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) 3) := by
    simpa [metricSec, SolutionFamily.connection] using
      zero_realizes_metric (I := I) (S.base.connection t) (S.base.metric t)
        (ricciMetricComp (I := I) S t)
  have hmetricEval :=
    TotalNabla0SRealizes.eval_smooth_slots (I := I) hmetricReal X W x
  have halphaReal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 (S.base.connection t) alphaSec hessSec := by
    simpa [alphaSec, hessSec] using scalarHessSec_realizes (I := I) S t
  have halphaEval :=
    TotalNabla0SRealizes.eval_smooth_slots (I := I) halphaReal X V0 x
  have hnabla :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (S.base.connection t) X V
      (scalarMetric1Sec (I := I) S t) x
  have hslots :
      (fun a : Fin 3 => V a x) = slots := by
    funext a
    exact hV a
  have hmetric_zero :
      mvfderiv (I := I) mfun x (X x) -
          ∑ a : Fin 2,
            metricSec x
              (Function.update (fun b : Fin 2 => W b x) a
                (((S.base.connection t) (fun p : M => W a p) x) (X x))) =
        0 := by
    simpa [metricSec, mfun, W] using hmetricEval.symm
  have halpha_eq :
      hessSec x (Fin.cons (X x) (fun _ : Fin 1 => V 0 x)) =
        mvfderiv (I := I) afun x (X x) -
          alphaSec x
            (Function.update (fun _ : Fin 1 => V 0 x) 0
              (((S.base.connection t) (fun p : M => V 0 p) x) (X x))) := by
    simpa [alphaSec, hessSec, afun, V0] using halphaEval
  calc
    scalarMetric2Sec (I := I) S t x (Fin.cons (X x) slots)
        =
          hessSec x (Fin.cons (X x) (fun _ : Fin 1 => slots 0)) *
            metricSec x (fun a : Fin 2 => slots (Fin.natAdd 1 a)) := by
          rw [scalarMetric2Sec_apply, Tensor0SSpace.product_apply]
          have hleft :
              Fin.cons (X x) slots ∘ Fin.castAdd 2 =
                Fin.cons (X x) (fun _ : Fin 1 => slots 0) := by
            funext a
            fin_cases a <;> rfl
          have hright :
              Fin.cons (X x) slots ∘ Fin.natAdd 2 =
                fun a : Fin 2 => slots (Fin.natAdd 1 a) := by
            funext a
            fin_cases a <;> rfl
          rw [hleft, hright]
      _ =
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            3 (S.base.connection t) X (scalarMetric1Sec (I := I) S t) x slots := by
          rw [← hslots]
          rw [hnabla]
          have hfun_eval :
              (fun p : M =>
                scalarMetric1Sec (I := I) S t p (fun a : Fin 3 => V a p)) =
                fun p : M => afun p * mfun p := by
            funext p
            rw [scalarMetric1Sec_apply, Tensor0SSpace.product_apply]
            have hleft :
                (fun a : Fin 3 => V a p) ∘ Fin.castAdd 2 =
                  fun _ : Fin 1 => V 0 p := by
              funext a
              fin_cases a
              rfl
            have hright :
                (fun a : Fin 3 => V a p) ∘ Fin.natAdd 1 =
                  fun a : Fin 2 => W a p := by
              funext a
              fin_cases a <;> rfl
            rw [hleft, hright]
          rw [hfun_eval, hprod]
          have hsum3 :
              (∑ a : Fin 3,
                scalarMetric1Sec (I := I) S t x
                  (Function.update (fun b : Fin 3 => V b x) a
                    (((S.base.connection t) (fun p : M => V a p) x)
                      (X x)))) =
                alphaSec x
                    (Function.update (fun _ : Fin 1 => V 0 x) 0
                      (((S.base.connection t) (fun p : M => V 0 p) x)
                        (X x))) *
                  mfun x +
                afun x *
                  ∑ a : Fin 2,
                    metricSec x
                      (Function.update (fun b : Fin 2 => W b x) a
                        (((S.base.connection t) (fun p : M => W a p) x)
                          (X x))) := by
            rw [Fin.sum_univ_three]
            repeat rw [scalarMetric1Sec_apply]
            repeat rw [Tensor0SSpace.product_apply]
            have h0left :
                (Function.update (fun b : Fin 3 => V b x) 0
                    (((S.base.connection t) (fun p : M => V 0 p) x)
                      (X x)) ∘ Fin.castAdd 2) =
                  Function.update (fun _ : Fin 1 => V 0 x) 0
                    (((S.base.connection t) (fun p : M => V 0 p) x)
                      (X x)) := by
              funext a
              fin_cases a
              rfl
            have h1left :
                (Function.update (fun b : Fin 3 => V b x) 1
                    (((S.base.connection t) (fun p : M => V 1 p) x)
                      (X x)) ∘ Fin.castAdd 2) =
                  fun _ : Fin 1 => V 0 x := by
              funext a
              fin_cases a
              rfl
            have h2left :
                (Function.update (fun b : Fin 3 => V b x) 2
                    (((S.base.connection t) (fun p : M => V 2 p) x)
                      (X x)) ∘ Fin.castAdd 2) =
                  fun _ : Fin 1 => V 0 x := by
              funext a
              fin_cases a
              rfl
            rw [h0left, h1left, h2left]
            repeat rw [metricTensorField_apply]
            simp [afun, mfun, alphaSec, metricSec, W, Function.update]
            ring_nf
          rw [hsum3]
          have hmetricInput :
              (fun a : Fin 2 => W a x) =
                fun a : Fin 2 => V (Fin.natAdd 1 a) x := rfl
          have hafunx :
              afun x = alphaSec x (fun _ : Fin 1 => V 0 x) := rfl
          have hmfunx :
              mfun x = metricSec x (fun a : Fin 2 => W a x) := rfl
          have hdm :
              (mvfderiv (I := I) mfun x) (X x) =
                ∑ a : Fin 2,
                  metricSec x
                    (Function.update (fun b : Fin 2 => W b x) a
                      (((S.base.connection t) (fun p : M => W a p) x)
                        (X x))) := by
            linarith [hmetric_zero]
          have hda :
              (mvfderiv (I := I) afun x) (X x) =
                hessSec x (Fin.cons (X x) (fun _ : Fin 1 => V 0 x)) +
                  alphaSec x
                    (Function.update (fun _ : Fin 1 => V 0 x) 0
                      (((S.base.connection t) (fun p : M => V 0 p) x)
                        (X x))) := by
            linarith [halpha_eq]
          rw [hdm, hda, hafunx, hmfunx]
          ring_nf
          simp [W]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalarMetric2Sec_realizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarMetric2Sec_realizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarMetric2Sec_realizes ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarMetric2Sec_realizes

noncomputable def pinchNablaModel
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) :
    TensorNabla1SecFamily (I := I) (M := M) :=
  fun t => ricciNablaWeakMaximumPrinciple (I := I) S t -
    delta • scalarMetric1Sec (I := I) S t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchNablaModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchNablaModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchNablaModel ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchNablaModel

noncomputable def pinchNab2ModelSec
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) :
    TensorNabla2SecFamily (I := I) (M := M) :=
  fun t => ricciNabla2WeakMaximumPrinciple (I := I) S t -
    delta • scalarMetric2Sec (I := I) S t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchNab2ModelSec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchNab2ModelSec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchNab2ModelSec ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchNab2ModelSec

@[simp]
theorem pinchNablaModel_apply
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta t : Real) (x : M) :
    pinchNablaModel (I := I) S delta t x =
      ricciNablaWeakMaximumPrinciple (I := I) S t x -
        delta • scalarMetric1Sec (I := I) S t x := by
  simp [pinchNablaModel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchNablaModel_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchNablaModel_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchNablaModel_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchNablaModel_apply

@[simp]
theorem pinchNab2ModelSec_apply
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta t : Real) (x : M) :
    pinchNab2ModelSec (I := I) S delta t x =
      pinchNab2Model (I := I) S delta t x := by
  simp [pinchNab2ModelSec, pinchNab2Model]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchNab2ModelSec_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchNab2ModelSec_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchNab2ModelSec_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchNab2ModelSec_apply

theorem pinchHeat_coord
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta t : Real)
    (x : M) (v : TangentSpace I x) :
    tensorHeatWithDrift2QuadMetricAt (I := I) (S.base.metric t)
        (fun _y : M => 0)
        (pinchNab2ModelSec (I := I) S delta t x)
        (pinchNablaModel (I := I) S delta t x) v =
      (∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord i v *
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord j v
              *
              coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x)
                t x i j) -
        delta *
          (DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S) t
              (S.scalar t) x *
            (S.base.metric t).inner x v v) := by
  rw [tensorHeatWithDrift2QuadMetricAt_zero_drift]
  rw [pinchNab2ModelSec_apply (I := I) S delta t x]
  rw [pinchNab2Model_trace (I := I) S delta t
    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x)
    (fun a b : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
      coordInv (I := I) S x t x a b)
    (coordInvReal (I := I) S x t) v]
  rw [ricciRoughTrace_coord (I := I) S t x v]
  rw [scalarHessTrace_eq_lap (I := I) S t x]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchHeat_coord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchHeat_coord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchHeat_coord ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchHeat_coord

def ricciCoordQuadRHS
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v : TangentSpace I x) : Real :=
  ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
    ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord i v *
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord j v *
          ricciEvolutionRHSInFrame
            (I := I) S S.base.rm04 (coordInv (I := I) S x)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
            (coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x))
            t x i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciCoordQuadRHS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciCoordQuadRHS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciCoordQuadRHS ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciCoordQuadRHS

def ricciCoordRough
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v : TangentSpace I x) : Real :=
  ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
    ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord i v *
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord j v *
          coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x) t x i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciCoordRough then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciCoordRough"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciCoordRough ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciCoordRough

def ricciCoordReact
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v : TangentSpace I x) : Real :=
  ricciCoordQuadRHS (I := I) S t x v -
    ricciCoordRough (I := I) S t x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciCoordReact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciCoordReact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciCoordReact ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciCoordReact

noncomputable def ricciPairReact
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v w : TangentSpace I x) : Real :=
  ricciPairRHS (I := I) S t x v w -
    ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
      ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord i v *
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord j w *
            coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x) t x i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciPairReact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciPairReact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciPairReact ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciPairReact

def pinchCoordTime
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (delta t : Real) (x : M) (v : TangentSpace I x) : Real :=
  ricciCoordQuadRHS (I := I) S t x v -
    delta *
      ((DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S) t
            (S.scalar t) x +
          2 * normSq0S (I := I) (S.family.metric t) x 2
            (S.ricci t x)) *
          (S.family.metric t).inner x v v +
        S.scalar t x *
          ((-2 : Real) * S.ricciAt t x
            (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchCoordTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchCoordTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchCoordTime ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchCoordTime

def pinchCoordReact
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (delta t : Real) (x : M) (v : TangentSpace I x) : Real :=
  ricciCoordReact (I := I) S t x v -
    delta *
      (2 * normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x) *
          (S.family.metric t).inner x v v +
        S.scalar t x *
          ((-2 : Real) * S.ricciAt t x
            (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchCoordReact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchCoordReact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchCoordReact ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchCoordReact

noncomputable def ricciActualReactAt
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) : Tensor02At (I := I) (M := M) x :=
  (-2 : Real) •
      rm04RicciContrAt (I := I) (M := M) (S.base.metric t)
        (S.base.rm04 t x) (S.ricci t x) -
    2 • ricciQuadAt (I := I) (M := M) (S.base.metric t) (S.ricci t x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciActualReactAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciActualReactAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciActualReactAt ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciActualReactAt

private theorem actualReact_apply
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v : Fin 2 → TangentSpace I x) :
    ricciActualReactAt (I := I) S t x v =
      (-2 : Real) *
          rm04RicciContrAt (I := I) (M := M) (S.base.metric t)
            (S.base.rm04 t x) (S.ricci t x) v -
        2 * ricciQuadAt (I := I) (M := M) (S.base.metric t) (S.ricci t x) v := by
  unfold ricciActualReactAt
  simp only [Tensor0SSpace.sub_apply, real_smul0S_apply,
    Tensor0SSpace.nsmul_apply, nsmul_eq_mul, Nat.cast_ofNat]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.actualReact_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.actualReact_apply target :: scope.openDecls } }

theorem actualReact_comp
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis (I := I) (S.base.metric t) x basis gInv)
    (i j : Idx) :
    ricciActualReactAt (I := I) S t x
        (vec2 (I := I) (basis i) (basis j)) =
      (-2 : Real) *
          DifferentialGeometry.Geometry.Curvature.rm04RicciContractionAt
            (I := I) basis (S.base.rm04 t x) gInv (S.ricci t x) i j -
        2 * DifferentialGeometry.Geometry.Curvature.ricciQuadraticAt
          (I := I) basis gInv (S.ricci t x) i j := by
  rw [actualReact_apply (I := I) (M := M) S t x
    (vec2 (I := I) (basis i) (basis j))]
  rw [rm04ContrAt_comp_basis (I := I) (M := M) basis gInv hinv,
    ricciQuadAt_comp_basis (I := I) (M := M) basis gInv hinv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.actualReact_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.actualReact_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.actualReact_comp ``Submission.DifferentialGeometry.PDE.RicciFlow.actualReact_comp

private theorem reaction3_apply
    (g : SmoothRiemannianMetric I M) {x : M}
    (Ric : Tensor02At (I := I) (M := M) x)
    (v : Fin 2 → TangentSpace I x) :
    ricciReaction3At (I := I) (M := M) g Ric v =
      2 * rm04RicciContrAt (I := I) (M := M) g
          (rm04OfRic3At (I := I) (M := M) g Ric) Ric v -
        2 * ricciQuadAt (I := I) (M := M) g Ric v := by
  unfold ricciReaction3At
  simp only [Tensor0SSpace.sub_apply, Tensor0SSpace.nsmul_apply,
    nsmul_eq_mul, Nat.cast_ofNat]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.reaction3_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.reaction3_apply target :: scope.openDecls } }

theorem ricciActualReactAt_eq_reaction3
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt
      (I := I) (S.base.metric t) x basis) :
    ricciActualReactAt (I := I) S t x =
      ricciReaction3At (I := I) (M := M) (S.base.metric t) (S.ricci t x) := by
  have htrace := traceData_metricTrace (I := I) (M := M) S horth
  have hsym : DifferentialGeometry.Geometry.Curvature.RicciSymAt (I := I) (S.ricci t x) := by
    simpa [SolutionOn.ricci, SolutionFamily.ricci, SolutionOn.ricciAt,
      SolutionFamily.ricciAt] using ricciAt_symm (I := I) S t x
  apply ext0S_basis (I := I) basis
  intro slots
  let i : Fin 3 := slots 0
  let j : Fin 3 := slots 1
  have hslots :
      (fun q : Fin 2 => basis (slots q)) =
        vec2 (I := I) (basis i) (basis j) := by
    funext q
    fin_cases q <;> rfl
  change
    ricciActualReactAt (I := I) S t x (fun q : Fin 2 => basis (slots q)) =
      ricciReaction3At (I := I) (M := M) (S.base.metric t) (S.ricci t x)
        (fun q : Fin 2 => basis (slots q))
  rw [hslots]
  have hactual :=
    rm04Contr_comp_orthonormal (I := I) (M := M) basis horth
      (S.base.rm04 t x) (S.ricci t x) i j
  have hcanon :=
    rm04Contr_comp_orthonormal (I := I) (M := M) basis horth
      (rm04OfRic3At (I := I) (M := M) (S.base.metric t) (S.ricci t x))
      (S.ricci t x) i j
  have hcontr :=
    actualRm04Contr_eq_canonical (I := I) (M := M) horth htrace i j
  calc
    ricciActualReactAt (I := I) S t x
        (vec2 (I := I) (basis i) (basis j)) =
      (-2 : Real) *
          rm04RicciContrAt (I := I) (M := M) (S.base.metric t)
            (S.base.rm04 t x) (S.ricci t x)
            (vec2 (I := I) (basis i) (basis j)) -
        2 * ricciQuadAt (I := I) (M := M) (S.base.metric t)
            (S.ricci t x) (vec2 (I := I) (basis i) (basis j)) := by
        exact actualReact_apply (I := I) (M := M) S t x
          (vec2 (I := I) (basis i) (basis j))
    _ =
      2 *
          rm04RicciContrAt (I := I) (M := M) (S.base.metric t)
            (rm04OfRic3At (I := I) (M := M) (S.base.metric t)
              (S.ricci t x)) (S.ricci t x)
            (vec2 (I := I) (basis i) (basis j)) -
        2 * ricciQuadAt (I := I) (M := M) (S.base.metric t)
            (S.ricci t x) (vec2 (I := I) (basis i) (basis j)) := by
        rw [hactual, hcanon, hcontr]
        ring
    _ =
      ricciReaction3At (I := I) (M := M) (S.base.metric t) (S.ricci t x)
        (vec2 (I := I) (basis i) (basis j)) := by
        exact (reaction3_apply (I := I) (M := M) (S.base.metric t)
          (S.ricci t x) (vec2 (I := I) (basis i) (basis j))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciActualReactAt_eq_reaction3 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciActualReactAt_eq_reaction3"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciActualReactAt_eq_reaction3 ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciActualReactAt_eq_reaction3

theorem ricciCoordReact_eq_actual
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v : TangentSpace I x) :
    ricciCoordReact (I := I) S t x v =
      ricciActualReactAt (I := I) S t x
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) := by
  classical
  let b := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x
  let frame := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
  let gInvAt : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j => coordInv (I := I) S x t x i j
  have hinv :
      MetricInverseInBasis (I := I) (S.base.metric t) x b gInvAt := by
    simpa [b, gInvAt] using coordInvReal (I := I) S x t
  have hbasis :
      ∀ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        b i = frame i x := by
    intro i
    simp [b, frame, DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply]
  have hcomp :
      ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ricciActualReactAt (I := I) S t x
            (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (frame i x) (frame j x)) =
          (-2 : Real) *
              rmRicciContractionCompInFrame
                (I := I) S S.base.rm04 (coordInv (I := I) S x)
                frame t x i j -
            2 * ricciQuadraticCompInFrame
                (I := I) S (coordInv (I := I) S x) frame t x i j := by
    intro i j
    have hrm :=
      rm04ContrAt_comp_basis (I := I) (M := M) b gInvAt hinv
        (S.base.rm04 t x) (S.ricci t x) i j
    have hquad :=
      ricciQuadAt_comp_basis (I := I) (M := M) b gInvAt hinv
        (S.ricci t x) i j
    calc
      ricciActualReactAt (I := I) S t x
          (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (frame i x) (frame j x)) =
        (-2 : Real) *
            rm04RicciContrAt (I := I) (M := M) (S.base.metric t)
              (S.base.rm04 t x) (S.ricci t x)
              (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (frame i x) (frame j x)) -
          2 * ricciQuadAt (I := I) (M := M) (S.base.metric t)
              (S.ricci t x)
              (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (frame i x) (frame j x)) := by
          exact actualReact_apply (I := I) (M := M) S t x
            (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (frame i x) (frame j x))
      _ =
        (-2 : Real) *
            DifferentialGeometry.Geometry.Curvature.rm04RicciContractionAt (I := I) b
              (S.base.rm04 t x)
              gInvAt (S.ricci t x) i j -
          2 * DifferentialGeometry.Geometry.Curvature.ricciQuadraticAt (I := I) b gInvAt
              (S.ricci t x) i j := by
          rw [← hbasis i, ← hbasis j]
          rw [hrm, hquad]
      _ =
          (-2 : Real) *
              rmRicciContractionCompInFrame
                (I := I) S S.base.rm04 (coordInv (I := I) S x)
                frame t x i j -
            2 * ricciQuadraticCompInFrame
                (I := I) S (coordInv (I := I) S x) frame t x i j := by
          simp [rmRicciContractionCompInFrame, raisedRicciCompInFrame,
            ricciQuadraticCompInFrame, ricciOneUpCompInFrame, ricciCompInFrame,
            DifferentialGeometry.Geometry.Curvature.rm04Comp,
              DifferentialGeometry.Geometry.Curvature.rm04Comp,
            DifferentialGeometry.Geometry.Curvature.rm04RicciContractionAt,
              DifferentialGeometry.Geometry.Curvature.raised02CompAt,
            DifferentialGeometry.Geometry.Curvature.ricciQuadraticAt,
              DifferentialGeometry.Geometry.Curvature.oneUp02CompAt,
            SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionOn.ricci,
            SolutionFamily.ricci, b, frame, gInvAt, hbasis]
  have hcomp_if :
      ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ricciActualReactAt (I := I) S t x
            (fun q : Fin 2 =>
              if q = 0 then frame i x else frame j x) =
          (-2 : Real) *
              rmRicciContractionCompInFrame
                (I := I) S S.base.rm04 (coordInv (I := I) S x)
                frame t x i j -
            2 * ricciQuadraticCompInFrame
                (I := I) S (coordInv (I := I) S x) frame t x i j := by
    intro i j
    rw [show (fun q : Fin 2 => if q = 0 then frame i x else frame j x) =
      DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (frame i x) (frame j x) by rfl]
    exact hcomp i j
  have hsum :=
    DifferentialGeometry.Tensor.Coordinates.tensor0S_two_eval_coordFrame_sum (I := I)
      (M := M) (x₀ := x) (Ax := ricciActualReactAt (I := I) S t x) v v
  symm
  change ricciActualReactAt (I := I) S t x
      (fun q : Fin 2 => if q = 0 then v else v) =
    ricciCoordReact (I := I) S t x v
  rw [hsum]
  simp only [ricciCoordReact, ricciCoordQuadRHS, ricciCoordRough,
    ricciEvolutionRHSInFrame, hcomp_if, frame]
  let c : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord i v *
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord j v
  let L : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j => coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x) t x i j
  let R : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      rmRicciContractionCompInFrame
        (I := I) S S.base.rm04 (coordInv (I := I) S x)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x) t x i j
  let Q : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      ricciQuadraticCompInFrame
        (I := I) S (coordInv (I := I) S x)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x) t x i j
  change
    (∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
      ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        c i j * ((-2 : Real) * R i j - 2 * Q i j)) =
      (∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          c i j * (L i j - 2 * R i j - 2 * Q i j)) -
        ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            c i j * L i j
  exact sum_coord_react_cancel c L R Q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciCoordReact_eq_actual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciCoordReact_eq_actual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciCoordReact_eq_actual ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciCoordReact_eq_actual


theorem ricciCoordReact_eq_reaction3
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (v : TangentSpace I x) :
    ricciCoordReact (I := I) S t x v =
      ricciReaction3At (I := I) (M := M) (S.base.metric t) (S.ricci t x)
        (vec2 (I := I) v v) := by
  by_cases hv : v = 0
  · subst v
    have hsym : DifferentialGeometry.Geometry.Curvature.RicciSymAt (I := I) (S.ricci t x) :=
      ricciAt_symm (I := I) S t x
    obtain ⟨basis, _l1, _l2, _l3, horth, _hdiag⟩ :=
      ricciEigen3 (I := I) (M := M) (S.base.metric t) (S.ricci t x) hdim hsym
    have hreact := ricciActualReactAt_eq_reaction3 (I := I) (M := M) S t x basis horth
    rw [ricciCoordReact_eq_actual (I := I) S t x 0]
    rw [← hreact]
  · obtain ⟨nb⟩ :=
      exists_nullOrthonormalBasis3At (I := I) (M := M) (S.base.metric t)
        (x := x) (v := v) hdim hv
    have hreact := ricciActualReactAt_eq_reaction3 (I := I) (M := M) S t x
      nb.basis nb.orthonormal
    rw [ricciCoordReact_eq_actual (I := I) S t x v]
    rw [← hreact]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciCoordReact_eq_reaction3 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciCoordReact_eq_reaction3"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciCoordReact_eq_reaction3 ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciCoordReact_eq_reaction3

theorem pairReact_eq_actual
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v w : TangentSpace I x) :
    ricciPairReact (I := I) S t x v w =
      ricciActualReactAt (I := I) S t x
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w) := by
  classical
  let b := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x
  let frame := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
  let gInvAt : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j => coordInv (I := I) S x t x i j
  have hinv :
      MetricInverseInBasis (I := I) (S.base.metric t) x b gInvAt := by
    simpa [b, gInvAt] using coordInvReal (I := I) S x t
  have hbasis :
      ∀ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        b i = frame i x := by
    intro i
    simp [b, frame, DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply]
  have hcomp :
      ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ricciActualReactAt (I := I) S t x
            (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (frame i x) (frame j x)) =
          (-2 : Real) *
              rmRicciContractionCompInFrame
                (I := I) S S.base.rm04 (coordInv (I := I) S x)
                frame t x i j -
            2 * ricciQuadraticCompInFrame
                (I := I) S (coordInv (I := I) S x) frame t x i j := by
    intro i j
    calc
      ricciActualReactAt (I := I) S t x
          (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (frame i x) (frame j x)) =
        ricciActualReactAt (I := I) S t x
          (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (b i) (b j)) := by
            rw [hbasis i, hbasis j]
      _ =
        (-2 : Real) *
            DifferentialGeometry.Geometry.Curvature.rm04RicciContractionAt
              (I := I) b (S.base.rm04 t x) gInvAt (S.ricci t x) i j -
          2 * DifferentialGeometry.Geometry.Curvature.ricciQuadraticAt
            (I := I) b gInvAt (S.ricci t x) i j :=
        actualReact_comp (I := I) (M := M) S t x b gInvAt hinv i j
      _ =
          (-2 : Real) *
              rmRicciContractionCompInFrame
                (I := I) S S.base.rm04 (coordInv (I := I) S x)
                frame t x i j -
            2 * ricciQuadraticCompInFrame
                (I := I) S (coordInv (I := I) S x) frame t x i j := by
          simp [rmRicciContractionCompInFrame, raisedRicciCompInFrame,
            ricciQuadraticCompInFrame, ricciOneUpCompInFrame, ricciCompInFrame,
            DifferentialGeometry.Geometry.Curvature.rm04Comp,
            DifferentialGeometry.Geometry.Curvature.rm04RicciContractionAt,
            DifferentialGeometry.Geometry.Curvature.raised02CompAt,
            DifferentialGeometry.Geometry.Curvature.ricciQuadraticAt,
            DifferentialGeometry.Geometry.Curvature.oneUp02CompAt,
            SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionOn.ricci,
            SolutionFamily.ricci, b, frame, gInvAt, hbasis]
  have hcomp_if :
      ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ricciActualReactAt (I := I) S t x
            (fun q : Fin 2 => if q = 0 then frame i x else frame j x) =
          (-2 : Real) *
              rmRicciContractionCompInFrame
                (I := I) S S.base.rm04 (coordInv (I := I) S x)
                frame t x i j -
            2 * ricciQuadraticCompInFrame
                (I := I) S (coordInv (I := I) S x) frame t x i j := by
    intro i j
    rw [show (fun q : Fin 2 => if q = 0 then frame i x else frame j x) =
      DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (frame i x) (frame j x) by rfl]
    exact hcomp i j
  have hsum :=
    DifferentialGeometry.Tensor.Coordinates.tensor0S_two_eval_coordFrame_sum (I := I)
      (M := M) (x₀ := x) (Ax := ricciActualReactAt (I := I) S t x) v w
  symm
  change ricciActualReactAt (I := I) S t x
      (fun q : Fin 2 => if q = 0 then v else w) =
    ricciPairReact (I := I) S t x v w
  rw [hsum]
  simp only [ricciPairReact, ricciPairRHS, ricciEvolutionRHSInFrame,
    hcomp_if, frame]
  let c : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord i v *
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x).coord j w
  let L : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j => coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x) t x i j
  let R : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      rmRicciContractionCompInFrame
        (I := I) S S.base.rm04 (coordInv (I := I) S x)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x) t x i j
  let Q : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      ricciQuadraticCompInFrame
        (I := I) S (coordInv (I := I) S x)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x) t x i j
  change
    (∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
      ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        c i j * ((-2 : Real) * R i j - 2 * Q i j)) =
      (∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          c i j * (L i j - 2 * R i j - 2 * Q i j)) -
        ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            c i j * L i j
  exact sum_coord_react_cancel c L R Q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pairReact_eq_actual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pairReact_eq_actual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pairReact_eq_actual ``Submission.DifferentialGeometry.PDE.RicciFlow.pairReact_eq_actual

theorem ricciPairDeriv
    [I.Boundaryless]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real => S.ricci s x
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w))
      (metricTraceFirstTwo0SAt (I := I) (S.base.metric (t : Real))
          (ricciNabla2WeakMaximumPrinciple (I := I) S (t : Real) x)
          (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w) +
        ricciActualReactAt (I := I) S (t : Real) x
          (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w))
      D.carrier (t : Real) := by
  have hcoord := ricciPairCoord (I := I) S hS x t v w
  have hrough := ricciRoughPair (I := I) S (t : Real) x v w
  have hreact := pairReact_eq_actual (I := I) S (t : Real) x v w
  have hvalue :
      ricciPairRHS (I := I) S (t : Real) x v w =
        metricTraceFirstTwo0SAt (I := I) (S.base.metric (t : Real))
            (ricciNabla2WeakMaximumPrinciple (I := I) S (t : Real) x)
            (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w) +
          ricciActualReactAt (I := I) S (t : Real) x
            (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w) := by
    unfold ricciPairReact at hreact
    rw [hrough]
    linarith
  exact hcoord.congr_deriv hvalue

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciPairDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciPairDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciPairDeriv ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciPairDeriv

theorem shiftNRaw_pinchCoordReact
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {delta t : Real} {x : M}
    (hdelta13 : delta < (1 : Real) / 3)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (v : TangentSpace I x) :
    (shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M)
        (pinchSec (I := I) S delta) t)) x v v =
      pinchCoordReact (I := I) S delta t x v := by
  classical
  by_cases hv : v = 0
  · subst v
    have hvec0 :
        vec2 (I := I) (0 : TangentSpace I x) 0 =
          (0 : Fin 2 → TangentSpace I x) := by
      funext q
      fin_cases q <;> rfl
    have hric :
        ricciCoordReact (I := I) S t x 0 = 0 := by
      rw [ricciCoordReact_eq_actual (I := I) S t x 0]
      rw [actualReact_apply (I := I) (M := M) S t x
        (vec2 (I := I) (0 : TangentSpace I x) 0)]
      rw [hvec0, tensor02_zero_apply, tensor02_zero_apply]
      ring
    rw [shiftNRaw_pinch (I := I) (M := M) S delta t (S.base.metric t) x 0 0]
    have hN :
        shiftNAt (I := I) (M := M) delta t (S.base.metric t) x
            ((pinchSec (I := I) S delta) t x)
            (vec2 (I := I) (0 : TangentSpace I x) 0) = 0 := by
      rw [hvec0]
      exact tensor02_zero_apply _
    rw [hN]
    unfold pinchCoordReact
    rw [hric]
    have hRicZero :
        S.ricciAt t x (vec2 (I := I) (0 : TangentSpace I x) 0) = 0 := by
      rw [hvec0]
      exact tensor02_zero_apply _
    rw [hRicZero]
    simp
  · obtain ⟨nb⟩ :=
      exists_nullOrthonormalBasis3At (I := I) (M := M)
        (S.base.metric t) hdim hv
    have hpinch := pinchSec_at_trace (I := I) (M := M) S delta t x
    have hden : (1 : Real) - 3 * delta ≠ 0 := by nlinarith
    have hshift :=
      shiftNAt_pinch (I := I) (M := M) nb.basis nb.orthonormal
        hden (S.ricci t x) (t := t)
    have hactual :=
      ricciActualReactAt_eq_reaction3 (I := I) (M := M) S t x
        nb.basis nb.orthonormal
    have hcoord := ricciCoordReact_eq_actual (I := I) S t x v
    rw [shiftNRaw_pinch (I := I) (M := M) S delta t (S.base.metric t) x v v]
    rw [hpinch, hshift, ← hactual]
    simp only [Tensor0SSpace.sub_apply, real_smul0S_apply]
    rw [← hcoord]
    simp [pinchCoordReact, metricTensorField_apply,
      SolutionOn.scalar_eq_metricTrace, vec2, DifferentialGeometry.Geometry.Curvature.vec2]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shiftNRaw_pinchCoordReact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shiftNRaw_pinchCoordReact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shiftNRaw_pinchCoordReact ``Submission.DifferentialGeometry.PDE.RicciFlow.shiftNRaw_pinchCoordReact

end DifferentialGeometry.PDE.RicciFlow
