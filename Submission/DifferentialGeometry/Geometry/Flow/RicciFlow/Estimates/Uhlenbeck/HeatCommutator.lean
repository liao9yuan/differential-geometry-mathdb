import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.FullyPulledDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped _root_.BigOperators

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

def covariantTensorSkewAction {q : Nat}
    (A : (Fin q -> Idx) -> Real) (c d : Idx) (b : Fin q -> Idx) : Real :=
  ∑ r : Fin q,
    ((if c = b r then A (Function.update b r d) else 0) -
      (if d = b r then A (Function.update b r c) else 0))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covariantTensorSkewAction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covariantTensorSkewAction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covariantTensorSkewAction ``Submission.DifferentialGeometry.PDE.RicciFlow.covariantTensorSkewAction

def curvatureSkewActionContraction {q : Nat}
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (DA : Idx -> (Fin q -> Idx) -> Real)
    (a : Idx) (b : Fin q -> Idx) : Real :=
  ∑ e : Idx, ∑ c : Idx, ∑ d : Idx,
    R a e d c * covariantTensorSkewAction (DA e) c d b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvatureSkewActionContraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvatureSkewActionContraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvatureSkewActionContraction ``Submission.DifferentialGeometry.PDE.RicciFlow.curvatureSkewActionContraction

def curvatureSlotActionContraction {q : Nat}
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (DA : Idx -> (Fin q -> Idx) -> Real)
    (a : Idx) (b : Fin q -> Idx) : Real :=
  2 * ∑ r : Fin q, ∑ e : Idx, ∑ d : Idx,
    R a e d (b r) * DA e (Function.update b r d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvatureSlotActionContraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvatureSlotActionContraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvatureSlotActionContraction ``Submission.DifferentialGeometry.PDE.RicciFlow.curvatureSlotActionContraction

theorem curvatureSkewActionContraction_eq_slots {q : Nat}
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (DA : Idx -> (Fin q -> Idx) -> Real)
    (hskew : ∀ a e c d, R a e c d = -R a e d c)
    (a : Idx) (b : Fin q -> Idx) :
    curvatureSkewActionContraction R DA a b =
      curvatureSlotActionContraction R DA a b := by
  classical
  have hslot (r : Fin q) (e : Idx) :
      (∑ c : Idx, ∑ d : Idx,
        R a e d c *
          ((if c = b r then DA e (Function.update b r d) else 0) -
            (if d = b r then DA e (Function.update b r c) else 0))) =
        2 * ∑ d : Idx,
          R a e d (b r) * DA e (Function.update b r d) := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, _root_.MulZeroClass.mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_pos]
    have hfirst :
        (∑ c : Idx, ∑ d : Idx,
          if c = b r then R a e d c * DA e (Function.update b r d) else 0) =
          ∑ d : Idx, R a e d (b r) * DA e (Function.update b r d) := by
      rw [Finset.sum_eq_single (b r)]
      · simp
      · intro c _ hc
        simp [hc]
      · intro h
        exact False.elim (h (Finset.mem_univ (b r)))
    rw [hfirst]
    calc
      (∑ d : Idx, R a e d (b r) * DA e (Function.update b r d)) -
          ∑ c : Idx, R a e (b r) c * DA e (Function.update b r c) =
        (∑ d : Idx, R a e d (b r) * DA e (Function.update b r d)) -
          ∑ c : Idx, (-R a e c (b r)) * DA e (Function.update b r c) := by
            congr 1
            refine Finset.sum_congr rfl fun c _ ↦ ?_
            rw [hskew a e (b r) c]
      _ = 2 * ∑ d : Idx,
          R a e d (b r) * DA e (Function.update b r d) := by
            simp only [neg_mul, Finset.sum_neg_distrib]
            ring
  simp only [curvatureSkewActionContraction, curvatureSlotActionContraction,
    covariantTensorSkewAction, Finset.mul_sum]
  calc
    (∑ e : Idx, ∑ c : Idx, ∑ d : Idx, ∑ r : Fin q,
        R a e d c *
          ((if c = b r then DA e (Function.update b r d) else 0) -
            (if d = b r then DA e (Function.update b r c) else 0))) =
      ∑ r : Fin q, ∑ e : Idx, ∑ c : Idx, ∑ d : Idx,
        R a e d c *
          ((if c = b r then DA e (Function.update b r d) else 0) -
            (if d = b r then DA e (Function.update b r c) else 0)) := by
          calc
            _ = ∑ e : Idx, ∑ c : Idx, ∑ r : Fin q, ∑ d : Idx,
                R a e d c *
                  ((if c = b r then DA e (Function.update b r d) else 0) -
                    (if d = b r then DA e (Function.update b r c) else 0)) := by
                  refine Finset.sum_congr rfl fun e _ ↦ ?_
                  refine Finset.sum_congr rfl fun c _ ↦ ?_
                  exact Finset.sum_comm
            _ = ∑ e : Idx, ∑ r : Fin q, ∑ c : Idx, ∑ d : Idx,
                R a e d c *
                  ((if c = b r then DA e (Function.update b r d) else 0) -
                    (if d = b r then DA e (Function.update b r c) else 0)) := by
                  refine Finset.sum_congr rfl fun e _ ↦ ?_
                  exact Finset.sum_comm
            _ = _ := Finset.sum_comm
    _ = ∑ r : Fin q, ∑ e : Idx,
        2 * ∑ d : Idx,
          R a e d (b r) * DA e (Function.update b r d) := by
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          refine Finset.sum_congr rfl fun e _ ↦ hslot r e
    _ = ∑ r : Fin q, ∑ e : Idx, ∑ d : Idx,
        2 * (R a e d (b r) * DA e (Function.update b r d)) := by
          simp only [Finset.mul_sum]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvatureSkewActionContraction_eq_slots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvatureSkewActionContraction_eq_slots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvatureSkewActionContraction_eq_slots ``Submission.DifferentialGeometry.PDE.RicciFlow.curvatureSkewActionContraction_eq_slots

omit [DecidableEq Idx] in
@[simp] theorem curvatureSlotActionContraction_zero
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (DA : Idx -> (Fin 0 -> Idx) -> Real)
    (a : Idx) (b : Fin 0 -> Idx) :
    curvatureSlotActionContraction R DA a b = 0 := by
  simp [curvatureSlotActionContraction]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvatureSlotActionContraction_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvatureSlotActionContraction_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvatureSlotActionContraction_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.curvatureSlotActionContraction_zero

omit [DecidableEq Idx] in
theorem curvatureSlotActionContraction_one
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (DA : Idx -> Idx -> Real) (a b : Idx) :
    curvatureSlotActionContraction R (fun e (slots : Fin 1 -> Idx) ↦ DA e (slots 0)) a
        (fun _ ↦ b) =
      2 * ∑ e : Idx, ∑ d : Idx, R a e d b * DA e d := by
  simp [curvatureSlotActionContraction]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvatureSlotActionContraction_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvatureSlotActionContraction_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvatureSlotActionContraction_one ``Submission.DifferentialGeometry.PDE.RicciFlow.curvatureSlotActionContraction_one

def covariantTensorSecondDerivativeCommutatorComponents {q : Nat}
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (A : (Fin q -> Idx) -> Real)
    (D2A : Idx -> Idx -> (Fin q -> Idx) -> Real) : Prop :=
  forall a b slots,
    D2A a b slots - D2A b a slots =
      (1 / 2 : Real) * ∑ c : Idx, ∑ d : Idx,
        R a b d c * covariantTensorSkewAction A c d slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covariantTensorSecondDerivativeCommutatorComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covariantTensorSecondDerivativeCommutatorComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covariantTensorSecondDerivativeCommutatorComponents ``Submission.DifferentialGeometry.PDE.RicciFlow.covariantTensorSecondDerivativeCommutatorComponents

theorem half_curvature_skew_action_eq_slots {q : Nat}
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (A : (Fin q -> Idx) -> Real)
    (hskewLast : forall a b c d, R a b c d = -R a b d c)
    (a b : Idx) (slots : Fin q -> Idx) :
    (1 / 2 : Real) * ∑ c : Idx, ∑ d : Idx,
        R a b d c * covariantTensorSkewAction A c d slots =
      ∑ r : Fin q, ∑ d : Idx,
        R a b d (slots r) * A (Function.update slots r d) := by
  classical
  have hslot (r : Fin q) :
      (∑ c : Idx, ∑ d : Idx,
          R a b d c *
            ((if c = slots r then A (Function.update slots r d) else 0) -
              (if d = slots r then A (Function.update slots r c) else 0))) =
        2 * ∑ d : Idx, R a b d (slots r) * A (Function.update slots r d) := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, _root_.MulZeroClass.mul_zero]
    have hfirst :
        (∑ c : Idx, ∑ d : Idx,
            if c = slots r then
              R a b d c * A (Function.update slots r d) else 0) =
          ∑ d : Idx,
            R a b d (slots r) * A (Function.update slots r d) := by
      rw [Finset.sum_eq_single (slots r)]
      · simp
      · intro c _ hc
        simp [hc]
      · intro h
        exact False.elim (h (Finset.mem_univ (slots r)))
    have hsecond :
        (∑ c : Idx, ∑ d : Idx,
            if d = slots r then
              R a b d c * A (Function.update slots r c) else 0) =
          ∑ c : Idx,
            R a b (slots r) c * A (Function.update slots r c) := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_eq_single (slots r)]
      · simp
      · intro d _ hd
        simp [hd]
      · intro h
        exact False.elim (h (Finset.mem_univ (slots r)))
    rw [hfirst, hsecond]
    calc
      (∑ d : Idx, R a b d (slots r) * A (Function.update slots r d)) -
          ∑ c : Idx, R a b (slots r) c * A (Function.update slots r c) =
        (∑ d : Idx, R a b d (slots r) * A (Function.update slots r d)) -
          ∑ c : Idx, (-R a b c (slots r)) * A (Function.update slots r c) := by
            congr 1
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [hskewLast a b (slots r) c]
      _ = _ := by
        simp only [neg_mul, Finset.sum_neg_distrib]
        ring_nf
  simp only [covariantTensorSkewAction]
  calc
    (1 / 2 : Real) *
        (∑ c : Idx, ∑ d : Idx,
          R a b d c *
            ∑ r : Fin q,
              ((if c = slots r then A (Function.update slots r d) else 0) -
                (if d = slots r then A (Function.update slots r c) else 0))) =
      (1 / 2 : Real) *
        (∑ c : Idx, ∑ d : Idx, ∑ r : Fin q,
          R a b d c *
            ((if c = slots r then A (Function.update slots r d) else 0) -
              (if d = slots r then A (Function.update slots r c) else 0))) := by
        congr 1
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum]
    _ =
    (1 / 2 : Real) *
        ∑ r : Fin q, ∑ c : Idx, ∑ d : Idx,
          R a b d c *
            ((if c = slots r then A (Function.update slots r d) else 0) -
              (if d = slots r then A (Function.update slots r c) else 0)) := by
        congr 1
        calc
          (∑ c : Idx, ∑ d : Idx, ∑ r : Fin q,
              R a b d c *
                ((if c = slots r then A (Function.update slots r d) else 0) -
                  (if d = slots r then A (Function.update slots r c) else 0))) =
            ∑ c : Idx, ∑ r : Fin q, ∑ d : Idx,
              R a b d c *
                ((if c = slots r then A (Function.update slots r d) else 0) -
                  (if d = slots r then A (Function.update slots r c) else 0)) := by
            refine Finset.sum_congr rfl fun c _ => Finset.sum_comm
          _ = _ := Finset.sum_comm
    _ = (1 / 2 : Real) *
        ∑ r : Fin q, 2 * ∑ d : Idx,
          R a b d (slots r) * A (Function.update slots r d) := by
      congr 1
      refine Finset.sum_congr rfl fun r _ => hslot r
    _ = _ := by
      simp only [Finset.mul_sum]
      ring_nf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.half_curvature_skew_action_eq_slots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.half_curvature_skew_action_eq_slots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.half_curvature_skew_action_eq_slots ``Submission.DifferentialGeometry.PDE.RicciFlow.half_curvature_skew_action_eq_slots

theorem covariantTensorSecondDerivativeCommutatorComponents_eq_slots {q : Nat}
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (A : (Fin q -> Idx) -> Real)
    (D2A : Idx -> Idx -> (Fin q -> Idx) -> Real)
    (hcomm : covariantTensorSecondDerivativeCommutatorComponents R A D2A)
    (hskewLast : forall a b c d, R a b c d = -R a b d c)
    (a b : Idx) (slots : Fin q -> Idx) :
    D2A a b slots - D2A b a slots =
      ∑ r : Fin q, ∑ d : Idx,
        R a b d (slots r) * A (Function.update slots r d) := by
  rw [hcomm a b slots]
  exact half_curvature_skew_action_eq_slots R A hskewLast a b slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covariantTensorSecondDerivativeCommutatorComponents_eq_slots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covariantTensorSecondDerivativeCommutatorComponents_eq_slots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covariantTensorSecondDerivativeCommutatorComponents_eq_slots ``Submission.DifferentialGeometry.PDE.RicciFlow.covariantTensorSecondDerivativeCommutatorComponents_eq_slots

def covariantTensorRicciSlotAction {q : Nat}
    (Ric : Idx -> Idx -> Real) (A : (Fin q -> Idx) -> Real)
    (b : Fin q -> Idx) : Real :=
  ∑ r : Fin q, ∑ c : Idx,
    Ric (b r) c * A (Function.update b r c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covariantTensorRicciSlotAction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covariantTensorRicciSlotAction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covariantTensorRicciSlotAction ``Submission.DifferentialGeometry.PDE.RicciFlow.covariantTensorRicciSlotAction

def covariantTensorNablaRicciSlotAction {q : Nat}
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (A : (Fin q -> Idx) -> Real) (a : Idx) (b : Fin q -> Idx) : Real :=
  ∑ r : Fin q, ∑ c : Idx,
    nablaRic a (b r) c * A (Function.update b r c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covariantTensorNablaRicciSlotAction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covariantTensorNablaRicciSlotAction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covariantTensorNablaRicciSlotAction ``Submission.DifferentialGeometry.PDE.RicciFlow.covariantTensorNablaRicciSlotAction

def ricciFlowConnectionVariationOrthonormal
    (nablaRic : Idx -> Idx -> Idx -> Real) (a b c : Idx) : Real :=
  -nablaRic a b c - nablaRic b a c + nablaRic c a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciFlowConnectionVariationOrthonormal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciFlowConnectionVariationOrthonormal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciFlowConnectionVariationOrthonormal ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciFlowConnectionVariationOrthonormal

def uhlenbeckTimeDerivativeOfCovariantDerivative {q : Nat}
    (Ric : Idx -> Idx -> Real) (nablaRic : Idx -> Idx -> Idx -> Real)
    (A : (Fin q -> Idx) -> Real) (DA : Idx -> (Fin q -> Idx) -> Real)
    (nablaDtA : Idx -> (Fin q -> Idx) -> Real)
    (a : Idx) (b : Fin q -> Idx) : Real :=
  nablaDtA a b -
      ∑ r : Fin q, ∑ c : Idx,
        ricciFlowConnectionVariationOrthonormal nablaRic a (b r) c *
          A (Function.update b r c) +
    (∑ c : Idx, Ric a c * DA c b) +
    covariantTensorRicciSlotAction Ric (DA a) b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeckTimeDerivativeOfCovariantDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeckTimeDerivativeOfCovariantDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeckTimeDerivativeOfCovariantDerivative ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeckTimeDerivativeOfCovariantDerivative

def uhlenbeckCovariantDerivativeOfTimeDerivative {q : Nat}
    (Ric : Idx -> Idx -> Real) (nablaRic : Idx -> Idx -> Idx -> Real)
    (A : (Fin q -> Idx) -> Real) (DA : Idx -> (Fin q -> Idx) -> Real)
    (nablaDtA : Idx -> (Fin q -> Idx) -> Real)
    (a : Idx) (b : Fin q -> Idx) : Real :=
  nablaDtA a b + covariantTensorNablaRicciSlotAction nablaRic A a b +
    covariantTensorRicciSlotAction Ric (DA a) b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCovariantDerivativeOfTimeDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeckCovariantDerivativeOfTimeDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCovariantDerivativeOfTimeDerivative ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeckCovariantDerivativeOfTimeDerivative

private theorem nablaRicciSkewAction_eq_slots {q : Nat}
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (A : (Fin q -> Idx) -> Real) (a : Idx) (b : Fin q -> Idx) :
    (∑ c : Idx, ∑ d : Idx,
        nablaRic c a d * covariantTensorSkewAction A c d b) =
      ∑ r : Fin q, ∑ c : Idx,
        (nablaRic (b r) a c - nablaRic c a (b r)) *
          A (Function.update b r c) := by
  classical
  simp only [covariantTensorSkewAction, Finset.mul_sum, mul_sub,
    mul_ite, _root_.MulZeroClass.mul_zero]
  calc
    (∑ c : Idx, ∑ d : Idx, ∑ r : Fin q,
        ((if c = b r then nablaRic c a d * A (Function.update b r d) else 0) -
          (if d = b r then nablaRic c a d * A (Function.update b r c) else 0))) =
      ∑ r : Fin q, ∑ c : Idx, ∑ d : Idx,
        ((if c = b r then nablaRic c a d * A (Function.update b r d) else 0) -
          (if d = b r then nablaRic c a d * A (Function.update b r c) else 0)) := by
            calc
              _ = ∑ c : Idx, ∑ r : Fin q, ∑ d : Idx,
                  ((if c = b r then nablaRic c a d * A (Function.update b r d) else 0) -
                    (if d = b r then nablaRic c a d * A (Function.update b r c) else 0)) := by
                      refine Finset.sum_congr rfl fun c _ ↦ ?_
                      exact Finset.sum_comm
              _ = _ := Finset.sum_comm
    _ = ∑ r : Fin q,
        ((∑ d : Idx, nablaRic (b r) a d * A (Function.update b r d)) -
          ∑ c : Idx, nablaRic c a (b r) * A (Function.update b r c)) := by
            refine Finset.sum_congr rfl fun r _ ↦ ?_
            simp only [Finset.sum_sub_distrib]
            congr 1
            · rw [Finset.sum_eq_single (b r)]
              · simp
              · intro c _ hc
                simp [hc]
              · intro h
                exact False.elim (h (Finset.mem_univ (b r)))
            · refine Finset.sum_congr rfl fun c _ ↦ ?_
              simp
    _ = ∑ r : Fin q, ∑ c : Idx,
        (nablaRic (b r) a c - nablaRic c a (b r)) *
          A (Function.update b r c) := by
            refine Finset.sum_congr rfl fun r _ ↦ ?_
            calc
              (∑ d : Idx, nablaRic (b r) a d * A (Function.update b r d)) -
                  ∑ c : Idx, nablaRic c a (b r) * A (Function.update b r c) =
                ∑ c : Idx,
                  (nablaRic (b r) a c * A (Function.update b r c) -
                    nablaRic c a (b r) * A (Function.update b r c)) := by
                      rw [Finset.sum_sub_distrib]
              _ = _ := by
                refine Finset.sum_congr rfl fun c _ ↦ ?_
                ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaRicciSkewAction_eq_slots
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.nablaRicciSkewAction_eq_slots target :: scope.openDecls } }

theorem uhlenbeck_time_covariantDerivative_commutator {q : Nat}
    (Ric : Idx -> Idx -> Real) (nablaRic : Idx -> Idx -> Idx -> Real)
    (A : (Fin q -> Idx) -> Real) (DA : Idx -> (Fin q -> Idx) -> Real)
    (nablaDtA : Idx -> (Fin q -> Idx) -> Real)
    (a : Idx) (b : Fin q -> Idx) :
    uhlenbeckTimeDerivativeOfCovariantDerivative Ric nablaRic A DA nablaDtA a b -
        uhlenbeckCovariantDerivativeOfTimeDerivative Ric nablaRic A DA nablaDtA a b =
      (∑ c : Idx, ∑ d : Idx,
        nablaRic c a d * covariantTensorSkewAction A c d b) +
      ∑ c : Idx, Ric a c * DA c b := by
  classical
  rw [nablaRicciSkewAction_eq_slots]
  have hconnection :
      -(∑ r : Fin q, ∑ c : Idx,
          ricciFlowConnectionVariationOrthonormal nablaRic a (b r) c *
            A (Function.update b r c)) -
          covariantTensorNablaRicciSlotAction nablaRic A a b =
        ∑ r : Fin q, ∑ c : Idx,
          (nablaRic (b r) a c - nablaRic c a (b r)) *
            A (Function.update b r c) := by
    rw [covariantTensorNablaRicciSlotAction]
    calc
      _ = ∑ r : Fin q, ∑ c : Idx,
          (-(ricciFlowConnectionVariationOrthonormal nablaRic a (b r) c *
              A (Function.update b r c)) -
            nablaRic a (b r) c * A (Function.update b r c)) := by
              simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      _ = _ := by
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        simp only [ricciFlowConnectionVariationOrthonormal]
        ring
  calc
    uhlenbeckTimeDerivativeOfCovariantDerivative Ric nablaRic A DA nablaDtA a b -
        uhlenbeckCovariantDerivativeOfTimeDerivative Ric nablaRic A DA nablaDtA a b =
      (-(∑ r : Fin q, ∑ c : Idx,
          ricciFlowConnectionVariationOrthonormal nablaRic a (b r) c *
            A (Function.update b r c)) -
        covariantTensorNablaRicciSlotAction nablaRic A a b) +
          ∑ c : Idx, Ric a c * DA c b := by
            simp only [uhlenbeckTimeDerivativeOfCovariantDerivative,
              uhlenbeckCovariantDerivativeOfTimeDerivative]
            ring
    _ = _ := by rw [hconnection]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeck_time_covariantDerivative_commutator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeck_time_covariantDerivative_commutator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeck_time_covariantDerivative_commutator ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeck_time_covariantDerivative_commutator

omit [DecidableEq Idx] in
theorem uhlenbeck_time_covariantDerivative_commutator_zero
    (Ric : Idx -> Idx -> Real) (nablaRic : Idx -> Idx -> Idx -> Real)
    (A : (Fin 0 -> Idx) -> Real) (DA : Idx -> (Fin 0 -> Idx) -> Real)
    (nablaDtA : Idx -> (Fin 0 -> Idx) -> Real)
    (a : Idx) (b : Fin 0 -> Idx) :
    uhlenbeckTimeDerivativeOfCovariantDerivative Ric nablaRic A DA nablaDtA a b -
        uhlenbeckCovariantDerivativeOfTimeDerivative Ric nablaRic A DA nablaDtA a b =
      ∑ c : Idx, Ric a c * DA c b := by
  classical
  simpa [covariantTensorSkewAction] using
    uhlenbeck_time_covariantDerivative_commutator
      (Ric := Ric) (nablaRic := nablaRic) (A := A) (DA := DA)
      (nablaDtA := nablaDtA) a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeck_time_covariantDerivative_commutator_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeck_time_covariantDerivative_commutator_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeck_time_covariantDerivative_commutator_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeck_time_covariantDerivative_commutator_zero

def prependCovariantDerivativeComponents {q : Nat}
    (DA : Idx -> (Fin q -> Idx) -> Real) (slots : Fin (q + 1) -> Idx) : Real :=
  DA (slots 0) (fun r ↦ slots r.succ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.prependCovariantDerivativeComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.prependCovariantDerivativeComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.prependCovariantDerivativeComponents ``Submission.DifferentialGeometry.PDE.RicciFlow.prependCovariantDerivativeComponents

omit [Fintype Idx] [DecidableEq Idx] in
private theorem prependCovariantDerivativeComponents_update_zero {q : Nat}
    (DA : Idx -> (Fin q -> Idx) -> Real) (e c : Idx) (b : Fin q -> Idx) :
    prependCovariantDerivativeComponents DA
        (Function.update (Fin.cons e b) 0 c) =
      DA c b := by
  classical
  simp [prependCovariantDerivativeComponents, Function.update]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.prependCovariantDerivativeComponents_update_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.prependCovariantDerivativeComponents_update_zero target :: scope.openDecls } }

omit [Fintype Idx] [DecidableEq Idx] in
private theorem prependCovariantDerivativeComponents_update_succ {q : Nat}
    (DA : Idx -> (Fin q -> Idx) -> Real) (e c : Idx) (b : Fin q -> Idx)
    (r : Fin q) :
    prependCovariantDerivativeComponents DA
        (Function.update (Fin.cons e b) r.succ c) =
      DA e (Function.update b r c) := by
  classical
  have hzero : ¬(0 : Fin (q + 1)) = r.succ := by
    exact (Fin.succ_ne_zero r) ∘ Eq.symm
  simp only [prependCovariantDerivativeComponents, Function.update_apply,
    hzero, if_false, Fin.cons_zero, Fin.cons_succ, Fin.succ_inj]
  apply congrArg (DA e)
  funext r₁
  simp only [Function.update_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.prependCovariantDerivativeComponents_update_succ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.prependCovariantDerivativeComponents_update_succ target :: scope.openDecls } }

omit [Fintype Idx] in
private theorem covariantTensorSkewAction_prepend {q : Nat}
    (DA : Idx -> (Fin q -> Idx) -> Real) (c d e : Idx)
    (b : Fin q -> Idx) :
    covariantTensorSkewAction (prependCovariantDerivativeComponents DA) c d
        (Fin.cons e b) =
      ((if c = e then DA d b else 0) - (if d = e then DA c b else 0)) +
        covariantTensorSkewAction (DA e) c d b := by
  classical
  rw [covariantTensorSkewAction, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ,
    prependCovariantDerivativeComponents_update_zero,
    prependCovariantDerivativeComponents_update_succ]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.covariantTensorSkewAction_prepend
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.covariantTensorSkewAction_prepend target :: scope.openDecls } }

omit [Fintype Idx] in
private theorem covariantTensorSkewAction_swap {q : Nat}
    (A : (Fin q -> Idx) -> Real) (c d : Idx) (b : Fin q -> Idx) :
    covariantTensorSkewAction A d c b =
      -covariantTensorSkewAction A c d b := by
  simp only [covariantTensorSkewAction]
  calc
    (∑ r, ((if d = b r then A (Function.update b r c) else 0) -
        (if c = b r then A (Function.update b r d) else 0))) =
      ∑ r, -((if c = b r then A (Function.update b r d) else 0) -
        (if d = b r then A (Function.update b r c) else 0)) := by
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          ring
    _ = -(∑ r, ((if c = b r then A (Function.update b r d) else 0) -
        (if d = b r then A (Function.update b r c) else 0))) :=
      by simp only [Finset.sum_neg_distrib]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.covariantTensorSkewAction_swap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.covariantTensorSkewAction_swap target :: scope.openDecls } }

def nablaCurvatureSkewActionContraction {q : Nat}
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (A : (Fin q -> Idx) -> Real) (a : Idx) (b : Fin q -> Idx) : Real :=
  ∑ e : Idx, ∑ c : Idx, ∑ d : Idx,
    nablaR e e a d c * covariantTensorSkewAction A c d b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nablaCurvatureSkewActionContraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nablaCurvatureSkewActionContraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nablaCurvatureSkewActionContraction ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaCurvatureSkewActionContraction

def gradientCurvatureSkewActionContraction {q : Nat}
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (DA : Idx -> (Fin q -> Idx) -> Real)
    (a : Idx) (b : Fin q -> Idx) : Real :=
  ∑ e : Idx, ∑ c : Idx, ∑ d : Idx,
    R e a d c *
      covariantTensorSkewAction (prependCovariantDerivativeComponents DA)
        c d (Fin.cons e b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.gradientCurvatureSkewActionContraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.gradientCurvatureSkewActionContraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.gradientCurvatureSkewActionContraction ``Submission.DifferentialGeometry.PDE.RicciFlow.gradientCurvatureSkewActionContraction

def roughLaplacianCovariantDerivativeComponents {q : Nat}
    (D3A : Idx -> Idx -> Idx -> (Fin q -> Idx) -> Real)
    (a : Idx) (b : Fin q -> Idx) : Real :=
  ∑ e : Idx, D3A e e a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.roughLaplacianCovariantDerivativeComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.roughLaplacianCovariantDerivativeComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.roughLaplacianCovariantDerivativeComponents ``Submission.DifferentialGeometry.PDE.RicciFlow.roughLaplacianCovariantDerivativeComponents

def covariantDerivativeRoughLaplacianComponents {q : Nat}
    (D3A : Idx -> Idx -> Idx -> (Fin q -> Idx) -> Real)
    (a : Idx) (b : Fin q -> Idx) : Real :=
  ∑ e : Idx, D3A a e e b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covariantDerivativeRoughLaplacianComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covariantDerivativeRoughLaplacianComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covariantDerivativeRoughLaplacianComponents ``Submission.DifferentialGeometry.PDE.RicciFlow.covariantDerivativeRoughLaplacianComponents

def differentiatedTensorRicciIdentityComponents {q : Nat}
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (A : (Fin q -> Idx) -> Real)
    (DA : Idx -> (Fin q -> Idx) -> Real)
    (D3A : Idx -> Idx -> Idx -> (Fin q -> Idx) -> Real) : Prop :=
  ∀ e a b,
    D3A e e a b - D3A e a e b =
      (1 / 2 : Real) *
        ((∑ c : Idx, ∑ d : Idx,
            nablaR e e a d c * covariantTensorSkewAction A c d b) +
          ∑ c : Idx, ∑ d : Idx,
            R e a d c * covariantTensorSkewAction (DA e) c d b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.differentiatedTensorRicciIdentityComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.differentiatedTensorRicciIdentityComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.differentiatedTensorRicciIdentityComponents ``Submission.DifferentialGeometry.PDE.RicciFlow.differentiatedTensorRicciIdentityComponents

def tensorGradientRicciIdentityComponents {q : Nat}
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (DA : Idx -> (Fin q -> Idx) -> Real)
    (D3A : Idx -> Idx -> Idx -> (Fin q -> Idx) -> Real) : Prop :=
  ∀ e a b,
    D3A e a e b - D3A a e e b =
      (1 / 2 : Real) *
        ∑ c : Idx, ∑ d : Idx,
          R e a d c *
            covariantTensorSkewAction (prependCovariantDerivativeComponents DA)
              c d (Fin.cons e b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.tensorGradientRicciIdentityComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.tensorGradientRicciIdentityComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.tensorGradientRicciIdentityComponents ``Submission.DifferentialGeometry.PDE.RicciFlow.tensorGradientRicciIdentityComponents

def contractedCurvatureDerivativeComponents
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ a c d,
    (∑ e : Idx, nablaR e e a d c) =
      nablaRic c a d - nablaRic d a c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.contractedCurvatureDerivativeComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.contractedCurvatureDerivativeComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.contractedCurvatureDerivativeComponents ``Submission.DifferentialGeometry.PDE.RicciFlow.contractedCurvatureDerivativeComponents

def curvatureRicciTraceComponents
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real) : Prop :=
  ∀ a d, (∑ e : Idx, R e a d e) = Ric a d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvatureRicciTraceComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvatureRicciTraceComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvatureRicciTraceComponents ``Submission.DifferentialGeometry.PDE.RicciFlow.curvatureRicciTraceComponents

omit [DecidableEq Idx] in
private theorem half_skewDifference_contraction
    (F K : Idx -> Idx -> Real)
    (hK : ∀ c d, K d c = -K c d) :
    (1 / 2 : Real) * ∑ c : Idx, ∑ d : Idx,
        (F c d - F d c) * K c d =
      ∑ c : Idx, ∑ d : Idx, F c d * K c d := by
  classical
  have hswap :
      (∑ c : Idx, ∑ d : Idx, F d c * K c d) =
        -∑ c : Idx, ∑ d : Idx, F c d * K c d := by
    calc
      (∑ c : Idx, ∑ d : Idx, F d c * K c d) =
          ∑ d : Idx, ∑ c : Idx, F c d * K d c := by
            rw [Finset.sum_comm]
      _ = ∑ d : Idx, ∑ c : Idx, -(F c d * K c d) := by
        refine Finset.sum_congr rfl fun d _ ↦ ?_
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        rw [hK c d]
        ring
      _ = -∑ d : Idx, ∑ c : Idx, F c d * K c d := by
        simp only [Finset.sum_neg_distrib]
      _ = -∑ c : Idx, ∑ d : Idx, F c d * K c d := by
        rw [Finset.sum_comm]
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [hswap]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.half_skewDifference_contraction
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.half_skewDifference_contraction target :: scope.openDecls } }

private theorem nablaCurvatureSkewActionContraction_eq
    {q : Nat}
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (A : (Fin q -> Idx) -> Real)
    (hcontract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (a : Idx) (b : Fin q -> Idx) :
    (1 / 2 : Real) * nablaCurvatureSkewActionContraction nablaR A a b =
      ∑ c : Idx, ∑ d : Idx,
        nablaRic c a d * covariantTensorSkewAction A c d b := by
  classical
  rw [nablaCurvatureSkewActionContraction]
  calc
    (1 / 2 : Real) *
        (∑ e : Idx, ∑ c : Idx, ∑ d : Idx,
          nablaR e e a d c * covariantTensorSkewAction A c d b) =
      (1 / 2 : Real) *
        ∑ c : Idx, ∑ d : Idx,
          (∑ e : Idx, nablaR e e a d c) *
            covariantTensorSkewAction A c d b := by
              congr 1
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun c _ ↦ ?_
              rw [Finset.sum_comm]
              simp only [Finset.sum_mul]
    _ = (1 / 2 : Real) *
        ∑ c : Idx, ∑ d : Idx,
          (nablaRic c a d - nablaRic d a c) *
            covariantTensorSkewAction A c d b := by
              congr 1
              refine Finset.sum_congr rfl fun c _ ↦ ?_
              refine Finset.sum_congr rfl fun d _ ↦ ?_
              rw [hcontract a c d]
    _ = _ := half_skewDifference_contraction
      (fun c d ↦ nablaRic c a d)
      (fun c d ↦ covariantTensorSkewAction A c d b)
      (fun c d ↦ covariantTensorSkewAction_swap A c d b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaCurvatureSkewActionContraction_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.nablaCurvatureSkewActionContraction_eq target :: scope.openDecls } }

private theorem gradientCurvatureSkewActionContraction_eq
    {q : Nat}
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (DA : Idx -> (Fin q -> Idx) -> Real)
    (hskew : ∀ e a c d, R e a c d = -R e a d c)
    (htrace : curvatureRicciTraceComponents R Ric)
    (a : Idx) (b : Fin q -> Idx) :
    gradientCurvatureSkewActionContraction R DA a b =
      2 * (∑ d : Idx, Ric a d * DA d b) +
        (∑ e : Idx, ∑ c : Idx, ∑ d : Idx,
          R e a d c * covariantTensorSkewAction (DA e) c d b) := by
  classical
  rw [gradientCurvatureSkewActionContraction]
  simp_rw [covariantTensorSkewAction_prepend]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  calc
    (∑ e : Idx, ∑ c : Idx, ∑ d : Idx,
        R e a d c *
          ((if c = e then DA d b else 0) - (if d = e then DA c b else 0))) =
      ∑ e : Idx, 2 * ∑ d : Idx, R e a d e * DA d b := by
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, _root_.MulZeroClass.mul_zero]
        have hfirst :
            (∑ c : Idx, ∑ d : Idx,
              if c = e then R e a d c * DA d b else 0) =
              ∑ d : Idx, R e a d e * DA d b := by
          rw [Finset.sum_eq_single e]
          · simp
          · intro c _ hc
            simp [hc]
          · intro h
            exact False.elim (h (Finset.mem_univ e))
        have hsecond :
            (∑ c : Idx, ∑ d : Idx,
              if d = e then R e a d c * DA c b else 0) =
              ∑ c : Idx, R e a e c * DA c b := by
          refine Finset.sum_congr rfl fun c _ ↦ ?_
          rw [Finset.sum_eq_single e]
          · simp
          · intro d _ hd
            simp [hd]
          · intro h
            exact False.elim (h (Finset.mem_univ e))
        rw [hfirst, hsecond]
        calc
          (∑ d : Idx, R e a d e * DA d b) -
              ∑ c : Idx, R e a e c * DA c b =
            (∑ d : Idx, R e a d e * DA d b) -
              ∑ c : Idx, (-R e a c e) * DA c b := by
                congr 1
                refine Finset.sum_congr rfl fun c _ ↦ ?_
                rw [hskew e a e c]
          _ = 2 * ∑ d : Idx, R e a d e * DA d b := by
                simp only [neg_mul, Finset.sum_neg_distrib]
                ring
    _ = 2 * ∑ d : Idx, Ric a d * DA d b := by
      simp only [Finset.mul_sum]
      calc
        (∑ e : Idx, ∑ d : Idx, 2 * (R e a d e * DA d b)) =
          ∑ d : Idx, 2 * ((∑ e : Idx, R e a d e) * DA d b) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun d _ ↦ ?_
            calc
              (∑ e : Idx, 2 * (R e a d e * DA d b)) =
                  2 * ∑ e : Idx, R e a d e * DA d b := by
                    rw [Finset.mul_sum]
              _ = 2 * ((∑ e : Idx, R e a d e) * DA d b) := by
                    rw [Finset.sum_mul]
        _ = _ := by
          refine Finset.sum_congr rfl fun d _ ↦ ?_
          rw [htrace a d]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.gradientCurvatureSkewActionContraction_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.gradientCurvatureSkewActionContraction_eq target :: scope.openDecls } }

theorem uhlenbeck_roughLaplacian_covariantDerivative_commutator
    {q : Nat}
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (A : (Fin q -> Idx) -> Real)
    (DA : Idx -> (Fin q -> Idx) -> Real)
    (D3A : Idx -> Idx -> Idx -> (Fin q -> Idx) -> Real)
    (hdiff : differentiatedTensorRicciIdentityComponents R nablaR A DA D3A)
    (hgrad : tensorGradientRicciIdentityComponents R DA D3A)
    (hcontract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (hskew : ∀ e a c d, R e a c d = -R e a d c)
    (htrace : curvatureRicciTraceComponents R Ric)
    (a : Idx) (b : Fin q -> Idx) :
    roughLaplacianCovariantDerivativeComponents D3A a b -
        covariantDerivativeRoughLaplacianComponents D3A a b =
      (∑ e : Idx, ∑ c : Idx, ∑ d : Idx,
        R e a d c * covariantTensorSkewAction (DA e) c d b) +
      (∑ d : Idx, Ric a d * DA d b) +
      ∑ c : Idx, ∑ d : Idx,
        nablaRic c a d * covariantTensorSkewAction A c d b := by
  classical
  have htraceDiff :
      roughLaplacianCovariantDerivativeComponents D3A a b -
          covariantDerivativeRoughLaplacianComponents D3A a b =
        (1 / 2 : Real) *
            (nablaCurvatureSkewActionContraction nablaR A a b +
              (∑ e : Idx, ∑ c : Idx, ∑ d : Idx,
                R e a d c * covariantTensorSkewAction (DA e) c d b)) +
          (1 / 2 : Real) *
            gradientCurvatureSkewActionContraction R DA a b := by
    rw [roughLaplacianCovariantDerivativeComponents,
      covariantDerivativeRoughLaplacianComponents]
    calc
      (∑ e : Idx, D3A e e a b) - ∑ e : Idx, D3A a e e b =
        ∑ e : Idx,
          ((D3A e e a b - D3A e a e b) +
            (D3A e a e b - D3A a e e b)) := by
              simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              ring
      _ = ∑ e : Idx,
          ((1 / 2 : Real) *
              ((∑ c : Idx, ∑ d : Idx,
                  nablaR e e a d c * covariantTensorSkewAction A c d b) +
                ∑ c : Idx, ∑ d : Idx,
                  R e a d c * covariantTensorSkewAction (DA e) c d b) +
            (1 / 2 : Real) *
              ∑ c : Idx, ∑ d : Idx,
                R e a d c *
                  covariantTensorSkewAction (prependCovariantDerivativeComponents DA)
                    c d (Fin.cons e b)) := by
              refine Finset.sum_congr rfl fun e _ ↦ ?_
              rw [hdiff e a b, hgrad e a b]
      _ = _ := by
        simp only [mul_add, Finset.mul_sum,
          Finset.sum_add_distrib,
          nablaCurvatureSkewActionContraction,
          gradientCurvatureSkewActionContraction]
  rw [htraceDiff, mul_add,
    nablaCurvatureSkewActionContraction_eq nablaR nablaRic A hcontract a b,
    gradientCurvatureSkewActionContraction_eq R Ric DA hskew htrace a b]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeck_roughLaplacian_covariantDerivative_commutator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeck_roughLaplacian_covariantDerivative_commutator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeck_roughLaplacian_covariantDerivative_commutator ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeck_roughLaplacian_covariantDerivative_commutator

theorem uhlenbeck_heat_covariantDerivative_commutator
    {q : Nat}
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (A : (Fin q -> Idx) -> Real)
    (DA : Idx -> (Fin q -> Idx) -> Real)
    (nablaDtA : Idx -> (Fin q -> Idx) -> Real)
    (D3A : Idx -> Idx -> Idx -> (Fin q -> Idx) -> Real)
    (hdiff : differentiatedTensorRicciIdentityComponents R nablaR A DA D3A)
    (hgrad : tensorGradientRicciIdentityComponents R DA D3A)
    (hcontract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (hskewFirst : ∀ a e c d, R a e c d = -R e a c d)
    (hskewLast : ∀ a e c d, R a e c d = -R a e d c)
    (htrace : curvatureRicciTraceComponents R Ric)
    (a : Idx) (b : Fin q -> Idx) :
    (uhlenbeckTimeDerivativeOfCovariantDerivative
          Ric nablaRic A DA nablaDtA a b -
        roughLaplacianCovariantDerivativeComponents D3A a b) -
      (uhlenbeckCovariantDerivativeOfTimeDerivative
          Ric nablaRic A DA nablaDtA a b -
        covariantDerivativeRoughLaplacianComponents D3A a b) =
      curvatureSlotActionContraction R DA a b := by
  classical
  have htime := uhlenbeck_time_covariantDerivative_commutator
    (Ric := Ric) (nablaRic := nablaRic) (A := A) (DA := DA)
    (nablaDtA := nablaDtA) a b
  have hspace := uhlenbeck_roughLaplacian_covariantDerivative_commutator
    (R := R) (nablaR := nablaR) (Ric := Ric) (nablaRic := nablaRic)
    (A := A) (DA := DA) (D3A := D3A) hdiff hgrad hcontract
    hskewLast htrace a b
  calc
    (uhlenbeckTimeDerivativeOfCovariantDerivative
          Ric nablaRic A DA nablaDtA a b -
        roughLaplacianCovariantDerivativeComponents D3A a b) -
      (uhlenbeckCovariantDerivativeOfTimeDerivative
          Ric nablaRic A DA nablaDtA a b -
        covariantDerivativeRoughLaplacianComponents D3A a b) =
        (uhlenbeckTimeDerivativeOfCovariantDerivative
            Ric nablaRic A DA nablaDtA a b -
          uhlenbeckCovariantDerivativeOfTimeDerivative
            Ric nablaRic A DA nablaDtA a b) -
        (roughLaplacianCovariantDerivativeComponents D3A a b -
          covariantDerivativeRoughLaplacianComponents D3A a b) := by
            ring
    _ =
        -(∑ e : Idx, ∑ c : Idx, ∑ d : Idx,
          R e a d c * covariantTensorSkewAction (DA e) c d b) := by
            rw [htime, hspace]
            ring
    _ = curvatureSkewActionContraction R DA a b := by
      rw [curvatureSkewActionContraction]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun e _ ↦ ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun d _ ↦ ?_
      rw [hskewFirst e a d c]
      ring
    _ = curvatureSlotActionContraction R DA a b :=
      curvatureSkewActionContraction_eq_slots R DA hskewLast a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeck_heat_covariantDerivative_commutator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeck_heat_covariantDerivative_commutator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeck_heat_covariantDerivative_commutator ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeck_heat_covariantDerivative_commutator

theorem uhlenbeck_heat_covariantDerivative_commutator_slots
    {q : Nat}
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (A : (Fin q -> Idx) -> Real)
    (DA : Idx -> (Fin q -> Idx) -> Real)
    (nablaDtA : Idx -> (Fin q -> Idx) -> Real)
    (D3A : Idx -> Idx -> Idx -> (Fin q -> Idx) -> Real)
    (hdiff : differentiatedTensorRicciIdentityComponents R nablaR A DA D3A)
    (hgrad : tensorGradientRicciIdentityComponents R DA D3A)
    (hcontract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (hskewFirst : ∀ a e c d, R a e c d = -R e a c d)
    (hskewLast : ∀ a e c d, R a e c d = -R a e d c)
    (htrace : curvatureRicciTraceComponents R Ric)
    (a : Idx) (b : Fin q -> Idx) :
    (uhlenbeckTimeDerivativeOfCovariantDerivative
          Ric nablaRic A DA nablaDtA a b -
        roughLaplacianCovariantDerivativeComponents D3A a b) -
      (uhlenbeckCovariantDerivativeOfTimeDerivative
          Ric nablaRic A DA nablaDtA a b -
        covariantDerivativeRoughLaplacianComponents D3A a b) =
      2 * ∑ r : Fin q, ∑ e : Idx, ∑ d : Idx,
        R a e d (b r) * DA e (Function.update b r d) := by
  rw [uhlenbeck_heat_covariantDerivative_commutator
    R nablaR Ric nablaRic A DA nablaDtA D3A hdiff hgrad hcontract
    hskewFirst hskewLast htrace a b]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeck_heat_covariantDerivative_commutator_slots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeck_heat_covariantDerivative_commutator_slots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeck_heat_covariantDerivative_commutator_slots ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeck_heat_covariantDerivative_commutator_slots

theorem uhlenbeck_heat_covariantDerivative_commutator_zero
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (A : (Fin 0 -> Idx) -> Real)
    (DA : Idx -> (Fin 0 -> Idx) -> Real)
    (nablaDtA : Idx -> (Fin 0 -> Idx) -> Real)
    (D3A : Idx -> Idx -> Idx -> (Fin 0 -> Idx) -> Real)
    (hdiff : differentiatedTensorRicciIdentityComponents R nablaR A DA D3A)
    (hgrad : tensorGradientRicciIdentityComponents R DA D3A)
    (hcontract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (hskewFirst : ∀ a e c d, R a e c d = -R e a c d)
    (hskewLast : ∀ a e c d, R a e c d = -R a e d c)
    (htrace : curvatureRicciTraceComponents R Ric)
    (a : Idx) (b : Fin 0 -> Idx) :
    (uhlenbeckTimeDerivativeOfCovariantDerivative
          Ric nablaRic A DA nablaDtA a b -
        roughLaplacianCovariantDerivativeComponents D3A a b) -
      (uhlenbeckCovariantDerivativeOfTimeDerivative
          Ric nablaRic A DA nablaDtA a b -
        covariantDerivativeRoughLaplacianComponents D3A a b) = 0 := by
  rw [uhlenbeck_heat_covariantDerivative_commutator
    R nablaR Ric nablaRic A DA nablaDtA D3A hdiff hgrad hcontract
    hskewFirst hskewLast htrace a b]
  exact curvatureSlotActionContraction_zero R DA a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeck_heat_covariantDerivative_commutator_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeck_heat_covariantDerivative_commutator_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeck_heat_covariantDerivative_commutator_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeck_heat_covariantDerivative_commutator_zero

theorem uhlenbeck_heat_covariantDerivative_commutator_one
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (A : Idx -> Real)
    (DA : Idx -> Idx -> Real)
    (nablaDtA : Idx -> Idx -> Real)
    (D3A : Idx -> Idx -> Idx -> Idx -> Real)
    (hdiff : differentiatedTensorRicciIdentityComponents R nablaR
      (fun slots : Fin 1 -> Idx ↦ A (slots 0))
      (fun e (slots : Fin 1 -> Idx) ↦ DA e (slots 0))
      (fun e f a (slots : Fin 1 -> Idx) ↦ D3A e f a (slots 0)))
    (hgrad : tensorGradientRicciIdentityComponents R
      (fun e (slots : Fin 1 -> Idx) ↦ DA e (slots 0))
      (fun e f a (slots : Fin 1 -> Idx) ↦ D3A e f a (slots 0)))
    (hcontract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (hskewFirst : ∀ a e c d, R a e c d = -R e a c d)
    (hskewLast : ∀ a e c d, R a e c d = -R a e d c)
    (htrace : curvatureRicciTraceComponents R Ric)
    (a b : Idx) :
    (uhlenbeckTimeDerivativeOfCovariantDerivative Ric nablaRic
          (fun slots : Fin 1 -> Idx ↦ A (slots 0))
          (fun e (slots : Fin 1 -> Idx) ↦ DA e (slots 0))
          (fun e (slots : Fin 1 -> Idx) ↦ nablaDtA e (slots 0))
          a (fun _ : Fin 1 ↦ b) -
        roughLaplacianCovariantDerivativeComponents
          (fun e f a (slots : Fin 1 -> Idx) ↦ D3A e f a (slots 0))
          a (fun _ : Fin 1 ↦ b)) -
      (uhlenbeckCovariantDerivativeOfTimeDerivative Ric nablaRic
          (fun slots : Fin 1 -> Idx ↦ A (slots 0))
          (fun e (slots : Fin 1 -> Idx) ↦ DA e (slots 0))
          (fun e (slots : Fin 1 -> Idx) ↦ nablaDtA e (slots 0))
          a (fun _ : Fin 1 ↦ b) -
        covariantDerivativeRoughLaplacianComponents
          (fun e f a (slots : Fin 1 -> Idx) ↦ D3A e f a (slots 0))
          a (fun _ : Fin 1 ↦ b)) =
      2 * ∑ e : Idx, ∑ d : Idx, R a e d b * DA e d := by
  rw [uhlenbeck_heat_covariantDerivative_commutator
    R nablaR Ric nablaRic (fun slots : Fin 1 -> Idx ↦ A (slots 0))
    (fun e (slots : Fin 1 -> Idx) ↦ DA e (slots 0))
    (fun e (slots : Fin 1 -> Idx) ↦ nablaDtA e (slots 0))
    (fun e f a (slots : Fin 1 -> Idx) ↦ D3A e f a (slots 0))
    hdiff hgrad hcontract hskewFirst hskewLast htrace a
    (fun _ : Fin 1 ↦ b)]
  exact curvatureSlotActionContraction_one R DA a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeck_heat_covariantDerivative_commutator_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeck_heat_covariantDerivative_commutator_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeck_heat_covariantDerivative_commutator_one ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeck_heat_covariantDerivative_commutator_one

end DifferentialGeometry.PDE.RicciFlow
