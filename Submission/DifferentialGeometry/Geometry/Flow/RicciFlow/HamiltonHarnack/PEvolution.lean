import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.HeatCommutator

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

def hamiltonPComponent
    (nablaRic : Idx -> Idx -> Idx -> Real) (a b c : Idx) : Real :=
  nablaRic a b c - nablaRic b a c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonPComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonPComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonPComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonPComponent

def hamiltonPTimeDerivativeComponent
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaDtRic : Idx -> Idx -> Idx -> Real)
    (a b c : Idx) : Real :=
  nablaDtRic a b c - nablaDtRic b a c -
    ∑ p : Idx,
      ricciFlowConnectionVariationOrthonormal nablaRic a c p * Ric p b +
    ∑ p : Idx,
      ricciFlowConnectionVariationOrthonormal nablaRic b c p * Ric p a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonPTimeDerivativeComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonPTimeDerivativeComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonPTimeDerivativeComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonPTimeDerivativeComponent

def hamiltonRawRicciReactionComponent
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real) (b c : Idx) : Real :=
  2 * ∑ d : Idx, ∑ e : Idx, R b d e c * Ric d e -
    2 * ∑ d : Idx, Ric b d * Ric d c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonRawRicciReactionComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonRawRicciReactionComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonRawRicciReactionComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonRawRicciReactionComponent

def hamiltonNablaRawRicciReactionComponent
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (a b c : Idx) : Real :=
  2 * ∑ d : Idx, ∑ e : Idx,
    (nablaR a b d e c * Ric d e + R b d e c * nablaRic a d e) -
  2 * ∑ d : Idx,
    (nablaRic a b d * Ric d c + Ric b d * nablaRic a d c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonNablaRawRicciReactionComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonNablaRawRicciReactionComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonNablaRawRicciReactionComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonNablaRawRicciReactionComponent

def hamiltonNablaRicciReactionComponent
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (a b c : Idx) : Real :=
  2 * ∑ d : Idx, ∑ e : Idx,
    (nablaR a b d e c * Ric d e + R b d e c * nablaRic a d e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonNablaRicciReactionComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonNablaRicciReactionComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonNablaRicciReactionComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonNablaRicciReactionComponent

omit [DecidableEq Idx] in
theorem hamilton_ricci_reaction_uhlenbeck_correction
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (hRic : forall a b, Ric a b = Ric b a)
    (hNablaRic : forall a b c, nablaRic a b c = nablaRic a c b)
    (a b c : Idx) :
    hamiltonNablaRawRicciReactionComponent R nablaR Ric nablaRic a b c +
        covariantTensorNablaRicciSlotAction nablaRic
          (fun slots : Fin 2 -> Idx => Ric (slots 0) (slots 1)) a
          (fun q : Fin 2 => if q = 0 then b else c) +
      covariantTensorRicciSlotAction Ric
          (fun slots : Fin 2 -> Idx => nablaRic a (slots 0) (slots 1))
          (fun q : Fin 2 => if q = 0 then b else c) =
      hamiltonNablaRicciReactionComponent R nablaR Ric nablaRic a b c := by
  classical
  simp only [hamiltonNablaRawRicciReactionComponent,
    hamiltonNablaRicciReactionComponent,
    covariantTensorNablaRicciSlotAction, covariantTensorRicciSlotAction,
    Fin.sum_univ_two, Function.update_apply]
  simp only [↓reduceIte, Fin.isValue, one_ne_zero, zero_ne_one]
  have hOne :
      (∑ d : Idx, nablaRic a b d * Ric d c) =
        ∑ d : Idx, Ric c d * nablaRic a b d := by
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hRic d c]
    ring
  have hTwo :
      (∑ d : Idx, Ric b d * nablaRic a d c) =
        ∑ d : Idx, nablaRic a c d * Ric b d := by
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hNablaRic a d c]
    ring
  simp only [Finset.sum_add_distrib]
  rw [hOne, hTwo]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamilton_ricci_reaction_uhlenbeck_correction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamilton_ricci_reaction_uhlenbeck_correction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamilton_ricci_reaction_uhlenbeck_correction ``Submission.DifferentialGeometry.PDE.RicciFlow.hamilton_ricci_reaction_uhlenbeck_correction

def hamiltonPEvolutionReactionComponent
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (a b c : Idx) : Real :=
  2 * ∑ d : Idx, ∑ e : Idx,
      R a d e b * hamiltonPComponent nablaRic d e c +
    2 * ∑ d : Idx, ∑ e : Idx,
      R a d e c * hamiltonPComponent nablaRic d b e +
    2 * ∑ d : Idx, ∑ e : Idx,
      R b d e c * hamiltonPComponent nablaRic a d e -
    2 * ∑ d : Idx, ∑ e : Idx, Ric d e * nablaR d a b e c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonPEvolutionReactionComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonPEvolutionReactionComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonPEvolutionReactionComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonPEvolutionReactionComponent

def uhlenbeckHeatNablaRicciComponent
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaDtRic : Idx -> Idx -> Idx -> Real)
    (nabla3Ric : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (a b c : Idx) : Real :=
  uhlenbeckTimeDerivativeOfCovariantDerivative Ric nablaRic
      (fun slots : Fin 2 -> Idx => Ric (slots 0) (slots 1))
      (fun e (slots : Fin 2 -> Idx) => nablaRic e (slots 0) (slots 1))
      (fun e (slots : Fin 2 -> Idx) => nablaDtRic e (slots 0) (slots 1))
      a (fun q : Fin 2 => if q = 0 then b else c) -
    roughLaplacianCovariantDerivativeComponents
      (fun e f d (slots : Fin 2 -> Idx) => nabla3Ric e f d (slots 0) (slots 1))
      a (fun q : Fin 2 => if q = 0 then b else c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeckHeatNablaRicciComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeckHeatNablaRicciComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeckHeatNablaRicciComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeckHeatNablaRicciComponent

def uhlenbeckNablaHeatRicciComponent
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaDtRic : Idx -> Idx -> Idx -> Real)
    (nabla3Ric : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (a b c : Idx) : Real :=
  uhlenbeckCovariantDerivativeOfTimeDerivative Ric nablaRic
      (fun slots : Fin 2 -> Idx => Ric (slots 0) (slots 1))
      (fun e (slots : Fin 2 -> Idx) => nablaRic e (slots 0) (slots 1))
      (fun e (slots : Fin 2 -> Idx) => nablaDtRic e (slots 0) (slots 1))
      a (fun q : Fin 2 => if q = 0 then b else c) -
    covariantDerivativeRoughLaplacianComponents
      (fun e f d (slots : Fin 2 -> Idx) => nabla3Ric e f d (slots 0) (slots 1))
      a (fun q : Fin 2 => if q = 0 then b else c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeckNablaHeatRicciComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeckNablaHeatRicciComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeckNablaHeatRicciComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeckNablaHeatRicciComponent

omit [DecidableEq Idx] in
theorem uhlenbeck_nabla_heat_ricci_eq_hamilton_reaction
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaDtRic : Idx -> Idx -> Idx -> Real)
    (nabla3Ric : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (hRic : forall a b, Ric a b = Ric b a)
    (hNablaRic : forall a b c, nablaRic a b c = nablaRic a c b)
    (hRaw : forall a b c,
      nablaDtRic a b c -
          covariantDerivativeRoughLaplacianComponents
            (fun e f d (slots : Fin 2 -> Idx) =>
              nabla3Ric e f d (slots 0) (slots 1)) a
            (fun q : Fin 2 => if q = 0 then b else c) =
        hamiltonNablaRawRicciReactionComponent
          R nablaR Ric nablaRic a b c)
    (a b c : Idx) :
    uhlenbeckNablaHeatRicciComponent
        Ric nablaRic nablaDtRic nabla3Ric a b c =
      hamiltonNablaRicciReactionComponent R nablaR Ric nablaRic a b c := by
  have hCorrection := hamilton_ricci_reaction_uhlenbeck_correction
    R nablaR Ric nablaRic hRic hNablaRic a b c
  rw [uhlenbeckNablaHeatRicciComponent,
    uhlenbeckCovariantDerivativeOfTimeDerivative]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
  linear_combination hRaw a b c + hCorrection

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeck_nabla_heat_ricci_eq_hamilton_reaction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeck_nabla_heat_ricci_eq_hamilton_reaction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeck_nabla_heat_ricci_eq_hamilton_reaction ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeck_nabla_heat_ricci_eq_hamilton_reaction

def hamiltonPHeatComponent
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaDtRic : Idx -> Idx -> Idx -> Real)
    (nabla3Ric : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (a b c : Idx) : Real :=
  uhlenbeckHeatNablaRicciComponent Ric nablaRic nablaDtRic nabla3Ric a b c -
    uhlenbeckHeatNablaRicciComponent Ric nablaRic nablaDtRic nabla3Ric b a c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonPHeatComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonPHeatComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonPHeatComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonPHeatComponent

omit [DecidableEq Idx] in
private theorem sum_swap_two (F : Idx -> Idx -> Real) :
    (∑ a : Idx, ∑ b : Idx, F a b) = ∑ a : Idx, ∑ b : Idx, F b a := by
  exact Finset.sum_comm.trans (by rfl)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.sum_swap_two
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.sum_swap_two target :: scope.openDecls } }

omit [DecidableEq Idx] in
private theorem hamiltonP_reaction_regroup
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (hPair : forall a b c d, R a b c d = R c d a b)
    (hSkewFirst : forall a b c d, R a b c d = -R b a c d)
    (hSkewLast : forall a b c d, R a b c d = -R a b d c)
    (hNablaSkewFirst : forall d a b c e,
      nablaR d a b c e = -nablaR d b a c e)
    (hSecond : forall a b d e c,
      nablaR a b d e c + nablaR b d a e c + nablaR d a b e c = 0)
    (a b c : Idx) :
    hamiltonNablaRicciReactionComponent R nablaR Ric nablaRic a b c -
        hamiltonNablaRicciReactionComponent R nablaR Ric nablaRic b a c +
        curvatureSlotActionContraction R
          (fun e (slots : Fin 2 -> Idx) => nablaRic e (slots 0) (slots 1)) a
          (fun q : Fin 2 => if q = 0 then b else c) -
      curvatureSlotActionContraction R
          (fun e (slots : Fin 2 -> Idx) => nablaRic e (slots 0) (slots 1)) b
          (fun q : Fin 2 => if q = 0 then a else c) =
      hamiltonPEvolutionReactionComponent R Ric nablaR nablaRic a b c := by
  classical
  have hBianchi (d e : Idx) :
      nablaR a b d e c - nablaR b a d e c = -nablaR d a b e c := by
    have h := hSecond a b d e c
    rw [hNablaSkewFirst b d a e c] at h
    linarith
  have hCurv (d e : Idx) : R b d e a = R a e d b := by
    calc
      R b d e a = R e a b d := hPair b d e a
      _ = -R a e b d := hSkewFirst e a b d
      _ = R a e d b := by rw [hSkewLast a e b d]; ring
  have hDerivative :
      (∑ d : Idx, ∑ e : Idx, nablaR a b d e c * Ric d e) -
          (∑ d : Idx, ∑ e : Idx, nablaR b a d e c * Ric d e) =
        -(∑ d : Idx, ∑ e : Idx, Ric d e * nablaR d a b e c) := by
    calc
      (∑ d : Idx, ∑ e : Idx, nablaR a b d e c * Ric d e) -
          (∑ d : Idx, ∑ e : Idx, nablaR b a d e c * Ric d e) =
        ∑ d : Idx, ∑ e : Idx,
          (nablaR a b d e c - nablaR b a d e c) * Ric d e := by
            simp only [sub_mul, Finset.sum_sub_distrib]
      _ = -(∑ d : Idx, ∑ e : Idx, Ric d e * nablaR d a b e c) := by
        simp_rw [hBianchi]
        simp only [neg_mul, Finset.sum_neg_distrib]
        congr 1
        refine Finset.sum_congr rfl fun d _ => ?_
        refine Finset.sum_congr rfl fun e _ => ?_
        ring
  have hReaction :
      hamiltonNablaRicciReactionComponent R nablaR Ric nablaRic a b c -
          hamiltonNablaRicciReactionComponent R nablaR Ric nablaRic b a c =
        -(2 * ∑ d : Idx, ∑ e : Idx, Ric d e * nablaR d a b e c) +
          2 * ∑ d : Idx, ∑ e : Idx, R b d e c * nablaRic a d e -
          2 * ∑ d : Idx, ∑ e : Idx, R a d e c * nablaRic b d e := by
    rw [hamiltonNablaRicciReactionComponent,
      hamiltonNablaRicciReactionComponent]
    simp only [Finset.sum_add_distrib, mul_add]
    linear_combination 2 * hDerivative
  have hswap :
      (∑ d : Idx, ∑ e : Idx, R b d e a * nablaRic d e c) =
        ∑ d : Idx, ∑ e : Idx, R a d e b * nablaRic e d c := by
    calc
      (∑ d : Idx, ∑ e : Idx, R b d e a * nablaRic d e c) =
          ∑ d : Idx, ∑ e : Idx, R a e d b * nablaRic d e c := by
            refine Finset.sum_congr rfl fun d _ => ?_
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [hCurv d e]
      _ = ∑ d : Idx, ∑ e : Idx, R a d e b * nablaRic e d c := by
            exact sum_swap_two
              (fun d e => R a e d b * nablaRic d e c)
  have hSlotA :
      curvatureSlotActionContraction R
          (fun e (slots : Fin 2 -> Idx) => nablaRic e (slots 0) (slots 1)) a
          (fun q : Fin 2 => if q = 0 then b else c) =
        2 * (∑ d : Idx, ∑ e : Idx, R a d e b * nablaRic d e c) +
          2 * (∑ d : Idx, ∑ e : Idx, R a d e c * nablaRic d b e) := by
    simp only [curvatureSlotActionContraction, Fin.sum_univ_two,
      Function.update_apply]
    simp
    ring
  have hSlotB :
      curvatureSlotActionContraction R
          (fun e (slots : Fin 2 -> Idx) => nablaRic e (slots 0) (slots 1)) b
          (fun q : Fin 2 => if q = 0 then a else c) =
        2 * (∑ d : Idx, ∑ e : Idx, R b d e a * nablaRic d e c) +
          2 * (∑ d : Idx, ∑ e : Idx, R b d e c * nablaRic d a e) := by
    simp only [curvatureSlotActionContraction, Fin.sum_univ_two,
      Function.update_apply]
    simp
    ring
  have hRHS :
      hamiltonPEvolutionReactionComponent R Ric nablaR nablaRic a b c =
        2 * (∑ d : Idx, ∑ e : Idx, R a d e b * nablaRic d e c) -
        2 * (∑ d : Idx, ∑ e : Idx, R a d e b * nablaRic e d c) +
        2 * (∑ d : Idx, ∑ e : Idx, R a d e c * nablaRic d b e) -
        2 * (∑ d : Idx, ∑ e : Idx, R a d e c * nablaRic b d e) +
        2 * (∑ d : Idx, ∑ e : Idx, R b d e c * nablaRic a d e) -
        2 * (∑ d : Idx, ∑ e : Idx, R b d e c * nablaRic d a e) -
        2 * (∑ d : Idx, ∑ e : Idx, Ric d e * nablaR d a b e c) := by
    simp only [hamiltonPEvolutionReactionComponent, hamiltonPComponent,
      mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hReaction, hSlotA, hSlotB, hRHS, hswap]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonP_reaction_regroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.hamiltonP_reaction_regroup target :: scope.openDecls } }

theorem hamiltonP_evolution
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaDtRic : Idx -> Idx -> Idx -> Real)
    (nabla3Ric : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (hdiff : differentiatedTensorRicciIdentityComponents R nablaR
      (fun slots : Fin 2 -> Idx => Ric (slots 0) (slots 1))
      (fun e (slots : Fin 2 -> Idx) => nablaRic e (slots 0) (slots 1))
      (fun e f d (slots : Fin 2 -> Idx) => nabla3Ric e f d (slots 0) (slots 1)))
    (hgrad : tensorGradientRicciIdentityComponents R
      (fun e (slots : Fin 2 -> Idx) => nablaRic e (slots 0) (slots 1))
      (fun e f d (slots : Fin 2 -> Idx) => nabla3Ric e f d (slots 0) (slots 1)))
    (hcontract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (hSkewFirst : forall a b c d, R a b c d = -R b a c d)
    (hSkewLast : forall a b c d, R a b c d = -R a b d c)
    (hPair : forall a b c d, R a b c d = R c d a b)
    (hTrace : curvatureRicciTraceComponents R Ric)
    (hNablaSkewFirst : forall d a b c e,
      nablaR d a b c e = -nablaR d b a c e)
    (hSecond : forall a b d e c,
      nablaR a b d e c + nablaR b d a e c + nablaR d a b e c = 0)
    (hRic : forall a b, Ric a b = Ric b a)
    (hNablaRic : forall a b c, nablaRic a b c = nablaRic a c b)
    (hRawRicciReactionDerivative : forall a b c,
      nablaDtRic a b c -
          covariantDerivativeRoughLaplacianComponents
            (fun e f d (slots : Fin 2 -> Idx) =>
              nabla3Ric e f d (slots 0) (slots 1)) a
            (fun q : Fin 2 => if q = 0 then b else c) =
        hamiltonNablaRawRicciReactionComponent
          R nablaR Ric nablaRic a b c)
    (a b c : Idx) :
    hamiltonPHeatComponent Ric nablaRic nablaDtRic nabla3Ric a b c =
      hamiltonPEvolutionReactionComponent R Ric nablaR nablaRic a b c := by
  have hRicciReactionDerivative :=
    uhlenbeck_nabla_heat_ricci_eq_hamilton_reaction
      R Ric nablaR nablaRic nablaDtRic nabla3Ric hRic hNablaRic
        hRawRicciReactionDerivative
  have hCommA := uhlenbeck_heat_covariantDerivative_commutator
    R nablaR Ric nablaRic
    (fun slots : Fin 2 -> Idx => Ric (slots 0) (slots 1))
    (fun e slots => nablaRic e (slots 0) (slots 1))
    (fun e slots => nablaDtRic e (slots 0) (slots 1))
    (fun e f d slots => nabla3Ric e f d (slots 0) (slots 1))
    hdiff hgrad hcontract hSkewFirst hSkewLast hTrace a
    (fun q => if q = 0 then b else c)
  have hCommB := uhlenbeck_heat_covariantDerivative_commutator
    R nablaR Ric nablaRic
    (fun slots : Fin 2 -> Idx => Ric (slots 0) (slots 1))
    (fun e slots => nablaRic e (slots 0) (slots 1))
    (fun e slots => nablaDtRic e (slots 0) (slots 1))
    (fun e f d slots => nabla3Ric e f d (slots 0) (slots 1))
    hdiff hgrad hcontract hSkewFirst hSkewLast hTrace b
    (fun q => if q = 0 then a else c)
  change
    uhlenbeckHeatNablaRicciComponent Ric nablaRic nablaDtRic nabla3Ric a b c -
        uhlenbeckNablaHeatRicciComponent Ric nablaRic nablaDtRic nabla3Ric a b c =
      curvatureSlotActionContraction R
        (fun e (slots : Fin 2 -> Idx) => nablaRic e (slots 0) (slots 1)) a
        (fun q : Fin 2 => if q = 0 then b else c) at hCommA
  change
    uhlenbeckHeatNablaRicciComponent Ric nablaRic nablaDtRic nabla3Ric b a c -
        uhlenbeckNablaHeatRicciComponent Ric nablaRic nablaDtRic nabla3Ric b a c =
      curvatureSlotActionContraction R
        (fun e (slots : Fin 2 -> Idx) => nablaRic e (slots 0) (slots 1)) b
        (fun q : Fin 2 => if q = 0 then a else c) at hCommB
  rw [hRicciReactionDerivative a b c] at hCommA
  rw [hRicciReactionDerivative b a c] at hCommB
  have hRegroup := hamiltonP_reaction_regroup R Ric nablaR nablaRic
    hPair hSkewFirst hSkewLast hNablaSkewFirst hSecond a b c
  rw [hamiltonPHeatComponent]
  linear_combination hRegroup + hCommA - hCommB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonP_evolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonP_evolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonP_evolution ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonP_evolution

end DifferentialGeometry.PDE.RicciFlow
