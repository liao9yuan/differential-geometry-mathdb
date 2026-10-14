import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.ChartFamily
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.StageConstruction.Seed

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open _root_.Filter _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

private structure NestedSubseq where
  sigma : Nat → Nat → Nat
  tau : Nat → Nat → Nat
  sigma_strict : ∀ m, StrictMono (sigma m)
  tau_strict : ∀ m, StrictMono (tau m)
  sigma_zero : sigma 0 = id
  sigma_succ : ∀ m, sigma (m + 1) = sigma m ∘ tau m

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.NestedSubseq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.NestedSubseq target :: scope.openDecls } }

namespace NestedSubseq

private def diag (T : NestedSubseq) (m : Nat) : Nat := T.sigma (m + 1) m

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.NestedSubseq.diag
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.NestedSubseq.diag target :: scope.openDecls } }

private def tailComp (T : NestedSubseq) (q : Nat) : Nat → (Nat → Nat)
  | 0 => id
  | n + 1 => T.tailComp q n ∘ T.tau (q + 1 + n)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.NestedSubseq.tailComp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.NestedSubseq.tailComp target :: scope.openDecls } }

private def tailFactor (T : NestedSubseq) (q n : Nat) : Nat :=
  T.tailComp q n (q + n)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.NestedSubseq.tailFactor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.NestedSubseq.tailFactor target :: scope.openDecls } }

private theorem tailComp_strict (T : NestedSubseq) (q : Nat) :
    ∀ n, StrictMono (T.tailComp q n) := by
  intro n
  induction n with
  | zero => exact strictMono_id
  | succ n ih =>
      exact ih.comp (T.tau_strict (q + 1 + n))

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.NestedSubseq.tailComp_strict
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.NestedSubseq.tailComp_strict target :: scope.openDecls } }

private theorem sigma_factor (T : NestedSubseq) (q n : Nat) :
    T.sigma (q + n + 1) = T.sigma (q + 1) ∘ T.tailComp q n := by
  induction n with
  | zero =>
      simp only [Nat.add_zero, tailComp, Function.comp_id]
  | succ n ih =>
      rw [show q + (n + 1) + 1 = (q + n + 1) + 1 by omega]
      rw [T.sigma_succ (q + n + 1), ih]
      ext x
      simp only [tailComp, Function.comp_apply]
      rw [show q + n + 1 = q + 1 + n by omega]

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.NestedSubseq.sigma_factor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.NestedSubseq.sigma_factor target :: scope.openDecls } }

private theorem tailFactor_strict (T : NestedSubseq) (q : Nat) :
    StrictMono (T.tailFactor q) := by
  apply strictMono_nat_of_lt_succ
  intro n
  dsimp only [tailFactor]
  rw [tailComp]
  simp only [Function.comp_apply]
  apply T.tailComp_strict q n
  have hlt : q + n < q + (n + 1) := by omega
  have hle := (T.tau_strict (q + 1 + n)).id_le (q + (n + 1))
  exact hlt.trans_le hle

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.NestedSubseq.tailFactor_strict
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.NestedSubseq.tailFactor_strict target :: scope.openDecls } }

private theorem diag_strict (T : NestedSubseq) : StrictMono T.diag := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [diag, diag, T.sigma_succ (n + 1)]
  simp only [Function.comp_apply]
  apply T.sigma_strict (n + 1)
  have hle := (T.tau_strict (n + 1)).id_le (n + 1)
  exact (Nat.lt_succ_self n).trans_le hle

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.NestedSubseq.diag_strict
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.NestedSubseq.diag_strict target :: scope.openDecls } }

private theorem diag_step_factor (T : NestedSubseq) (q n : Nat) :
    T.diag (q + n) =
      T.sigma q (T.tau q (T.tailFactor q n)) := by
  have hfactor := congrFun (T.sigma_factor q n) (q + n)
  rw [T.sigma_succ q] at hfactor
  simpa only [diag, tailFactor, Function.comp_apply] using hfactor

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.NestedSubseq.diag_step_factor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.NestedSubseq.diag_step_factor target :: scope.openDecls } }

end NestedSubseq

structure StageConvergenceSelection
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r) where
  phi : Nat → Nat
  phi_strict : StrictMono phi
  U : LiveSlot L inp.pack r → Set E
  C0 : LiveSlot L inp.pack r → Set E
  C1 : LiveSlot L inp.pack r → Set E
  aInf : (alpha : LiveSlot L inp.pack r) →
    Fin (inp.pack.A r) → E → Real
  Jinf : (alpha : LiveSlot L inp.pack r) →
    InterSlot L inp.pack r alpha → E → E
  Jbarinf : (alpha : LiveSlot L inp.pack r) →
    InterSlot L inp.pack r alpha → E → E
  gInf : LiveSlot L inp.pack r →
    E → (E →L[Real] E →L[Real] Real)
  convergence : HasStageJetConvergence inp P L hr phi phi_strict U C0 C1
    aInf Jinf Jbarinf gInf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.StageConvergenceSelection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.StageConvergenceSelection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.StageConvergenceSelection ``Submission.DifferentialGeometry.CheegerGromovCompactness.StageConvergenceSelection

private theorem HasStageRefine.payload_nonempty
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    (h : HasStageRefine inp P L r hr) :
    Nonempty (StageConvergenceSelection inp P L r hr) := by
  rcases h with ⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, gInf, hdata⟩
  exact ⟨⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, gInf, hdata⟩⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.HasStageRefine
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasStageRefine.payload_nonempty
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HasStageRefine.payload_nonempty target :: scope.openDecls } }

structure StageConvergenceSelectionOn
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (chart : NormalChartFamily (I := I) X)
    (r : Real) (hr : 0 ≤ r) where
  phi : Nat → Nat
  phi_strict : StrictMono phi
  V : LiveSlot L inp.pack r → Set E
  U : LiveSlot L inp.pack r → Set E
  C0 : LiveSlot L inp.pack r → Set E
  C1 : LiveSlot L inp.pack r → Set E
  aInf : (alpha : LiveSlot L inp.pack r) →
    Fin (inp.pack.A r) → E → Real
  Jinf : (alpha : LiveSlot L inp.pack r) →
    InterSlot L inp.pack r alpha → E → E
  Jbarinf : (alpha : LiveSlot L inp.pack r) →
    InterSlot L inp.pack r alpha → E → E
  gInf : LiveSlot L inp.pack r →
    E → (E →L[Real] E →L[Real] Real)
  convergence : HasStageJetConvergenceOn inp P L hr phi phi_strict chart
    V U C0 C1 aInf Jinf Jbarinf gInf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.StageConvergenceSelectionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.StageConvergenceSelectionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.StageConvergenceSelectionOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.StageConvergenceSelectionOn

private theorem HasStageRefineOn.payload_nonempty
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (chart : NormalChartFamily (I := I) X)
    (r : Real) (hr : 0 ≤ r)
    (h : HasStageRefineOn inp P L chart r hr) :
    Nonempty (StageConvergenceSelectionOn inp P L chart r hr) := by
  rcases h with
    ⟨phi, hphi, V, U, C0, C1, aInf, Jinf, Jbarinf, gInf, hdata⟩
  exact
    ⟨⟨phi, hphi, V, U, C0, C1, aInf, Jinf, Jbarinf, gInf, hdata⟩⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.HasStageRefineOn
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasStageRefineOn.payload_nonempty
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HasStageRefineOn.payload_nonempty target :: scope.openDecls } }

structure StageSubsequence where
  sigma : Nat → Nat
  sigma_strict : StrictMono sigma

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.StageSubsequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.StageSubsequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.StageSubsequence ``Submission.DifferentialGeometry.CheegerGromovCompactness.StageSubsequence

private noncomputable def choosePayload
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hseed : HasStageSeed inp P L0)
    (S : StageSubsequence) (m : Nat) :
    StageConvergenceSelection inp P (L0.subseq S.sigma_strict) (m : Real)
      (Nat.cast_nonneg m) :=
  Classical.choice <| HasStageRefine.payload_nonempty inp P
    (L0.subseq S.sigma_strict) (m : Real) (Nat.cast_nonneg m) <|
      hseed.refine inp P L0 (L0.subseq S.sigma_strict)
        (NetLimitData.stable_subseq inp.decay P L0 S.sigma_strict hseed.1)
        (m : Real) (Nat.cast_nonneg m)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.choosePayload
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.choosePayload target :: scope.openDecls } }

private noncomputable def nextState
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hseed : HasStageSeed inp P L0)
    (S : StageSubsequence) (m : Nat) : StageSubsequence :=
  let d := choosePayload inp P L0 hseed S m
  ⟨S.sigma ∘ d.phi, S.sigma_strict.comp d.phi_strict⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.nextState
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.nextState target :: scope.openDecls } }

noncomputable def stageSubsequence
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hseed : HasStageSeed inp P L0) : Nat → StageSubsequence
  | 0 => ⟨id, strictMono_id⟩
  | m + 1 => nextState inp P L0 hseed
      (stageSubsequence inp P L0 hseed m) m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.stageSubsequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.stageSubsequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.stageSubsequence ``Submission.DifferentialGeometry.CheegerGromovCompactness.stageSubsequence

noncomputable def radiusConvergenceSelection
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hseed : HasStageSeed inp P L0) (m : Nat) :=
  choosePayload inp P L0 hseed
    (stageSubsequence inp P L0 hseed m) m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.radiusConvergenceSelection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.radiusConvergenceSelection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.radiusConvergenceSelection ``Submission.DifferentialGeometry.CheegerGromovCompactness.radiusConvergenceSelection

private noncomputable def stageNested
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hseed : HasStageSeed inp P L0) : NestedSubseq where
  sigma m := (stageSubsequence inp P L0 hseed m).sigma
  tau m := (radiusConvergenceSelection inp P L0 hseed m).phi
  sigma_strict m := (stageSubsequence inp P L0 hseed m).sigma_strict
  tau_strict m := (radiusConvergenceSelection inp P L0 hseed m).phi_strict
  sigma_zero := rfl
  sigma_succ m := by
    rw [stageSubsequence]
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.stageNested
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.stageNested target :: scope.openDecls } }

def HasRadiusTail
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hseed : HasStageSeed inp P L0)
    (psi : Nat → Nat) (q : Nat) : Prop :=
  let S := stageSubsequence inp P L0 hseed q
  let d := radiusConvergenceSelection inp P L0 hseed q
  ∃ (rho : Nat → Nat) (hrho : StrictMono rho),
    (∀ n,
      (((L0.subseq S.sigma_strict).subseq
        (d.phi_strict.comp hrho)).φ n) = psi (q + n)) ∧
    HasStageJetConvergence inp P (L0.subseq S.sigma_strict)
      (Nat.cast_nonneg q) (d.phi ∘ rho) (d.phi_strict.comp hrho)
      d.U d.C0 d.C1 d.aInf d.Jinf d.Jbarinf d.gInf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HasRadiusTail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HasRadiusTail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HasRadiusTail ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasRadiusTail

theorem HasStageSeed.exists_radius_diag
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hseed : HasStageSeed inp P L0) :
    ∃ (psi : Nat → Nat) (_hpsi : StrictMono psi),
      ∀ q : Nat, HasRadiusTail inp P L0 hseed psi q := by
  let T := stageNested inp P L0 hseed
  let psi := L0.φ ∘ T.diag
  have hpsi : StrictMono psi := L0.φ_mono.comp T.diag_strict
  refine ⟨psi, hpsi, ?_⟩
  intro q
  let S := stageSubsequence inp P L0 hseed q
  let d := radiusConvergenceSelection inp P L0 hseed q
  let rho := T.tailFactor q
  have hrho : StrictMono rho := T.tailFactor_strict q
  change ∃ (rho : Nat → Nat) (hrho : StrictMono rho),
    (∀ n,
      (((L0.subseq S.sigma_strict).subseq
        (d.phi_strict.comp hrho)).φ n) = psi (q + n)) ∧
    HasStageJetConvergence inp P (L0.subseq S.sigma_strict)
      (Nat.cast_nonneg q) (d.phi ∘ rho) (d.phi_strict.comp hrho)
      d.U d.C0 d.C1 d.aInf d.Jinf d.Jbarinf d.gInf
  refine ⟨rho, hrho, ?_, ?_⟩
  · intro n
    have hfactor := congrArg L0.φ (T.diag_step_factor q n)
    simpa only [NetLimitData.subseq_phi, Function.comp_apply, psi, T, S, d,
      rho, stageNested] using hfactor.symm
  · exact d.convergence.subseq inp P (L0.subseq S.sigma_strict)
      (Nat.cast_nonneg q) d.phi_strict d.U d.C0 d.C1 d.aInf
      d.Jinf d.Jbarinf d.gInf hrho

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HasStageSeed.exists_radius_diag then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HasStageSeed.exists_radius_diag"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HasStageSeed.exists_radius_diag ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasStageSeed.exists_radius_diag

private noncomputable def choosePayloadOn
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (chart : NormalChartFamily (I := I) X)
    (hseed : HasStageSeedOn inp P L0 chart)
    (S : StageSubsequence) (m : Nat) :
    StageConvergenceSelectionOn inp P (L0.subseq S.sigma_strict) chart
      (m : Real) (Nat.cast_nonneg m) :=
  Classical.choice <| HasStageRefineOn.payload_nonempty inp P
    (L0.subseq S.sigma_strict) chart (m : Real)
    (Nat.cast_nonneg m) <|
      hseed.refine inp P L0 chart (L0.subseq S.sigma_strict)
        (NetLimitData.stable_subseq inp.decay P L0 S.sigma_strict hseed.1)
        (m : Real) (Nat.cast_nonneg m)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.choosePayloadOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.choosePayloadOn target :: scope.openDecls } }

private noncomputable def nextStateOn
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (chart : NormalChartFamily (I := I) X)
    (hseed : HasStageSeedOn inp P L0 chart)
    (S : StageSubsequence) (m : Nat) : StageSubsequence :=
  let d := choosePayloadOn inp P L0 chart hseed S m
  ⟨S.sigma ∘ d.phi, S.sigma_strict.comp d.phi_strict⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.nextStateOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.nextStateOn target :: scope.openDecls } }

noncomputable def stageSubsequenceOn
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (chart : NormalChartFamily (I := I) X)
    (hseed : HasStageSeedOn inp P L0 chart) : Nat → StageSubsequence
  | 0 => ⟨id, strictMono_id⟩
  | m + 1 => nextStateOn inp P L0 chart hseed
      (stageSubsequenceOn inp P L0 chart hseed m) m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.stageSubsequenceOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.stageSubsequenceOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.stageSubsequenceOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.stageSubsequenceOn

noncomputable def radiusConvergenceSelectionOn
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (chart : NormalChartFamily (I := I) X)
    (hseed : HasStageSeedOn inp P L0 chart) (m : Nat) :=
  choosePayloadOn inp P L0 chart hseed
    (stageSubsequenceOn inp P L0 chart hseed m) m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.radiusConvergenceSelectionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.radiusConvergenceSelectionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.radiusConvergenceSelectionOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.radiusConvergenceSelectionOn

private noncomputable def stageNestedOn
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (chart : NormalChartFamily (I := I) X)
    (hseed : HasStageSeedOn inp P L0 chart) : NestedSubseq where
  sigma m := (stageSubsequenceOn inp P L0 chart hseed m).sigma
  tau m := (radiusConvergenceSelectionOn inp P L0 chart hseed m).phi
  sigma_strict m :=
    (stageSubsequenceOn inp P L0 chart hseed m).sigma_strict
  tau_strict m :=
    (radiusConvergenceSelectionOn inp P L0 chart hseed m).phi_strict
  sigma_zero := rfl
  sigma_succ m := by
    rw [stageSubsequenceOn]
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.stageNestedOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.stageNestedOn target :: scope.openDecls } }

def HasRadiusTailOn
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (chart : NormalChartFamily (I := I) X)
    (hseed : HasStageSeedOn inp P L0 chart)
    (psi : Nat → Nat) (q : Nat) : Prop :=
  let S := stageSubsequenceOn inp P L0 chart hseed q
  let d := radiusConvergenceSelectionOn inp P L0 chart hseed q
  ∃ (rho : Nat → Nat) (hrho : StrictMono rho),
    (∀ n,
      (((L0.subseq S.sigma_strict).subseq
        (d.phi_strict.comp hrho)).φ n) = psi (q + n)) ∧
    HasStageJetConvergenceOn inp P (L0.subseq S.sigma_strict)
      (Nat.cast_nonneg q) (d.phi ∘ rho) (d.phi_strict.comp hrho)
      chart d.V d.U d.C0 d.C1 d.aInf d.Jinf d.Jbarinf d.gInf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HasRadiusTailOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HasRadiusTailOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HasRadiusTailOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasRadiusTailOn

theorem HasStageSeedOn.exists_radius_diag
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (chart : NormalChartFamily (I := I) X)
    (hseed : HasStageSeedOn inp P L0 chart) :
    ∃ (psi : Nat → Nat) (_hpsi : StrictMono psi),
      ∀ q : Nat, HasRadiusTailOn inp P L0 chart hseed psi q := by
  let T := stageNestedOn inp P L0 chart hseed
  let psi := L0.φ ∘ T.diag
  have hpsi : StrictMono psi := L0.φ_mono.comp T.diag_strict
  refine ⟨psi, hpsi, ?_⟩
  intro q
  let S := stageSubsequenceOn inp P L0 chart hseed q
  let d := radiusConvergenceSelectionOn inp P L0 chart hseed q
  let rho := T.tailFactor q
  have hrho : StrictMono rho := T.tailFactor_strict q
  change ∃ (rho : Nat → Nat) (hrho : StrictMono rho),
    (∀ n,
      (((L0.subseq S.sigma_strict).subseq
        (d.phi_strict.comp hrho)).φ n) = psi (q + n)) ∧
    HasStageJetConvergenceOn inp P (L0.subseq S.sigma_strict)
      (Nat.cast_nonneg q) (d.phi ∘ rho) (d.phi_strict.comp hrho)
      chart d.V d.U d.C0 d.C1 d.aInf d.Jinf d.Jbarinf d.gInf
  refine ⟨rho, hrho, ?_, ?_⟩
  · intro n
    have hfactor := congrArg L0.φ (T.diag_step_factor q n)
    simpa only [NetLimitData.subseq_phi, Function.comp_apply, psi, T, S, d,
      rho, stageNestedOn] using hfactor.symm
  · exact d.convergence.subseq inp P (L0.subseq S.sigma_strict)
      (Nat.cast_nonneg q) d.phi_strict chart d.V d.U d.C0 d.C1
      d.aInf d.Jinf d.Jbarinf d.gInf hrho

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HasStageSeedOn.exists_radius_diag then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HasStageSeedOn.exists_radius_diag"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HasStageSeedOn.exists_radius_diag ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasStageSeedOn.exists_radius_diag

theorem MetricCompactBase.exists_stage_diag
    (b : MetricCompactBase (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) :
    ∃ (inp : MetricCompactnessAssumptions (I := I) X)
        (L0 : NetLimitData inp.decay inp.D
          (properMetricsOfCompleteConnected (I := I) hcomplete hconn))
        (hseed : HasStageSeed inp (properMetricsOfCompleteConnected (I := I) hcomplete hconn) L0)
        (psi : Nat → Nat) (_hpsi : StrictMono psi),
      ∀ q : Nat, HasRadiusTail inp (properMetricsOfCompleteConnected (I := I) hcomplete hconn)
        L0 hseed psi q := by
  obtain ⟨inp, L0, hseed⟩ := b.exists_stage_seed hcomplete hconn
  obtain ⟨psi, hpsi, htail⟩ :=
    hseed.exists_radius_diag inp (properMetricsOfCompleteConnected (I := I) hcomplete hconn)
      L0
  exact ⟨inp, L0, hseed, psi, hpsi, htail⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactBase.exists_stage_diag then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactBase.exists_stage_diag"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactBase.exists_stage_diag ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactBase.exists_stage_diag

end CheegerGromovCompactness
end DifferentialGeometry
