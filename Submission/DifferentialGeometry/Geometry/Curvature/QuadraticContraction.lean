import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped _root_.BigOperators

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure Rm04Symm (Rm : ι → ι → ι → ι → Real) : Prop where

  swap12 : ∀ a b c d : ι, Rm a b c d = -Rm b a c d

  swap34 : ∀ a b c d : ι, Rm a b c d = -Rm a b d c

  pair : ∀ a b c d : ι, Rm a b c d = Rm c d a b

  bianchi : ∀ a b c d : ι, Rm a b c d + Rm b c a d + Rm c a b d = 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Rm04Symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Rm04Symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Rm04Symm ``Submission.DifferentialGeometry.PDE.RicciFlow.Rm04Symm

structure Rm04PairSymm (Rm : ι → ι → ι → ι → Real) : Prop where

  swap12 : ∀ a b c d : ι, Rm a b c d = -Rm b a c d

  swap34 : ∀ a b c d : ι, Rm a b c d = -Rm a b d c

  pair : ∀ a b c d : ι, Rm a b c d = Rm c d a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Rm04PairSymm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Rm04PairSymm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Rm04PairSymm ``Submission.DifferentialGeometry.PDE.RicciFlow.Rm04PairSymm

omit [Fintype ι] [DecidableEq ι] in
theorem Rm04Symm.pair_symm {Rm : ι → ι → ι → ι → Real}
    (hRm : Rm04Symm Rm) : Rm04PairSymm Rm :=
  ⟨hRm.swap12, hRm.swap34, hRm.pair⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Rm04Symm
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Rm04Symm.pair_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Rm04Symm.pair_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Rm04Symm.pair_symm ``Submission.DifferentialGeometry.PDE.RicciFlow.Rm04Symm.pair_symm

omit [DecidableEq ι] in
private theorem sum4Swap (F : ι → ι → ι → ι → Real) :
    (∑ a : ι, ∑ b : ι, ∑ c : ι, ∑ d : ι, F a b c d)
      = ∑ c : ι, ∑ d : ι, ∑ a : ι, ∑ b : ι, F a b c d := by
  calc (∑ a : ι, ∑ b : ι, ∑ c : ι, ∑ d : ι, F a b c d)
      = ∑ a : ι, ∑ c : ι, ∑ b : ι, ∑ d : ι, F a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c : ι, ∑ a : ι, ∑ b : ι, ∑ d : ι, F a b c d := Finset.sum_comm
    _ = ∑ c : ι, ∑ a : ι, ∑ d : ι, ∑ b : ι, F a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c : ι, ∑ d : ι, ∑ a : ι, ∑ b : ι, F a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.sum4Swap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.sum4Swap target :: scope.openDecls } }

def quadSum (gInv : ι → ι → Real) (X : ι → ι → ι → ι → Real) : Real :=
  ∑ p : ι, ∑ q : ι, ∑ r : ι, ∑ s : ι, gInv p q * gInv r s * X p q r s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.quadSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.quadSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.quadSum ``Submission.DifferentialGeometry.PDE.RicciFlow.quadSum

omit [DecidableEq ι] in
theorem quadSum_congr (gInv : ι → ι → Real) {X Y : ι → ι → ι → ι → Real}
    (h : ∀ p q r s : ι, X p q r s = Y p q r s) :
    quadSum gInv X = quadSum gInv Y :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.quadSum_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.quadSum_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.quadSum_congr ``Submission.DifferentialGeometry.PDE.RicciFlow.quadSum_congr

omit [DecidableEq ι] in
private theorem quadSum4 (gInv : ι → ι → Real) (X₁ X₂ X₃ X₄ : ι → ι → ι → ι → Real) :
    quadSum gInv (fun p q r s => X₁ p q r s - X₂ p q r s - X₃ p q r s + X₄ p q r s)
      = quadSum gInv X₁ - quadSum gInv X₂ - quadSum gInv X₃ + quadSum gInv X₄ := by
  unfold quadSum
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.quadSum4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.quadSum4 target :: scope.openDecls } }

omit [DecidableEq ι] in
private theorem quadSumAdd (gInv : ι → ι → Real) (X Y : ι → ι → ι → ι → Real) :
    quadSum gInv (fun p q r s => X p q r s + Y p q r s)
      = quadSum gInv X + quadSum gInv Y := by
  unfold quadSum
  simp only [mul_add, Finset.sum_add_distrib]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.quadSumAdd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.quadSumAdd target :: scope.openDecls } }

omit [DecidableEq ι] in
private theorem quadSumA4 (gInv : ι → ι → Real) (X₁ X₂ X₃ X₄ : ι → ι → ι → ι → Real) :
    quadSum gInv (fun p q r s => X₁ p q r s + X₂ p q r s + X₃ p q r s + X₄ p q r s)
      = quadSum gInv X₁ + quadSum gInv X₂ + quadSum gInv X₃ + quadSum gInv X₄ := by
  unfold quadSum
  simp only [mul_add, Finset.sum_add_distrib]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.quadSumA4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.quadSumA4 target :: scope.openDecls } }

omit [DecidableEq ι] in
private theorem quadSumNeg (gInv : ι → ι → Real) (X : ι → ι → ι → ι → Real) :
    quadSum gInv (fun p q r s => -X p q r s) = -quadSum gInv X := by
  unfold quadSum
  simp only [mul_neg, Finset.sum_neg_distrib]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.quadSumNeg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.quadSumNeg target :: scope.openDecls } }

omit [DecidableEq ι] in
private theorem quadSwapPR (gInv : ι → ι → Real) (X : ι → ι → ι → ι → Real) :
    quadSum gInv X = quadSum gInv (fun p q r s => X r s p q) := by
  unfold quadSum
  calc (∑ p : ι, ∑ q : ι, ∑ r : ι, ∑ s : ι, gInv p q * gInv r s * X p q r s)
      = ∑ r : ι, ∑ s : ι, ∑ p : ι, ∑ q : ι, gInv p q * gInv r s * X p q r s :=
        sum4Swap _
    _ = ∑ p : ι, ∑ q : ι, ∑ r : ι, ∑ s : ι, gInv p q * gInv r s * X r s p q :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.quadSwapPR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.quadSwapPR target :: scope.openDecls } }

omit [DecidableEq ι] in
private theorem quadSwapRS (gInv : ι → ι → Real)
    (hgi : ∀ a b : ι, gInv a b = gInv b a) (X : ι → ι → ι → ι → Real) :
    quadSum gInv X = quadSum gInv (fun p q r s => X p q s r) := by
  unfold quadSum
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  calc (∑ r : ι, ∑ s : ι, gInv p q * gInv r s * X p q r s)
      = ∑ s : ι, ∑ r : ι, gInv p q * gInv r s * X p q r s := Finset.sum_comm
    _ = ∑ r : ι, ∑ s : ι, gInv p q * gInv r s * X p q s r :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hgi b a]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.quadSwapRS
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.quadSwapRS target :: scope.openDecls } }

omit [DecidableEq ι] in
private theorem quadSwapPQ (gInv : ι → ι → Real)
    (hgi : ∀ a b : ι, gInv a b = gInv b a) (X : ι → ι → ι → ι → Real) :
    quadSum gInv X = quadSum gInv (fun p q r s => X q p r s) := by
  unfold quadSum
  calc (∑ p : ι, ∑ q : ι, ∑ r : ι, ∑ s : ι, gInv p q * gInv r s * X p q r s)
      = ∑ q : ι, ∑ p : ι, ∑ r : ι, ∑ s : ι, gInv p q * gInv r s * X p q r s :=
        Finset.sum_comm
    _ = ∑ p : ι, ∑ q : ι, ∑ r : ι, ∑ s : ι, gInv p q * gInv r s * X q p r s :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [hgi b a]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.quadSwapPQ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.quadSwapPQ target :: scope.openDecls } }

def bComp (gInv : ι → ι → Real) (Rm : ι → ι → ι → ι → Real) (a b c d : ι) : Real :=
  ∑ e : ι, ∑ g : ι, ∑ f : ι, ∑ r : ι,
    gInv e g * gInv f r * Rm a e b f * Rm c g d r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.bComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.bComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.bComp ``Submission.DifferentialGeometry.PDE.RicciFlow.bComp

omit [DecidableEq ι] in
private theorem bComp_quad (gInv : ι → ι → Real) (Rm : ι → ι → ι → ι → Real)
    (a b c d : ι) :
    bComp gInv Rm a b c d = quadSum gInv (fun p q r s => Rm a p b r * Rm c q d s) :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.bComp_quad
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.bComp_quad target :: scope.openDecls } }

omit [DecidableEq ι] in
private theorem quadB (gInv : ι → ι → Real) (Rm : ι → ι → ι → ι → Real) (a b c d : ι) :
    quadSum gInv (fun p q r s => Rm a r b p * Rm c s d q) = bComp gInv Rm a b c d := by
  rw [bComp_quad]
  exact quadSwapPR gInv (fun p q r s => Rm a r b p * Rm c s d q)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.quadB
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.quadB target :: scope.openDecls } }

omit [DecidableEq ι] in
theorem bComp_swap (gInv : ι → ι → Real) {Rm : ι → ι → ι → ι → Real}
    (hsym : Rm04Symm Rm) (a b c d : ι) :
    bComp gInv Rm a b c d = bComp gInv Rm b a d c := by
  calc bComp gInv Rm a b c d
      = quadSum gInv (fun p q r s => Rm a r b p * Rm c s d q) := (quadB gInv Rm a b c d).symm
    _ = quadSum gInv (fun p q r s => Rm b p a r * Rm d q c s) :=
        quadSum_congr gInv fun p q r s => by rw [hsym.pair a r b p, hsym.pair c s d q]
    _ = bComp gInv Rm b a d c := (bComp_quad gInv Rm b a d c).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.bComp_swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.bComp_swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.bComp_swap ``Submission.DifferentialGeometry.PDE.RicciFlow.bComp_swap

def rmQ1 (gInv : ι → ι → Real) (Rm : ι → ι → ι → ι → Real) (i j k l : ι) : Real :=
  quadSum gInv (fun p q r s => Rm i j p s * Rm r q k l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmQ1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmQ1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmQ1 ``Submission.DifferentialGeometry.PDE.RicciFlow.rmQ1

def rmQ2 (gInv : ι → ι → Real) (Rm : ι → ι → ι → ι → Real) (i j k l : ι) : Real :=
  quadSum gInv (fun p q r s => Rm p i k s * Rm j q r l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmQ2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmQ2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmQ2 ``Submission.DifferentialGeometry.PDE.RicciFlow.rmQ2

def rmQ4 (gInv : ι → ι → Real) (Rm : ι → ι → ι → ι → Real) (i j k l : ι) : Real :=
  quadSum gInv (fun p q r s => Rm p i r l * Rm j q k s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmQ4 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmQ4"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmQ4 ``Submission.DifferentialGeometry.PDE.RicciFlow.rmQ4

def rmQuad (gInv : ι → ι → Real) (Rm : ι → ι → ι → ι → Real) (i j k l : ι) : Real :=
  rmQ1 gInv Rm i j k l - 2 * rmQ2 gInv Rm i j k l + 2 * rmQ4 gInv Rm i j k l

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmQuad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmQuad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmQuad ``Submission.DifferentialGeometry.PDE.RicciFlow.rmQuad

omit [DecidableEq ι] in
theorem rmQuad_eq_sum_raised
    (gInv : ι → ι → ℝ) (Rm Rm13 : ι → ι → ι → ι → ℝ)
    (hraise : ∀ i j k r, Rm13 i j k r = ∑ s, gInv r s * Rm i j k s)
    (i j k l : ι) :
    rmQuad gInv Rm i j k l =
      ∑ p, ∑ q, ∑ r, gInv p q *
        (Rm13 i j p r * Rm r q k l - 2 * Rm13 p i k r * Rm j q r l +
          2 * Rm p i r l * Rm13 j q k r) := by
  simp only [rmQuad, rmQ1, rmQ2, rmQ4, quadSum, hraise,
    Finset.mul_sum, Finset.sum_mul, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring_nf
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmQuad_eq_sum_raised then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmQuad_eq_sum_raised"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmQuad_eq_sum_raised ``Submission.DifferentialGeometry.PDE.RicciFlow.rmQuad_eq_sum_raised

omit [DecidableEq ι] in
theorem rmQ2_eq_b (gInv : ι → ι → Real) {Rm : ι → ι → ι → ι → Real}
    (hsym : Rm04Symm Rm) (hgi : ∀ a b : ι, gInv a b = gInv b a) (i j k l : ι) :
    rmQ2 gInv Rm i j k l = bComp gInv Rm i k j l := by
  calc rmQ2 gInv Rm i j k l
      = quadSum gInv (fun p q r s => Rm i p k s * Rm j q l r) :=
        quadSum_congr gInv fun p q r s => by
          rw [hsym.swap12 p i k s, hsym.swap34 j q r l]; ring
    _ = quadSum gInv (fun p q r s => Rm i p k r * Rm j q l s) :=
        quadSwapRS gInv hgi (fun p q r s => Rm i p k s * Rm j q l r)
    _ = bComp gInv Rm i k j l := (bComp_quad gInv Rm i k j l).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmQ2_eq_b then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmQ2_eq_b"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmQ2_eq_b ``Submission.DifferentialGeometry.PDE.RicciFlow.rmQ2_eq_b

omit [DecidableEq ι] in
theorem rmQ4_eq_b (gInv : ι → ι → Real) {Rm : ι → ι → ι → ι → Real}
    (hsym : Rm04Symm Rm) (i j k l : ι) :
    rmQ4 gInv Rm i j k l = bComp gInv Rm i l j k := by
  calc rmQ4 gInv Rm i j k l
      = quadSum gInv (fun p q r s => Rm i p l r * Rm j q k s) :=
        quadSum_congr gInv fun p q r s => by
          rw [hsym.swap12 p i r l, hsym.swap34 i p r l]; ring
    _ = bComp gInv Rm i l j k := (bComp_quad gInv Rm i l j k).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmQ4_eq_b then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmQ4_eq_b"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmQ4_eq_b ``Submission.DifferentialGeometry.PDE.RicciFlow.rmQ4_eq_b

omit [DecidableEq ι] in
theorem rmQ1_eq_b (gInv : ι → ι → Real) {Rm : ι → ι → ι → ι → Real}
    (hsym : Rm04Symm Rm) (hgi : ∀ a b : ι, gInv a b = gInv b a) (i j k l : ι) :
    rmQ1 gInv Rm i j k l = -2 * (bComp gInv Rm i j k l - bComp gInv Rm i j l k) := by
  have hA : ∀ p s : ι, Rm i j p s = Rm s p j i := by
    intro p s
    rw [hsym.pair i j p s, hsym.swap12 p s i j, hsym.swap34 s p i j]
    ring
  have hB1 : ∀ r p : ι, Rm r p j i = -Rm i r j p + Rm j r i p := by
    intro r p
    have h : Rm j i r p + Rm i r j p + Rm r j i p = 0 := hsym.bianchi j i r p
    have h2 : Rm r j i p = -Rm j r i p := hsym.swap12 r j i p
    rw [hsym.pair r p j i]
    linarith
  have hB2 : ∀ s q : ι, Rm s q k l = -Rm l s k q + Rm k s l q := by
    intro s q
    have h : Rm k l s q + Rm l s k q + Rm s k l q = 0 := hsym.bianchi k l s q
    have h2 : Rm s k l q = -Rm k s l q := hsym.swap12 s k l q
    rw [hsym.pair s q k l]
    linarith
  calc rmQ1 gInv Rm i j k l
      = quadSum gInv (fun p q r s => Rm s p j i * Rm r q k l) :=
        quadSum_congr gInv fun p q r s => by rw [hA p s]
    _ = quadSum gInv (fun p q r s => Rm r p j i * Rm s q k l) :=
        quadSwapRS gInv hgi (fun p q r s => Rm s p j i * Rm r q k l)
    _ = quadSum gInv (fun p q r s =>
          Rm i r j p * Rm l s k q - Rm i r j p * Rm k s l q
            - Rm j r i p * Rm l s k q + Rm j r i p * Rm k s l q) :=
        quadSum_congr gInv fun p q r s => by rw [hB1 r p, hB2 s q]; ring
    _ = quadSum gInv (fun p q r s => Rm i r j p * Rm l s k q)
          - quadSum gInv (fun p q r s => Rm i r j p * Rm k s l q)
          - quadSum gInv (fun p q r s => Rm j r i p * Rm l s k q)
          + quadSum gInv (fun p q r s => Rm j r i p * Rm k s l q) :=
        quadSum4 gInv _ _ _ _
    _ = bComp gInv Rm i j l k - bComp gInv Rm i j k l
          - bComp gInv Rm j i l k + bComp gInv Rm j i k l := by
        rw [quadB gInv Rm i j l k, quadB gInv Rm i j k l, quadB gInv Rm j i l k,
          quadB gInv Rm j i k l]
    _ = -2 * (bComp gInv Rm i j k l - bComp gInv Rm i j l k) := by
        rw [bComp_swap gInv hsym j i l k, bComp_swap gInv hsym j i k l]
        ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmQ1_eq_b then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmQ1_eq_b"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmQ1_eq_b ``Submission.DifferentialGeometry.PDE.RicciFlow.rmQ1_eq_b

omit [DecidableEq ι] in
theorem rmQuad_eq_b (gInv : ι → ι → Real) {Rm : ι → ι → ι → ι → Real}
    (hsym : Rm04Symm Rm) (hgi : ∀ a b : ι, gInv a b = gInv b a) (i j k l : ι) :
    rmQuad gInv Rm i j k l
      = -2 * (bComp gInv Rm i j k l - bComp gInv Rm i j l k
          + bComp gInv Rm i k j l - bComp gInv Rm i l j k) := by
  rw [rmQuad, rmQ1_eq_b gInv hsym hgi i j k l, rmQ2_eq_b gInv hsym hgi i j k l,
    rmQ4_eq_b gInv hsym i j k l]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmQuad_eq_b then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmQuad_eq_b"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmQuad_eq_b ``Submission.DifferentialGeometry.PDE.RicciFlow.rmQuad_eq_b

def rmLap (gInv : ι → ι → Real) (n2Rm : ι → ι → ι → ι → ι → ι → Real)
    (i j k l : ι) : Real :=
  ∑ p : ι, ∑ q : ι, gInv p q * n2Rm p q i j k l

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmLap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmLap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmLap ``Submission.DifferentialGeometry.PDE.RicciFlow.rmLap

def rmDrift (Rup : ι → ι → Real) (Rm : ι → ι → ι → ι → Real) (i j k l : ι) : Real :=
  (∑ p : ι, Rup i p * Rm p j k l) + (∑ p : ι, Rup j p * Rm i p k l) +
    (∑ p : ι, Rup k p * Rm i j p l) + (∑ p : ι, Rup l p * Rm i j k p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmDrift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmDrift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmDrift ``Submission.DifferentialGeometry.PDE.RicciFlow.rmDrift

def rmHess (n2Ric : ι → ι → ι → ι → Real) (i j k l : ι) : Real :=
  -n2Ric i k j l + n2Ric i l j k + n2Ric j k i l - n2Ric j l i k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmHess then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmHess"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmHess ``Submission.DifferentialGeometry.PDE.RicciFlow.rmHess

def nabGamma (gInv : ι → ι → Real) (n2Ric : ι → ι → ι → ι → Real)
    (d c a b : ι) : Real :=
  ∑ q : ι, gInv c q * (-n2Ric d a b q - n2Ric d b a q + n2Ric d q a b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nabGamma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nabGamma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nabGamma ``Submission.DifferentialGeometry.PDE.RicciFlow.nabGamma

def rmVar (g gInv : ι → ι → Real) (Ric : ι → ι → Real)
    (Rm13 : ι → ι → ι → ι → Real) (n2Ric : ι → ι → ι → ι → Real)
    (i j k l : ι) : Real :=
  ∑ p : ι,
    ((nabGamma gInv n2Ric i p j k - nabGamma gInv n2Ric j p i k) * g l p +
      Rm13 i j k p * ((-2 : Real) * Ric l p))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmVar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmVar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmVar ``Submission.DifferentialGeometry.PDE.RicciFlow.rmVar

private theorem lowerGamma (g gInv : ι → ι → Real) (n2Ric : ι → ι → ι → ι → Real)
    (hcon : ∀ a b : ι, (∑ p : ι, g a p * gInv p b) = if a = b then 1 else 0)
    (d a b l : ι) :
    (∑ p : ι, nabGamma gInv n2Ric d p a b * g l p)
      = -n2Ric d a b l - n2Ric d b a l + n2Ric d l a b := by
  calc (∑ p : ι, nabGamma gInv n2Ric d p a b * g l p)
      = ∑ p : ι, ∑ q : ι,
          g l p * gInv p q * (-n2Ric d a b q - n2Ric d b a q + n2Ric d q a b) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [nabGamma, Finset.sum_mul]
        exact Finset.sum_congr rfl fun q _ => by ring
    _ = ∑ q : ι, ∑ p : ι,
          g l p * gInv p q * (-n2Ric d a b q - n2Ric d b a q + n2Ric d q a b) :=
        Finset.sum_comm
    _ = ∑ q : ι, (∑ p : ι, g l p * gInv p q) *
          (-n2Ric d a b q - n2Ric d b a q + n2Ric d q a b) :=
        Finset.sum_congr rfl fun q _ => (Finset.sum_mul _ _ _).symm
    _ = -n2Ric d a b l - n2Ric d b a l + n2Ric d l a b := by
        simp only [hcon, ite_mul, one_mul, _root_.MulZeroClass.zero_mul, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.lowerGamma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.lowerGamma target :: scope.openDecls } }

theorem rmVar_eq_hess (g gInv : ι → ι → Real) (Ric : ι → ι → Real)
    (Rm13 : ι → ι → ι → ι → Real) (n2Ric : ι → ι → ι → ι → Real)
    (hcon : ∀ a b : ι, (∑ p : ι, g a p * gInv p b) = if a = b then 1 else 0)
    (i j k l : ι) :
    rmVar g gInv Ric Rm13 n2Ric i j k l
      = (n2Ric j i k l - n2Ric i j k l) + rmHess n2Ric i j k l
        - 2 * ∑ p : ι, Rm13 i j k p * Ric l p := by
  have h1 : (∑ p : ι,
        (nabGamma gInv n2Ric i p j k - nabGamma gInv n2Ric j p i k) * g l p)
      = (∑ p : ι, nabGamma gInv n2Ric i p j k * g l p)
        - (∑ p : ι, nabGamma gInv n2Ric j p i k * g l p) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have h2 : (∑ p : ι, Rm13 i j k p * ((-2 : Real) * Ric l p))
      = -2 * ∑ p : ι, Rm13 i j k p * Ric l p := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [rmVar, Finset.sum_add_distrib, h1, h2,
    lowerGamma g gInv n2Ric hcon i j k l, lowerGamma g gInv n2Ric hcon j i k l, rmHess]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmVar_eq_hess then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmVar_eq_hess"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmVar_eq_hess ``Submission.DifferentialGeometry.PDE.RicciFlow.rmVar_eq_hess

def RicCommAt (Rm13 : ι → ι → ι → ι → Real) (Ric : ι → ι → Real)
    (n2Ric : ι → ι → ι → ι → Real) : Prop :=
  ∀ i j k l : ι,
    n2Ric j i k l - n2Ric i j k l
      = (∑ p : ι, Rm13 i j k p * Ric p l) + (∑ p : ι, Rm13 i j l p * Ric k p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.RicCommAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.RicCommAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.RicCommAt ``Submission.DifferentialGeometry.PDE.RicciFlow.RicCommAt

omit [DecidableEq ι] in
private theorem contractRm13 (gInv : ι → ι → Real) (Ric Rup : ι → ι → Real)
    (Rm13 Rm : ι → ι → ι → ι → Real)
    (hraise : ∀ a b c d : ι, Rm13 a b c d = ∑ q : ι, gInv d q * Rm a b c q)
    (hRup : ∀ a b : ι, Rup a b = ∑ q : ι, gInv b q * Ric a q)
    (hgi : ∀ a b : ι, gInv a b = gInv b a)
    (a b c e : ι) :
    (∑ p : ι, Rm13 a b c p * Ric e p) = ∑ p : ι, Rup e p * Rm a b c p := by
  calc (∑ p : ι, Rm13 a b c p * Ric e p)
      = ∑ p : ι, ∑ q : ι, gInv p q * Rm a b c q * Ric e p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hraise a b c p, Finset.sum_mul]
    _ = ∑ q : ι, ∑ p : ι, gInv p q * Rm a b c q * Ric e p := Finset.sum_comm
    _ = ∑ q : ι, Rup e q * Rm a b c q := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hRup e q, Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => by rw [hgi q p]; ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.contractRm13
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.contractRm13 target :: scope.openDecls } }

omit [DecidableEq ι] in
theorem comm_eq_drift (gInv : ι → ι → Real) (Ric Rup : ι → ι → Real)
    (Rm13 Rm : ι → ι → ι → ι → Real) (n2Ric : ι → ι → ι → ι → Real)
    (hsym : Rm04Symm Rm)
    (hcomm : RicCommAt Rm13 Ric n2Ric)
    (hricsym : ∀ a b : ι, Ric a b = Ric b a)
    (hraise : ∀ a b c d : ι, Rm13 a b c d = ∑ q : ι, gInv d q * Rm a b c q)
    (hRup : ∀ a b : ι, Rup a b = ∑ q : ι, gInv b q * Ric a q)
    (hgi : ∀ a b : ι, gInv a b = gInv b a)
    (i j k l : ι) :
    n2Ric j i k l - n2Ric i j k l
      = (∑ p : ι, Rup l p * Rm i j k p) - (∑ p : ι, Rup k p * Rm i j p l) := by
  have hfirst : (∑ p : ι, Rm13 i j k p * Ric p l) = ∑ p : ι, Rup l p * Rm i j k p := by
    rw [show (∑ p : ι, Rm13 i j k p * Ric p l) = ∑ p : ι, Rm13 i j k p * Ric l p from
      Finset.sum_congr rfl fun p _ => by rw [hricsym p l]]
    exact contractRm13 gInv Ric Rup Rm13 Rm hraise hRup hgi i j k l
  have hsecond : (∑ p : ι, Rm13 i j l p * Ric k p) = -∑ p : ι, Rup k p * Rm i j p l := by
    rw [contractRm13 gInv Ric Rup Rm13 Rm hraise hRup hgi i j l k, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun p _ => by rw [hsym.swap34 i j l p]; ring
  rw [hcomm i j k l, hfirst, hsecond]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.comm_eq_drift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.comm_eq_drift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.comm_eq_drift ``Submission.DifferentialGeometry.PDE.RicciFlow.comm_eq_drift

structure Rm04LapIn (gInv : ι → ι → Real) (Rm : ι → ι → ι → ι → Real)
    (Ric : ι → ι → Real) (n2Ric : ι → ι → ι → ι → Real)
    (n2Rm : ι → ι → ι → ι → ι → ι → Real) : Prop where

  bianchi2 : ∀ p a b c d e : ι,
    n2Rm p a b c d e + n2Rm p b c a d e + n2Rm p c a b d e = 0

  ricciId : ∀ a b c d e f : ι,
    n2Rm a b c d e f - n2Rm b a c d e f
      = -∑ q : ι, ∑ r : ι, gInv q r *
          (Rm a b c r * Rm q d e f + Rm a b d r * Rm c q e f +
            Rm a b e r * Rm c d q f + Rm a b f r * Rm c d e q)

  ricTrace : ∀ a b : ι, Ric a b = ∑ p : ι, ∑ q : ι, gInv p q * Rm p a b q

  n2RicTrace : ∀ a b c d : ι,
    n2Ric a b c d = ∑ p : ι, ∑ q : ι, gInv p q * n2Rm a b p c d q

  n2RmSwap12 : ∀ a b c d e f : ι, n2Rm a b c d e f = -n2Rm a b d c e f

  n2RmPair : ∀ a b c d e f : ι, n2Rm a b c d e f = n2Rm a b e f c d

  n2RicSym : ∀ a b c d : ι, n2Ric a b c d = n2Ric a b d c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Rm04LapIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Rm04LapIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Rm04LapIn ``Submission.DifferentialGeometry.PDE.RicciFlow.Rm04LapIn

omit [DecidableEq ι] in
private theorem traceMid (gInv : ι → ι → Real) {Ric : ι → ι → Real}
    {Rm : ι → ι → ι → ι → Real} (hsym : Rm04Symm Rm)
    (hric : ∀ a b : ι, Ric a b = ∑ p : ι, ∑ q : ι, gInv p q * Rm p a b q) (a b : ι) :
    (∑ p : ι, ∑ q : ι, gInv p q * Rm p a q b) = -Ric a b := by
  rw [hric a b, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun q _ => by rw [hsym.swap34 p a q b]; ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.traceMid
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.traceMid target :: scope.openDecls } }

omit [DecidableEq ι] in
private theorem quadTr (gInv : ι → ι → Real) {Ric : ι → ι → Real}
    {Rm : ι → ι → ι → ι → Real} (hsym : Rm04Symm Rm)
    (hric : ∀ a b : ι, Ric a b = ∑ p : ι, ∑ q : ι, gInv p q * Rm p a b q)
    (F : ι → Real) (a : ι) :
    quadSum gInv (fun p q u v => Rm p a q v * F u)
      = ∑ u : ι, ∑ v : ι, gInv u v * (-Ric a v) * F u := by
  unfold quadSum
  calc (∑ p : ι, ∑ q : ι, ∑ u : ι, ∑ v : ι, gInv p q * gInv u v * (Rm p a q v * F u))
      = ∑ u : ι, ∑ v : ι, ∑ p : ι, ∑ q : ι,
          gInv p q * gInv u v * (Rm p a q v * F u) := sum4Swap _
    _ = ∑ u : ι, ∑ v : ι, gInv u v * (∑ p : ι, ∑ q : ι, gInv p q * Rm p a q v) * F u := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        simp only [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ u : ι, ∑ v : ι, gInv u v * (-Ric a v) * F u :=
        Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by
          rw [traceMid gInv hsym hric a v]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.quadTr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.quadTr target :: scope.openDecls } }

omit [DecidableEq ι] in
private theorem quadTrDrift (gInv : ι → ι → Real) {Ric Rup : ι → ι → Real}
    {Rm : ι → ι → ι → ι → Real} (hsym : Rm04Symm Rm)
    (hric : ∀ a b : ι, Ric a b = ∑ p : ι, ∑ q : ι, gInv p q * Rm p a b q)
    (hRup : ∀ a b : ι, Rup a b = ∑ q : ι, gInv b q * Ric a q)
    (F G : ι → Real) (hFG : ∀ u : ι, F u = -G u) (a : ι) :
    quadSum gInv (fun p q u v => Rm p a q v * F u) = ∑ u : ι, Rup a u * G u := by
  rw [quadTr gInv hsym hric F a]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [hRup a u, Finset.sum_mul]
  exact Finset.sum_congr rfl fun v _ => by rw [hFG u]; ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.quadTrDrift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.quadTrDrift target :: scope.openDecls } }

omit [DecidableEq ι] in
private theorem tracedBi (gInv : ι → ι → Real) {Ric : ι → ι → Real}
    {Rm : ι → ι → ι → ι → Real} {n2Ric : ι → ι → ι → ι → Real}
    {n2Rm : ι → ι → ι → ι → ι → ι → Real}
    (hin : Rm04LapIn gInv Rm Ric n2Ric n2Rm) (d a k l : ι) :
    (∑ p : ι, ∑ q : ι, gInv p q * n2Rm d p a q k l)
      = n2Ric d k a l - n2Ric d l a k := by
  have hpt : ∀ p q : ι,
      n2Rm d p a q k l = n2Rm d k p l a q - n2Rm d l p k a q := by
    intro p q
    have hb := hin.bianchi2 d p k l a q
    have h1 : n2Rm d p a q k l = n2Rm d p k l a q := hin.n2RmPair d p a q k l
    have h2 : n2Rm d k l p a q = -n2Rm d k p l a q := hin.n2RmSwap12 d k l p a q
    rw [h1]
    linarith
  calc (∑ p : ι, ∑ q : ι, gInv p q * n2Rm d p a q k l)
      = ∑ p : ι, ∑ q : ι,
          (gInv p q * n2Rm d k p l a q - gInv p q * n2Rm d l p k a q) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
          rw [hpt p q]; ring
    _ = (∑ p : ι, ∑ q : ι, gInv p q * n2Rm d k p l a q)
          - (∑ p : ι, ∑ q : ι, gInv p q * n2Rm d l p k a q) := by
        simp only [Finset.sum_sub_distrib]
    _ = n2Ric d k a l - n2Ric d l a k := by
        rw [← hin.n2RicTrace d k l a, ← hin.n2RicTrace d l k a,
          hin.n2RicSym d k l a, hin.n2RicSym d l k a]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.tracedBi
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.tracedBi target :: scope.openDecls } }

private def rmW (gInv : ι → ι → Real) (Rm : ι → ι → ι → ι → Real) (i j k l : ι) : Real :=
  quadSum gInv (fun p q u v =>
      Rm p i j v * Rm u q k l + Rm p i q v * Rm j u k l +
        Rm p i k v * Rm j q u l + Rm p i l v * Rm j q k u) +
    quadSum gInv (fun p q u v =>
      Rm p j q v * Rm u i k l + Rm p j i v * Rm q u k l +
        Rm p j k v * Rm q i u l + Rm p j l v * Rm q i k u)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.rmW
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.rmW target :: scope.openDecls } }

omit [DecidableEq ι] in
private theorem lapHessW (gInv : ι → ι → Real) {Ric : ι → ι → Real}
    {Rm : ι → ι → ι → ι → Real} {n2Ric : ι → ι → ι → ι → Real}
    {n2Rm : ι → ι → ι → ι → ι → ι → Real}
    (hin : Rm04LapIn gInv Rm Ric n2Ric n2Rm) (i j k l : ι) :
    rmLap gInv n2Rm i j k l = rmHess n2Ric i j k l + rmW gInv Rm i j k l := by
  have hpt : ∀ p q : ι,
      n2Rm p q i j k l
        = -n2Rm i p j q k l - n2Rm j p q i k l
          + (∑ u : ι, ∑ v : ι, gInv u v *
              (Rm p i j v * Rm u q k l + Rm p i q v * Rm j u k l +
                Rm p i k v * Rm j q u l + Rm p i l v * Rm j q k u))
          + (∑ u : ι, ∑ v : ι, gInv u v *
              (Rm p j q v * Rm u i k l + Rm p j i v * Rm q u k l +
                Rm p j k v * Rm q i u l + Rm p j l v * Rm q i k u)) := by
    intro p q
    have hb := hin.bianchi2 p q i j k l
    have h1 := hin.ricciId p i j q k l
    have h2 := hin.ricciId p j q i k l
    linarith
  have hsplit : rmLap gInv n2Rm i j k l
      = -(∑ p : ι, ∑ q : ι, gInv p q * n2Rm i p j q k l)
        - (∑ p : ι, ∑ q : ι, gInv p q * n2Rm j p q i k l)
        + rmW gInv Rm i j k l := by
    unfold rmLap rmW quadSum
    calc (∑ p : ι, ∑ q : ι, gInv p q * n2Rm p q i j k l)
        = ∑ p : ι, ∑ q : ι,
            (-(gInv p q * n2Rm i p j q k l) - gInv p q * n2Rm j p q i k l
              + (∑ u : ι, ∑ v : ι, gInv p q * gInv u v *
                  (Rm p i j v * Rm u q k l + Rm p i q v * Rm j u k l +
                    Rm p i k v * Rm j q u l + Rm p i l v * Rm j q k u))
              + (∑ u : ι, ∑ v : ι, gInv p q * gInv u v *
                  (Rm p j q v * Rm u i k l + Rm p j i v * Rm q u k l +
                    Rm p j k v * Rm q i u l + Rm p j l v * Rm q i k u))) := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
          rw [hpt p q]
          simp only [mul_add, mul_sub, mul_neg, Finset.mul_sum, mul_assoc]
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_neg_distrib]
          ring
  have hswap : (∑ p : ι, ∑ q : ι, gInv p q * n2Rm j p q i k l)
      = -(∑ p : ι, ∑ q : ι, gInv p q * n2Rm j p i q k l) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun q _ => by rw [hin.n2RmSwap12 j p q i k l]; ring
  rw [hsplit, hswap, tracedBi gInv hin i j k l, tracedBi gInv hin j i k l, rmHess]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.lapHessW
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.lapHessW target :: scope.openDecls } }

omit [DecidableEq ι] in
private theorem wEq (gInv : ι → ι → Real) {Ric Rup : ι → ι → Real}
    {Rm : ι → ι → ι → ι → Real} (hsym : Rm04Symm Rm)
    (hgi : ∀ a b : ι, gInv a b = gInv b a)
    (hric : ∀ a b : ι, Ric a b = ∑ p : ι, ∑ q : ι, gInv p q * Rm p a b q)
    (hRup : ∀ a b : ι, Rup a b = ∑ q : ι, gInv b q * Ric a q) (i j k l : ι) :
    rmW gInv Rm i j k l
      = (∑ p : ι, Rup i p * Rm p j k l) + (∑ p : ι, Rup j p * Rm i p k l)
        - rmQuad gInv Rm i j k l := by
  have h16 : quadSum gInv (fun p q u v => Rm p i j v * Rm u q k l)
        + quadSum gInv (fun p q u v => Rm p j i v * Rm q u k l)
      = -rmQ1 gInv Rm i j k l := by
    rw [← quadSumAdd gInv (fun p q u v => Rm p i j v * Rm u q k l)
      (fun p q u v => Rm p j i v * Rm q u k l), rmQ1, ← quadSumNeg]
    refine quadSum_congr gInv fun p q u v => ?_
    have hb := hsym.bianchi p i j v
    have hs : Rm j p i v = -Rm p j i v := hsym.swap12 j p i v
    have hq : Rm q u k l = -Rm u q k l := hsym.swap12 q u k l
    have hx : Rm p i j v = -Rm i j p v + Rm p j i v := by linarith
    rw [hq, hx]
    ring
  have h2 : quadSum gInv (fun p q u v => Rm p i q v * Rm j u k l)
      = ∑ u : ι, Rup i u * Rm u j k l :=
    quadTrDrift gInv hsym hric hRup (fun u => Rm j u k l) (fun u => Rm u j k l)
      (fun u => hsym.swap12 j u k l) i
  have h5 : quadSum gInv (fun p q u v => Rm p j q v * Rm u i k l)
      = ∑ u : ι, Rup j u * Rm i u k l :=
    quadTrDrift gInv hsym hric hRup (fun u => Rm u i k l) (fun u => Rm i u k l)
      (fun u => hsym.swap12 u i k l) j
  have h3 : quadSum gInv (fun p q u v => Rm p i k v * Rm j q u l)
      = rmQ2 gInv Rm i j k l := rfl
  have h4 : quadSum gInv (fun p q u v => Rm p i l v * Rm j q k u)
      = -rmQ4 gInv Rm i j k l := by
    rw [quadSwapRS gInv hgi (fun p q u v => Rm p i l v * Rm j q k u), rmQ4, ← quadSumNeg]
    exact quadSum_congr gInv fun p q r s => by rw [hsym.swap34 p i l r]; ring
  have h7 : quadSum gInv (fun p q u v => Rm p j k v * Rm q i u l)
      = -rmQ4 gInv Rm i j k l := by
    rw [quadSwapPQ gInv hgi (fun p q u v => Rm p j k v * Rm q i u l), rmQ4, ← quadSumNeg]
    exact quadSum_congr gInv fun p q r s => by rw [hsym.swap12 q j k s]; ring
  have h8 : quadSum gInv (fun p q u v => Rm p j l v * Rm q i k u)
      = rmQ2 gInv Rm i j k l := by
    rw [quadSwapPQ gInv hgi (fun p q u v => Rm p j l v * Rm q i k u)]
    rw [quadSwapRS gInv hgi (fun p q r s => Rm q j l s * Rm p i k r), rmQ2]
    refine quadSum_congr gInv fun p q r s => ?_
    rw [hsym.swap12 q j l r, hsym.swap34 j q l r]
    ring
  rw [rmW, quadSumA4 gInv (fun p q u v => Rm p i j v * Rm u q k l)
      (fun p q u v => Rm p i q v * Rm j u k l) (fun p q u v => Rm p i k v * Rm j q u l)
      (fun p q u v => Rm p i l v * Rm j q k u),
    quadSumA4 gInv (fun p q u v => Rm p j q v * Rm u i k l)
      (fun p q u v => Rm p j i v * Rm q u k l) (fun p q u v => Rm p j k v * Rm q i u l)
      (fun p q u v => Rm p j l v * Rm q i k u),
    h2, h3, h4, h5, h7, h8, rmQuad]
  linarith [h16]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.wEq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.wEq target :: scope.openDecls } }

omit [DecidableEq ι] in
theorem rmHess_eq_lap (gInv : ι → ι → Real) {Ric Rup : ι → ι → Real}
    {Rm : ι → ι → ι → ι → Real} {n2Ric : ι → ι → ι → ι → Real}
    {n2Rm : ι → ι → ι → ι → ι → ι → Real}
    (hsym : Rm04Symm Rm) (hgi : ∀ a b : ι, gInv a b = gInv b a)
    (hin : Rm04LapIn gInv Rm Ric n2Ric n2Rm)
    (hRup : ∀ a b : ι, Rup a b = ∑ q : ι, gInv b q * Ric a q)
    (i j k l : ι) :
    rmHess n2Ric i j k l
      = rmLap gInv n2Rm i j k l + rmQuad gInv Rm i j k l
        - (∑ p : ι, Rup i p * Rm p j k l) - (∑ p : ι, Rup j p * Rm i p k l) := by
  rw [lapHessW gInv hin i j k l, wEq gInv hsym hgi hin.ricTrace hRup i j k l]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmHess_eq_lap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmHess_eq_lap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmHess_eq_lap ``Submission.DifferentialGeometry.PDE.RicciFlow.rmHess_eq_lap

theorem rmVar_eq_uhl (g gInv : ι → ι → Real) (Ric Rup : ι → ι → Real)
    (Rm13 Rm : ι → ι → ι → ι → Real) (n2Ric : ι → ι → ι → ι → Real)
    (n2Rm : ι → ι → ι → ι → ι → ι → Real)
    (hsym : Rm04Symm Rm) (hgi : ∀ a b : ι, gInv a b = gInv b a)
    (hricsym : ∀ a b : ι, Ric a b = Ric b a)
    (hcon : ∀ a b : ι, (∑ p : ι, g a p * gInv p b) = if a = b then 1 else 0)
    (hraise : ∀ a b c d : ι, Rm13 a b c d = ∑ q : ι, gInv d q * Rm a b c q)
    (hRup : ∀ a b : ι, Rup a b = ∑ q : ι, gInv b q * Ric a q)
    (hcomm : RicCommAt Rm13 Ric n2Ric)
    (hin : Rm04LapIn gInv Rm Ric n2Ric n2Rm)
    (i j k l : ι) :
    rmVar g gInv Ric Rm13 n2Ric i j k l
      = rmLap gInv n2Rm i j k l
        - 2 * (bComp gInv Rm i j k l - bComp gInv Rm i j l k
            + bComp gInv Rm i k j l - bComp gInv Rm i l j k)
        - rmDrift Rup Rm i j k l := by
  have hdrift4 : (∑ p : ι, Rm13 i j k p * Ric l p) = ∑ p : ι, Rup l p * Rm i j k p :=
    contractRm13 gInv Ric Rup Rm13 Rm hraise hRup hgi i j k l
  rw [rmVar_eq_hess g gInv Ric Rm13 n2Ric hcon i j k l,
    comm_eq_drift gInv Ric Rup Rm13 Rm n2Ric hsym hcomm hricsym hraise hRup hgi i j k l,
    rmHess_eq_lap gInv hsym hgi hin hRup i j k l,
    rmQuad_eq_b gInv hsym hgi i j k l, hdrift4, rmDrift]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmVar_eq_uhl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmVar_eq_uhl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmVar_eq_uhl ``Submission.DifferentialGeometry.PDE.RicciFlow.rmVar_eq_uhl

end Algebra

end DifferentialGeometry.PDE.RicciFlow
