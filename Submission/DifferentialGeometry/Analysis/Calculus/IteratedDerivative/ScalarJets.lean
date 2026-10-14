import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set
open scoped _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Analysis

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def scalarJetProjection {m k : ℕ} (h : m ≤ k) :
    (ℝ × ℝ × (Fin k → F)) →L[ℝ] (ℝ × ℝ × (Fin m → F)) :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × (Fin k → F))).prod
    (((ContinuousLinearMap.fst ℝ ℝ (Fin k → F)).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × (Fin k → F)))).prod
      (ContinuousLinearMap.pi fun i => (ContinuousLinearMap.proj (Fin.castLE h i)).comp
        ((ContinuousLinearMap.snd ℝ ℝ (Fin k → F)).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × (Fin k → F))))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.scalarJetProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.scalarJetProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.scalarJetProjection ``Submission.DifferentialGeometry.Analysis.scalarJetProjection

@[simp]
theorem scalarJetProjection_apply {m k : ℕ} (h : m ≤ k)
    (p : ℝ × ℝ × (Fin k → F)) :
    scalarJetProjection h p = (p.1, p.2.1, fun i => p.2.2 (Fin.castLE h i)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.scalarJetProjection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.scalarJetProjection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.scalarJetProjection_apply ``Submission.DifferentialGeometry.Analysis.scalarJetProjection_apply

private def scalarJetTangent (k : ℕ) (p : ℝ × ℝ × (Fin (k + 1) → F)) :
    ℝ × ℝ × (Fin k → F) := (0, 1, fun i => p.2.2 i.succ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.scalarJetTangent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.scalarJetTangent target :: scope.openDecls } }

def scalarJetProlongation {m : ℕ} (Φ : ℝ × ℝ × (Fin m → F) → G) :
    (n : ℕ) → (ℝ × ℝ × (Fin (m + n) → F)) → G
  | 0 => Φ
  | n + 1 => fun p => fderiv ℝ (scalarJetProlongation Φ n)
      (scalarJetProjection (Nat.le_succ (m + n)) p) (scalarJetTangent (m + n) p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.scalarJetProlongation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.scalarJetProlongation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.scalarJetProlongation ``Submission.DifferentialGeometry.Analysis.scalarJetProlongation

@[simp]
theorem scalarJetProlongation_zero {m : ℕ} (Φ : ℝ × ℝ × (Fin m → F) → G) :
    scalarJetProlongation Φ 0 = Φ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.scalarJetProlongation_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.scalarJetProlongation_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.scalarJetProlongation_zero ``Submission.DifferentialGeometry.Analysis.scalarJetProlongation_zero

private theorem contDiff_scalarJetTangent (k : ℕ) :
    ContDiff ℝ ∞ (scalarJetTangent (F := F) k) := by
  apply ContDiff.prodMk contDiff_const
  apply ContDiff.prodMk contDiff_const
  exact contDiff_pi.mpr fun i => (contDiff_apply ℝ F i.succ).comp (contDiff_snd.comp contDiff_snd)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.contDiff_scalarJetTangent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.contDiff_scalarJetTangent target :: scope.openDecls } }

theorem contDiffOn_scalarJetProlongation {m : ℕ}
    {Φ : ℝ × ℝ × (Fin m → F) → G} {U : Set (ℝ × ℝ × (Fin m → F))}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U) (n : ℕ) :
    ContDiffOn ℝ ∞ (scalarJetProlongation Φ n)
      (scalarJetProjection (Nat.le_add_right m n) ⁻¹' U) := by
  induction n with
  | zero =>
    have hset : scalarJetProjection (F := F) (Nat.le_add_right m 0) ⁻¹' U = U := by
      ext p
      rfl
    rw [hset]
    exact hΦ
  | succ n ih =>
    have hopen : IsOpen (scalarJetProjection (F := F) (Nat.le_add_right m n) ⁻¹' U) :=
      hU.preimage (scalarJetProjection _).continuous
    have hd := ih.fderiv_of_isOpen hopen (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
    have hcomp := hd.comp ((scalarJetProjection (F := F) (Nat.le_succ (m + n))).contDiff.contDiffOn)
      (fun p hp => hp)
    exact hcomp.clm_apply (contDiff_scalarJetTangent (F := F) (m + n)).contDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiffOn_scalarJetProlongation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiffOn_scalarJetProlongation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiffOn_scalarJetProlongation ``Submission.DifferentialGeometry.Analysis.contDiffOn_scalarJetProlongation

theorem hasDerivAt_scalarJetTuple_of_contDiffOn {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ → F) {V : Set ℝ} (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    (m : ℕ) (t : ℝ) {x : ℝ} (hx : x ∈ V) :
    HasDerivAt (fun y => (t, y, fun i : Fin m => iteratedDeriv i.val g y))
      (0, 1, fun i : Fin m => iteratedDeriv (i.val + 1) g x) x := by
  have hpi : HasDerivAt (fun y => fun i : Fin m => iteratedDeriv i.val g y)
      (fun i : Fin m => iteratedDeriv (i.val + 1) g x) x := by
    apply hasDerivAt_pi.mpr
    intro i
    have hi := hg.differentiableOn_iteratedDerivWithin
      (m := i.val) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top i.val)) hV.uniqueDiffOn
    have hd : DifferentiableAt ℝ (iteratedDerivWithin i.val g V) x :=
      (hi x hx).differentiableAt (hV.mem_nhds hx)
    have heq : iteratedDeriv i.val g =ᶠ[𝓝 x] iteratedDerivWithin i.val g V := by
      filter_upwards [hV.mem_nhds hx] with y hy
      exact (iteratedDerivWithin_of_isOpen hV hy).symm
    have hdi := hd.congr_of_eventuallyEq heq
    convert hdi.hasDerivAt using 1
    rw [iteratedDeriv_succ]
  exact (hasDerivAt_const (x := x) t).prodMk ((hasDerivAt_id x).prodMk hpi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasDerivAt_scalarJetTuple_of_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasDerivAt_scalarJetTuple_of_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasDerivAt_scalarJetTuple_of_contDiffOn ``Submission.DifferentialGeometry.Analysis.hasDerivAt_scalarJetTuple_of_contDiffOn

theorem hasDerivAt_scalarJetTuple {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ → F) (hg : ContDiff ℝ ∞ g) (m : ℕ) (t x : ℝ) :
    HasDerivAt (fun y => (t, y, fun i : Fin m => iteratedDeriv i.val g y))
      (0, 1, fun i : Fin m => iteratedDeriv (i.val + 1) g x) x := by
  exact hasDerivAt_scalarJetTuple_of_contDiffOn g isOpen_univ hg.contDiffOn m t (_root_.Set.mem_univ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasDerivAt_scalarJetTuple then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasDerivAt_scalarJetTuple"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasDerivAt_scalarJetTuple ``Submission.DifferentialGeometry.Analysis.hasDerivAt_scalarJetTuple

theorem iteratedDeriv_eq_scalarJetProlongation_of_contDiffOn {m : ℕ}
    {Φ : ℝ × ℝ × (Fin m → F) → G} {U : Set (ℝ × ℝ × (Fin m → F))}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U) {g : ℝ → F} {V : Set ℝ}
    (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V) (t : ℝ)
    (hmap : ∀ x ∈ V, (t, x, fun i : Fin m => iteratedDeriv i.val g x) ∈ U)
    (n : ℕ) {x : ℝ} (hx : x ∈ V) :
    iteratedDeriv n (fun y => Φ (t, y, fun i : Fin m => iteratedDeriv i.val g y)) x =
      scalarJetProlongation Φ n (t, x, fun i : Fin (m + n) => iteratedDeriv i.val g x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : (fun y => iteratedDeriv n
        (fun z => Φ (t, z, fun i : Fin m => iteratedDeriv i.val g z)) y) =ᶠ[𝓝 x]
        (fun y => scalarJetProlongation Φ n
          (t, y, fun i : Fin (m + n) => iteratedDeriv i.val g y)) := by
      filter_upwards [hV.mem_nhds hx] with y hy
      exact ih hy
    rw [heq.deriv_eq]
    have hdn := contDiffOn_scalarJetProlongation hU hΦ n
    have hopen : IsOpen (scalarJetProjection (F := F) (Nat.le_add_right m n) ⁻¹' U) :=
      hU.preimage (scalarJetProjection _).continuous
    have hmem : (t, x, fun i : Fin (m + n) => iteratedDeriv i.val g x) ∈
        scalarJetProjection (F := F) (Nat.le_add_right m n) ⁻¹' U := hmap x hx
    have hdiff := (hdn.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)
    exact (hdiff.hasFDerivAt.comp_hasDerivAt x
      (hasDerivAt_scalarJetTuple_of_contDiffOn g hV hg (m + n) t hx)).deriv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.iteratedDeriv_eq_scalarJetProlongation_of_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.iteratedDeriv_eq_scalarJetProlongation_of_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.iteratedDeriv_eq_scalarJetProlongation_of_contDiffOn ``Submission.DifferentialGeometry.Analysis.iteratedDeriv_eq_scalarJetProlongation_of_contDiffOn

theorem iteratedDeriv_eq_scalarJetProlongation {m : ℕ}
    {Φ : ℝ × ℝ × (Fin m → F) → G} {U : Set (ℝ × ℝ × (Fin m → F))}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U) {g : ℝ → F}
    (hg : ContDiff ℝ ∞ g) (t : ℝ)
    (hmap : ∀ x : ℝ, (t, x, fun i : Fin m => iteratedDeriv i.val g x) ∈ U)
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => Φ (t, y, fun i : Fin m => iteratedDeriv i.val g y)) x =
      scalarJetProlongation Φ n (t, x, fun i : Fin (m + n) => iteratedDeriv i.val g x) := by
  exact iteratedDeriv_eq_scalarJetProlongation_of_contDiffOn hU hΦ isOpen_univ hg.contDiffOn t
    (fun x _ => hmap x) n (_root_.Set.mem_univ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.iteratedDeriv_eq_scalarJetProlongation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.iteratedDeriv_eq_scalarJetProlongation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.iteratedDeriv_eq_scalarJetProlongation ``Submission.DifferentialGeometry.Analysis.iteratedDeriv_eq_scalarJetProlongation

end DifferentialGeometry.Analysis
