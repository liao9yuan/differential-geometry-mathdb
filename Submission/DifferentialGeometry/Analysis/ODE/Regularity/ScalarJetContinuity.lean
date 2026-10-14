import Submission.DifferentialGeometry.Analysis.Calculus.IteratedDerivative.ScalarComposition
import Mathlib.Analysis.Calculus.Deriv.Prod
import Submission.DifferentialGeometry.Analysis.Calculus.TimeJet.MixedJetsAlongCurve
import Submission.DifferentialGeometry.Analysis.Calculus.TimeJet.EvolutionJets

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis

private abbrev ScalarFlowJetState (n : ℕ) :=
  (Fin (n + 1) → ℝ) × (Fin (n + 1) → Fin (n + 1) → ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.ScalarFlowJetState
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.ScalarFlowJetState target :: scope.openDecls } }

private def scalarFlowJetProjection (n : ℕ) :
    ScalarFlowJetState (n + 1) →L[ℝ] ScalarFlowJetState n :=
  let p : (Fin ((n + 1) + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    ContinuousLinearMap.pi fun j =>
      ContinuousLinearMap.proj (Fin.castLE (Nat.le_succ (n + 1)) j)
  let q : (Fin ((n + 1) + 1) → Fin ((n + 1) + 1) → ℝ) →L[ℝ]
      (Fin (n + 1) → Fin (n + 1) → ℝ) :=
    ContinuousLinearMap.pi fun k =>
      p.comp (ContinuousLinearMap.proj (Fin.castLE (Nat.le_succ (n + 1)) k))
  p.prodMap q

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.scalarFlowJetProjection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.scalarFlowJetProjection target :: scope.openDecls } }

private theorem scalarFlowJetProjection_apply (n : ℕ) (v : ScalarFlowJetState (n + 1)) :
    scalarFlowJetProjection n v =
      (fun j => v.1 (Fin.castLE (Nat.le_succ (n + 1)) j),
        fun k j => v.2 (Fin.castLE (Nat.le_succ (n + 1)) k)
          (Fin.castLE (Nat.le_succ (n + 1)) j)) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.scalarFlowJetProjection_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.scalarFlowJetProjection_apply target :: scope.openDecls } }

private def scalarFlowJetTimeLift (n : ℕ) :
    ScalarFlowJetState (n + 1) → ScalarFlowJetState n :=
  fun v =>
    (fun j => scalarJetComposition (𝕜 := ℝ) (F := ℝ) j.val
      (fun i => v.1 (Fin.castLE (by omega : j.val + 1 ≤ (n + 1) + 1) i),
        fun i => v.2 0 (Fin.castLE (by omega : j.val + 1 ≤ (n + 1) + 1) i)),
      fun k j =>
        v.2 k.succ (Fin.castLE (Nat.le_succ (n + 1)) j) +
          v.2 (Fin.castLE (Nat.le_succ (n + 1)) k) j.succ * v.2 0 0)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.scalarFlowJetTimeLift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.scalarFlowJetTimeLift target :: scope.openDecls } }

private theorem contDiff_scalarFlowJetTimeLift (n : ℕ) :
    ContDiff ℝ ∞ (scalarFlowJetTimeLift n) := by
  unfold scalarFlowJetTimeLift
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro j
    apply (contDiff_scalarJetComposition (𝕜 := ℝ) (F := ℝ) j.val).comp
    apply ContDiff.prodMk
    · apply contDiff_pi.mpr
      intro i
      exact (contDiff_apply ℝ ℝ
        (Fin.castLE (by omega : j.val + 1 ≤ (n + 1) + 1) i)).comp contDiff_fst
    · apply contDiff_pi.mpr
      intro i
      exact ((contDiff_apply ℝ ℝ
        (Fin.castLE (by omega : j.val + 1 ≤ (n + 1) + 1) i)).comp
          (contDiff_apply ℝ (Fin ((n + 1) + 1) → ℝ) 0)).comp contDiff_snd
  · apply contDiff_pi.mpr
    intro k
    apply contDiff_pi.mpr
    intro j
    have hEval (r s : Fin ((n + 1) + 1)) :
        ContDiff ℝ ∞ (fun v : ScalarFlowJetState (n + 1) => v.2 r s) :=
      ((contDiff_apply ℝ ℝ s).comp
        (contDiff_apply ℝ (Fin ((n + 1) + 1) → ℝ) r)).comp contDiff_snd
    exact (hEval k.succ (Fin.castLE (Nat.le_succ (n + 1)) j)).add
      ((hEval (Fin.castLE (Nat.le_succ (n + 1)) k) j.succ).mul (hEval 0 0))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.contDiff_scalarFlowJetTimeLift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.contDiff_scalarFlowJetTimeLift target :: scope.openDecls } }


private def scalarFlowJet (J : Set ℝ) (γ ξ : ℝ → ℝ → ℝ) (n : ℕ)
    (x t : ℝ) : ScalarFlowJetState n :=
  (fun i => iteratedDeriv i.val (γ t) x,
    fun i l => iteratedDerivWithin i.val
      (fun s => iteratedDeriv l.val (ξ s) (γ t x)) J t)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.scalarFlowJet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.scalarFlowJet target :: scope.openDecls } }

private theorem scalarFlowJetProjection_scalarFlowJet
    (J : Set ℝ) (γ ξ : ℝ → ℝ → ℝ) (n : ℕ) (x t : ℝ) :
    scalarFlowJetProjection n (scalarFlowJet J γ ξ (n + 1) x t) =
      scalarFlowJet J γ ξ n x t := by
  rw [scalarFlowJetProjection_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.scalarFlowJetProjection_scalarFlowJet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.scalarFlowJetProjection_scalarFlowJet target :: scope.openDecls } }

private theorem hasDerivWithinAt_scalarFlowJet
    {J V : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (hacc : J ⊆ closure (interior J)) (hV : IsOpen V)
    {γ ξ : ℝ → ℝ → ℝ}
    (hγ : ContDiffOn ℝ ∞ (Function.uncurry γ) (J ×ˢ V))
    (hξ : ContDiffOn ℝ ∞ (Function.uncurry ξ) (J ×ˢ _root_.Set.univ))
    (hode : ∀ t ∈ J, ∀ x ∈ V,
      HasDerivWithinAt (fun s => γ s x) (ξ t (γ t x)) J t)
    (n : ℕ) {t x : ℝ} (ht : t ∈ J) (hx : x ∈ V) :
    HasDerivWithinAt (scalarFlowJet J γ ξ n x)
      (scalarFlowJetTimeLift n (scalarFlowJet J γ ξ (n + 1) x t)) J t := by
  apply HasDerivWithinAt.prodMk
  · apply hasDerivWithinAt_pi.mpr
    intro i
    have hd := hasDerivWithinAt_iteratedDeriv_of_evolution hJ hacc hV
      (hγ) (hode) i.val ht hx
    have hgs : ContDiffOn ℝ ∞ (γ t) V :=
      (hγ).comp (contDiffOn_const.prodMk contDiffOn_id)
        (fun x hx => ⟨ht, hx⟩)
    have hxs : ContDiffOn ℝ ∞ (ξ t) univ :=
      (hξ).comp (contDiffOn_const.prodMk contDiffOn_id)
        (fun x hx => ⟨ht, hx⟩)
    have heq := iteratedDeriv_eq_scalarJetComposition
      (n := i.val)
      ((hgs.contDiffAt (hV.mem_nhds hx)).of_le
        (WithTop.coe_le_coe.mpr le_top : (i.val : ℕ∞ω) ≤ ∞))
      ((hxs.contDiffAt (isOpen_univ.mem_nhds (_root_.Set.mem_univ (γ t x)))).of_le
        (WithTop.coe_le_coe.mpr le_top : (i.val : ℕ∞ω) ≤ ∞))
    change iteratedDeriv i.val (fun x => ξ t (γ t x)) x = _ at heq
    rw [heq] at hd
    simpa only [scalarFlowJet, scalarFlowJetTimeLift, Fin.val_zero, iteratedDerivWithin_zero,
      Fin.val_castLE] using hd
  · apply hasDerivWithinAt_pi.mpr
    intro i
    apply hasDerivWithinAt_pi.mpr
    intro l
    have hd := hasDerivWithinAt_mixed_derivatives_comp_graph hJ hacc
      (hξ) ht (hode t ht x hx) i.val l.val
    simpa only [scalarFlowJet, scalarFlowJetTimeLift, Fin.val_castLE, Fin.val_succ,
      Fin.val_zero, iteratedDerivWithin_zero, iteratedDeriv_zero,
      smul_eq_mul, mul_comm] using hd

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.hasDerivWithinAt_scalarFlowJet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.hasDerivWithinAt_scalarFlowJet target :: scope.openDecls } }

private theorem continuousOn_scalarFlowJet
    {P : Type*} [TopologicalSpace P] {S : Set P} {J V : Set ℝ}
    {γ ξ : P → ℝ → ℝ → ℝ}
    (hγjets : ∀ j : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDeriv j (γ q.1 q.2.1) q.2.2)
      (S ×ˢ J ×ˢ V))
    (hξjets : ∀ k j : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ =>
        iteratedDerivWithin k (fun t => iteratedDeriv j (ξ q.1 t) q.2.2) J q.2.1)
      (S ×ˢ J ×ˢ _root_.Set.univ)) (n : ℕ) :
    ContinuousOn
      (fun q : P × ℝ × ℝ => scalarFlowJet J (γ q.1) (ξ q.1) n q.2.2 q.2.1)
      (S ×ˢ J ×ˢ V) := by
  have hγcont : ContinuousOn (fun q : P × ℝ × ℝ => γ q.1 q.2.1 q.2.2)
      (S ×ˢ J ×ˢ V) := by
    simpa only [iteratedDeriv_zero] using hγjets 0
  apply ContinuousOn.prodMk
  · exact continuousOn_pi.mpr fun i => hγjets i.val
  · apply continuousOn_pi.mpr
    intro i
    exact continuousOn_pi.mpr fun l =>
      continuousOn_mixed_derivatives_comp_graph hγcont hξjets i.val l.val

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.continuousOn_scalarFlowJet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.continuousOn_scalarFlowJet target :: scope.openDecls } }

theorem continuousOn_iteratedDerivWithin_iteratedDeriv_of_scalar_ode
    {P : Type*} [TopologicalSpace P] {S : Set P} {J V : Set ℝ}
    (hJ : UniqueDiffOn ℝ J) (hacc : J ⊆ closure (interior J)) (hV : IsOpen V)
    {γ ξ : P → ℝ → ℝ → ℝ}
    (hγ : ∀ p ∈ S, ContDiffOn ℝ ∞ (Function.uncurry (γ p)) (J ×ˢ V))
    (hξ : ∀ p ∈ S, ContDiffOn ℝ ∞ (Function.uncurry (ξ p)) (J ×ˢ _root_.Set.univ))
    (hγjets : ∀ j : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDeriv j (γ q.1 q.2.1) q.2.2)
      (S ×ˢ J ×ˢ V))
    (hξjets : ∀ k j : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ =>
        iteratedDerivWithin k (fun t => iteratedDeriv j (ξ q.1 t) q.2.2) J q.2.1)
      (S ×ˢ J ×ˢ _root_.Set.univ))
    (hode : ∀ p ∈ S, ∀ t ∈ J, ∀ x ∈ V,
      HasDerivWithinAt (fun s => γ p s x) (ξ p t (γ p t x)) J t)
    (k j : ℕ) :
    ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDerivWithin k
        (fun t => iteratedDeriv j (γ q.1 t) q.2.2) J q.2.1)
      (S ×ˢ J ×ˢ V) := by
  let u : ∀ n, (P × ℝ) → ℝ → ScalarFlowJetState n := fun n q =>
    scalarFlowJet J (γ q.1) (ξ q.1) n q.2
  have hperm : ContinuousOn (fun q : (P × ℝ) × ℝ => (q.1.1, q.2, q.1.2))
      ((S ×ˢ V) ×ˢ J) := by fun_prop
  have hmaps : _root_.Set.MapsTo (fun q : (P × ℝ) × ℝ => (q.1.1, q.2, q.1.2))
      ((S ×ˢ V) ×ˢ J) (S ×ˢ J ×ˢ V) :=
    fun q hq => ⟨hq.1.1, hq.2, hq.1.2⟩
  have hu (n : ℕ) : ContinuousOn
      (fun q : (P × ℝ) × ℝ => u n q.1 q.2) ((S ×ˢ V) ×ˢ J) :=
    (continuousOn_scalarFlowJet hγjets hξjets n).comp hperm hmaps
  have hdu (n : ℕ) (q : P × ℝ) (hq : q ∈ S ×ˢ V) (t : ℝ) (ht : t ∈ J) :
      HasDerivWithinAt (u n q)
        (scalarFlowJetTimeLift n (u (n + 1) q t)) J t :=
    hasDerivWithinAt_scalarFlowJet hJ hacc hV (hγ q.1 hq.1) (hξ q.1 hq.1)
      (hode q.1 hq.1) n ht hq.2
  let Fproj : ScalarFlowJetState j → ℝ := fun v => v.1 ⟨j, Nat.lt_succ_self j⟩
  have hproj : ContDiffOn ℝ ∞ Fproj univ :=
    ((contDiff_apply ℝ ℝ (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))).comp
      contDiff_fst).contDiffOn
  have hh : ContinuousOn
      (fun q : (P × ℝ) × ℝ => iteratedDerivWithin k
        (fun t => iteratedDeriv j (γ q.1.1 t) q.1.2) J q.2) ((S ×ˢ V) ×ˢ J) := by
    simpa only [Fproj, u, scalarFlowJet] using
      continuousOn_iteratedDerivWithin_of_smooth_lifts
        (P := P × ℝ) (S := S ×ˢ V) (J := J)
      (X := ScalarFlowJetState) (next := fun n => n + 1)
      scalarFlowJetProjection scalarFlowJetTimeLift (fun _ => _root_.Set.univ)
      (fun _ => isOpen_univ) (fun _ _ _ => _root_.Set.mem_univ _)
      (fun n => (contDiff_scalarFlowJetTimeLift n).contDiffOn) hJ u hu
      (fun _ _ _ _ _ => _root_.Set.mem_univ _)
      (fun n q _ t _ => scalarFlowJetProjection_scalarFlowJet J (γ q.1) (ξ q.1) n q.2 t)
      hdu k j Fproj hproj
  have hp : ContinuousOn (fun q : P × ℝ × ℝ => ((q.1, q.2.2), q.2.1))
      (S ×ˢ J ×ˢ V) := by fun_prop
  exact hh.comp hp (fun q hq => ⟨⟨hq.1, hq.2.2⟩, hq.2.1⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.continuousOn_iteratedDerivWithin_iteratedDeriv_of_scalar_ode then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.continuousOn_iteratedDerivWithin_iteratedDeriv_of_scalar_ode"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.continuousOn_iteratedDerivWithin_iteratedDeriv_of_scalar_ode ``Submission.DifferentialGeometry.Analysis.continuousOn_iteratedDerivWithin_iteratedDeriv_of_scalar_ode

theorem continuousOn_iteratedFDerivWithin_of_scalar_ode
    {P : Type*} [TopologicalSpace P] {S : Set P} {J V : Set ℝ}
    (hJ : UniqueDiffOn ℝ J) (hacc : J ⊆ closure (interior J)) (hV : IsOpen V)
    {γ ξ : P → ℝ → ℝ → ℝ}
    (hγ : ∀ p ∈ S, ContDiffOn ℝ ∞ (Function.uncurry (γ p)) (J ×ˢ V))
    (hξ : ∀ p ∈ S, ContDiffOn ℝ ∞ (Function.uncurry (ξ p)) (J ×ˢ _root_.Set.univ))
    (hγjets : ∀ j : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDeriv j (γ q.1 q.2.1) q.2.2)
      (S ×ˢ J ×ˢ V))
    (hξjets : ∀ k j : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ =>
        iteratedDerivWithin k (fun t => iteratedDeriv j (ξ q.1 t) q.2.2) J q.2.1)
      (S ×ˢ J ×ˢ _root_.Set.univ))
    (hode : ∀ p ∈ S, ∀ t ∈ J, ∀ x ∈ V,
      HasDerivWithinAt (fun s => γ p s x) (ξ p t (γ p t x)) J t)
    (n : ℕ) :
    ContinuousOn
      (fun q : P × ℝ × ℝ =>
        iteratedFDerivWithin ℝ n (Function.uncurry (γ q.1)) (J ×ˢ V) q.2)
      (S ×ˢ J ×ˢ V) :=
  continuousOn_iteratedFDerivWithin_of_mixed_derivatives hJ hacc hV hγ
    (continuousOn_iteratedDerivWithin_iteratedDeriv_of_scalar_ode
      hJ hacc hV hγ hξ hγjets hξjets hode) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.continuousOn_iteratedFDerivWithin_of_scalar_ode then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.continuousOn_iteratedFDerivWithin_of_scalar_ode"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.continuousOn_iteratedFDerivWithin_of_scalar_ode ``Submission.DifferentialGeometry.Analysis.continuousOn_iteratedFDerivWithin_of_scalar_ode

end DifferentialGeometry.Analysis
