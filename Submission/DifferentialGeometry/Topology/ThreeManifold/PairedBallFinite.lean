import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallLoop
import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallMerge
import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallEmpty
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteCongruence
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ChoiceIndependence
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedCongruence
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.LocallyConstant.Basic
import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallQuotientSmooth
import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallLoopSmooth
import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallLoopRadial
import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallDistinctSmooth
import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallDistinctRadial
import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallEmptySmooth
import Submission.DifferentialGeometry.Topology.Manifold.Diffeomorph.Sigma

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Metric _root_.Submission.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

section

namespace DifferentialGeometry.Topology.PairedBallGluing

universe v w t
variable {V : Type v} {E : Type w} {A : Type t}
  (endpoint : E → Bool → V) (s : E)
  (assign : A → V) (L : V → List A)

private def loopLabels : Option {v // v ≠ endpoint s _root_.Bool.false} → List A
  | none => L (endpoint s _root_.Bool.false)
  | some v => L v.val

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.loopLabels
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.loopLabels target :: scope.openDecls } }

private def mergeLabels : Option {v // v ≠ endpoint s _root_.Bool.false ∧ v ≠ endpoint s _root_.Bool.true} → List A
  | none => L (endpoint s _root_.Bool.false) ++ L (endpoint s _root_.Bool.true)
  | some v => L v.val

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergeLabels
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.mergeLabels target :: scope.openDecls } }

private theorem mem_loopLabels
    (hL : ∀ v a, a ∈ L v ↔ assign a = v)
    (v : Option {v // v ≠ endpoint s _root_.Bool.false}) (a : A) :
    a ∈ loopLabels endpoint s L v ↔ loopVertex endpoint s (assign a) = v := by
  classical
  cases v with
  | none => simp only [loopLabels, hL, loopVertex]; split_ifs <;> simp_all
  | some v =>
    simp only [loopLabels, hL, loopVertex]
    by_cases h : assign a = endpoint s _root_.Bool.false
    · simp only [dif_pos h]
      constructor
      · intro ha
        exact (v.property (ha.symm.trans h)).elim
      · intro he
        exact (Option.some_ne_none _ he.symm).elim
    · simp only [dif_neg h, Option.some.injEq]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mem_loopLabels
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.mem_loopLabels target :: scope.openDecls } }

private theorem mem_mergeLabels
    (hL : ∀ v a, a ∈ L v ↔ assign a = v)
    (v : Option {v // v ≠ endpoint s _root_.Bool.false ∧ v ≠ endpoint s _root_.Bool.true}) (a : A) :
    a ∈ mergeLabels endpoint s L v ↔ mergeVertex endpoint s (assign a) = v := by
  classical
  cases v with
  | none =>
    simp only [mergeLabels, List.mem_append, hL, mergeVertex]
    split_ifs <;> simp_all
  | some v =>
    simp only [mergeLabels, hL, mergeVertex]
    by_cases h : assign a = endpoint s _root_.Bool.false
    · simp only [dif_pos h]
      constructor
      · intro ha
        exact (v.property.1 (ha.symm.trans h)).elim
      · intro he
        exact (Option.some_ne_none _ he.symm).elim
    · simp only [dif_neg h]
      by_cases h' : assign a = endpoint s _root_.Bool.true
      · simp only [dif_pos h']
        constructor
        · intro ha
          exact (v.property.2 (ha.symm.trans h')).elim
        · intro he
          exact (Option.some_ne_none _ he.symm).elim
      · simp only [dif_neg h', Option.some.injEq]
        exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mem_mergeLabels
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.mem_mergeLabels target :: scope.openDecls } }

private theorem nodup_loopLabels (hL : ∀ v, (L v).Nodup)
    (v : Option {v // v ≠ endpoint s _root_.Bool.false}) : (loopLabels endpoint s L v).Nodup := by
  cases v <;> exact hL _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.nodup_loopLabels
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.nodup_loopLabels target :: scope.openDecls } }

private theorem nodup_mergeLabels (hends : endpoint s _root_.Bool.false ≠ endpoint s _root_.Bool.true)
    (hL : ∀ v a, a ∈ L v ↔ assign a = v) (hn : ∀ v, (L v).Nodup)
    (v : Option {v // v ≠ endpoint s _root_.Bool.false ∧ v ≠ endpoint s _root_.Bool.true}) :
    (mergeLabels endpoint s L v).Nodup := by
  cases v with
  | some v => exact hn _
  | none =>
    apply (hn _).append (hn _)
    rw [List.disjoint_left]
    intro a ha hb
    exact hends ((hL _ a).mp ha |>.symm.trans ((hL _ a).mp hb))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.nodup_mergeLabels
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.nodup_mergeLabels target :: scope.openDecls } }


end DifferentialGeometry.Topology.PairedBallGluing

end

section

namespace DifferentialGeometry.Topology

universe u v

private theorem nonempty_orientedDiffeomorph_connectedSum_append_replicate_succ
    {A : Type v} (original : A → ConnectedClosedOrientedManifold.{u} 3)
    (L : List A) (Z X : ConnectedClosedOrientedManifold.{u} 3) (b : ℕ)
    (hX : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph X.toClosedOrientedManifold
      (finiteConnectedSum (L.map original ++ List.replicate b Z)).toClosedOrientedManifold)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X Z).toClosedOrientedManifold
      (finiteConnectedSum (L.map original ++ List.replicate (b + 1)
          Z)).toClosedOrientedManifold) := by
  obtain ⟨F⟩ := connectedSumOrientedTransport_holds X
    (finiteConnectedSum (L.map original ++ List.replicate b Z)) Z Z hX
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
  obtain ⟨G⟩ := finiteConnectedSum_append_orientedDiffeomorph
    (L.map original ++ List.replicate b Z) [Z]
  refine ⟨F.trans ?_⟩
  simpa only [finiteConnectedSum_singleton, List.replicate_succ', List.append_assoc]
    using G.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_connectedSum_append_replicate_succ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_connectedSum_append_replicate_succ target :: scope.openDecls } }

private theorem nonempty_orientedDiffeomorph_smoothConnectedSum_append_replicate
    {A : Type v} (original : A → ConnectedClosedOrientedManifold.{u} 3)
    (L K : List A) (Z X Y : ConnectedClosedOrientedManifold.{u} 3) (b c : ℕ)
    (p : OrientedBallChart X.toClosedOrientedManifold)
    (q : OrientedBallChart Y.toClosedOrientedManifold)
    (hX : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph X.toClosedOrientedManifold
      (finiteConnectedSum (L.map original ++ List.replicate b Z)).toClosedOrientedManifold))
    (hY : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Y.toClosedOrientedManifold
      (finiteConnectedSum (K.map original ++ List.replicate c Z)).toClosedOrientedManifold)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum X Y p q
          boundaryAttachment).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (finiteConnectedSum ((L ++ K).map original ++ List.replicate (b + c)
          Z)).toClosedOrientedManifold) := by
  obtain ⟨F₀⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts
    p (orientedBallChart X) q (orientedBallChart Y) boundaryAttachment
  obtain ⟨F₁⟩ := connectedSumOrientedTransport_holds X
    (finiteConnectedSum (L.map original ++ List.replicate b Z)) Y
    (finiteConnectedSum (K.map original ++ List.replicate c Z)) hX hY
  obtain ⟨F₂⟩ := finiteConnectedSum_append_orientedDiffeomorph
    (L.map original ++ List.replicate b Z) (K.map original ++ List.replicate c Z)
  have hperm : List.Perm
      ((L.map original ++ List.replicate b Z) ++ (K.map original ++ List.replicate c Z))
      ((L ++ K).map original ++ List.replicate (b + c) Z) := by
    rw [List.map_append, List.replicate_add, List.append_assoc, List.append_assoc]
    exact List.Perm.append_left (L.map original)
      (List.perm_append_comm_assoc (List.replicate b Z) (K.map original) (List.replicate c Z))
  obtain ⟨F₃⟩ := finiteConnectedSum_perm_orientedDiffeomorph hperm
  exact ⟨((F₀.trans F₁).trans F₂.symm).trans F₃⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_smoothConnectedSum_append_replicate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_smoothConnectedSum_append_replicate target :: scope.openDecls } }


end DifferentialGeometry.Topology

end

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w t
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.E3 target :: scope.openDecls } }

private theorem remaining_card_lt {E : Type w} [Finite E] (s : E) :
    Nat.card {e // e ≠ s} < Nat.card E := by
  classical
  let := Fintype.ofFinite E
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_subtype_lt (x := s) (by simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.remaining_card_lt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.remaining_card_lt target :: scope.openDecls } }

private theorem exists_finite_smooth_quotient_with_factor_lists {A : Type t}
    (original : A → ConnectedClosedOrientedManifold.{u} 3) :
    ∀ n, ∀ {V : Type v} {E : Type w}, [Finite V] → [Finite E] → Nat.card E = n →
      ∀ (N : V → ConnectedClosedOrientedManifold.{u} 3) (endpoint : E → Bool → V)
      (chart : (e : E) → (b : Bool) →
        OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
      (hdisj : Pairwise fun p q =>
        Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
          (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2))
      (C : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
        {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉
          ⋃ p, flagMap N endpoint chart p '' _root_.Metric.ball (0 : E3) 1})
      (assign : A → V) (L : V → List A) (k : V → ℕ),
      (∀ v a, a ∈ L v ↔ assign a = v) → (∀ v, (L v).Nodup) → (∀ v, L v ≠ []) →
      (∀ v, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph (N v).toClosedOrientedManifold
        (finiteConnectedSum ((L v).map original ++
          List.replicate (k v) (sphereTwoTimesCircleLift.ulift.{0,
              u}))).toClosedOrientedManifold)) →
      ∃ (W : Type v) (_ : Finite W) (M : W → ConnectedClosedOrientedManifold.{u} 3)
        (assign' : A → W) (L' : W → List A) (k' : W → ℕ),
        (∀ w a, a ∈ L' w ↔ assign' a = w) ∧ (∀ w, (L' w).Nodup) ∧ (∀ w, L' w ≠ []) ∧
        (∀ w, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph (M w).toClosedOrientedManifold
          (finiteConnectedSum ((L' w).map original ++
            List.replicate (k' w) (sphereTwoTimesCircleLift.ulift.{0,
                u}))).toClosedOrientedManifold)) ∧
        let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
          (PuncturedFactor N endpoint chart v) := fun v => (C v).toChartedSpace
        ∃ Qcharts : ChartedSpace E3
          (Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e boundaryAttachment x y)),
          let _ := Qcharts
          IsManifold (𝓡 3) ∞
            (Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e boundaryAttachment x y)) ∧
          IsLocalDiffeomorph (𝓡∂ 3) (𝓡 3) ∞
            (allCoreInclusion N endpoint chart hdisj (fun _ => boundaryAttachment)) ∧
          (∀ e, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
            (allSeamChart N endpoint chart hdisj (fun _ => boundaryAttachment) e)) ∧
          Nonempty (Diffeomorph (𝓡 3) (𝓡 3)
            (Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e boundaryAttachment x y))
            (Σ w, (M w).Carrier) ∞) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E hV hE hcard N endpoint chart hdisj C assign L k hmem hnodup hnonempty hpres
    let := hV
    let := hE
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
      (PuncturedFactor N endpoint chart v) := fun v => (C v).toChartedSpace
    cases isEmpty_or_nonempty E with
    | inl he =>
      let := he
      obtain ⟨Qcharts, hm, hc, hs, D, hD⟩ :=
        exists_smooth_quotient_atlas_of_isEmpty N endpoint chart hdisj
          (fun _ => boundaryAttachment) C
      exact ⟨V, hV, N, assign, L, k, hmem, hnodup, hnonempty, hpres,
        Qcharts, hm, hc, hs, ⟨D⟩⟩
    | inr he =>
      let := he
      let s : E := Classical.choice he
      have hlt : Nat.card {e // e ≠ s} < n := hcard ▸ remaining_card_lt s
      by_cases hloop : endpoint s _root_.Bool.true = endpoint s _root_.Bool.false
      · obtain ⟨S, F, b, hb, hd, H, hfirst, hu, hH, J, hJ⟩ :=
          exists_quotient_homeomorph_loop N endpoint chart s hloop hdisj
            (fun _ => boundaryAttachment) rfl
        let N' := loopFactor N endpoint s
        let ep' := fun e t => (loopFlag N endpoint chart s b e t).fst
        let ch' := fun e t => (loopFlag N endpoint chart s b e t).snd
        let assign' := loopVertex endpoint s ∘ assign
        let L' := loopLabels endpoint s L
        let k' : Option {v // v ≠ endpoint s _root_.Bool.false} → ℕ
          | none => k (endpoint s _root_.Bool.false) + 1
          | some v => k v.val
        have hmem' : ∀ v a, a ∈ L' v ↔ assign' a = v :=
          mem_loopLabels endpoint s assign L hmem
        have hn' : ∀ v, (L' v).Nodup := nodup_loopLabels endpoint s L hnodup
        have hne' : ∀ v, L' v ≠ [] := by intro v; cases v <;> exact hnonempty _
        have hp' : ∀ v, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (N' v).toClosedOrientedManifold
            (finiteConnectedSum ((L' v).map original ++
              List.replicate (k' v) (sphereTwoTimesCircleLift.ulift.{0,
                  u}))).toClosedOrientedManifold) := by
          intro v
          cases v with
          | some v => exact hpres _
          | none =>
            obtain ⟨G⟩ := nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph
              (M := N (endpoint s _root_.Bool.false)) (M' := N (endpoint s _root_.Bool.false))
              (N := sphereTwoTimesCircleLift) (N' := sphereTwoTimesCircleLift.ulift.{0, u})
              (ClosedOrientedManifold.OrientedDiffeomorph.refl
                (N (endpoint s _root_.Bool.false)).toClosedOrientedManifold)
              (ClosedOrientedManifold.uliftOrientedDiffeomorph.{0, u}
                sphereTwoTimesCircleLift.toClosedOrientedManifold)
            obtain ⟨K⟩ := nonempty_orientedDiffeomorph_connectedSum_append_replicate_succ
              original (L (endpoint s _root_.Bool.false)) (sphereTwoTimesCircleLift.ulift.{0, u})
              (N (endpoint s _root_.Bool.false)) (k (endpoint s _root_.Bool.false)) (hpres _)
            exact ⟨G.trans K⟩
        choose C' _ using fun v => exists_smoothBoundaryAtlas_puncturedFactor N' ep' ch' hd v
        let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
          (PuncturedFactor N' ep' ch' v) := fun v => (C' v).toChartedSpace
        obtain ⟨W, hW, M, assign'', L'', k'', hmem'', hn'', hne'', hp'',
          Qcharts', hm', hc', hs', ⟨K⟩⟩ :=
          ih _ hlt (V := Option {v // v ≠ endpoint s _root_.Bool.false}) (E := {e // e ≠ s}) rfl
            N' ep' ch' hd C' assign' L' k' hmem' hn' hne' hp'
        let _ := Qcharts'
        let _ := hm'
        obtain ⟨A, hmH, hcH, hsH, G, hG⟩ :=
          exists_loop_smooth_atlas_of_factor_representatives N endpoint chart s hloop hdisj
            S F b hb C C' H hfirst hu
        let _ := A
        have hGc : (fun q => G q) = H := funext hG
        have hcoreH : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
            (H ∘ seamCoreInclusion N endpoint chart hdisj s boundaryAttachment) := by
          have hh := DifferentialGeometry.isLocalDiffeomorph_comp G.isLocalDiffeomorph hcH
          simpa only [hGc] using hh
        have hseamH : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞
            (H ∘ seamChart N endpoint chart hdisj s boundaryAttachment) := by
          have hh := DifferentialGeometry.isLocalDiffeomorph_comp G.isLocalDiffeomorph hsH
          simpa only [hGc] using hh
        have hrad := loop_homeomorph_radialPoint N endpoint chart s hloop hdisj
          S F b hb H hfirst hu hd
        obtain ⟨Qcharts, hm, hc, hs, D, _⟩ :=
          exists_smooth_quotient_step_atlas N endpoint chart hdisj (fun _ => boundaryAttachment) s
            N' ep' ch' hd H J hJ (𝓡 3) hcoreH hseamH hrad hc' hs'
        let _ := Qcharts
        exact ⟨W, hW, M, assign'', L'', k'', hmem'', hn'', hne'', hp'',
          Qcharts, hm, hc, hs, ⟨D.trans K⟩⟩
      · have hends : endpoint s _root_.Bool.false ≠ endpoint s true := Ne.symm hloop
        obtain ⟨b, hbL, hbR, hd, H, hfirst, hsecond, hu, hH, J, hJ⟩ :=
          exists_quotient_homeomorph_merge N endpoint chart s hdisj
            (fun _ => boundaryAttachment) hends
        let N' := mergeFactor N endpoint chart s boundaryAttachment
        let ep' := fun e t => (mergeFlag N endpoint chart s boundaryAttachment b e t).fst
        let ch' := fun e t => (mergeFlag N endpoint chart s boundaryAttachment b e t).snd
        let assign' := mergeVertex endpoint s ∘ assign
        let L' := mergeLabels endpoint s L
        let k' : Option {v // v ≠ endpoint s _root_.Bool.false ∧ v ≠ endpoint s _root_.Bool.true} → ℕ
          | none => k (endpoint s _root_.Bool.false) + k (endpoint s _root_.Bool.true)
          | some v => k v.val
        have hmem' : ∀ v a, a ∈ L' v ↔ assign' a = v :=
          mem_mergeLabels endpoint s assign L hmem
        have hn' : ∀ v, (L' v).Nodup := nodup_mergeLabels endpoint s assign L hends hmem hnodup
        have hne' : ∀ v, L' v ≠ [] := by
          intro v
          cases v with
          | some v => exact hnonempty _
          | none => exact fun h => hnonempty _ (List.append_eq_nil_iff.mp h).1
        have hp' : ∀ v, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (N' v).toClosedOrientedManifold
            (finiteConnectedSum ((L' v).map original ++
              List.replicate (k' v) (sphereTwoTimesCircleLift.ulift.{0,
                  u}))).toClosedOrientedManifold) := by
          intro v
          cases v with
          | some v => exact hpres _
          | none =>
            exact nonempty_orientedDiffeomorph_smoothConnectedSum_append_replicate
              original (L (endpoint s _root_.Bool.false)) (L (endpoint s _root_.Bool.true))
                  (sphereTwoTimesCircleLift.ulift.{0, u})
              (N (endpoint s _root_.Bool.false)) (N (endpoint s _root_.Bool.true)) (k (endpoint s _root_.Bool.false))
              (k (endpoint s _root_.Bool.true)) (chart s _root_.Bool.false) (chart s _root_.Bool.true) (hpres _) (hpres _)
        choose C' _ using fun v => exists_smoothBoundaryAtlas_puncturedFactor N' ep' ch' hd v
        let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
          (PuncturedFactor N' ep' ch' v) := fun v => (C' v).toChartedSpace
        obtain ⟨W, hW, M, assign'', L'', k'', hmem'', hn'', hne'', hp'',
          Qcharts', hm', hc', hs', ⟨K⟩⟩ :=
          ih _ hlt (V := Option {v // v ≠ endpoint s _root_.Bool.false ∧ v ≠ endpoint s _root_.Bool.true})
            (E := {e // e ≠ s}) rfl N' ep' ch' hd C' assign' L' k' hmem' hn' hne' hp'
        let _ := Qcharts'
        let _ := hm'
        have hbd := pairwise_disjoint_survivorChart_of_mergeFlag N endpoint chart s
          boundaryAttachment hends b hd
        obtain ⟨A, hmH, hcH, hsH, G, hG⟩ :=
          exists_smooth_distinct_merge_of_factor_representatives N endpoint chart hdisj s
            boundaryAttachment hends b C C' H hfirst hsecond hu hbd hbL hbR
        let _ := A
        have hGc : (fun q => G q) = H := funext hG
        have hcoreH : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
            (H ∘ seamCoreInclusion N endpoint chart hdisj s boundaryAttachment) := by
          have hh := DifferentialGeometry.isLocalDiffeomorph_comp G.isLocalDiffeomorph hcH
          simpa only [hGc] using hh
        have hseamH : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞
            (H ∘ seamChart N endpoint chart hdisj s boundaryAttachment) := by
          have hh := DifferentialGeometry.isLocalDiffeomorph_comp G.isLocalDiffeomorph hsH
          simpa only [hGc] using hh
        have hrad := merge_homeomorph_radialPoint N endpoint chart hdisj s boundaryAttachment
          hends b H hfirst hsecond hu hbL hbR hd
        obtain ⟨Qcharts, hm, hc, hs, D, _⟩ :=
          exists_smooth_quotient_step_atlas N endpoint chart hdisj (fun _ => boundaryAttachment) s
            N' ep' ch' hd H J hJ (𝓡 3) hcoreH hseamH hrad hc' hs'
        let _ := Qcharts
        exact ⟨W, hW, M, assign'', L'', k'', hmem'', hn'', hne'', hp'',
          Qcharts, hm, hc, hs, ⟨D.trans K⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.exists_finite_smooth_quotient_with_factor_lists
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.exists_finite_smooth_quotient_with_factor_lists target :: scope.openDecls } }


theorem exists_finite_connectedSum_diffeomorph
    {V : Type v} {E : Type w} [Finite V] [Finite E]
    (N : V → ConnectedClosedOrientedManifold.{u} 3)
    (endpoint : E → Bool → V)
    (chart : (e : E) → (b : Bool) →
      OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2))
    (C : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
      {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉
        ⋃ p, flagMap N endpoint chart p '' _root_.Metric.ball (0 : E3) 1}) :
    ∃ (W : Type v) (_ : Finite W) (assign : V → W) (L : W → List V) (k : W → ℕ),
      (∀ w v, v ∈ L w ↔ assign v = w) ∧ (∀ w, (L w).Nodup) ∧ (∀ w, L w ≠ []) ∧
      let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
        (PuncturedFactor N endpoint chart v) := fun v => (C v).toChartedSpace
      ∃ Qcharts : ChartedSpace E3
        (Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e boundaryAttachment x y)),
        let _ := Qcharts
        IsManifold (𝓡 3) ∞
          (Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e boundaryAttachment x y)) ∧
        IsLocalDiffeomorph (𝓡∂ 3) (𝓡 3) ∞
          (allCoreInclusion N endpoint chart hdisj (fun _ => boundaryAttachment)) ∧
        (∀ e, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
          (allSeamChart N endpoint chart hdisj (fun _ => boundaryAttachment) e)) ∧
        Nonempty (Diffeomorph (𝓡 3) (𝓡 3)
          (Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e boundaryAttachment x y))
          (Σ w, (finiteConnectedSum ((L w).map N ++
            List.replicate (k w) (sphereTwoTimesCircleLift.ulift.{0, u}))).Carrier) ∞) := by
  classical
  have hpres (v : V) : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (N v).toClosedOrientedManifold
      (finiteConnectedSum (([v] : List V).map N ++
        List.replicate 0 (sphereTwoTimesCircleLift.ulift.{0, u}))).toClosedOrientedManifold) :=
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
  obtain ⟨W, hW, M, assign, L, k, hm, hn, hne, hp, Qcharts, hman, hcore, hseam, ⟨H⟩⟩ :=
    exists_finite_smooth_quotient_with_factor_lists N (Nat.card E) rfl N endpoint chart hdisj C id
      (fun v => [v]) (fun _ => 0) (fun _ _ => List.mem_singleton) (fun _ => List.nodup_singleton _)
      (fun _ => List.cons_ne_nil _ _) hpres
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
    (PuncturedFactor N endpoint chart v) := fun v => (C v).toChartedSpace
  let _ := Qcharts
  let F := fun w => Classical.choice (hp w)
  exact ⟨W, hW, assign, L, k, hm, hn, hne, Qcharts, hman, hcore, hseam,
    ⟨H.trans (sigmaCongrRightDiffeomorph fun w => (F w).val)⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.exists_finite_connectedSum_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.exists_finite_connectedSum_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.exists_finite_connectedSum_diffeomorph ``Submission.DifferentialGeometry.Topology.PairedBallGluing.exists_finite_connectedSum_diffeomorph

theorem exists_finite_connectedSum_quotient
    {V : Type v} {E : Type w} [Finite V] [Finite E]
    (N : V → ConnectedClosedOrientedManifold.{u} 3)
    (endpoint : E → Bool → V)
    (chart : (e : E) → (t : Bool) →
      OrientedBallChart (N (endpoint e t)).toClosedOrientedManifold)
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2)) :
    ∃ (W : Type v) (_ : Finite W) (assign : V → W) (L : W → List V) (k : W → ℕ),
      (∀ w v, v ∈ L w ↔ assign v = w) ∧ (∀ w, (L w).Nodup) ∧ (∀ w, L w ≠ []) ∧
      Nonempty (Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e boundaryAttachment x y) ≃ₜ
        (Σ w, (finiteConnectedSum ((L w).map N ++
          List.replicate (k w) (sphereTwoTimesCircleLift.ulift.{0, u}))).Carrier)) := by
  classical
  choose C _ using fun v => exists_smoothBoundaryAtlas_puncturedFactor N endpoint chart hdisj v
  obtain ⟨W, hW, assign, L, k, hm, hn, hne, Qcharts, _, _, _, ⟨D⟩⟩ :=
    exists_finite_connectedSum_diffeomorph N endpoint chart hdisj C
  exact ⟨W, hW, assign, L, k, hm, hn, hne, ⟨D.toHomeomorph⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.exists_finite_connectedSum_quotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.exists_finite_connectedSum_quotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.exists_finite_connectedSum_quotient ``Submission.DifferentialGeometry.Topology.PairedBallGluing.exists_finite_connectedSum_quotient

theorem exists_connectedSum_quotient_of_preconnected
    {V : Type v} {E : Type w} [Finite V] [Finite E] [Nonempty V]
    (N : V → ConnectedClosedOrientedManifold.{u} 3)
    (endpoint : E → Bool → V)
    (chart : (e : E) → (t : Bool) →
      OrientedBallChart (N (endpoint e t)).toClosedOrientedManifold)
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2))
    [PreconnectedSpace (Quot (fun x y => ∃ e,
      seamRel N endpoint chart hdisj e boundaryAttachment x y))] :
    ∃ (L : List V) (k : ℕ), L.Nodup ∧ (∀ v, v ∈ L) ∧
      Nonempty (Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e boundaryAttachment x y) ≃ₜ
        (finiteConnectedSum (L.map N ++
          List.replicate k (sphereTwoTimesCircleLift.ulift.{0, u}))).Carrier) := by
  classical
  obtain ⟨W, hW, assign, L, k, hm, hn, hne, ⟨H⟩⟩ :=
    exists_finite_connectedSum_quotient N endpoint chart hdisj
  let M := fun w => finiteConnectedSum ((L w).map N ++
    List.replicate (k w) (sphereTwoTimesCircleLift.ulift.{0, u}))
  have hpre : PreconnectedSpace (Σ w, (M w).Carrier) :=
    H.surjective.denseRange.preconnectedSpace H.continuous
  let := hpre
  have hf : IsLocallyConstant (Sigma.fst : (Σ w, (M w).Carrier) → W) :=
    fun S => isOpen_sigma_fst_preimage S
  have hw : Subsingleton W := ⟨fun x y => by
    let p := Classical.choice (inferInstance : Nonempty (M x).Carrier)
    let q := Classical.choice (inferInstance : Nonempty (M y).Carrier)
    exact hf.apply_eq_of_preconnectedSpace ⟨x, p⟩ ⟨y, q⟩⟩
  let := hw
  let w₀ := assign (Classical.choice (inferInstance : Nonempty V))
  let K : (Σ w, (M w).Carrier) ≃ₜ (M w₀).Carrier :=
    { toFun := fun x => (Subsingleton.elim x.fst w₀) ▸ x.snd
      invFun := fun x => ⟨w₀, x⟩
      left_inv := by
        intro x
        obtain ⟨w, x⟩ := x
        have h : w = w₀ := Subsingleton.elim _ _
        subst w
        rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_sigma fun w => by
        have h : w = w₀ := Subsingleton.elim _ _
        subst w
        exact continuous_id
      continuous_invFun := @continuous_sigmaMk W (fun w => (M w).Carrier)
        (fun w => (M w).topology) w₀ }
  exact ⟨L w₀, k w₀, hn _, fun v => (hm _ v).mpr (Subsingleton.elim _ _), ⟨H.trans K⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.exists_connectedSum_quotient_of_preconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.exists_connectedSum_quotient_of_preconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.exists_connectedSum_quotient_of_preconnected ``Submission.DifferentialGeometry.Topology.PairedBallGluing.exists_connectedSum_quotient_of_preconnected

end DifferentialGeometry.Topology.PairedBallGluing
