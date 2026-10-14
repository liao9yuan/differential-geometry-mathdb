import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallDistinctLocalMaps
import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallSeam
import Submission.DifferentialGeometry.Topology.Manifold.OpenCoverLocalDiffeomorph
import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallMerge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Metric _root_.Submission.Metric _root_.Function _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.E3 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.IC target :: scope.openDecls } }

variable {V : Type v} {E : Type w} [Finite E]
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (s : E) (a : BoundaryAttachment) (hends : endpoint s false ≠ endpoint s true)

private abbrev LFlag := {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.LFlag
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.LFlag target :: scope.openDecls } }
private abbrev RFlag := {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.true}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.RFlag
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.RFlag target :: scope.openDecls } }
private abbrev CS := (smoothConnectedSum (N (endpoint s _root_.Bool.false)) (N (endpoint s _root_.Bool.true))
  (chart s _root_.Bool.false) (chart s _root_.Bool.true) a).toConnectedClosedOrientedManifold

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.CS
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.CS target :: scope.openDecls } }
private abbrev Rest := {v // v ≠ endpoint s _root_.Bool.false ∧ v ≠ endpoint s _root_.Bool.true}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.Rest
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.Rest target :: scope.openDecls } }

variable (b : LFlag endpoint s ⊕ RFlag endpoint s → OrientedBallChart (CS N endpoint chart s a).toClosedOrientedManifold)
  (C : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉
      ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1})
  (D : SmoothBoundaryAtlas (𝓡 3) 3 (⋃ p, (b p).chart '' ball (0 : E3) 1)ᶜ)
  (C' : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (mergeFactor N endpoint chart s a v).Carrier |
      (⟨v, x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier) ∉
        ⋃ p, flagMap (mergeFactor N endpoint chart s a)
          (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
          (fun e t => (mergeFlag N endpoint chart s a b e t).snd) p '' ball (0 : E3) 1})
  (H : Quot (seamRel N endpoint chart hdisj s a) ≃ₜ
    (Σ v, PuncturedFactor (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v))

variable
  (hL : ∀ x : PuncturedFactor N endpoint chart (endpoint s false),
    ∃ y, mergePuncturedFactorHomeomorph N endpoint chart s a b hends
        (H (Quot.mk _ ⟨endpoint s false, x⟩)) = Sum.inl y ∧
      y.val = ConnectedSumQuotient.inl (chart s false).toBallChart (chart s true).toBallChart
        a.1.toHomeomorph (selectedPuncturedFactorHomeomorph N endpoint chart s false hends x).val)
  (hR : ∀ x : PuncturedFactor N endpoint chart (endpoint s true),
    ∃ y, mergePuncturedFactorHomeomorph N endpoint chart s a b hends
        (H (Quot.mk _ ⟨endpoint s true, x⟩)) = Sum.inl y ∧
      y.val = ConnectedSumQuotient.inr (chart s false).toBallChart (chart s true).toBallChart
        a.1.toHomeomorph (selectedPuncturedFactorHomeomorph N endpoint chart s true hends x).val)
  (hu : ∀ (v : Rest endpoint s) (x : PuncturedFactor N endpoint chart v.val),
    mergePuncturedFactorHomeomorph N endpoint chart s a b hends
      (H (Quot.mk _ ⟨v.val, x⟩)) = Sum.inr ⟨v, x⟩)

include hdisj hends hL hR hu D in
theorem exists_smooth_distinct_merge_of_representatives
    (hbL : ∀ p x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
      ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.false) p).chart x ∉
          (chart s _root_.Bool.false).chart '' _root_.Metric.ball (0 : E3) 1,
        (b (Sum.inl p)).chart x = ConnectedSumQuotient.inl (chart s _root_.Bool.false).toBallChart
          (chart s _root_.Bool.true).toBallChart a.1.toHomeomorph
          ⟨(remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.false) p).chart x, hx⟩)
    (hbR : ∀ p x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
      ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.true) p).chart x ∉
          (chart s _root_.Bool.true).chart '' _root_.Metric.ball (0 : E3) 1,
        (b (Sum.inr p)).chart x = ConnectedSumQuotient.inr (chart s _root_.Bool.false).toBallChart
          (chart s _root_.Bool.true).toBallChart a.1.toHomeomorph
          ⟨(remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.true) p).chart x, hx⟩) :
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) :=
      fun v => (C v).toChartedSpace
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
      (PuncturedFactor (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v) := fun v => (C' v).toChartedSpace
    ∃ Qcharts : ChartedSpace (EuclideanHalfSpace 3) (Quot (seamRel N endpoint chart hdisj s a)),
      let _ := Qcharts
      IsManifold (𝓡∂ 3) ∞ (Quot (seamRel N endpoint chart hdisj s a)) ∧
        IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ (seamCoreInclusion N endpoint chart hdisj s a) ∧
        IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (seamChart N endpoint chart hdisj s a) ∧
        ∃ diff : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) (Quot (seamRel N endpoint chart hdisj s a))
          (Σ v, PuncturedFactor (mergeFactor N endpoint chart s a)
            (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
            (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v) ∞,
          ∀ x, diff x = H x := by
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) :=
    fun v => (C v).toChartedSpace
  let _ : ∀ v, IsManifold (𝓡∂ 3) ∞ (PuncturedFactor N endpoint chart v) := fun v => (C v).isManifold
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
    (PuncturedFactor (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v) := fun v => (C' v).toChartedSpace
  let _ : ∀ v, IsManifold (𝓡∂ 3) ∞
    (PuncturedFactor (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v) := fun v => (C' v).isManifold
  let _ : ChartedSpace (EuclideanHalfSpace 3)
      {q : (mergeFactor N endpoint chart s a _root_.Option.none).Carrier //
        q ∉ ⋃ p, (b p).chart '' _root_.Metric.ball (0 : E3) 1} := D.toChartedSpace
  let _ := D.isManifold
  let _ : ChartedSpace (EuclideanHalfSpace 3)
      ↥((⋃ p, (b p).chart '' _root_.Metric.ball (0 : E3) 1)ᶜ) := D.toChartedSpace
  let _ : ChartedSpace (EuclideanHalfSpace 3)
      (Σ v : Rest endpoint s, PuncturedFactor N endpoint chart v.val) :=
    sigmaChartedSpace (M := fun v : Rest endpoint s => PuncturedFactor N endpoint chart v.val)
  dsimp only
  let split : (Σ v, PuncturedFactor (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v) ≃ₜ
      (↥((⋃ p, (b p).chart '' _root_.Metric.ball (0 : E3) 1)ᶜ) ⊕
        (Σ v : Rest endpoint s, PuncturedFactor N endpoint chart v.val)) :=
    mergePuncturedFactorHomeomorph N endpoint chart s a b hends
  have hsplit : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ split :=
    mergePuncturedFactorHomeomorph_isLocalDiffeomorph N endpoint chart s a hends b C D C'
  have hcore := isLocalDiffeomorph_core_comp_of_factor_representatives N endpoint chart hdisj s a hends
    b C D (split ∘ H) hL hR hu hbL hbR
  have hseam := isLocalDiffeomorph_seam_comp_of_factor_representatives N endpoint chart hdisj s a hends
    b D (split ∘ H) hL hR hbL hbR
  have hcore' : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (H ∘ seamCoreInclusion N endpoint chart hdisj s a) := by
    intro x
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp_right
      (split.isInducing.continuousAt_iff.mpr (hcore x).contMDiffAt.continuousAt)
      (hsplit _) (hcore x)
  have hseam' : IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (H ∘ seamChart N endpoint chart hdisj s a) := by
    intro x
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp_right
      (split.isInducing.continuousAt_iff.mpr (hseam x).contMDiffAt.continuousAt)
      (hsplit _) (hseam x)
  exact exists_smooth_seam_atlas_of_comp_local_maps N endpoint chart hdisj s a H hcore' hseam'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_distinct_merge_of_representatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_distinct_merge_of_representatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_distinct_merge_of_representatives ``Submission.DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_distinct_merge_of_representatives

end DifferentialGeometry.Topology.PairedBallGluing

end

end

section

noncomputable section

open _root_.Set _root_.Metric _root_.Submission.Metric _root_.Function _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w

variable {V : Type v} {E : Type w} [Finite E]
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (s : E) (a : BoundaryAttachment) (hends : endpoint s false ≠ endpoint s true)


variable (b : LFlag endpoint s ⊕ RFlag endpoint s → OrientedBallChart (CS N endpoint chart s a).toClosedOrientedManifold)
  (C : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉
      ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1})
  (C' : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (mergeFactor N endpoint chart s a v).Carrier |
      (⟨v, x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier) ∉
        ⋃ p, flagMap (mergeFactor N endpoint chart s a)
          (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
          (fun e t => (mergeFlag N endpoint chart s a b e t).snd) p '' ball (0 : E3) 1})
  (H : Quot (seamRel N endpoint chart hdisj s a) ≃ₜ
    (Σ v, PuncturedFactor (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v))

variable
  (hL : ∀ x : PuncturedFactor N endpoint chart (endpoint s false),
    ∃ y, mergePuncturedFactorHomeomorph N endpoint chart s a b hends
        (H (Quot.mk _ ⟨endpoint s false, x⟩)) = Sum.inl y ∧
      y.val = ConnectedSumQuotient.inl (chart s false).toBallChart (chart s true).toBallChart
        a.1.toHomeomorph (selectedPuncturedFactorHomeomorph N endpoint chart s false hends x).val)
  (hR : ∀ x : PuncturedFactor N endpoint chart (endpoint s true),
    ∃ y, mergePuncturedFactorHomeomorph N endpoint chart s a b hends
        (H (Quot.mk _ ⟨endpoint s true, x⟩)) = Sum.inl y ∧
      y.val = ConnectedSumQuotient.inr (chart s false).toBallChart (chart s true).toBallChart
        a.1.toHomeomorph (selectedPuncturedFactorHomeomorph N endpoint chart s true hends x).val)
  (hu : ∀ (v : Rest endpoint s) (x : PuncturedFactor N endpoint chart v.val),
    mergePuncturedFactorHomeomorph N endpoint chart s a b hends
      (H (Quot.mk _ ⟨v.val, x⟩)) = Sum.inr ⟨v, x⟩)

include hdisj hends hL hR hu in
theorem exists_smooth_distinct_merge_of_factor_representatives
    (hb : Pairwise fun p q => Disjoint ((b p).chart '' _root_.Metric.closedBall (0 : E3) 2)
      ((b q).chart '' _root_.Metric.closedBall (0 : E3) 2))
    (hbL : ∀ p x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
      ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.false) p).chart x ∉
          (chart s _root_.Bool.false).chart '' _root_.Metric.ball (0 : E3) 1,
        (b (Sum.inl p)).chart x = ConnectedSumQuotient.inl (chart s _root_.Bool.false).toBallChart
          (chart s _root_.Bool.true).toBallChart a.1.toHomeomorph
          ⟨(remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.false) p).chart x, hx⟩)
    (hbR : ∀ p x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
      ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.true) p).chart x ∉
          (chart s _root_.Bool.true).chart '' _root_.Metric.ball (0 : E3) 1,
        (b (Sum.inr p)).chart x = ConnectedSumQuotient.inr (chart s _root_.Bool.false).toBallChart
          (chart s _root_.Bool.true).toBallChart a.1.toHomeomorph
          ⟨(remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.true) p).chart x, hx⟩) :
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) :=
      fun v => (C v).toChartedSpace
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
      (PuncturedFactor (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v) := fun v => (C' v).toChartedSpace
    ∃ Qcharts : ChartedSpace (EuclideanHalfSpace 3) (Quot (seamRel N endpoint chart hdisj s a)),
      let _ := Qcharts
      IsManifold (𝓡∂ 3) ∞ (Quot (seamRel N endpoint chart hdisj s a)) ∧
        IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ (seamCoreInclusion N endpoint chart hdisj s a) ∧
        IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (seamChart N endpoint chart hdisj s a) ∧
        ∃ diff : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) (Quot (seamRel N endpoint chart hdisj s a))
          (Σ v, PuncturedFactor (mergeFactor N endpoint chart s a)
            (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
            (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v) ∞,
          ∀ x, diff x = H x := by
  obtain ⟨D, _⟩ := BallChart.exists_smoothBoundaryAtlas_ball_complement
    (fun p => (b p).toBallChart) hb
  exact exists_smooth_distinct_merge_of_representatives N endpoint chart hdisj s a hends
    b C D C' H hL hR hu hbL hbR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_distinct_merge_of_factor_representatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_distinct_merge_of_factor_representatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_distinct_merge_of_factor_representatives ``Submission.DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_distinct_merge_of_factor_representatives

end DifferentialGeometry.Topology.PairedBallGluing

end

end

section

noncomputable section

open _root_.Set _root_.Metric _root_.Submission.Metric _root_.Function _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w

variable {V : Type v} {E : Type w} [Finite E]
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (s : E) (a : BoundaryAttachment) (hends : endpoint s false ≠ endpoint s true)


variable (b : LFlag endpoint s ⊕ RFlag endpoint s → OrientedBallChart (CS N endpoint chart s a).toClosedOrientedManifold)
  (H : Quot (seamRel N endpoint chart hdisj s a) ≃ₜ
    (Σ v, PuncturedFactor (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v))

variable
  (hL : ∀ x : PuncturedFactor N endpoint chart (endpoint s false),
    ∃ y, mergePuncturedFactorHomeomorph N endpoint chart s a b hends
        (H (Quot.mk _ ⟨endpoint s false, x⟩)) = Sum.inl y ∧
      y.val = ConnectedSumQuotient.inl (chart s false).toBallChart (chart s true).toBallChart
        a.1.toHomeomorph (selectedPuncturedFactorHomeomorph N endpoint chart s false hends x).val)
  (hR : ∀ x : PuncturedFactor N endpoint chart (endpoint s true),
    ∃ y, mergePuncturedFactorHomeomorph N endpoint chart s a b hends
        (H (Quot.mk _ ⟨endpoint s true, x⟩)) = Sum.inl y ∧
      y.val = ConnectedSumQuotient.inr (chart s false).toBallChart (chart s true).toBallChart
        a.1.toHomeomorph (selectedPuncturedFactorHomeomorph N endpoint chart s true hends x).val)
  (hu : ∀ (v : Rest endpoint s) (x : PuncturedFactor N endpoint chart v.val),
    mergePuncturedFactorHomeomorph N endpoint chart s a b hends
      (H (Quot.mk _ ⟨v.val, x⟩)) = Sum.inr ⟨v, x⟩)

include hdisj hends hL hR hu in
theorem exists_smooth_distinct_merge_atlas
    (hb : Pairwise fun p q => Disjoint ((b p).chart '' _root_.Metric.closedBall (0 : E3) 2)
      ((b q).chart '' _root_.Metric.closedBall (0 : E3) 2))
    (hbL : ∀ p x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
      ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.false) p).chart x ∉
          (chart s _root_.Bool.false).chart '' _root_.Metric.ball (0 : E3) 1,
        (b (Sum.inl p)).chart x = ConnectedSumQuotient.inl (chart s _root_.Bool.false).toBallChart
          (chart s _root_.Bool.true).toBallChart a.1.toHomeomorph
          ⟨(remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.false) p).chart x, hx⟩)
    (hbR : ∀ p x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
      ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.true) p).chart x ∉
          (chart s _root_.Bool.true).chart '' _root_.Metric.ball (0 : E3) 1,
        (b (Sum.inr p)).chart x = ConnectedSumQuotient.inr (chart s _root_.Bool.false).toBallChart
          (chart s _root_.Bool.true).toBallChart a.1.toHomeomorph
          ⟨(remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.true) p).chart x, hx⟩) :
    ∃ C : (v : V) → SmoothBoundaryAtlas (𝓡 3) 3
        {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉
          ⋃ p, flagMap N endpoint chart p '' _root_.Metric.ball (0 : E3) 1},
      ∃ C' : (v : Option (Rest endpoint s)) → SmoothBoundaryAtlas (𝓡 3) 3
        {x : (mergeFactor N endpoint chart s a v).Carrier |
          (⟨v, x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier) ∉
            ⋃ p, flagMap (mergeFactor N endpoint chart s a)
              (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
              (fun e t => (mergeFlag N endpoint chart s a b e t).snd) p '' _root_.Metric.ball (0 : E3) 1},
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) :=
      fun v => (C v).toChartedSpace
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
      (PuncturedFactor (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v) := fun v => (C' v).toChartedSpace
    ∃ Qcharts : ChartedSpace (EuclideanHalfSpace 3) (Quot (seamRel N endpoint chart hdisj s a)),
      let _ := Qcharts
      IsManifold (𝓡∂ 3) ∞ (Quot (seamRel N endpoint chart hdisj s a)) ∧
        IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ (seamCoreInclusion N endpoint chart hdisj s a) ∧
        IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (seamChart N endpoint chart hdisj s a) ∧
        ∃ diff : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) (Quot (seamRel N endpoint chart hdisj s a))
          (Σ v, PuncturedFactor (mergeFactor N endpoint chart s a)
            (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
            (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v) ∞,
          ∀ x, diff x = H x := by
  classical
  choose C _ using fun v => exists_smoothBoundaryAtlas_puncturedFactor N endpoint chart hdisj v
  have hb' := pairwise_disjoint_mergeFlag_image N endpoint chart s a b hdisj hb
  choose C' _ using fun v => exists_smoothBoundaryAtlas_puncturedFactor
    (mergeFactor N endpoint chart s a)
    (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
    (fun e t => (mergeFlag N endpoint chart s a b e t).snd) hb' v
  refine ⟨C,C',?_⟩
  exact exists_smooth_distinct_merge_of_factor_representatives N endpoint chart hdisj s a hends
    b C C' H hL hR hu hb hbL hbR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_distinct_merge_atlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_distinct_merge_atlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_distinct_merge_atlas ``Submission.DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_distinct_merge_atlas

end DifferentialGeometry.Topology.PairedBallGluing

end

end

section

noncomputable section
open _root_.Set _root_.Metric _root_.Submission.Metric
namespace DifferentialGeometry.Topology.PairedBallGluing
universe u v w
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (t : Bool) → OrientedBallChart (N (endpoint e t)).toClosedOrientedManifold)
  (s : E) (a : BoundaryAttachment) (hends : endpoint s false ≠ endpoint s true)
  (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} ⊕
    {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s true}) →
    OrientedBallChart (mergeFactor N endpoint chart s a none).toClosedOrientedManifold)
include hends in
theorem pairwise_disjoint_survivorChart_of_mergeFlag
    (hb : Pairwise fun p q =>
      Disjoint (flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) q '' _root_.Metric.closedBall (0 : E3) 2)) :
    Pairwise fun p q => Disjoint ((b p).chart '' _root_.Metric.closedBall (0 : E3) 2)
      ((b q).chart '' _root_.Metric.closedBall (0 : E3) 2) := by
  let f : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.true}) → {e // e ≠ s} × Bool :=
    Sum.elim (fun p => (⟨p.val.1,p.property.1⟩,p.val.2))
      (fun p => (⟨p.val.1,p.property.1⟩,p.val.2))
  have hfinj : Function.Injective f := by
    intro p q hpq
    have hbase : Sum.elim (fun p => p.val) (fun p => p.val) p =
        Sum.elim (fun p => p.val) (fun p => p.val) q := by
      have h := congrArg (fun z : {e // e ≠ s} × Bool => (z.1.val,z.2)) hpq
      cases p <;> cases q <;> exact h
    cases p with
    | inl p => cases q with
      | inl q => exact congrArg Sum.inl (Subtype.ext hbase)
      | inr q => exact False.elim (hends (p.property.2.symm.trans
          ((congrArg (fun z : E × Bool => endpoint z.1 z.2) hbase).trans q.property.2)))
    | inr p => cases q with
      | inl q => exact False.elim (hends (q.property.2.symm.trans
          ((congrArg (fun z : E × Bool => endpoint z.1 z.2) hbase.symm).trans p.property.2)))
      | inr q => exact congrArg Sum.inr (Subtype.ext hbase)
  have heq (p) (x : E3) :
      flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) (f p) x = ⟨none,(b p).chart x⟩ := by
    cases p with
    | inl p =>
      exact mergeFlag_flagMap_left N endpoint chart s a b
        ⟨p.val.1,p.property.1⟩ p.val.2 p.property.2 x
    | inr p =>
      exact mergeFlag_flagMap_right N endpoint chart s a b
        ⟨p.val.1,p.property.1⟩ p.val.2 (fun h => hends (h.symm.trans p.property.2)) p.property.2 x
  intro p q hpq
  rw [_root_.Set.disjoint_left]
  rintro x ⟨y,hy,hyx⟩ ⟨z,hz,hzx⟩
  apply disjoint_left.mp (hb (show f p ≠ f q from fun h => hpq (hfinj h)))
    (⟨y,hy,rfl⟩ : flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) (f p) y ∈
      flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) (f p) '' _root_.Metric.closedBall (0 : E3) 2)
  refine ⟨z,hz,?_⟩
  rw [heq,heq,hyx,hzx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.pairwise_disjoint_survivorChart_of_mergeFlag then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.pairwise_disjoint_survivorChart_of_mergeFlag"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.pairwise_disjoint_survivorChart_of_mergeFlag ``Submission.DifferentialGeometry.Topology.PairedBallGluing.pairwise_disjoint_survivorChart_of_mergeFlag
end DifferentialGeometry.Topology.PairedBallGluing

end

end

section

noncomputable section

open _root_.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
variable {V : Type v} {E : Type w} [Finite E]
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (s : E) (a : BoundaryAttachment)
private abbrev RemainingVertex := {v // v ≠ endpoint s _root_.Bool.false ∧ v ≠ endpoint s _root_.Bool.true}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.RemainingVertex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.RemainingVertex target :: scope.openDecls } }

theorem exists_smooth_merge_homeomorph
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2))
    (hends : endpoint s _root_.Bool.false ≠ endpoint s _root_.Bool.true) :
    ∃ b : LFlag endpoint s ⊕ RFlag endpoint s →
      OrientedBallChart (mergeFactor N endpoint chart s a _root_.Option.none).toClosedOrientedManifold,
      (∀ p x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
        ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.false) p).chart x ∉
            (chart s _root_.Bool.false).chart '' _root_.Metric.ball (0 : E3) 1,
          (b (Sum.inl p)).chart x = ConnectedSumQuotient.inl
            (chart s _root_.Bool.false).toBallChart (chart s _root_.Bool.true).toBallChart a.1.toHomeomorph
            ⟨(remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.false) p).chart x, hx⟩) ∧
      (∀ p x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
        ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.true) p).chart x ∉
            (chart s _root_.Bool.true).chart '' _root_.Metric.ball (0 : E3) 1,
          (b (Sum.inr p)).chart x = ConnectedSumQuotient.inr
            (chart s _root_.Bool.false).toBallChart (chart s _root_.Bool.true).toBallChart a.1.toHomeomorph
            ⟨(remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.true) p).chart x, hx⟩) ∧
      ∃ hb : Pairwise fun p q =>
        Disjoint (flagMap (mergeFactor N endpoint chart s a)
          (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
          (fun e t => (mergeFlag N endpoint chart s a b e t).snd) p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap (mergeFactor N endpoint chart s a)
          (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
          (fun e t => (mergeFlag N endpoint chart s a b e t).snd) q '' _root_.Metric.closedBall (0 : E3) 2),
        ∃ H : Quot (seamRel N endpoint chart hdisj s a) ≃ₜ
          (Σ v, PuncturedFactor (mergeFactor N endpoint chart s a)
            (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
            (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v),
          (∀ x : PuncturedFactor N endpoint chart (endpoint s _root_.Bool.false),
            ∃ y, mergePuncturedFactorHomeomorph N endpoint chart s a b hends
                (H (Quot.mk _ ⟨endpoint s _root_.Bool.false, x⟩)) = Sum.inl y ∧
              y.val = ConnectedSumQuotient.inl (chart s _root_.Bool.false).toBallChart
                (chart s _root_.Bool.true).toBallChart a.1.toHomeomorph
                (selectedPuncturedFactorHomeomorph N endpoint chart s _root_.Bool.false hends x).val) ∧
          (∀ x : PuncturedFactor N endpoint chart (endpoint s _root_.Bool.true),
            ∃ y, mergePuncturedFactorHomeomorph N endpoint chart s a b hends
                (H (Quot.mk _ ⟨endpoint s _root_.Bool.true, x⟩)) = Sum.inl y ∧
              y.val = ConnectedSumQuotient.inr (chart s _root_.Bool.false).toBallChart
                (chart s _root_.Bool.true).toBallChart a.1.toHomeomorph
                (selectedPuncturedFactorHomeomorph N endpoint chart s _root_.Bool.true hends x).val) ∧
          (∀ (v : {v // v ≠ endpoint s _root_.Bool.false ∧ v ≠ endpoint s _root_.Bool.true})
            (x : PuncturedFactor N endpoint chart v.val),
            mergePuncturedFactorHomeomorph N endpoint chart s a b hends
              (H (Quot.mk _ ⟨v.val, x⟩)) = Sum.inr ⟨v, x⟩) ∧
          (∀ (e : {e // e ≠ s}) (t : Bool) (z : _root_.Metric.sphere (0 : E3) 1),
            H (Quot.mk _ ⟨endpoint e.val t, boundaryPoint N endpoint chart hdisj e.val t z⟩) =
              ⟨(mergeFlag N endpoint chart s a b e t).fst,
                boundaryPoint (mergeFactor N endpoint chart s a)
                  (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
                  (fun e t => (mergeFlag N endpoint chart s a b e t).snd) hb e t z⟩) ∧
    ∃ C : (v : V) → SmoothBoundaryAtlas (𝓡 3) 3
        {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉
          ⋃ p, flagMap N endpoint chart p '' _root_.Metric.ball (0 : E3) 1},
      ∃ C' : (v : Option (RemainingVertex endpoint s)) → SmoothBoundaryAtlas (𝓡 3) 3
        {x : (mergeFactor N endpoint chart s a v).Carrier |
          (⟨v, x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier) ∉
            ⋃ p, flagMap (mergeFactor N endpoint chart s a)
              (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
              (fun e t => (mergeFlag N endpoint chart s a b e t).snd) p '' _root_.Metric.ball (0 : E3) 1},
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) :=
      fun v => (C v).toChartedSpace
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
      (PuncturedFactor (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v) := fun v => (C' v).toChartedSpace
    ∃ Qcharts : ChartedSpace (EuclideanHalfSpace 3) (Quot (seamRel N endpoint chart hdisj s a)),
      let _ := Qcharts
      IsManifold (𝓡∂ 3) ∞ (Quot (seamRel N endpoint chart hdisj s a)) ∧
        IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ (seamCoreInclusion N endpoint chart hdisj s a) ∧
        IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (seamChart N endpoint chart hdisj s a) ∧
        ∃ diff : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) (Quot (seamRel N endpoint chart hdisj s a))
          (Σ v, PuncturedFactor (mergeFactor N endpoint chart s a)
            (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
            (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v) ∞,
          ∀ x, diff x = H x := by
  obtain ⟨b,hbL,hbR,hb,H,hL,hR,hu,hboundary⟩ := exists_merge_homeomorph N endpoint chart s a hdisj hends
  refine ⟨b,hbL,hbR,hb,H,hL,hR,hu,hboundary,?_⟩
  have hbd := pairwise_disjoint_survivorChart_of_mergeFlag N endpoint chart s a hends b hb
  exact exists_smooth_distinct_merge_atlas N endpoint chart hdisj s a hends b H hL hR hu hbd hbL hbR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_merge_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_merge_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_merge_homeomorph ``Submission.DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_merge_homeomorph

end DifferentialGeometry.Topology.PairedBallGluing

end

end
