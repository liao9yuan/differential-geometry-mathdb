import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallSeam
import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallMerge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.E3 target :: scope.openDecls } }
private abbrev S2 := _root_.Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.S2 target :: scope.openDecls } }

variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (s : E) (a : BoundaryAttachment) (hends : endpoint s false ≠ endpoint s true)

private theorem radialPoint_cast_sigma (i j : V) (h : i = j)
    (x : PuncturedFactor N endpoint chart i) :
    (Sigma.mk j (h ▸ x) : Σ v, PuncturedFactor N endpoint chart v) = Sigma.mk i x := by
  cases h
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.radialPoint_cast_sigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.radialPoint_cast_sigma target :: scope.openDecls } }

theorem left_radial_representative_of_factor_representatives
    (p : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false})
    (B : OrientedBallChart
      (smoothConnectedSum (N (endpoint s _root_.Bool.false)) (N (endpoint s _root_.Bool.true))
        (chart s _root_.Bool.false) (chart s _root_.Bool.true) a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
    (hB : ∀ v ∈ _root_.Metric.closedBall (0 : E3) 2,
      ∃ hv : (remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.false) p).chart v ∉
          (chart s _root_.Bool.false).chart '' _root_.Metric.ball (0 : E3) 1,
        B.chart v = ConnectedSumQuotient.inl (chart s _root_.Bool.false).toBallChart (chart s _root_.Bool.true).toBallChart
          a.1.toHomeomorph ⟨(remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.false) p).chart v, hv⟩)
    {Z : Type*} {K : Set
      (smoothConnectedSum (N (endpoint s _root_.Bool.false)) (N (endpoint s _root_.Bool.true))
        (chart s _root_.Bool.false) (chart s _root_.Bool.true) a).toConnectedClosedOrientedManifold.Carrier}
    (H : Quot (seamRel N endpoint chart hdisj s a) → K ⊕ Z)
    (hH : ∀ x : PuncturedFactor N endpoint chart (endpoint s _root_.Bool.false),
      ∃ y, H (Quot.mk _ ⟨endpoint s _root_.Bool.false,x⟩) = Sum.inl y ∧
        y.val = ConnectedSumQuotient.inl (chart s _root_.Bool.false).toBallChart (chart s _root_.Bool.true).toBallChart
          a.1.toHomeomorph (selectedPuncturedFactorHomeomorph N endpoint chart s _root_.Bool.false hends x).val)
    (q : S2 × _root_.Set.Icc (1 : ℝ) 2) :
    ∃ y, H (Quot.mk _ ⟨endpoint p.val.1 p.val.2,
      radialPoint N endpoint chart hdisj p.val.1 p.val.2 q.1 q.2.val q.2.property⟩) = Sum.inl y ∧
        y.val = B.chart ((q.2 : ℝ) • (q.1 : E3)) := by
  let x : PuncturedFactor N endpoint chart (endpoint s _root_.Bool.false) :=
    p.property.2 ▸ radialPoint N endpoint chart hdisj p.val.1 p.val.2 q.1 q.2.val q.2.property
  obtain ⟨y,hy,hyval⟩ := hH x
  refine ⟨y,?_,?_⟩
  · exact (congrArg (fun v => H (Quot.mk _ v))
      (radialPoint_cast_sigma N endpoint chart _ _ p.property.2
        (radialPoint N endpoint chart hdisj p.val.1 p.val.2 q.1 q.2.val q.2.property))).symm.trans hy
  · have hq : (q.2 : ℝ) • (q.1 : E3) ∈ _root_.Metric.closedBall (0 : E3) 2 := by
      rw [_root_.Metric.mem_closedBall,dist_zero_right,
        BallChart.norm_radial q.1 (le_trans (by norm_num) q.2.property.1)]
      exact q.2.property.2
    obtain ⟨hv,hvB⟩ := hB _ hq
    rw [hyval,hvB]
    congr 1
    apply Subtype.ext
    change x.val = (remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.false) p).chart
      ((q.2 : ℝ) • (q.1 : E3))
    have hxSigma := congrArg (fun y : Σ v, PuncturedFactor N endpoint chart v =>
      (⟨y.fst,y.snd.val⟩ : Σ v, (N v).Carrier))
      (radialPoint_cast_sigma N endpoint chart _ _ p.property.2
        (radialPoint N endpoint chart hdisj p.val.1 p.val.2 q.1 q.2.val q.2.property))
    exact eq_of_heq (Sigma.mk.inj (hxSigma.trans
      (remainingIncidenceChart_sigma_apply N endpoint chart s
        (endpoint s _root_.Bool.false) p ((q.2 : ℝ) • (q.1 : E3))).symm)).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.left_radial_representative_of_factor_representatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.left_radial_representative_of_factor_representatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.left_radial_representative_of_factor_representatives ``Submission.DifferentialGeometry.Topology.PairedBallGluing.left_radial_representative_of_factor_representatives

theorem right_radial_representative_of_factor_representatives
    (p : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.true})
    (B : OrientedBallChart
      (smoothConnectedSum (N (endpoint s _root_.Bool.false)) (N (endpoint s _root_.Bool.true))
        (chart s _root_.Bool.false) (chart s _root_.Bool.true) a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
    (hB : ∀ v ∈ _root_.Metric.closedBall (0 : E3) 2,
      ∃ hv : (remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.true) p).chart v ∉
          (chart s _root_.Bool.true).chart '' _root_.Metric.ball (0 : E3) 1,
        B.chart v = ConnectedSumQuotient.inr (chart s _root_.Bool.false).toBallChart (chart s _root_.Bool.true).toBallChart
          a.1.toHomeomorph ⟨(remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.true) p).chart v, hv⟩)
    {Z : Type*} {K : Set
      (smoothConnectedSum (N (endpoint s _root_.Bool.false)) (N (endpoint s _root_.Bool.true))
        (chart s _root_.Bool.false) (chart s _root_.Bool.true) a).toConnectedClosedOrientedManifold.Carrier}
    (H : Quot (seamRel N endpoint chart hdisj s a) → K ⊕ Z)
    (hH : ∀ x : PuncturedFactor N endpoint chart (endpoint s _root_.Bool.true),
      ∃ y, H (Quot.mk _ ⟨endpoint s _root_.Bool.true,x⟩) = Sum.inl y ∧
        y.val = ConnectedSumQuotient.inr (chart s _root_.Bool.false).toBallChart (chart s _root_.Bool.true).toBallChart
          a.1.toHomeomorph (selectedPuncturedFactorHomeomorph N endpoint chart s _root_.Bool.true hends x).val)
    (q : S2 × _root_.Set.Icc (1 : ℝ) 2) :
    ∃ y, H (Quot.mk _ ⟨endpoint p.val.1 p.val.2,
      radialPoint N endpoint chart hdisj p.val.1 p.val.2 q.1 q.2.val q.2.property⟩) = Sum.inl y ∧
        y.val = B.chart ((q.2 : ℝ) • (q.1 : E3)) := by
  let x : PuncturedFactor N endpoint chart (endpoint s _root_.Bool.true) :=
    p.property.2 ▸ radialPoint N endpoint chart hdisj p.val.1 p.val.2 q.1 q.2.val q.2.property
  obtain ⟨y,hy,hyval⟩ := hH x
  refine ⟨y,?_,?_⟩
  · exact (congrArg (fun v => H (Quot.mk _ v))
      (radialPoint_cast_sigma N endpoint chart _ _ p.property.2
        (radialPoint N endpoint chart hdisj p.val.1 p.val.2 q.1 q.2.val q.2.property))).symm.trans hy
  · have hq : (q.2 : ℝ) • (q.1 : E3) ∈ _root_.Metric.closedBall (0 : E3) 2 := by
      rw [_root_.Metric.mem_closedBall,dist_zero_right,
        BallChart.norm_radial q.1 (le_trans (by norm_num) q.2.property.1)]
      exact q.2.property.2
    obtain ⟨hv,hvB⟩ := hB _ hq
    rw [hyval,hvB]
    congr 1
    apply Subtype.ext
    change x.val = (remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.true) p).chart
      ((q.2 : ℝ) • (q.1 : E3))
    have hxSigma := congrArg (fun y : Σ v, PuncturedFactor N endpoint chart v =>
      (⟨y.fst,y.snd.val⟩ : Σ v, (N v).Carrier))
      (radialPoint_cast_sigma N endpoint chart _ _ p.property.2
        (radialPoint N endpoint chart hdisj p.val.1 p.val.2 q.1 q.2.val q.2.property))
    exact eq_of_heq (Sigma.mk.inj (hxSigma.trans
      (remainingIncidenceChart_sigma_apply N endpoint chart s
        (endpoint s _root_.Bool.true) p ((q.2 : ℝ) • (q.1 : E3))).symm)).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.right_radial_representative_of_factor_representatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.right_radial_representative_of_factor_representatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.right_radial_representative_of_factor_representatives ``Submission.DifferentialGeometry.Topology.PairedBallGluing.right_radial_representative_of_factor_representatives

end DifferentialGeometry.Topology.PairedBallGluing

end

end

section

noncomputable section
open _root_.Set _root_.Metric _root_.Submission.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
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
private abbrev Y (v) := PuncturedFactor (mergeFactor N endpoint chart s a)
  (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
  (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.Y
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.Y target :: scope.openDecls } }

theorem mergePuncturedFactorHomeomorph_eq_inl_iff
    (x : Σ v, Y N endpoint chart s a b v)
    (y : {q : (mergeFactor N endpoint chart s a _root_.Option.none).Carrier //
      q ∉ ⋃ p, (b p).chart '' _root_.Metric.ball (0 : E3) 1}) :
    mergePuncturedFactorHomeomorph N endpoint chart s a b hends x = Sum.inl y ↔
      ∃ z : Y N endpoint chart s a b _root_.Option.none, x = ⟨none,z⟩ ∧ z.val = y.val := by
  constructor
  · intro h
    have hz : (⟨none,y.val⟩ : Σ v,(mergeFactor N endpoint chart s a v).Carrier) ∉
        ⋃ p,flagMap (mergeFactor N endpoint chart s a)
          (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
          (fun e t => (mergeFlag N endpoint chart s a b e t).snd) p '' _root_.Metric.ball (0 : E3) 1 := by
      exact fun h => y.property ((Set.ext_iff.mp
        (mergeFlag_holes_none N endpoint chart s a b hends (_root_.Metric.ball (0 : E3) 1)) y.val).mp h)
    let z : Y N endpoint chart s a b none := ⟨y.val,hz⟩
    refine ⟨z,?_,rfl⟩
    apply (mergePuncturedFactorHomeomorph N endpoint chart s a b hends).injective
    exact h
  · rintro ⟨z,rfl,hzy⟩
    have hz : z.val ∉ ⋃ p,(b p).chart '' _root_.Metric.ball (0 : E3) 1 := by
      exact fun h => z.property ((Set.ext_iff.mp
        (mergeFlag_holes_none N endpoint chart s a b hends (_root_.Metric.ball (0 : E3) 1)) z.val).mpr h)
    exact (mergePuncturedFactorHomeomorph_none N endpoint chart s a b hends z hz).trans
      (congrArg Sum.inl (Subtype.ext hzy))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph_eq_inl_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph_eq_inl_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph_eq_inl_iff ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph_eq_inl_iff

theorem mergePuncturedFactorHomeomorph_eq_inr_iff
    (v : {v // v ≠ endpoint s _root_.Bool.false ∧ v ≠ endpoint s _root_.Bool.true})
    (x : Σ v, Y N endpoint chart s a b v) (y : PuncturedFactor N endpoint chart v.val) :
    mergePuncturedFactorHomeomorph N endpoint chart s a b hends x = Sum.inr ⟨v,y⟩ ↔
      ∃ z : Y N endpoint chart s a b (_root_.Option.some v), x = ⟨some v,z⟩ ∧ z.val = y.val := by
  constructor
  · intro h
    have hz : (⟨some v,y.val⟩ : Σ v,(mergeFactor N endpoint chart s a v).Carrier) ∉
        ⋃ p,flagMap (mergeFactor N endpoint chart s a)
          (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
          (fun e t => (mergeFlag N endpoint chart s a b e t).snd) p '' _root_.Metric.ball (0 : E3) 1 := by
      exact fun h => y.property ((Set.ext_iff.mp
        (mergeFlag_holes_some N endpoint chart s a b v (_root_.Metric.ball (0 : E3) 1)) y.val).mp h)
    let z : Y N endpoint chart s a b (_root_.Option.some v) := ⟨y.val,hz⟩
    refine ⟨z,?_,rfl⟩
    apply (mergePuncturedFactorHomeomorph N endpoint chart s a b hends).injective
    exact h
  · rintro ⟨z,rfl,hzy⟩
    have hz : (⟨v.val,z.val⟩ : Σ v,(N v).Carrier) ∉
        ⋃ p,flagMap N endpoint chart p '' _root_.Metric.ball (0 : E3) 1 := by
      exact fun h => z.property ((Set.ext_iff.mp
        (mergeFlag_holes_some N endpoint chart s a b v (_root_.Metric.ball (0 : E3) 1)) z.val).mpr h)
    have hy : (⟨z.val,hz⟩ : PuncturedFactor N endpoint chart v.val) = y := Subtype.ext hzy
    simpa only [hy] using mergePuncturedFactorHomeomorph_some N endpoint chart s a b hends v z hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph_eq_inr_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph_eq_inr_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph_eq_inr_iff ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph_eq_inr_iff

end DifferentialGeometry.Topology.PairedBallGluing

end

end

section

noncomputable section

open _root_.Set _root_.Metric _root_.Submission.Metric _root_.Function _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.IC target :: scope.openDecls } }

variable {V : Type v} {E : Type w}
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

variable
    (hbL : ∀ p x, x ∈ closedBall (0 : E3) 2 →
      ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s false) p).chart x ∉
          (chart s false).chart '' ball (0 : E3) 1,
        (b (Sum.inl p)).chart x = ConnectedSumQuotient.inl (chart s false).toBallChart
          (chart s true).toBallChart a.1.toHomeomorph
          ⟨(remainingIncidenceChart N endpoint chart s (endpoint s false) p).chart x, hx⟩)
    (hbR : ∀ p x, x ∈ closedBall (0 : E3) 2 →
      ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s true) p).chart x ∉
          (chart s true).chart '' ball (0 : E3) 1,
        (b (Sum.inr p)).chart x = ConnectedSumQuotient.inr (chart s false).toBallChart
          (chart s true).toBallChart a.1.toHomeomorph
          ⟨(remainingIncidenceChart N endpoint chart s (endpoint s true) p).chart x, hx⟩)
  (hb : Pairwise fun p q =>
    Disjoint (flagMap (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) p '' closedBall (0 : E3) 2)
      (flagMap (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) q '' closedBall (0 : E3) 2))

private theorem sigma_subtype_val_injective :
    Function.Injective (fun x : Σ v, PuncturedFactor (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v =>
      (⟨x.fst,x.snd.val⟩ : Σ v,(mergeFactor N endpoint chart s a v).Carrier)) := by
  rintro ⟨v,x⟩ ⟨w,y⟩ h
  have hv : v = w := congrArg Sigma.fst h
  subst w
  exact congrArg (Sigma.mk v) (Subtype.ext (eq_of_heq (Sigma.mk.inj h).2))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.sigma_subtype_val_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.sigma_subtype_val_injective target :: scope.openDecls } }

include hL hR hu hbL hbR in
theorem merge_homeomorph_radialPoint (e : {e // e ≠ s}) (t : Bool)
    (z : Metric.sphere (0 : E3) 1) (r : ℝ) (hr : r ∈ _root_.Set.Icc 1 2) :
    H (Quot.mk _ ⟨endpoint e.val t,radialPoint N endpoint chart hdisj e.val t z r hr⟩) =
      ⟨(mergeFlag N endpoint chart s a b e t).fst,
        radialPoint (mergeFactor N endpoint chart s a)
          (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
          (fun e t => (mergeFlag N endpoint chart s a b e t).snd) hb e t z r hr⟩ := by
  let split := mergePuncturedFactorHomeomorph N endpoint chart s a b hends
  by_cases hi : endpoint e.val t = endpoint s _root_.Bool.false
  · let p : LFlag endpoint s := ⟨(e.val,t),e.property,hi⟩
    obtain ⟨y,hy,hyval⟩ := left_radial_representative_of_factor_representatives
      N endpoint chart hdisj s a hends p (b (Sum.inl p)) (hbL p) (split ∘ H) hL (z,⟨r,hr⟩)
    obtain ⟨q,hq,hqval⟩ := (mergePuncturedFactorHomeomorph_eq_inl_iff N endpoint chart s a hends b _ y).mp hy
    rw [hq]
    apply sigma_subtype_val_injective N endpoint chart s a b
    change (⟨none,q.val⟩ : Σ v,(mergeFactor N endpoint chart s a v).Carrier) =
      flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) (e,t) (r • z.val)
    rw [mergeFlag_flagMap_left N endpoint chart s a b e t hi, hqval, hyval]
  · by_cases hj : endpoint e.val t = endpoint s _root_.Bool.true
    · let p : RFlag endpoint s := ⟨(e.val,t),e.property,hj⟩
      obtain ⟨y,hy,hyval⟩ := right_radial_representative_of_factor_representatives
        N endpoint chart hdisj s a hends p (b (Sum.inr p)) (hbR p) (split ∘ H) hR (z,⟨r,hr⟩)
      obtain ⟨q,hq,hqval⟩ := (mergePuncturedFactorHomeomorph_eq_inl_iff N endpoint chart s a hends b _ y).mp hy
      rw [hq]
      apply sigma_subtype_val_injective N endpoint chart s a b
      change (⟨none,q.val⟩ : Σ v,(mergeFactor N endpoint chart s a v).Carrier) =
        flagMap (mergeFactor N endpoint chart s a)
          (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
          (fun e t => (mergeFlag N endpoint chart s a b e t).snd) (e,t) (r • z.val)
      rw [mergeFlag_flagMap_right N endpoint chart s a b e t hi hj, hqval, hyval]
    · let v : Rest endpoint s := ⟨endpoint e.val t,hi,hj⟩
      let x := radialPoint N endpoint chart hdisj e.val t z r hr
      obtain ⟨q,hq,hqval⟩ := (mergePuncturedFactorHomeomorph_eq_inr_iff N endpoint chart s a hends b v _ x).mp (hu v x)
      rw [hq]
      apply sigma_subtype_val_injective N endpoint chart s a b
      change (⟨some v,q.val⟩ : Σ v,(mergeFactor N endpoint chart s a v).Carrier) =
        flagMap (mergeFactor N endpoint chart s a)
          (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
          (fun e t => (mergeFlag N endpoint chart s a b e t).snd) (e,t) (r • z.val)
      rw [mergeFlag_flagMap_remaining N endpoint chart s a b e t hi hj,hqval]
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.merge_homeomorph_radialPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.merge_homeomorph_radialPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.merge_homeomorph_radialPoint ``Submission.DifferentialGeometry.Topology.PairedBallGluing.merge_homeomorph_radialPoint

end DifferentialGeometry.Topology.PairedBallGluing

end

end
