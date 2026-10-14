import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallLoopSmooth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Metric _root_.Submission.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.E3 target :: scope.openDecls } }
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (s : E) (hloop : endpoint s true = endpoint s false)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (S : SmoothSelfAttachment (chart s false) (loopSecondChart N endpoint chart s hloop)
    (disjoint_loop_charts N endpoint chart s hloop hdisj) boundaryAttachment)
  (F : ClosedOrientedManifold.OrientedDiffeomorph S.toConnectedClosedOrientedManifold.toClosedOrientedManifold
    (loopFactor N endpoint s none).toClosedOrientedManifold)
  (b : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} →
    OrientedBallChart (loopFactor N endpoint s none).toClosedOrientedManifold)
  (hb : ∀ i x, x ∈ closedBall (0 : E3) 2 →
    ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s false) i).chart x ∈
      ((chart s false).chart '' ball 0 1 ∪ (loopSecondChart N endpoint chart s hloop).chart '' ball 0 1)ᶜ,
      (b i).chart x = F.val (SelfAttachment.coreInclusion (chart s false).toBallChart
        (loopSecondChart N endpoint chart s hloop).toBallChart
        (disjoint_loop_charts N endpoint chart s hloop hdisj) boundaryAttachment.val.toHomeomorph
        ⟨(remainingIncidenceChart N endpoint chart s (endpoint s false) i).chart x, hx⟩))
  (C : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉ ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1})
  (D : SmoothBoundaryAtlas (𝓡 3) 3
    {y : (loopFactor N endpoint s none).Carrier | y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1})
  (C' : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (loopFactor N endpoint s v).Carrier |
      (⟨v, x⟩ : Σ v, (loopFactor N endpoint s v).Carrier) ∉
        ⋃ p, flagMap (loopFactor N endpoint s)
          (fun e t => (loopFlag N endpoint chart s b e t).fst)
          (fun e t => (loopFlag N endpoint chart s b e t).snd) p '' ball (0 : E3) 1})
  (H : Quot (seamRel N endpoint chart hdisj s boundaryAttachment) ≃ₜ
    (Σ v, PuncturedFactor (loopFactor N endpoint s)
      (fun e t => (loopFlag N endpoint chart s b e t).fst)
      (fun e t => (loopFlag N endpoint chart s b e t).snd) v))
  (hH : ∀ x : PuncturedFactor N endpoint chart (endpoint s false),
    ∃ y, loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop (H (Quot.mk _ ⟨endpoint s false, x⟩)) = Sum.inl y ∧
      y.val = F.val (SelfAttachment.coreToBand (chart s false).toBallChart
        (loopSecondChart N endpoint chart s hloop).toBallChart
        (disjoint_loop_charts N endpoint chart s hloop hdisj) boundaryAttachment.val.toHomeomorph
        (loopPuncturedFactorHomeomorph N endpoint chart s hloop x).val))
  (hR : ∀ (v : {v // v ≠ endpoint s false}) (x : PuncturedFactor N endpoint chart v.val),
    loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop (H (Quot.mk _ ⟨v.val, x⟩)) = Sum.inr ⟨v, x⟩)


include hH in
theorem loop_homeomorph_selected (x : PuncturedFactor N endpoint chart (endpoint s _root_.Bool.false)) :
    ∃ y : PuncturedFactor (loopFactor N endpoint s)
        (fun e t => (loopFlag N endpoint chart s b e t).fst)
        (fun e t => (loopFlag N endpoint chart s b e t).snd) _root_.Option.none,
      H (Quot.mk _ ⟨endpoint s _root_.Bool.false, x⟩) = ⟨none, y⟩ ∧
        y.val = F.val (SelfAttachment.coreToBand (chart s _root_.Bool.false).toBallChart
          (loopSecondChart N endpoint chart s hloop).toBallChart
          (disjoint_loop_charts N endpoint chart s hloop hdisj) boundaryAttachment.val.toHomeomorph
          (loopPuncturedFactorHomeomorph N endpoint chart s hloop x).val) := by
  obtain ⟨y, hy, hyval⟩ := hH x
  let y' : PuncturedFactor (loopFactor N endpoint s)
      (fun e t => (loopFlag N endpoint chart s b e t).fst)
      (fun e t => (loopFlag N endpoint chart s b e t).snd) none :=
    ⟨y.val, fun h => y.property
      ((Set.ext_iff.mp (loopFlag_holes_none N endpoint chart s b (_root_.Metric.ball 0 1)) y.val).mp h)⟩
  refine ⟨y', ?_, hyval⟩
  apply (loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop).injective
  exact hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.loop_homeomorph_selected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.loop_homeomorph_selected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.loop_homeomorph_selected ``Submission.DifferentialGeometry.Topology.PairedBallGluing.loop_homeomorph_selected

include hR in
theorem loop_homeomorph_remaining (v : {v // v ≠ endpoint s _root_.Bool.false}) (x : PuncturedFactor N endpoint chart v.val) :
    ∃ y : PuncturedFactor (loopFactor N endpoint s)
        (fun e t => (loopFlag N endpoint chart s b e t).fst)
        (fun e t => (loopFlag N endpoint chart s b e t).snd) (_root_.Option.some v),
      H (Quot.mk _ ⟨v.val, x⟩) = ⟨some v, y⟩ ∧ y.val = x.val := by
  let y : PuncturedFactor (loopFactor N endpoint s)
      (fun e t => (loopFlag N endpoint chart s b e t).fst)
      (fun e t => (loopFlag N endpoint chart s b e t).snd) (_root_.Option.some v) :=
    ⟨x.val, fun h => x.property
      ((Set.ext_iff.mp (loopFlag_holes_some N endpoint chart s b hloop v (_root_.Metric.ball 0 1)) x.val).mp h)⟩
  refine ⟨y, ?_, rfl⟩
  apply (loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop).injective
  exact hR v x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.loop_homeomorph_remaining then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.loop_homeomorph_remaining"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.loop_homeomorph_remaining ``Submission.DifferentialGeometry.Topology.PairedBallGluing.loop_homeomorph_remaining

end DifferentialGeometry.Topology.PairedBallGluing

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (s : E) (hloop : endpoint s true = endpoint s false)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (S : SmoothSelfAttachment (chart s false) (loopSecondChart N endpoint chart s hloop)
    (disjoint_loop_charts N endpoint chart s hloop hdisj) boundaryAttachment)
  (F : ClosedOrientedManifold.OrientedDiffeomorph S.toConnectedClosedOrientedManifold.toClosedOrientedManifold
    (loopFactor N endpoint s none).toClosedOrientedManifold)
  (b : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} →
    OrientedBallChart (loopFactor N endpoint s none).toClosedOrientedManifold)
  (hb : ∀ i x, x ∈ closedBall (0 : E3) 2 →
    ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s false) i).chart x ∈
      ((chart s false).chart '' ball 0 1 ∪ (loopSecondChart N endpoint chart s hloop).chart '' ball 0 1)ᶜ,
      (b i).chart x = F.val (SelfAttachment.coreInclusion (chart s false).toBallChart
        (loopSecondChart N endpoint chart s hloop).toBallChart
        (disjoint_loop_charts N endpoint chart s hloop hdisj) boundaryAttachment.val.toHomeomorph
        ⟨(remainingIncidenceChart N endpoint chart s (endpoint s false) i).chart x, hx⟩))
  (C : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉ ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1})
  (D : SmoothBoundaryAtlas (𝓡 3) 3
    {y : (loopFactor N endpoint s none).Carrier | y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1})
  (C' : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (loopFactor N endpoint s v).Carrier |
      (⟨v, x⟩ : Σ v, (loopFactor N endpoint s v).Carrier) ∉
        ⋃ p, flagMap (loopFactor N endpoint s)
          (fun e t => (loopFlag N endpoint chart s b e t).fst)
          (fun e t => (loopFlag N endpoint chart s b e t).snd) p '' ball (0 : E3) 1})
  (H : Quot (seamRel N endpoint chart hdisj s boundaryAttachment) ≃ₜ
    (Σ v, PuncturedFactor (loopFactor N endpoint s)
      (fun e t => (loopFlag N endpoint chart s b e t).fst)
      (fun e t => (loopFlag N endpoint chart s b e t).snd) v))
  (hH : ∀ x : PuncturedFactor N endpoint chart (endpoint s false),
    ∃ y, loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop (H (Quot.mk _ ⟨endpoint s false, x⟩)) = Sum.inl y ∧
      y.val = F.val (SelfAttachment.coreToBand (chart s false).toBallChart
        (loopSecondChart N endpoint chart s hloop).toBallChart
        (disjoint_loop_charts N endpoint chart s hloop hdisj) boundaryAttachment.val.toHomeomorph
        (loopPuncturedFactorHomeomorph N endpoint chart s hloop x).val))
  (hR : ∀ (v : {v // v ≠ endpoint s false}) (x : PuncturedFactor N endpoint chart v.val),
    loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop (H (Quot.mk _ ⟨v.val, x⟩)) = Sum.inr ⟨v, x⟩)



private theorem radialPoint_cast_sigma (e : E) (t : Bool) (v : V) (hv : endpoint e t = v)
    (z : _root_.Metric.sphere (0 : E3) 1) (r : ℝ) (hr : r ∈ _root_.Set.Icc 1 2) :
    (⟨v, hv ▸ radialPoint N endpoint chart hdisj e t z r hr⟩ :
      Σ v, PuncturedFactor N endpoint chart v) =
      ⟨endpoint e t, radialPoint N endpoint chart hdisj e t z r hr⟩ := by
  subst v
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.radialPoint_cast_sigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.radialPoint_cast_sigma target :: scope.openDecls } }

private theorem radialPoint_cast_val (e : E) (t : Bool) (v : V) (hv : endpoint e t = v)
    (z : _root_.Metric.sphere (0 : E3) 1) (r : ℝ) (hr : r ∈ _root_.Set.Icc 1 2) :
    (hv ▸ radialPoint N endpoint chart hdisj e t z r hr).val =
      (incidenceChart N endpoint chart v ⟨(e, t), hv⟩).chart (r • z.val) := by
  subst v
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.radialPoint_cast_val
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.radialPoint_cast_val target :: scope.openDecls } }

variable (hb' : Pairwise fun p q =>
    Disjoint (flagMap (loopFactor N endpoint s)
      (fun e t => (loopFlag N endpoint chart s b e t).fst)
      (fun e t => (loopFlag N endpoint chart s b e t).snd) p '' closedBall (0 : E3) 2)
    (flagMap (loopFactor N endpoint s)
      (fun e t => (loopFlag N endpoint chart s b e t).fst)
      (fun e t => (loopFlag N endpoint chart s b e t).snd) q '' closedBall (0 : E3) 2))

private theorem sigma_subtype_val_injective :
    Function.Injective (fun x : Σ v, PuncturedFactor (loopFactor N endpoint s)
      (fun e t => (loopFlag N endpoint chart s b e t).fst)
      (fun e t => (loopFlag N endpoint chart s b e t).snd) v =>
      (⟨x.fst, x.snd.val⟩ : Σ v, (loopFactor N endpoint s v).Carrier)) := by
  rintro ⟨v, x⟩ ⟨w, y⟩ h
  have hv : v = w := congrArg Sigma.fst h
  subst w
  exact congrArg (Sigma.mk v) (Subtype.ext (eq_of_heq (Sigma.mk.inj h).2))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.sigma_subtype_val_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.sigma_subtype_val_injective target :: scope.openDecls } }

include hb hH hR in
theorem loop_homeomorph_radialPoint (e : {e // e ≠ s}) (t : Bool)
    (z : _root_.Metric.sphere (0 : E3) 1) (r : ℝ) (hr : r ∈ _root_.Set.Icc 1 2) :
    H (Quot.mk _ ⟨endpoint e.val t, radialPoint N endpoint chart hdisj e.val t z r hr⟩) =
      ⟨(loopFlag N endpoint chart s b e t).fst,
        radialPoint (loopFactor N endpoint s)
          (fun e t => (loopFlag N endpoint chart s b e t).fst)
          (fun e t => (loopFlag N endpoint chart s b e t).snd) hb' e t z r hr⟩ := by
  have hrad : r • z.val ∈ _root_.Metric.closedBall (0 : E3) 2 := by
    rw [_root_.Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial z (by linarith [hr.1])]
    exact hr.2
  by_cases hi : endpoint e.val t = endpoint s _root_.Bool.false
  · let i : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false} :=
      ⟨(e.val, t), e.property, hi⟩
    let x : PuncturedFactor N endpoint chart (endpoint s _root_.Bool.false) :=
      hi ▸ radialPoint N endpoint chart hdisj e.val t z r hr
    have hxSigma : (⟨endpoint s _root_.Bool.false, x⟩ : Σ v, PuncturedFactor N endpoint chart v) =
        ⟨endpoint e.val t, radialPoint N endpoint chart hdisj e.val t z r hr⟩ :=
      radialPoint_cast_sigma N endpoint chart hdisj e.val t (endpoint s _root_.Bool.false) hi z r hr
    have hxval : x.val = (remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.false) i).chart (r • z.val) :=
      radialPoint_cast_val N endpoint chart hdisj e.val t (endpoint s _root_.Bool.false) hi z r hr
    obtain ⟨y, hy, hyval⟩ := loop_homeomorph_selected N endpoint chart s hloop hdisj S F b H hH x
    have hp := remainingIncidenceChart_avoids_incidence N endpoint chart s hdisj
      (endpoint s _root_.Bool.false) i _root_.Bool.false rfl (r • z.val) hrad
    have hq := remainingIncidenceChart_avoids_incidence N endpoint chart s hdisj
      (endpoint s _root_.Bool.false) i _root_.Bool.true hloop (r • z.val) hrad
    obtain ⟨hmem, hbval⟩ := hb i (r • z.val) hrad
    have hyb : y.val = (b i).chart (r • z.val) := by
      rw [hyval]
      have hc : (loopPuncturedFactorHomeomorph N endpoint chart s hloop x).val =
          ⟨(remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.false) i).chart (r • z.val), hmem⟩ :=
        Subtype.ext hxval
      rw [hc, SelfAttachment.coreToBand_of_not_mem_chart_image _ _ _ _ _ hp hq]
      exact hbval.symm
    have hy' := (congrArg (fun q => H (Quot.mk _ q)) hxSigma).symm.trans hy
    rw [hy']
    apply sigma_subtype_val_injective N endpoint chart s b
    change (⟨none, y.val⟩ : Σ v, (loopFactor N endpoint s v).Carrier) =
      flagMap (loopFactor N endpoint s)
        (fun e t => (loopFlag N endpoint chart s b e t).fst)
        (fun e t => (loopFlag N endpoint chart s b e t).snd) (e, t) (r • z.val)
    rw [loopFlag_flagMap_selected N endpoint chart s b e t hi, hyb]
  · obtain ⟨y, hy, hyval⟩ := loop_homeomorph_remaining N endpoint chart s hloop hdisj b H hR
      ⟨endpoint e.val t, hi⟩ (radialPoint N endpoint chart hdisj e.val t z r hr)
    rw [hy]
    apply sigma_subtype_val_injective N endpoint chart s b
    change (⟨some ⟨endpoint e.val t, hi⟩, y.val⟩ : Σ v, (loopFactor N endpoint s v).Carrier) =
      flagMap (loopFactor N endpoint s)
        (fun e t => (loopFlag N endpoint chart s b e t).fst)
        (fun e t => (loopFlag N endpoint chart s b e t).snd) (e, t) (r • z.val)
    rw [loopFlag_flagMap_remaining N endpoint chart s b e t hi, hyval]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.loop_homeomorph_radialPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.loop_homeomorph_radialPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.loop_homeomorph_radialPoint ``Submission.DifferentialGeometry.Topology.PairedBallGluing.loop_homeomorph_radialPoint

end DifferentialGeometry.Topology.PairedBallGluing
