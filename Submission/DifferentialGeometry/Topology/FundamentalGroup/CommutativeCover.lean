/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.FundamentalGroup.SimplyConnected
import Submission.DifferentialGeometry.Topology.FundamentalGroup.CollaredClosedCover
import Submission.DifferentialGeometry.Topology.VanKampen.FreeProduct
import Submission.DifferentialGeometry.Topology.VanKampen.TwoSidedCollarCover

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology

open _root_.Set _root_.Submission.DifferentialGeometry.Topology.VanKampen

theorem simplyConnectedSpace_or_of_open_cover_of_isMulCommutative
    {X : Type*} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V] [SimplyConnectedSpace (↑(U ∩ V))]
    (x : X) (hx : x ∈ U ∩ V) (hcomm : IsMulCommutative (FundamentalGroup X x)) :
    SimplyConnectedSpace U ∨ SimplyConnectedSpace V := by
  classical
  by_contra hn
  obtain ⟨hUn, hVn⟩ := not_or.mp hn
  obtain ⟨a, ha⟩ := exists_fundamentalGroup_ne_one_of_not_simplyConnectedSpace
    hUn (leftBasepoint U x hx.1)
  obtain ⟨b, hb⟩ := exists_fundamentalGroup_ne_one_of_not_simplyConnectedSpace
    hVn (rightBasepoint V x hx.2)
  let G := fundamentalGroupFactor U V x hx
  let wa : Monoid.CoprodI.Word G := Monoid.CoprodI.Word.cons (i := _root_.Bool.false) a
    .empty (by simp [Monoid.CoprodI.Word.fstIdx, Monoid.CoprodI.Word.empty]) ha
  let wb : Monoid.CoprodI.Word G := Monoid.CoprodI.Word.cons (i := _root_.Bool.true) b
    .empty (by simp [Monoid.CoprodI.Word.fstIdx, Monoid.CoprodI.Word.empty]) hb
  let wab : Monoid.CoprodI.Word G := Monoid.CoprodI.Word.cons (i := _root_.Bool.false) a wb
    (by change _root_.Option.some _root_.Bool.true ≠ _root_.Option.some _root_.Bool.false; decide) ha
  let wba : Monoid.CoprodI.Word G := Monoid.CoprodI.Word.cons (i := _root_.Bool.true) b wa
    (by change _root_.Option.some _root_.Bool.false ≠ _root_.Option.some _root_.Bool.true; decide) hb
  let e := fundamentalGroupEquivFreeProduct U V hU hV hcover x hx
  have hprod : wab.prod = wba.prod := by
    apply e.injective
    simp only [wab, wba, wa, wb, Monoid.CoprodI.Word.prod_cons, map_mul]
    exact isMulCommutative_iff.mp hcomm _ _
  have hw : wab = wba := (Monoid.CoprodI.Word.equiv (M := G)).symm.injective hprod
  have hi := congrArg Monoid.CoprodI.Word.fstIdx hw
  simp only [wab, wba, Monoid.CoprodI.Word.fstIdx_cons, Option.some.injEq,
    Bool.false_eq_true] at hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplyConnectedSpace_or_of_open_cover_of_isMulCommutative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplyConnectedSpace_or_of_open_cover_of_isMulCommutative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplyConnectedSpace_or_of_open_cover_of_isMulCommutative ``Submission.DifferentialGeometry.Topology.simplyConnectedSpace_or_of_open_cover_of_isMulCommutative

theorem ThreeManifold.TwoSidedCollar.simplyConnectedSpace_or_of_closed_cover_of_isMulCommutative
    {S X : Type*} [TopologicalSpace S] [TopologicalSpace X] [SimplyConnectedSpace S]
    {e : S → X} (c : ThreeManifold.TwoSidedCollar e) {P Q : Set X}
    [PathConnectedSpace P] [PathConnectedSpace Q]
    (hcover : P ∪ Q = _root_.Set.univ) (hmeet : P ∩ Q = Set.range e)
    (hPcl : closure (P \ Q) = P) (hQcl : closure (Q \ P) = Q)
    (s : S) (hcomm : IsMulCommutative (FundamentalGroup X (e s))) :
    SimplyConnectedSpace P ∨ SimplyConnectedSpace Q := by
  have hP : IsClosed P := hPcl ▸ isClosed_closure
  have hQ : IsClosed Q := hQcl ▸ isClosed_closure
  have hQP : Q ∪ P = univ := (_root_.Set.union_comm Q P).trans hcover
  have hPf : frontier P = Set.range e :=
    (frontier_eq_inter_of_closure_sdiff_eq hcover hPcl hQcl).trans hmeet
  have hQf : frontier Q = Set.range e :=
    (frontier_eq_inter_of_closure_sdiff_eq hQP hQcl hPcl).trans
      ((_root_.Set.inter_comm Q P).trans hmeet)
  obtain ⟨d, _, hdP, hdrQ, hUV, hUVinter⟩ :=
    c.exists_open_cover_of_closed_cover hcover hmeet hPcl hQcl
  let U := d.domainNeighborhood P
  let V := d.reverse.domainNeighborhood Q
  let _ : PathConnectedSpace U := d.pathConnectedSpace_domainNeighborhood hP hPf.subset hdP
  let _ : PathConnectedSpace V := d.reverse.pathConnectedSpace_domainNeighborhood hQ hQf.subset hdrQ
  let j : d.range ≃ₜ ↑(U ∩ V) := (Homeomorph.setCongr hUVinter).symm
  let _ : SimplyConnectedSpace (↑(U ∩ V)) :=
    (j.symm.toHomotopyEquiv.trans d.rangeHomotopyEquiv).simplyConnectedSpace
  have hx : e s ∈ U ∩ V := hUVinter.symm.subset ⟨(s, 0), d.zero_eq s⟩
  rcases simplyConnectedSpace_or_of_open_cover_of_isMulCommutative U V
      (d.isOpen_domainNeighborhood P) (d.reverse.isOpen_domainNeighborhood Q)
      hUV (e s) hx hcomm with hU | hV
  · let _ := hU
    exact Or.inl (ThreeManifold.TwoSidedCollar.simplyConnectedSpace_of_retract
      (d.domainInclusion hP hPf.subset) (d.domainRetraction hdP)
      (ContinuousMap.ext (d.domainRetraction_leftInverse hP hPf.subset hdP)))
  · let _ := hV
    exact Or.inr (ThreeManifold.TwoSidedCollar.simplyConnectedSpace_of_retract
      (d.reverse.domainInclusion hQ hQf.subset) (d.reverse.domainRetraction hdrQ)
      (ContinuousMap.ext (d.reverse.domainRetraction_leftInverse hQ hQf.subset hdrQ)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.simplyConnectedSpace_or_of_closed_cover_of_isMulCommutative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.simplyConnectedSpace_or_of_closed_cover_of_isMulCommutative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.simplyConnectedSpace_or_of_closed_cover_of_isMulCommutative ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.simplyConnectedSpace_or_of_closed_cover_of_isMulCommutative

end DifferentialGeometry.Topology
