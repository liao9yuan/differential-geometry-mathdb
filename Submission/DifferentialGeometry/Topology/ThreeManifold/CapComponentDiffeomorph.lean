import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallAllSeam
import Submission.DifferentialGeometry.Topology.ThreeManifold.CapComponentQuotient
import Submission.DifferentialGeometry.Topology.ThreeManifold.UncappingSmoothStructure
import Submission.DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Interior
import Submission.DifferentialGeometry.Topology.Manifold.Diffeomorph.Sigma
import Submission.DifferentialGeometry.Topology.ThreeManifold.UncappingProjectionInterior

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Submission.Metric _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.E3 target :: scope.openDecls } }
private abbrev S2 := _root_.Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.S2 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.IC target :: scope.openDecls } }
variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)
private abbrev hd := E.pairwise_disjoint_capComponentBallChart_image

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.hd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.hd target :: scope.openDecls } }
private abbrev N := E.capped.component

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.N
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.N target :: scope.openDecls } }
private abbrev ep := E.cutCapVertex

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.ep
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.ep target :: scope.openDecls } }
private abbrev ch := fun a t => E.capComponentBallChart (a,t)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.ch
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.ch target :: scope.openDecls } }
private abbrev Raw := Quot (fun x y => ∃ a,
  PairedBallGluing.seamRel (N E) (ep E) (ch E) (hd E) a boundaryAttachment x y)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.Raw
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.Raw target :: scope.openDecls } }

private def uncappingSeamCoordinates :
    Diffeomorph IC IC SelfAttachment.directSeamDomain ConnectedSumQuotient.CollarDomain ∞ where
  toFun p := (p.val.1, ⟨p.val.2, p.property.2⟩)
  invFun p := ⟨(p.1,p.2.val),_root_.Set.mem_univ _,p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    apply ContMDiff.prodMk (contMDiff_fst.comp contMDiff_subtype_val)
    intro p
    exact DifferentialGeometry.codRestr_contMDiffAt
      (V := ConnectedSumQuotient.collarInterval) (fun p => p.property.2)
      ((contMDiff_snd.comp contMDiff_subtype_val).contMDiffAt)
  contMDiff_invFun := by
    intro p
    change ContMDiffAt IC IC ∞
      (fun p : ConnectedSumQuotient.CollarDomain =>
        (⟨(p.1,p.2.val),_root_.Set.mem_univ _,p.2.property⟩ : SelfAttachment.directSeamDomain)) p
    exact DifferentialGeometry.codRestr_contMDiffAt
      (V := SelfAttachment.directSeamDomain) (fun p => ⟨mem_univ _,p.2.property⟩)
      ((contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)).contMDiffAt)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.uncappingSeamCoordinates
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.uncappingSeamCoordinates target :: scope.openDecls } }

private theorem capComponent_radial_annulus (a : E.tubes.Index) (t : Bool) (z : S2)
    (r : ℝ) (hr : r ∈ _root_.Set.Icc (1 : ℝ) 2) :
    ((E.capComponentBallChart (a, t)).chart (r • z.val)).val =
      E.capping.capAnnulusMap (a, t)
        ((if t then z else -z), ⟨r / 4, by constructor <;> linarith [hr.1,hr.2]⟩) := by
  have hrad : r • z.val ∈ _root_.Metric.closedBall (0 : E3) 2 := by
    rw [_root_.Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial z (by linarith [hr.1])]
    exact hr.2
  rw [E.capComponentBallChart_apply_closedBall (a,t) hrad]
  have hsmall : ‖(if t then (1 / 4 : ℝ) else -(1 / 4 : ℝ)) • (r • z.val)‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, BallChart.norm_radial z (by linarith [hr.1])]
    have ht : |if t then (1 / 4 : ℝ) else -(1 / 4 : ℝ)| = 1 / 4 := by cases t <;> norm_num
    rw [ht]
    linarith [hr.2]
  rw [E.capping.capBallChart_apply (a,t) (r • z.val) hsmall]
  apply congrArg (E.capping.cap (a,t))
  apply Subtype.ext
  change (if t then (1 / 4 : ℝ) else -(1 / 4 : ℝ)) • (r • z.val) =
    (r / 4) • ((if t then z else -z) : S2).val
  cases t with
  | false =>
    change (-(1 / 4 : ℝ)) • (r • z.val) = (r / 4) • (-z.val)
    rw [smul_smul, smul_neg, ← neg_smul]
    congr 1
    ring
  | true =>
    change (1 / 4 : ℝ) • (r • z.val) = (r / 4) • z.val
    rw [smul_smul]
    congr 1
    ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.capComponent_radial_annulus
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.capComponent_radial_annulus target :: scope.openDecls } }

theorem pairedBallUncappingHomeomorph_allSeam (a : E.tubes.Index)
    (p : SelfAttachment.directSeamDomain) :
    E.pairedBallUncappingHomeomorph
      (PairedBallGluing.allSeamChart E.capped.component E.cutCapVertex
        (fun a t => E.capComponentBallChart (a,t)) E.pairwise_disjoint_capComponentBallChart_image
        (fun _ => boundaryAttachment) a p) =
      E.capping.uncappingSeam a (p.val.1, ⟨p.val.2,p.property.2⟩) := by
  change _ = E.capping.uncappingSeam a (uncappingSeamCoordinates p)
  by_cases ht : 0 ≤ p.val.2
  · rw [PairedBallGluing.allSeamChart_nonneg _ _ _ _ _ a p ht,
      E.pairedBallUncappingHomeomorph_mk,
      E.capping.uncappingSeam_of_nonneg a (uncappingSeamCoordinates p) ht]
    apply E.capping.uncappingProjection_annulus (a,_root_.Bool.false)
    exact capComponent_radial_annulus E a _root_.Bool.false p.val.1 (1 + p.val.2)
      ⟨by linarith, by linarith [p.property.2.2]⟩
  · rw [PairedBallGluing.allSeamChart_neg _ _ _ _ _ a p (lt_of_not_ge ht),
      E.pairedBallUncappingHomeomorph_mk,
      E.capping.uncappingSeam_of_nonpos a (uncappingSeamCoordinates p) (le_of_not_ge ht)]
    apply E.capping.uncappingProjection_annulus (a,_root_.Bool.true)
    have h := capComponent_radial_annulus E a _root_.Bool.true (-p.val.1) (1 - p.val.2)
      ⟨by linarith, by linarith [p.property.2.1]⟩
    exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.pairedBallUncappingHomeomorph_allSeam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.pairedBallUncappingHomeomorph_allSeam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.pairedBallUncappingHomeomorph_allSeam ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.pairedBallUncappingHomeomorph_allSeam

private theorem allCore_val_mem_uncappingInterior
    (x : PairedBallGluing.allCore (N E) (ep E) (ch E) (hd E)) :
    x.val.snd.val.val ∈ E.capping.uncappingInterior := by
  intro hx
  obtain ⟨⟨a,t⟩, z, hz, hzx⟩ := mem_iUnion.mp hx
  have hz2 : z ∈ _root_.Metric.closedBall (0 : E3) 2 :=
    _root_.Metric.closedBall_subset_closedBall (by norm_num) hz
  have hsig : PairedBallGluing.flagMap (N E) (ep E) (ch E) (a,t) z =
      (⟨x.val.fst,x.val.snd.val⟩ : Σ K, (E.capped.component K).Carrier) := by
    apply E.capped.componentUnionHomeomorph.injective
    exact (E.capComponentBallChart_apply_closedBall (a,t) hz2).trans hzx
  by_cases hb : z ∈ _root_.Metric.ball (0 : E3) 1
  · exact x.val.snd.property (mem_iUnion.mpr ⟨(a,t),z,hb,hsig⟩)
  · have hs : z ∈ _root_.Metric.sphere (0 : E3) 1 := by
      exact le_antisymm hz (not_lt.mp hb)
    apply x.property
    refine mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨t, ⟨⟨z,hs⟩, ?_⟩⟩⟩
    have hi : Function.Injective
        (fun y : Σ K, PairedBallGluing.PuncturedFactor (N E) (ep E) (ch E) K =>
          (⟨y.fst,y.snd.val⟩ : Σ K, (E.capped.component K).Carrier)) :=
      by
        rintro ⟨i,v⟩ ⟨j,w⟩ h
        obtain rfl : i = j := congrArg Sigma.fst h
        have hv : v.val = w.val :=
          (@sigma_mk_injective (ConnectedComponents E.capped.Carrier)
            (fun K => (E.capped.component K).Carrier) i) h
        obtain rfl : v = w := Subtype.ext hv
        rfl
    exact hi hsig

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.allCore_val_mem_uncappingInterior
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.allCore_val_mem_uncappingInterior target :: scope.openDecls } }

def capAllCoreMap : PairedBallGluing.allCore (N E) (ep E) (ch E) (hd E) →
    E.capping.uncappingInterior :=
  fun x => ⟨x.val.snd.val.val, allCore_val_mem_uncappingInterior E x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.capAllCoreMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.capAllCoreMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.capAllCoreMap ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.capAllCoreMap

@[simp] theorem capAllCoreMap_val
    (x : PairedBallGluing.allCore (N E) (ep E) (ch E) (hd E)) :
    (E.capAllCoreMap x).val = x.val.snd.val.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.capAllCoreMap_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.capAllCoreMap_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.capAllCoreMap_val ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.capAllCoreMap_val

theorem pairedBallUncappingHomeomorph_allCore
    (x : PairedBallGluing.allCore (N E) (ep E) (ch E) (hd E)) :
    E.pairedBallUncappingHomeomorph
      (PairedBallGluing.allCoreInclusion (N E) (ep E) (ch E) (hd E)
        (fun _ => boundaryAttachment) x) =
      E.capping.uncappingInteriorProjection (E.capAllCoreMap x) := by
  change E.pairedBallUncappingHomeomorph (Quot.mk _ x.val) = _
  rw [E.pairedBallUncappingHomeomorph_mk]
  apply congrArg E.capping.uncappingProjection
  apply Subtype.ext
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.pairedBallUncappingHomeomorph_allCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.pairedBallUncappingHomeomorph_allCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.pairedBallUncappingHomeomorph_allCore ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.pairedBallUncappingHomeomorph_allCore

variable (C : ∀ K, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (E.capped.component K).Carrier | (⟨K,x⟩ : Σ K, (E.capped.component K).Carrier) ∉
      ⋃ p, PairedBallGluing.flagMap (N E) (ep E) (ch E) p '' ball (0 : E3) 1})

private theorem componentInterior_mem
    (K : ConnectedComponents E.capped.Carrier) (y : (E.capped.component K).Carrier)
    (hy : y.val ∈ E.capping.uncappingInterior) :
    y ∈ interior {x : (E.capped.component K).Carrier |
      (⟨K,x⟩ : Σ K, (E.capped.component K).Carrier) ∉
        ⋃ p, PairedBallGluing.flagMap (N E) (ep E) (ch E) p '' _root_.Metric.ball (0 : E3) 1} := by
  let U : Set (E.capped.component K).Carrier :=
    (Subtype.val : (E.capped.component K).Carrier → E.capped.Carrier) ⁻¹'
      E.capping.uncappingInterior
  have ho : IsOpen U := E.capping.uncappingInterior.isOpen.preimage continuous_subtype_val
  refine interior_maximal ?_ ho hy
  intro x hx hbad
  obtain ⟨p,z,hz,hzx⟩ := mem_iUnion.mp hbad
  have hz2 : z ∈ _root_.Metric.closedBall (0 : E3) 2 :=
    ball_subset_closedBall.trans (_root_.Metric.closedBall_subset_closedBall (by norm_num)) hz
  have heq := congrArg E.capped.componentUnionHomeomorph hzx
  have hval : (E.capping.capBallChart p).chart z = x.val :=
    (E.capComponentBallChart_apply_closedBall p hz2).symm.trans heq
  exact hx (mem_iUnion.mpr ⟨p,z,_root_.Metric.ball_subset_closedBall hz,hval⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentInterior_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.componentInterior_mem target :: scope.openDecls } }

include C in
theorem isLocalDiffeomorph_capAllCoreMap :
    let _ : ∀ K, ChartedSpace (EuclideanHalfSpace 3)
      (PairedBallGluing.PuncturedFactor (N E) (ep E) (ch E) K) := fun K => (C K).toChartedSpace
    IsLocalDiffeomorph (𝓡∂ 3) (𝓡 3) ∞ (E.capAllCoreMap) := by
  let _ : ∀ K, ChartedSpace (EuclideanHalfSpace 3)
    (PairedBallGluing.PuncturedFactor (N E) (ep E) (ch E) K) := fun K => (C K).toChartedSpace
  let _ : ∀ K, IsManifold (𝓡∂ 3) ∞
    (PairedBallGluing.PuncturedFactor (N E) (ep E) (ch E) K) := fun K => (C K).isManifold
  let g : (Σ K, PairedBallGluing.PuncturedFactor (N E) (ep E) (ch E) K) → E.capped.Carrier :=
    fun x => x.snd.val.val
  change IsLocalDiffeomorph (𝓡∂ 3) (𝓡 3) ∞ (E.capAllCoreMap)
  intro x
  have hfirst : IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡 3) ∞
      (Subtype.val : PairedBallGluing.PuncturedFactor (N E) (ep E) (ch E) x.val.fst →
        (E.capped.component x.val.fst).Carrier) x.val.snd :=
    (C x.val.fst).isLocalDiffeomorphAt_subtype_val
      (componentInterior_mem E x.val.fst x.val.snd.val (allCore_val_mem_uncappingInterior E x))
  have hcomp : IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡 3) ∞
      (g ∘ Sigma.mk x.val.fst) x.val.snd :=
    hfirst.comp (𝓡 3) E.capped.Carrier
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val
        (E.capped.componentOpen x.val.fst) x.val.snd.val)
  have hg : IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡 3) ∞ g x.val :=
    DifferentialGeometry.isLocalDiffeomorphAt_of_comp
      (f := Sigma.mk x.val.fst) (g := g) (x := x.val.snd) hcomp
      (isLocalDiffeomorph_sigmaMk (I := 𝓡∂ 3) x.val.fst x.val.snd)
  apply DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
    (V := E.capping.uncappingInterior) (allCore_val_mem_uncappingInterior E)
  exact (DifferentialGeometry.isLocalDiffeomorph_subtype_val
    (PairedBallGluing.allCore (N E) (ep E) (ch E) (hd E)) x).comp
      (𝓡 3) E.capped.Carrier hg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorph_capAllCoreMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorph_capAllCoreMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorph_capAllCoreMap ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorph_capAllCoreMap

private theorem capRaw_homeomorph_local
    (charts : ChartedSpace E3 (Raw E))
    (hcore :
      let _ : ∀ K, ChartedSpace (EuclideanHalfSpace 3)
        (PairedBallGluing.PuncturedFactor (N E) (ep E) (ch E) K) := fun K => (C K).toChartedSpace
      let _ := charts
      IsLocalDiffeomorph (𝓡∂ 3) (𝓡 3) ∞
        (PairedBallGluing.allCoreInclusion (N E) (ep E) (ch E) (hd E)
          (fun _ => boundaryAttachment)))
    (hseam :
      let _ := charts
      ∀ a z, IsLocalDiffeomorphAt IC (𝓡 3) ∞
        (PairedBallGluing.allSeamChart (N E) (ep E) (ch E) (hd E)
          (fun _ => boundaryAttachment) a)
        ⟨(z,0),_root_.Set.mem_univ _,by norm_num [SelfAttachment.directSeamDomain]⟩) :
    let _ := charts
    ∃ H : (Raw E) ≃ₜ M.Carrier, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ H := by
  let _ := charts
  let _ : ∀ K, ChartedSpace (EuclideanHalfSpace 3)
    (PairedBallGluing.PuncturedFactor (N E) (ep E) (ch E) K) := fun K => (C K).toChartedSpace
  obtain ⟨U, hUcore, hUi, hUs⟩ := E.capping.exists_uncapping_homeomorph_localDiffeomorph
  let H := E.pairedBallUncappingHomeomorph.trans U
  change ∃ H : (Raw E) ≃ₜ M.Carrier, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ H
  refine ⟨H, ?_⟩
  intro q
  rcases PairedBallGluing.all_local_maps_cover (N E) (ep E) (ch E) (hd E)
      (fun _ => boundaryAttachment) q with ⟨x,hx⟩ | ⟨a,z,hz⟩
  · subst q
    have heq : H ∘ PairedBallGluing.allCoreInclusion (N E) (ep E) (ch E) (hd E)
        (fun _ => boundaryAttachment) = E.capping.uncappingInteriorMap U ∘ E.capAllCoreMap := by
      funext x
      exact congrArg U (E.pairedBallUncappingHomeomorph_allCore x)
    have hg := (E.isLocalDiffeomorph_capAllCoreMap C x).comp (𝓡 3) M.Carrier
      (hUi (E.capAllCoreMap x))
    have hh : IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡 3) ∞
        (H ∘ PairedBallGluing.allCoreInclusion (N E) (ep E) (ch E) (hd E)
          (fun _ => boundaryAttachment)) x := heq.symm ▸ hg
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp hh (hcore x)
  · subst q
    let p : SelfAttachment.directSeamDomain :=
      ⟨(z,0),_root_.Set.mem_univ _,by norm_num [SelfAttachment.directSeamDomain]⟩
    have heq : H ∘ PairedBallGluing.allSeamChart (N E) (ep E) (ch E) (hd E)
        (fun _ => boundaryAttachment) a =
          (U ∘ E.capping.uncappingSeam a) ∘ uncappingSeamCoordinates := by
      funext x
      exact congrArg U (E.pairedBallUncappingHomeomorph_allSeam a x)
    have hg := (uncappingSeamCoordinates.isLocalDiffeomorph p).comp (𝓡 3) M.Carrier (hUs a z)
    have hh : IsLocalDiffeomorphAt IC (𝓡 3) ∞
        (H ∘ PairedBallGluing.allSeamChart (N E) (ep E) (ch E) (hd E)
          (fun _ => boundaryAttachment) a) p := heq.symm ▸ hg
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp hh (hseam a z)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.capRaw_homeomorph_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.capRaw_homeomorph_local target :: scope.openDecls } }

theorem exists_pairedBallQuotient_diffeomorph
    (charts : ChartedSpace E3 (Raw E))
    (hcore :
      let _ : ∀ K, ChartedSpace (EuclideanHalfSpace 3)
        (PairedBallGluing.PuncturedFactor (N E) (ep E) (ch E) K) := fun K => (C K).toChartedSpace
      let _ := charts
      IsLocalDiffeomorph (𝓡∂ 3) (𝓡 3) ∞
        (PairedBallGluing.allCoreInclusion (N E) (ep E) (ch E) (hd E)
          (fun _ => boundaryAttachment)))
    (hseam :
      let _ := charts
      ∀ a z, IsLocalDiffeomorphAt IC (𝓡 3) ∞
        (PairedBallGluing.allSeamChart (N E) (ep E) (ch E) (hd E)
          (fun _ => boundaryAttachment) a)
        ⟨(z,0),_root_.Set.mem_univ _,by norm_num [SelfAttachment.directSeamDomain]⟩) :
    let _ := charts
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) (Raw E) M.Carrier ∞) := by
  let _ := charts
  obtain ⟨H,hH⟩ := capRaw_homeomorph_local E C charts hcore hseam
  exact ⟨hH.diffeomorphOfBijective H.bijective⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_pairedBallQuotient_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_pairedBallQuotient_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_pairedBallQuotient_diffeomorph ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_pairedBallQuotient_diffeomorph

end DifferentialGeometry.Topology.SphericalCutCapTransition
