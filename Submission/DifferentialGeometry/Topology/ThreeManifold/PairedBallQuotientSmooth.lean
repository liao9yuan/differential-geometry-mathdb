import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallAllSeam
import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallSeamFibers
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Metric _root_.Submission.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w u' v'
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
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (a : E → BoundaryAttachment) (s : E)
  {V' : Type v'} (N' : V' → ConnectedClosedOrientedManifold.{u'} 3)
  (endpoint' : {e // e ≠ s} → Bool → V')
  (chart' : (e : {e // e ≠ s}) → (b : Bool) →
    OrientedBallChart (N' (endpoint' e b)).toClosedOrientedManifold)
  (hdisj' : Pairwise fun p q =>
    Disjoint (flagMap N' endpoint' chart' p '' closedBall (0 : E3) 2)
      (flagMap N' endpoint' chart' q '' closedBall (0 : E3) 2))
  (H : Quot (seamRel N endpoint chart hdisj s (a s)) ≃ₜ
    (Σ v, PuncturedFactor N' endpoint' chart' v))
  (J : Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e (a e) x y) ≃ₜ
    Quot (fun x y => ∃ e : {e // e ≠ s},
      seamRel N' endpoint' chart' hdisj' e (a e.val) x y))
  (hJ : ∀ x, J (Quot.mk _ x) = Quot.mk _ (H (Quot.mk _ x)))

include hJ in
theorem quotient_step_selected_seam (p : SelfAttachment.directSeamDomain) :
    J (allSeamChart N endpoint chart hdisj a s p) =
      Quot.mk _ (H (seamChart N endpoint chart hdisj s (a s) p)) := by
  by_cases ht : 0 ≤ p.val.2
  · rw [allSeamChart_nonneg N endpoint chart hdisj a s p ht, hJ]
    rw [seamChart, dif_pos ht]
  · rw [allSeamChart_neg N endpoint chart hdisj a s p (lt_of_not_ge ht), hJ]
    rw [seamChart, dif_neg ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.quotient_step_selected_seam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.quotient_step_selected_seam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.quotient_step_selected_seam ``Submission.DifferentialGeometry.Topology.PairedBallGluing.quotient_step_selected_seam

include hJ in
theorem quotient_step_surviving_seam
    (hrad : ∀ (e : {e // e ≠ s}) (b : Bool) (z : _root_.Metric.sphere (0 : E3) 1)
      (r : ℝ) (hr : r ∈ _root_.Set.Icc 1 2),
      H (Quot.mk _ ⟨endpoint e.val b,
        radialPoint N endpoint chart hdisj e.val b z r hr⟩) =
      ⟨endpoint' e b, radialPoint N' endpoint' chart' hdisj' e b z r hr⟩)
    (e : {e // e ≠ s}) (p : SelfAttachment.directSeamDomain) :
    J (allSeamChart N endpoint chart hdisj a e.val p) =
      allSeamChart N' endpoint' chart' hdisj' (fun e => a e.val) e p := by
  by_cases ht : 0 ≤ p.val.2
  · rw [allSeamChart_nonneg N endpoint chart hdisj a e.val p ht, hJ,
      allSeamChart_nonneg N' endpoint' chart' hdisj' (fun e => a e.val) e p ht]
    exact congrArg (Quot.mk _) (hrad e _root_.Bool.false p.val.1 (1 + p.val.2) _)
  · rw [allSeamChart_neg N endpoint chart hdisj a e.val p (lt_of_not_ge ht), hJ,
      allSeamChart_neg N' endpoint' chart' hdisj' (fun e => a e.val) e p (lt_of_not_ge ht)]
    exact congrArg (Quot.mk _) (hrad e _root_.Bool.true ((a e.val).val p.val.1) (1 - p.val.2) _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.quotient_step_surviving_seam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.quotient_step_surviving_seam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.quotient_step_surviving_seam ``Submission.DifferentialGeometry.Topology.PairedBallGluing.quotient_step_surviving_seam

variable [Finite E]

theorem allCore_subset_seamCore :
    (allCore N endpoint chart hdisj : Set (Σ v, PuncturedFactor N endpoint chart v)) ⊆
      seamCore N endpoint chart hdisj s := by
  intro x hx hx'
  rcases hx' with hx' | hx'
  · exact hx (mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨false, hx'⟩⟩)
  · exact hx (mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨true, hx'⟩⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.allCore_subset_seamCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.allCore_subset_seamCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.allCore_subset_seamCore ``Submission.DifferentialGeometry.Topology.PairedBallGluing.allCore_subset_seamCore


omit [Finite E] in
theorem quotient_step_boundary_point
    (hrad : ∀ (e : {e // e ≠ s}) (b : Bool) (z : _root_.Metric.sphere (0 : E3) 1)
      (r : ℝ) (hr : r ∈ _root_.Set.Icc 1 2),
      H (Quot.mk _ ⟨endpoint e.val b,
        radialPoint N endpoint chart hdisj e.val b z r hr⟩) =
      ⟨endpoint' e b, radialPoint N' endpoint' chart' hdisj' e b z r hr⟩)
    (e : {e // e ≠ s}) (b : Bool) (z : _root_.Metric.sphere (0 : E3) 1) :
    H (Quot.mk _ ⟨endpoint e.val b, boundaryPoint N endpoint chart hdisj e.val b z⟩) =
      ⟨endpoint' e b, boundaryPoint N' endpoint' chart' hdisj' e b z⟩ := by
  simpa only [radialPoint_one] using hrad e b z 1 (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.quotient_step_boundary_point then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.quotient_step_boundary_point"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.quotient_step_boundary_point ``Submission.DifferentialGeometry.Topology.PairedBallGluing.quotient_step_boundary_point

theorem quotient_step_core_mem
    (hboundary : ∀ (e : {e // e ≠ s}) (b : Bool) (z : _root_.Metric.sphere (0 : E3) 1),
      H (Quot.mk _ ⟨endpoint e.val b, boundaryPoint N endpoint chart hdisj e.val b z⟩) =
        ⟨endpoint' e b, boundaryPoint N' endpoint' chart' hdisj' e b z⟩)
    (x : allCore N endpoint chart hdisj) :
    H (Quot.mk _ x.val) ∈ allCore N' endpoint' chart' hdisj' := by
  intro hx
  obtain ⟨e, hx⟩ := mem_iUnion.mp hx
  obtain ⟨b, z, hz⟩ := mem_iUnion.mp hx
  have heq : Quot.mk (seamRel N endpoint chart hdisj s (a s)) x.val =
      Quot.mk _ ⟨endpoint e.val b, boundaryPoint N endpoint chart hdisj e.val b z⟩ :=
    H.injective (hz.symm.trans (hboundary e b z).symm)
  have hxval := (quot_mk_eq_boundaryPoint_iff_of_ne N endpoint chart hdisj s (a s)
    (Ne.symm e.property) b z x.val).mp heq
  exact x.property (mem_iUnion.mpr ⟨e.val, mem_iUnion.mpr ⟨b, z, hxval.symm⟩⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.quotient_step_core_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.quotient_step_core_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.quotient_step_core_mem ``Submission.DifferentialGeometry.Topology.PairedBallGluing.quotient_step_core_mem

theorem quotient_step_seam_mem
    (hboundary : ∀ (e : {e // e ≠ s}) (b : Bool) (z : _root_.Metric.sphere (0 : E3) 1),
      H (Quot.mk _ ⟨endpoint e.val b, boundaryPoint N endpoint chart hdisj e.val b z⟩) =
        ⟨endpoint' e b, boundaryPoint N' endpoint' chart' hdisj' e b z⟩)
    (p : SelfAttachment.directSeamDomain) :
    H (seamChart N endpoint chart hdisj s (a s) p) ∈
      allCore N' endpoint' chart' hdisj' := by
  intro hx
  obtain ⟨e, hx⟩ := mem_iUnion.mp hx
  obtain ⟨b, z, hz⟩ := mem_iUnion.mp hx
  exact seamChart_ne_quot_mk_boundaryPoint N endpoint chart hdisj s (a s)
    (Ne.symm e.property) p b z (H.injective (hz.symm.trans (hboundary e b z).symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.quotient_step_seam_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.quotient_step_seam_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.quotient_step_seam_mem ``Submission.DifferentialGeometry.Topology.PairedBallGluing.quotient_step_seam_mem

variable {F K : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace K] (I : ModelWithCorners ℝ F K)
  [∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v)]
  [∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N' endpoint' chart' v)]
  [ChartedSpace K
    (Quot (fun x y => ∃ e : {e // e ≠ s},
      seamRel N' endpoint' chart' hdisj' e (a e.val) x y))]
  [IsManifold I ∞
    (Quot (fun x y => ∃ e : {e // e ≠ s},
      seamRel N' endpoint' chart' hdisj' e (a e.val) x y))]

include hJ in
theorem exists_smooth_quotient_step_atlas
    (hhcore : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (H ∘ seamCoreInclusion N endpoint chart hdisj s (a s)))
    (hhseam : IsLocalDiffeomorph IC (𝓡∂ 3) ∞
      (H ∘ seamChart N endpoint chart hdisj s (a s)))
    (hrad : ∀ (e : {e // e ≠ s}) (b : Bool) (z : _root_.Metric.sphere (0 : E3) 1)
      (r : ℝ) (hr : r ∈ _root_.Set.Icc 1 2),
      H (Quot.mk _ ⟨endpoint e.val b,
        radialPoint N endpoint chart hdisj e.val b z r hr⟩) =
      ⟨endpoint' e b, radialPoint N' endpoint' chart' hdisj' e b z r hr⟩)
    (htargetcore : IsLocalDiffeomorph (𝓡∂ 3) I ∞
      (allCoreInclusion N' endpoint' chart' hdisj' (fun e => a e.val)))
    (htargetseam : ∀ e, IsLocalDiffeomorph IC I ∞
      (allSeamChart N' endpoint' chart' hdisj' (fun e => a e.val) e)) :
    ∃ C : ChartedSpace K
      (Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e (a e) x y)),
      let _ := C
      IsManifold I ∞
        (Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e (a e) x y)) ∧
      IsLocalDiffeomorph (𝓡∂ 3) I ∞ (allCoreInclusion N endpoint chart hdisj a) ∧
      (∀ e, IsLocalDiffeomorph IC I ∞ (allSeamChart N endpoint chart hdisj a e)) ∧
      ∃ D : Diffeomorph I I
        (Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e (a e) x y))
        (Quot (fun x y => ∃ e : {e // e ≠ s},
          seamRel N' endpoint' chart' hdisj' e (a e.val) x y)) ∞,
        ∀ q, D q = J q := by
  have hboundary := quotient_step_boundary_point N endpoint chart hdisj a s
    N' endpoint' chart' hdisj' H hrad
  have hcoremem := quotient_step_core_mem N endpoint chart hdisj a s
    N' endpoint' chart' hdisj' H hboundary
  have hseammem := quotient_step_seam_mem N endpoint chart hdisj a s
    N' endpoint' chart' hdisj' H hboundary
  have hcore : IsLocalDiffeomorph (𝓡∂ 3) I ∞
      (J ∘ allCoreInclusion N endpoint chart hdisj a) := by
    let i : allCore N endpoint chart hdisj → seamCore N endpoint chart hdisj s :=
      fun x => ⟨x.val, allCore_subset_seamCore N endpoint chart hdisj s x.property⟩
    have hi : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ i := fun x =>
      DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
        (fun y => allCore_subset_seamCore N endpoint chart hdisj s y.property)
        (DifferentialGeometry.isLocalDiffeomorph_subtype_val
          (I := 𝓡∂ 3) (allCore N endpoint chart hdisj) x)
    have hcomp : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
        (fun x : allCore N endpoint chart hdisj => H (Quot.mk _ x.val)) :=
      DifferentialGeometry.isLocalDiffeomorph_comp (f := i)
        (g := H ∘ seamCoreInclusion N endpoint chart hdisj s (a s)) hhcore hi
    let g : allCore N endpoint chart hdisj → allCore N' endpoint' chart' hdisj' :=
      fun x => ⟨H (Quot.mk _ x.val), hcoremem x⟩
    have hg : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ g := fun x =>
      DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict hcoremem (hcomp x)
    have h := DifferentialGeometry.isLocalDiffeomorph_comp htargetcore hg
    have heq : allCoreInclusion N' endpoint' chart' hdisj' (fun e => a e.val) ∘ g =
        J ∘ allCoreInclusion N endpoint chart hdisj a := by
      funext x
      exact (hJ x.val).symm
    rwa [heq] at h
  have hseam : ∀ e, IsLocalDiffeomorph IC I ∞
      (J ∘ allSeamChart N endpoint chart hdisj a e) := by
    intro e
    by_cases he : e = s
    · subst e
      let g : SelfAttachment.directSeamDomain → allCore N' endpoint' chart' hdisj' :=
        fun p => ⟨H (seamChart N endpoint chart hdisj s (a s) p), hseammem p⟩
      have hg : IsLocalDiffeomorph IC (𝓡∂ 3) ∞ g := fun p =>
        DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict hseammem (hhseam p)
      have h := DifferentialGeometry.isLocalDiffeomorph_comp htargetcore hg
      have heq : allCoreInclusion N' endpoint' chart' hdisj' (fun e => a e.val) ∘ g =
          J ∘ allSeamChart N endpoint chart hdisj a s := by
        funext p
        exact (quotient_step_selected_seam N endpoint chart hdisj a s
          N' endpoint' chart' hdisj' H J hJ p).symm
      rwa [heq] at h
    · have heq : J ∘ allSeamChart N endpoint chart hdisj a e =
          allSeamChart N' endpoint' chart' hdisj' (fun e => a e.val) ⟨e, he⟩ := by
        funext p
        exact quotient_step_surviving_seam N endpoint chart hdisj a s
          N' endpoint' chart' hdisj' H J hJ hrad ⟨e, he⟩ p
      rw [heq]
      exact htargetseam ⟨e, he⟩
  let C := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := K) J
  let _ := C
  let _ := DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
    (I := I) (n := ∞) J
  refine ⟨C, inferInstance, ?_, ?_,
    DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph (I := I) (n := ∞) J,
    fun _ => rfl⟩
  · exact isLocalDiffeomorph_pullback_of_comp J _ hcore
  · intro e
    exact isLocalDiffeomorph_pullback_of_comp J _ (hseam e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_quotient_step_atlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_quotient_step_atlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_quotient_step_atlas ``Submission.DifferentialGeometry.Topology.PairedBallGluing.exists_smooth_quotient_step_atlas

end DifferentialGeometry.Topology.PairedBallGluing
