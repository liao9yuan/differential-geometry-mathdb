import Submission.DifferentialGeometry.Geometry.Neck.FiniteFrontierEnd
import Submission.DifferentialGeometry.Geometry.Neck.SpatialFreshBand
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCoreCylinderAbsorption
import Batteries.Tactic.OpenPrivate

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private RecordedNeckSphere RecordedNeckSphere.map RecordedNeckSphere.range_map
  RecordedNeckSphere.mk NeckFrontierState NeckFrontierState.mk
  NeckFrontierState.exists_outward_graph_of_neck from
  Submission.DifferentialGeometry.Geometry.Neck.FiniteFrontierEnd

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ}

private theorem CapCore.exists_extension_of_spatial_neck_frontier
    {W : Set M} (cap : CapCore W)
    {x : M} (old : SpatialNeck g eps x) (a : ℝ) (ha : |a| ≤ 4)
    (hfront : frontier W = _root_.Set.range (fun q : Sphere 2 => old.map (q, a)))
    (heps : eps ≤ Classical.choose (exists_spatial_neck_level_graph_tolerance.{u}))
    (hepsstep : eps ≤ Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, 0}))
    (hneck : Nonempty (SpatialNeck g eps (old.map (old.center, a)))) :
    ∃ (V : Set M) (p : M) (nk : SpatialNeck g eps p)
      (A : PartialDiffeomorph IC I3 Cylinder M ∞),
      Nonempty (CapCore V) ∧ W ⊆ V ∧ closure (interior V) = V ∧
      frontier V = _root_.Set.range (fun q : Sphere 2 => nk.map (q, 3)) ∧
      p ∈ frontier W ∧
      _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ A.source ∧
      V = W ∪ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      frontier W = _root_.Set.range (fun q : Sphere 2 => A (q, 0)) ∧
      (∀ q : Sphere 2, A (q, 1) = nk.map (q, 3)) ∧
      A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ W = frontier W ∧
      nk.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (1 : ℝ) 2) ⊆ V \ W ∧
      V \ W ⊆ nk.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-4 : ℝ) 4) := by
  classical
  have hW := cap.closure_interior_carrier
  let sphere : RecordedNeckSphere g eps :=
    RecordedNeckSphere.mk x old a ha (Diffeomorph.refl I2 (Sphere 2) ∞)
  let S : NeckFrontierState g eps Unit :=
    NeckFrontierState.mk W cap.isCompact_carrier cap.nonempty_carrier hW Finset.univ
      (fun _ => sphere)
      (by simpa only [Finset.mem_univ, _root_.Set.iUnion_true, _root_.Set.iUnion_const,
        RecordedNeckSphere.range_map] using hfront)
      (by intro i _ j _ hij; exact (hij (Subsingleton.elim _ _)).elim)
  obtain ⟨p, nk, f, eta, hf, hfsmall, hfzero, hmap, hout, hpoint⟩ :=
    NeckFrontierState.exists_outward_graph_of_neck g eps Unit S Unit.unit
      (Finset.mem_univ _) heps hneck
  have hactive : _root_.Set.range (fun q => nk.map (q, f q)) = frontier W := by
    rw [hfront]
    ext y
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨eta q, (hmap q).symm.trans hq⟩
    · rintro ⟨q, hq⟩
      refine ⟨eta.symm q, (hmap _).trans ?_⟩
      change old.map (eta (eta.symm q), a) = y
      rw [eta.apply_symm_apply]
      exact hq
  have hstep :=
    (Classical.choose_spec (exists_spatial_neck_finite_frontier_step_tolerance.{u, 0})).2
  have hfront' : frontier W = _root_.Set.range (fun q => nk.map (q, f q)) ∪
      ⋃ i : PEmpty, _root_.Set.range (fun q : Sphere 2 => (PEmpty.elim i : SpatialNeck g eps p).map (q, 0)) := by
    simpa only [_root_.Set.iUnion_of_empty, _root_.Set.union_empty] using hactive.symm
  rcases hstep eps hepsstep M g p nk PEmpty (fun _ => p) (fun i => PEmpty.elim i)
    (fun _ => 0) (fun i => PEmpty.elim i) (fun i => PEmpty.elim i)
    f hf hfsmall hfzero W hW hfront' (fun i => PEmpty.elim i) hout with ho | hr
  · obtain ⟨A, hA, hformula, hzero, hone, hcompact, hinter, hregular, hfrontV, hfresh⟩ := ho
    have hfrontA : frontier W = _root_.Set.range (fun q : Sphere 2 => A (q, 0)) := by
      rw [← hactive]
      congr 1
      exact (funext hzero).symm
    have hside (q : Sphere 2) (t : ℝ) (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1)
        (hxW : A (q, t) ∈ W) : t = 0 := by
      have hxF : A (q, t) ∈ _root_.Set.range (fun q => nk.map (q, f q)) :=
        hinter ▸ (show A (q, t) ∈ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ W from
          ⟨⟨(q, t), ⟨mem_univ _, ht⟩, rfl⟩, hxW⟩)
      obtain ⟨r, hr⟩ := hxF
      have he : A (q, t) = A (r, 0) := hr.symm.trans (hzero r).symm
      exact congrArg Prod.snd (A.injOn (hA ⟨mem_univ _, ht⟩)
        (hA ⟨mem_univ _, by norm_num⟩) he)
    let V := W ∪ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)
    refine ⟨V, p, nk, A, cap.nonempty_union_cylinder A hA hfrontA hside,
      _root_.Set.subset_union_left, hregular, ?_, ?_, hA, rfl, hfrontA, hone,
      hinter.trans hactive, ?_, ?_⟩
    · simpa only [_root_.Set.iUnion_of_empty, _root_.Set.empty_union] using hfrontV
    · change p ∈ _root_.Set.range (RecordedNeckSphere.map g eps sphere) at hpoint
      rw [RecordedNeckSphere.range_map] at hpoint
      exact hfront.symm ▸ hpoint
    · intro y hy
      exact ⟨Or.inr (hfresh hy).1, (hfresh hy).2⟩
    · rintro y ⟨hyV, hyW⟩
      rcases hyV with hyW' | ⟨⟨q, t⟩, ht, hty⟩
      · exact (hyW hyW').elim
      · refine ⟨(q, f q + (3 - f q) * t), ⟨mem_univ _, ?_⟩,
          (hformula q t).symm.trans hty⟩
        constructor <;> nlinarith [ht.2.1, ht.2.2, (abs_lt.mp (hfsmall q)).1,
          (abs_lt.mp (hfsmall q)).2]
  · obtain ⟨i, _⟩ := hr
    exact PEmpty.elim i

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapCore.exists_extension_of_spatial_neck_frontier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapCore.exists_extension_of_spatial_neck_frontier target :: scope.openDecls } }


private structure CapNeckRegion where
  region : Set M
  cap : CapCore region
  point : M
  neck : SpatialNeck g eps point
  level : ℝ
  level_bound : |level| ≤ 4
  frontier_eq : frontier region = _root_.Set.range (fun q : Sphere 2 => neck.map (q, level))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapNeckRegion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapNeckRegion target :: scope.openDecls } }

theorem exists_spatial_neck_cap_frontier_non_neck_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M]
        (g : SmoothRiemannianMetric I3 M) (W : Set M),
        CapCore W →
        ∀ (x : M) (initial : SpatialNeck g eps x) (a : ℝ), |a| ≤ 4 →
          frontier W = _root_.Set.range (fun q : Sphere 2 => initial.map (q, a)) →
          ∃ (K : Set M) (p : M) (neck : SpatialNeck g eps p) (level : ℝ),
            Nonempty (CapCore K) ∧ W ⊆ K ∧ closure (interior K) = K ∧
            |level| ≤ 4 ∧ frontier K = _root_.Set.range (fun q : Sphere 2 => neck.map (q, level)) ∧
            ¬ Nonempty (SpatialNeck g eps (neck.map (neck.center, level))) := by
  classical
  let eta₁ := Classical.choose (exists_spatial_neck_level_graph_tolerance.{u})
  let eta₂ := Classical.choose (exists_spatial_neck_finite_frontier_step_tolerance.{u, 0})
  have hη₁ : 0 < eta₁ :=
    (Classical.choose_spec (exists_spatial_neck_level_graph_tolerance.{u})).1
  have hη₂ : 0 < eta₂ :=
    (Classical.choose_spec (exists_spatial_neck_finite_frontier_step_tolerance.{u, 0})).1
  refine ⟨min eta₁ (_root_.Min.min eta₂ (1 / 156000)), lt_min hη₁ (lt_min hη₂ (by norm_num)), ?_⟩
  intro eps heps M _ _ _ _ _ g W cap x initial a ha hfront
  have heps₁ : eps ≤ eta₁ := heps.trans (min_le_left _ _)
  have heps₂ : eps ≤ eta₂ := heps.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hepsrec : eps ≤ 1 / 156000 := heps.trans ((min_le_right _ _).trans (min_le_right _ _))
  let S₀ : CapNeckRegion (g := g) (eps := eps) :=
    ⟨W, cap, x, initial, a, ha, hfront⟩
  by_contra hstop
  have hneck (T : CapNeckRegion (g := g) (eps := eps)) (hWT : W ⊆ T.region) :
      Nonempty (SpatialNeck g eps (T.neck.map (T.neck.center, T.level))) := by
    by_contra hn
    exact hstop ⟨T.region, T.point, T.neck, T.level, ⟨T.cap⟩, hWT, T.cap.closure_interior_carrier,
      T.level_bound, T.frontier_eq, hn⟩
  let State := {T : CapNeckRegion (g := g) (eps := eps) // W ⊆ T.region}
  have hnext (T : State) :
      ∃ U : State, T.val.region ⊆ U.val.region ∧
        ∃ (p : M) (nk : SpatialNeck g eps p),
          nk.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (1 : ℝ) 2) ⊆ U.val.region \ T.val.region := by
    obtain ⟨V, p, nk, A, hcap, hsub, hregular, hfrontier, _, _, _, _, _, _, hband, _⟩ :=
      T.val.cap.exists_extension_of_spatial_neck_frontier T.val.neck
        T.val.level T.val.level_bound T.val.frontier_eq heps₁ heps₂ (hneck T.val T.property)
    let U : CapNeckRegion (g := g) (eps := eps) :=
      ⟨V, hcap.some, p, nk, 3, by norm_num, hfrontier⟩
    exact ⟨⟨U, T.property.trans hsub⟩, hsub, p, nk, hband⟩
  choose next hstep using hnext
  let seq : ℕ → State := fun n => next^[n] ⟨S₀, subset_rfl⟩
  have hseq (n : ℕ) : seq (n + 1) = next (seq n) := Function.iterate_succ_apply' _ _ _
  have hmono : Monotone (fun n => (seq n).val.region) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hseq]
    exact (hstep (seq n)).1
  have hband (n : ℕ) : ∃ (p : M) (nk : SpatialNeck g eps p),
      nk.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (1 : ℝ) 2) ⊆ (seq (n + 1)).val.region \ (seq n).val.region := by
    rw [hseq]
    exact (hstep (seq n)).2
  choose point neck hfresh using hband
  exact not_forall_spatial_neck_unit_band_subset_sdiff g isCompact_univ hepsrec point neck
    (fun _ => _root_.Set.mem_univ _) (fun n => (seq n).val.region) hmono hfresh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_cap_frontier_non_neck_tolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_cap_frontier_non_neck_tolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_cap_frontier_non_neck_tolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_cap_frontier_non_neck_tolerance

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
