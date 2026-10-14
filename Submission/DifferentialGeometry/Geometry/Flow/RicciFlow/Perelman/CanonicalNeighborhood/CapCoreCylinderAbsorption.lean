import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CapCylinder
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.BallComplementCylinder
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure
import Submission.DifferentialGeometry.Topology.OpenPartialHomeomorph.CapFilling
import Submission.DifferentialGeometry.Topology.Diffeomorph.FiberwiseAffine

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [T2Space M]

theorem CapCore.nonempty_union_cylinder
    {X : Set M} (cap : CapCore X) (T : PartialDiffeomorph IC I3 Cylinder M ∞)
    (hT : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ T.source)
    (hfront : frontier X = _root_.Set.range (fun q : Sphere 2 => T (q, 0)))
    (hside : ∀ q : Sphere 2, ∀ a ∈ _root_.Set.Icc (0 : ℝ) 1, T (q, a) ∈ X → a = 0) :
    Nonempty (CapCore (X ∪ T '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1))) := by
  cases cap with
  | ball C hC hX =>
    have hboundary : C '' _root_.Metric.sphere (0 : ThreeSpace) 1 = _root_.Set.range (fun q : Sphere 2 => T (q, 0)) := by
      rw [← hX] at hfront
      rw [← C.image_frontier_of_isCompact (_root_.ProperSpace.isCompact_closedBall _ _) hC,
        frontier_closedBall _ one_ne_zero] at hfront
      exact hfront
    obtain ⟨B, hB, hBi, _⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_ball_and_cylinder_eqOn_neighborhoods
        C T hC hT hboundary (fun q a ha h => hside q a ha (hX ▸ h))
    exact ⟨CapCore.ball B hB (hX ▸ hBi)⟩
  | projective Z pr b hb P hP hX =>
    have hb1 : _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ b.source :=
      (_root_.Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)).trans hb
    have hK : IsCompact (b '' Metric.ball (0 : ThreeSpace) 1)ᶜ :=
      (b.toOpenPartialHomeomorph.isOpen_image_of_subset_source _root_.Metric.isOpen_ball
        (ball_subset_closedBall.trans hb1)).isClosed_compl.isCompact
    have hboundary : P '' (b '' _root_.Metric.sphere (0 : ThreeSpace) 1) = _root_.Set.range (fun q : Sphere 2 => T (q, 0)) := by
      rw [DifferentialGeometry.Topology.Manifold.image_sphere_eq_frontier_of_ball_complement
        b P hb1 hK hP, hX, hfront]
    obtain ⟨B, F, hF, hBs, hBi, _, _, _⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_ball_complement_chart_of_ball_complement_and_cylinder
        b P T hb1 hP hT hboundary (fun q a ha h => hside q a ha (hX ▸ h))
    let D : ThreeSpace ≃ₘ[ℝ] ThreeSpace :=
      (LinearEquiv.smulOfNeZero ℝ ThreeSpace (1 / 2 : ℝ) (by norm_num)).toContinuousLinearEquiv.toDiffeomorph
    let b' := (D.toPartialDiffeomorph.trans F.toPartialDiffeomorph).trans b
    have hb' : _root_.Metric.closedBall (0 : ThreeSpace) 2 ⊆ b'.source := by
      intro z hz
      refine ⟨⟨mem_univ _, _root_.Set.mem_univ _⟩, hb1 ?_⟩
      apply hF.subset
      refine ⟨(1 / 2 : ℝ) • z, ?_, rfl⟩
      rw [mem_closedBall_zero_iff, norm_smul]
      have hn := mem_closedBall_zero_iff.mp hz
      norm_num
      linarith
    have hball : b' '' Metric.ball (0 : ThreeSpace) 1 =
        (b ∘ F) '' Metric.ball (0 : ThreeSpace) (1 / 2) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨(1 / 2 : ℝ) • z, ?_, rfl⟩
        rw [mem_ball_zero_iff, norm_smul]
        have hn := mem_ball_zero_iff.mp hz
        norm_num
        linarith
      · rintro ⟨z, hz, rfl⟩
        refine ⟨(2 : ℝ) • z, ?_, ?_⟩
        · rw [mem_ball_zero_iff, norm_smul]
          have hn := mem_ball_zero_iff.mp hz
          norm_num
          linarith
        · change b (F ((1 / 2 : ℝ) • ((2 : ℝ) • z))) = b (F z)
          rw [smul_smul]
          norm_num
    exact ⟨CapCore.projective Z pr b' hb' B (hball.symm ▸ hBs) (hball.symm ▸ hX ▸ hBi)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapCore.nonempty_union_cylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapCore.nonempty_union_cylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapCore.nonempty_union_cylinder ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapCore.nonempty_union_cylinder

theorem CapCore.subset_or_nonempty_union_cylinder_of_frontier
    {K : Set M} (cap : CapCore K)
    (A : PartialDiffeomorph IC I3 Cylinder M ∞)
    (hA : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ A.source)
    (hfront : frontier K = _root_.Set.range (fun q : Sphere 2 => A (q,1))) :
    A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ K ∨
      Nonempty (CapCore (K ∪ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1))) ∧
        K ∩ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = _root_.Set.range (fun q : Sphere 2 => A (q,1)) ∧
        frontier (K ∪ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) =
          range (fun q : Sphere 2 => A (q,0)) := by
  let L := A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)
  have hLc : IsCompact L := (isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc).image_of_continuousOn
    (A.contMDiffOn_toFun.continuousOn.mono hA)
  have hLr : closure (interior L) = L := by
    apply A.toOpenPartialHomeomorph.closure_interior_image_of_subset_source hA _ hLc.isClosed
    rw [interior_prod_eq,interior_univ,interior_Icc,closure_prod_eq,closure_univ,closure_Ioo zero_ne_one]
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) zero_le_one)
  have hLint : IsPreconnected (interior L) := by
    have hi : interior L = A '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (0 : ℝ) 1) := by
      have hh := A.toOpenPartialHomeomorph.image_interior_of_subset_source hA
      change A '' interior (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = interior L at hh
      rw [interior_prod_eq, interior_univ, interior_Icc] at hh
      exact hh.symm
    rw [hi]
    exact (isPreconnected_univ.prod isPreconnected_Ioo).image _
      (A.contMDiffOn_toFun.continuousOn.mono ((_root_.Set.prod_mono subset_rfl _root_.Set.Ioo_subset_Icc_self).trans hA))
  have hends : frontier L = _root_.Set.range (fun q : Sphere 2 => A (q,1)) ∪
      range (fun q : Sphere 2 => A (q,0)) := by
    have h := A.toOpenPartialHomeomorph.image_frontier_of_subset_source hA
      (isClosed_univ.prod isClosed_Icc) hLc.isClosed
    change A '' frontier (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = frontier L at h
    rw [frontier_univ_prod_eq,frontier_Icc zero_le_one] at h
    rw [← h]
    ext y
    constructor
    · rintro ⟨⟨q,t⟩,⟨_,ht⟩,rfl⟩
      rcases ht with ht | ht
      · have ht : t = 0 := ht
        subst t
        exact Or.inr (_root_.Set.mem_range_self q)
      · have ht : t = 1 := ht
        subst t
        exact Or.inl (_root_.Set.mem_range_self q)
    · rintro (⟨q,rfl⟩ | ⟨q,rfl⟩)
      · exact ⟨(q,1),⟨mem_univ _,Or.inr rfl⟩,rfl⟩
      · exact ⟨(q,0),⟨mem_univ _,Or.inl rfl⟩,rfl⟩
  have hdis : Disjoint (_root_.Set.range (fun q : Sphere 2 => A (q,1)))
      (_root_.Set.range (fun q : Sphere 2 => A (q,0))) := by
    rw [_root_.Set.disjoint_left]
    rintro y ⟨q,hq⟩ ⟨r,hr⟩
    have hh := congrArg Prod.snd (A.injOn (hA ⟨mem_univ _,by norm_num⟩)
      (hA ⟨mem_univ _,by norm_num⟩) (hq.trans hr.symm))
    norm_num at hh
  have hclosed : IsClosed (_root_.Set.range (fun q : Sphere 2 => A (q,0))) :=
    (isCompact_range (A.contMDiffOn_toFun.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) (fun q => hA ⟨mem_univ _,by norm_num⟩))).isClosed
  let shift : Cylinder ≃ₜ Cylinder :=
    { toFun := fun q => (q.1,1+q.2)
      invFun := fun q => (q.1,q.2-1)
      left_inv := by intro q; ext <;> simp
      right_inv := by intro q; ext <;> simp
      continuous_toFun := continuous_fst.prodMk (continuous_const.add continuous_snd)
      continuous_invFun := continuous_fst.prodMk (continuous_snd.sub continuous_const) }
  let T := shift.transOpenPartialHomeomorph A.toOpenPartialHomeomorph
  have hT0 (q : Sphere 2) : T (q,0) = A (q,1) := by change A (q,1+0)=_; rw [add_zero]
  have hTs (q : Sphere 2) : (q,0) ∈ T.source := by
    change (q,1+0) ∈ A.source
    rw [add_zero]
    exact hA ⟨mem_univ _,by norm_num⟩
  rcases DifferentialGeometry.Topology.subset_or_fill_of_shared_cylinder_boundary T hTs
      hLr cap.closure_interior_carrier hLint hclosed
      (by simpa only [hT0] using hends)
      (by simpa only [hT0] using hfront)
      (by simpa only [hT0] using hdis) with hsub | ⟨hinter,_,hunion,_⟩
  · exact Or.inl hsub
  · right
    let D : Cylinder ≃ₘ⟮IC,IC⟯ Cylinder :=
      Diffeomorph.fiberwiseAffine (fun _ => (1:ℝ)) (fun _ => (-1:ℝ))
        contMDiff_const contMDiff_const (fun _ => by norm_num)
    let B := D.toPartialDiffeomorph.trans A
    have hB (q : Sphere 2) (t : ℝ) : B (q,t) = A (q,1-t) := by
      change A (q,1+(-1)*t) = A (q,1-t)
      have he : (1 : ℝ) + (-1) * t = 1 - t := by ring
      rw [he]
    have hBs : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ B.source := by
      rintro ⟨q,t⟩ ⟨_,ht⟩
      refine ⟨mem_univ _, hA ?_⟩
      change (q, 1 + (-1) * t) ∈ _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1
      exact ⟨mem_univ _, by constructor <;> linarith [ht.1, ht.2]⟩
    have hBi : B '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = L := by
      ext y
      constructor
      · rintro ⟨⟨q,t⟩,⟨_,ht⟩,rfl⟩
        exact ⟨(q,1-t),⟨mem_univ _,by constructor <;> linarith [ht.1,ht.2]⟩,(hB q t).symm⟩
      · rintro ⟨⟨q,t⟩,⟨_,ht⟩,rfl⟩
        refine ⟨(q,1-t),⟨mem_univ _,by constructor <;> linarith [ht.1,ht.2]⟩,?_⟩
        rw [hB,sub_sub_cancel]
    have hfrontB : frontier K = _root_.Set.range (fun q : Sphere 2 => B (q,0)) := by
      simpa only [hB,sub_zero] using hfront
    have hside (q : Sphere 2) (t : ℝ) (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) (hq : B (q,t) ∈ K) : t = 0 := by
      have hmem : B (q,t) ∈ K ∩ L := ⟨hq,hBi ▸ _root_.Set.mem_image_of_mem B ⟨mem_univ _,ht⟩⟩
      have hf := hinter ▸ hmem
      obtain ⟨z,hz⟩ := hf
      change T (z,0) = B (q,t) at hz
      rw [hT0] at hz
      have he : A (z,1) = A (q,1-t) := hz.trans (hB q t)
      have hh := congrArg Prod.snd (A.injOn (hA ⟨mem_univ _,by norm_num⟩)
        (hA ⟨mem_univ _,by constructor <;> linarith [ht.1,ht.2]⟩) he)
      linarith
    have hc := cap.nonempty_union_cylinder B hBs hfrontB hside
    rw [hBi] at hc
    refine ⟨hc, ?_, ?_⟩
    · simpa only [hT0] using hinter
    · simpa only [_root_.Set.union_comm] using hunion

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapCore.subset_or_nonempty_union_cylinder_of_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapCore.subset_or_nonempty_union_cylinder_of_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapCore.subset_or_nonempty_union_cylinder_of_frontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapCore.subset_or_nonempty_union_cylinder_of_frontier


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
