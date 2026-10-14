import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrectionPlacementArcs
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.RectangleArcPair
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34PlanarDiskBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem square_frontier_mem {p : ℝ × ℝ} :
    p ∈ frontier (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ↔
      (p.1 ∈ _root_.Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ ({0, 1} : Set ℝ)) ∨
        (p.1 ∈ ({0, 1} : Set ℝ) ∧ p.2 ∈ _root_.Set.Icc (0 : ℝ) 1) := by
  rw [frontier_prod_eq, isClosed_Icc.closure_eq, frontier_Icc (zero_le_one' ℝ)]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.square_frontier_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.square_frontier_mem target :: scope.openDecls } }

theorem IsPLHomeomorphOn.image_vertical_subarc_mem_nhdsWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {θ : ℝ × ℝ → E} {P B : Set E}
    (hθ : IsPLHomeomorphOn θ (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) P)
    (hB : θ '' frontier (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) = B)
    {r s a b : ℝ} (hr : r ∈ ({0, 1} : Set ℝ)) (has : a < s) (hsb : s < b)
    (ha : 0 ≤ a) (hb : b ≤ 1) :
    θ '' ({r} ×ˢ _root_.Set.Icc a b) ∈ 𝓝[B] (θ (r, s)) := by
  let Q := _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1
  let τ := Function.invFunOn θ Q
  have hs : s ∈ _root_.Set.Icc (0 : ℝ) 1 := ⟨ha.trans has.le, hsb.le.trans hb⟩
  have hrI : r ∈ _root_.Set.Icc (0 : ℝ) 1 := by rcases hr with rfl | rfl <;> norm_num
  have hleft : τ (θ (r, s)) = (r, s) := hθ.bijOn.invOn_invFunOn.1 ⟨hrI, hs⟩
  have hBP : B ⊆ P := by
    rw [← hB]
    exact (_root_.Set.image_mono isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset).trans
      hθ.image_eq.subset
  have hyp : θ (r, s) ∈ B := hB.subset ⟨(r, s), square_frontier_mem.mpr (Or.inr ⟨hr, hs⟩), rfl⟩
  have hcont := (hθ.symm.isPiecewiseAffineOn.continuousOn.mono hBP) _ hyp
  have hopen : IsOpen {p : ℝ × ℝ | |p.1 - r| < 1 / 2 ∧ p.2 ∈ _root_.Set.Ioo a b} :=
    (isOpen_lt (continuous_abs.comp (continuous_fst.sub continuous_const))
      continuous_const).inter (isOpen_Ioo.preimage continuous_snd)
  have hmem : τ (θ (r, s)) ∈ {p : ℝ × ℝ | |p.1 - r| < 1 / 2 ∧ p.2 ∈ _root_.Set.Ioo a b} := by
    rw [hleft]
    exact ⟨by norm_num, has, hsb⟩
  filter_upwards [hcont.preimage_mem_nhdsWithin (hopen.mem_nhds hmem),
    self_mem_nhdsWithin] with y hy hyB
  obtain ⟨p, hp, rfl⟩ := hB.symm.subset hyB
  have hpQ : p ∈ Q := isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset hp
  change |(τ (θ p)).1 - r| < 1 / 2 ∧ (τ (θ p)).2 ∈ _root_.Set.Ioo a b at hy
  have hpInv : τ (θ p) = p := hθ.bijOn.invOn_invFunOn.1 hpQ
  rw [hpInv] at hy
  have hpedge : p.1 ∈ ({0, 1} : Set ℝ) := by
    rcases square_frontier_mem.mp hp with h | h
    · rcases h.2 with hzero | hone
      · have he : p.2 = 0 := hzero
        linarith [hy.2.1]
      · have he : p.2 = 1 := hone
        linarith [hy.2.2]
    · exact h.1
  have hpr : p.1 = r := by
    rcases hpedge with hpzero | hpone <;> rcases hr with hrzero | hrone
    · exact hpzero.trans hrzero.symm
    · have he : p.1 - r = -1 := by rw [hpzero, hrone]; norm_num
      rw [he] at hy
      norm_num at hy
    · have he : p.1 - r = 1 := by rw [hpone, hrzero]; norm_num
      rw [he] at hy
      norm_num at hy
    · exact hpone.trans hrone.symm
  exact ⟨p, ⟨hpr, hy.2.1.le, hy.2.2.le⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_vertical_subarc_mem_nhdsWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_vertical_subarc_mem_nhdsWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_vertical_subarc_mem_nhdsWithin ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_vertical_subarc_mem_nhdsWithin

theorem IsPLHomeomorphOn.image_horizontal_subarc_mem_nhdsWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {θ : ℝ × ℝ → E} {P B : Set E}
    (hθ : IsPLHomeomorphOn θ (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) P)
    (hB : θ '' frontier (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) = B)
    {r s a b : ℝ} (hr : r ∈ ({0, 1} : Set ℝ)) (has : a < s) (hsb : s < b)
    (ha : 0 ≤ a) (hb : b ≤ 1) :
    θ '' (_root_.Set.Icc a b ×ˢ {r}) ∈ 𝓝[B] (θ (s, r)) := by
  have hswap : IsPLHomeomorphOn (Prod.swap : ℝ × ℝ → ℝ × ℝ)
      (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
      isPLBall_unit_square.isPolyhedron
      (isPiecewiseAffineOn_of_affine_of_isHPolytope
        (LinearEquiv.prodComm ℝ ℝ ℝ).toLinearMap.toAffineMap
        (isHPolytope_Icc.prod isHPolytope_Icc))
      ⟨fun _ hp => ⟨hp.2, hp.1⟩, Prod.swap_injective.injOn,
        fun p hp => ⟨p.swap, ⟨hp.2, hp.1⟩, Prod.swap_swap p⟩⟩
  have hswapFront : Prod.swap '' frontier (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
      frontier (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) :=
    hswap.image_frontier rfl isPLBall_unit_square.isPolyhedron.isClosed
      isPLBall_unit_square.isPolyhedron.isClosed
  have hB' : (θ ∘ Prod.swap) '' frontier (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) = B := by
    rw [_root_.Set.image_comp, hswapFront, hB]
  have h := (hswap.trans hθ).image_vertical_subarc_mem_nhdsWithin hB' hr has hsb ha hb
  change (θ ∘ Prod.swap) '' ({r} ×ˢ _root_.Set.Icc a b) ∈ 𝓝[B] (θ (s, r)) at h
  simpa only [_root_.Set.image_comp, _root_.Set.image_swap_prod] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_horizontal_subarc_mem_nhdsWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_horizontal_subarc_mem_nhdsWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_horizontal_subarc_mem_nhdsWithin ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_horizontal_subarc_mem_nhdsWithin

open _root_.Classical in
theorem exists_seam_correction_rectangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {A B : Set E} {δ ε : ℝ → E}
    (hδ : IsPLHomeomorphOn δ (_root_.Set.Icc 0 1) A) (hε : IsPLHomeomorphOn ε (_root_.Set.Icc 0 1) B)
    (hεzero : ε 0 = δ 0) (hεone : ε 1 = δ 1)
    (hcover : A ∪ B = (boundaryComplex 2 K).space) (hAB : A ∩ B = {δ 0, δ 1}) :
    ∃ (θ : ℝ × ℝ → E) (r s : ℝ),
      IsPLHomeomorphOn θ (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) K.space ∧
      θ (1 / 2, 0) = δ 0 ∧
      θ '' (_root_.Set.Icc (0 : ℝ) 1 ×ˢ {0}) =
        ε '' _root_.Set.Icc (0 : ℝ) (1 / 4) ∪ δ '' _root_.Set.Icc (0 : ℝ) (1 / 4) ∧
      θ '' (_root_.Set.Icc (0 : ℝ) (1 / 2) ×ˢ {0}) = ε '' _root_.Set.Icc (0 : ℝ) (1 / 4) ∧
      θ '' (_root_.Set.Icc (1 / 2 : ℝ) 1 ×ˢ {0}) = δ '' _root_.Set.Icc (0 : ℝ) (1 / 4) ∧
      θ '' (_root_.Set.Icc (0 : ℝ) 1 ×ˢ {1}) = δ '' _root_.Set.Icc (1 / 2 : ℝ) (3 / 4) ∧
      Disjoint (θ '' (_root_.Set.Icc (0 : ℝ) 1 ×ˢ {1})) ({δ 0, δ 1} : Set E) ∧
      θ '' (_root_.Set.Icc (1 / 4 : ℝ) (3 / 4) ×ˢ {0}) ∈
        𝓝[(boundaryComplex 2 K).space] (δ 0) ∧
      r ∈ ({0, 1} : Set ℝ) ∧ s ∈ _root_.Set.Ioo (0 : ℝ) 1 ∧ θ (r, s) = δ 1 ∧
      θ '' ({r} ×ˢ _root_.Set.Icc (s / 2) ((s + 1) / 2)) ∈
        𝓝[(boundaryComplex 2 K).space] (δ 1) := by
  obtain ⟨γ, hγ, -, hγmid, -, hγleft, hγright, hdis, hybot, hdisEnds⟩ :=
    exists_seam_arc_and_disjoint_compensation_arc hδ hε hεzero hεone hAB
  have hAK : A ⊆ (boundaryComplex 2 K).space := hcover ▸ _root_.Set.subset_union_left
  have hBK : B ⊆ (boundaryComplex 2 K).space := hcover ▸ _root_.Set.subset_union_right
  have hsmall : _root_.Set.Icc (0 : ℝ) (1 / 4) ⊆ _root_.Set.Icc (0 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hmid : _root_.Set.Icc (1 / 2 : ℝ) (3 / 4) ⊆ _root_.Set.Icc (0 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hfirst : γ '' _root_.Set.Icc (0 : ℝ) 1 ⊆ (boundaryComplex 2 K).space := by
    rw [hγ.image_eq]
    exact _root_.Set.union_subset ((_root_.Set.image_mono hsmall).trans (hε.image_eq.subset.trans hBK))
      ((_root_.Set.image_mono hsmall).trans (hδ.image_eq.subset.trans hAK))
  have hlast : δ '' _root_.Set.Icc (1 / 2 : ℝ) (3 / 4) ⊆ (boundaryComplex 2 K).space :=
    (_root_.Set.image_mono hmid).trans (hδ.image_eq.subset.trans hAK)
  have hlastBall : IsPLBall 1 (δ '' _root_.Set.Icc (1 / 2 : ℝ) (3 / 4)) :=
    (isPLBall_Icc (by norm_num : (1 / 2 : ℝ) < 3 / 4)).of_isPLHomeomorphOn
      (hδ.restrict isHPolytope_Icc.isPolyhedron hmid)
  obtain ⟨θ, hθ, hbottom, htop⟩ := exists_isPLHomeomorphOn_rectangle_map_ends
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) K hK
    hfirst hlastBall hlast hdis (by rw [hγ.image_eq]; exact hγ)
  have hbottomImage : θ '' (_root_.Set.Icc (0 : ℝ) 1 ×ˢ {0}) = γ '' _root_.Set.Icc (0 : ℝ) 1 := by
    rw [_root_.Set.prod_singleton, _root_.Set.image_image]
    exact _root_.Set.image_congr hbottom
  have hbottomSub (I : Set ℝ) (hI : I ⊆ _root_.Set.Icc (0 : ℝ) 1) :
      θ '' (I ×ˢ {0}) = γ '' I := by
    rw [_root_.Set.prod_singleton, _root_.Set.image_image]
    exact _root_.Set.image_congr (fun t ht => hbottom t (hI ht))
  have hbd : θ '' frontier (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
      (boundaryComplex 2 K).space := by
    obtain ⟨q, hq⟩ := isPLBall_unit_square
    rw [← hq.image_stdSimplexBoundary_eq_frontier_real_prod, ← _root_.Set.image_comp]
    exact (hq.trans hθ).image_stdSimplexBoundary_eq_boundaryComplex K rfl
  have hyK := hAK (hδ.bijOn.mapsTo (show (1 : ℝ) ∈ _root_.Set.Icc 0 1 by norm_num))
  obtain ⟨p, hp, hpY⟩ := hbd.symm.subset hyK
  have hpQ := isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset hp
  have hpzero : p.2 ≠ 0 := by
    intro h
    apply hybot
    rw [← hbottomImage]
    exact ⟨p, ⟨hpQ.1, h⟩, hpY⟩
  have hpone : p.2 ≠ 1 := by
    intro h
    apply (disjoint_left.mp hdisEnds) ?_ (by simp : δ 1 ∈ ({δ 0, δ 1} : Set E))
    rw [← htop]
    exact ⟨p, ⟨hpQ.1, h⟩, hpY⟩
  have hs : p.2 ∈ _root_.Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hpQ.2.1 hpzero.symm, lt_of_le_of_ne hpQ.2.2 hpone⟩
  have hr : p.1 ∈ ({0, 1} : Set ℝ) := by
    rcases square_frontier_mem.mp hp with h | h
    · exact False.elim (h.2.elim hpzero hpone)
    · exact h.1
  have hcore : θ (1 / 2, 0) = δ 0 := (hbottom _ (by norm_num)).trans hγmid
  refine ⟨θ, p.1, p.2, hθ, hcore, hbottomImage.trans hγ.image_eq,
    (hbottomSub _ (_root_.Set.Icc_subset_Icc le_rfl (by norm_num))).trans hγleft,
    (hbottomSub _ (_root_.Set.Icc_subset_Icc (by norm_num) le_rfl)).trans hγright, htop,
    htop.symm ▸ hdisEnds, ?_, hr, hs, hpY, ?_⟩
  · rw [← hcore]
    exact hθ.image_horizontal_subarc_mem_nhdsWithin hbd (by simp) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · rw [← hpY]
    exact hθ.image_vertical_subarc_mem_nhdsWithin hbd hr (by linarith [hs.1])
      (by linarith [hs.2]) (by linarith [hs.1]) (by linarith [hs.2])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_seam_correction_rectangle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_seam_correction_rectangle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_seam_correction_rectangle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_seam_correction_rectangle

end DifferentialGeometry.Topology.PiecewiseLinear
