import Batteries.Tactic.OpenPrivate
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.BaseHornMetricEvent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open private normalized_neck_scalar_bounds_of_small reparametrized_prefix_scalar_le from
  Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornFirstScalarLevel

open private scalar_le_on_retainedCore_of_truncated_bound from
  Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornFirstScalarLevel

open private exists_common_deep_coordinates_after_rescaling
  scalar_le_on_rescaled_reparametrized_truncatedRegion exists_oriented_horn_neck_data_of_matching
  exists_finite_oriented_neck_data_of_chosen_family from
  Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.BaseHornMetricEvent

set_option autoImplicit false

section

open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

def FineCutNecks (εc Qc : ℝ) : Prop :=
  ∀ (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (x : D.slab.terminalRegularOpen),
    x ∈ interior (_root_.Set.range fun p : HalfNeckCylinder => P.horn c e p.1) →
    Qc ≤ metricScalarAt D.terminal.metric x →
    ∃ (δ : ℝ) (k : ℕ) (N : NormalizedNeck D.terminal.metric δ k),
      N.center = x ∧ δ ≤ εc ∧ ⌊εc⁻¹⌋₊ + 1 ≤ k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.FineCutNecks then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.FineCutNecks"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.FineCutNecks ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.FineCutNecks

theorem exists_fine_neck_at_horn_first_scalar_level {εc Qc : ℝ} (hfine : P.FineCutNecks εc Qc)
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {Q : ℝ} (hQ : Λ * (P.coreRadius ^ 2)⁻¹ < Q) (hQc : Qc ≤ Q) :
    ∃ t : ℝ, 0 < t ∧ ∃ y : Sphere 2, ∃ δ : ℝ, ∃ k : ℕ,
      ∃ N : NormalizedNeck D.terminal.metric δ k,
        N.center = P.horn c e (y, t) ∧ N.scale = Q ∧
        δ ≤ εc ∧ ⌊εc⁻¹⌋₊ + 1 ≤ k ∧
        (∀ s ∈ _root_.Set.Ico 0 t, ∀ z : Sphere 2,
          metricScalarAt D.terminal.metric (P.horn c e (z, s)) < Q) ∧
        ∀ z : Sphere 2, metricScalarAt D.terminal.metric (P.horn c e (z, t)) ≤ Q := by
  obtain ⟨t, ht, y, heq, hbefore, hlevel⟩ := P.exists_horn_first_scalar_level c e hQ
  have hsub : P.horn c e '' (_root_.Set.univ ×ˢ _root_.Set.Ioi (0 : ℝ)) ⊆
      range (fun p : HalfNeckCylinder => P.horn c e p.val) := by
    rintro x ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp.2.le⟩, rfl⟩
  have hin : P.horn c e (y, t) ∈
      interior (_root_.Set.range (fun p : HalfNeckCylinder => P.horn c e p.val)) :=
    interior_maximal hsub (P.isOpen_positive_horn c e) ⟨(y, t), ⟨mem_univ _, ht⟩, rfl⟩
  obtain ⟨δ, k, N, hcenter, hδ, hk⟩ := hfine c e _ hin (hQc.trans heq.ge)
  refine ⟨t, ht, y, δ, k, N, hcenter, ?_, hδ, hk, hbefore, hlevel⟩
  rw [N.scale_scalar, hcenter, heq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.exists_fine_neck_at_horn_first_scalar_level then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.exists_fine_neck_at_horn_first_scalar_level"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.exists_fine_neck_at_horn_first_scalar_level ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.exists_fine_neck_at_horn_first_scalar_level

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

noncomputable section

open _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u


private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instConnectedSpaceElemEuclideanSpaceRealFinHAddNatOfNatSphere : ConnectedSpace (Sphere 2) :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instConnectedSpaceElemEuclideanSpaceRealFinHAddNatOfNatSphere
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instConnectedSpaceElemEuclideanSpaceRealFinHAddNatOfNatSphere target :: scope.openDecls } }

theorem exists_horn_first_scalar_level_inner_scalar_bound_tolerance_of_fineCutNecks :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {εc Qc : ℝ}, 0 < εc → εc ≤ ε → P.FineCutNecks εc Qc →
        ∀ (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
          {Q : ℝ}, 2 * (Λ * (P.coreRadius ^ 2)⁻¹) < Q → Qc ≤ Q →
          ∃ (t : ℝ), 0 < t ∧ ∃ (y : Sphere 2) (δ : ℝ) (k : ℕ)
            (N : NormalizedNeck D.terminal.metric δ k),
            N.center = P.horn c e (y,t) ∧ N.scale = Q ∧ δ ≤ εc ∧
            ⌊εc⁻¹⌋₊ + 1 ≤ k ∧
            (∀ s ∈ _root_.Set.Ico 0 t, ∀ z : Sphere 2,
              metricScalarAt D.terminal.metric (P.horn c e (z,s)) < Q) ∧
            (∀ s ∈ _root_.Set.Icc 0 t, ∀ z : Sphere 2,
              metricScalarAt D.terminal.metric (P.horn c e (z,s)) ≤ Q) ∧
            ∃ Θ : neckCentralOpen δ → positiveHornDomain,
              _root_.Manifold.IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ ∧
              (∀ z, P.horn c e (Θ z).val =
                N.chart (TopologicalSpace.Opens.inclusion (neckCentralOpen_le_buffer δ) z)) ∧
              ∃ (p : ComplementPair (_root_.Set.range (fun q : Sphere 2 => Θ ⟨(q,0),_root_.Set.mem_univ _,
                    neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)))
                (R : ℝ), 0 < R ∧
                (closure p.left = p.left ∪ _root_.Set.range (fun q : Sphere 2 => Θ ⟨(q,0),_root_.Set.mem_univ _,
                    neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)) ∧
                (closure p.right = p.right ∪ _root_.Set.range (fun q : Sphere 2 => Θ ⟨(q,0),_root_.Set.mem_univ _,
                    neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)) ∧
                IsCompact (closure ((Subtype.val : positiveHornDomain → NeckCylinder) '' p.left)) ∧
                (∀ q : positiveHornDomain, q.val.2 < Real.exp (-R) → q ∈ p.left) ∧
                (∀ q : positiveHornDomain, Real.exp R < q.val.2 → q ∈ p.right) ∧
                ∀ x ∈ closure p.left,
                  metricScalarAt D.terminal.metric (P.horn c e x.val) ≤ 3 * Q := by
  obtain ⟨eta,heta,hseparate⟩ := exists_horn_neck_end_separation_tolerance
  refine ⟨min eta (1 / 8646),lt_min heta (by norm_num),?_⟩
  intro D ε Λ P hε εc Qc hεc hεcε hfine c e Q hQ hQc
  have hεsmall : ε ≤ 1 / 8646 := hε.trans (min_le_right _ _)
  have hεeta : ε ≤ eta := hε.trans (min_le_left _ _)
  have hbase : 0 < Λ * (P.coreRadius ^ 2)⁻¹ :=
    mul_pos (zero_lt_one.trans_le P.Lambda_ge_one) (inv_pos.mpr (sq_pos_of_pos P.coreRadius_pos))
  have hQpos : 0 < Q := by linarith
  have hε1 : 1 ≤ ε⁻¹ := ((one_lt_inv₀ P.epsilon_pos).mpr (by linarith : ε < 1)).le
  have hfloor : 1 ≤ ⌊ε⁻¹⌋₊ := Nat.le_floor (by exact_mod_cast hε1)
  have hinv : ε⁻¹ ≤ εc⁻¹ := inv_anti₀ hεc hεcε
  have hfloorc : ⌊ε⁻¹⌋₊ ≤ ⌊εc⁻¹⌋₊ := Nat.floor_mono hinv
  obtain ⟨t,ht,y,δ,k,N,hcenter,hscale,hδ,hk,hbefore,hlevel⟩ :=
    P.exists_fine_neck_at_horn_first_scalar_level hfine c e (Q := Q) (by linarith) hQc
  have hk2 : 2 ≤ k := by omega
  have hδε : δ ≤ ε := hδ.trans hεcε
  have hkε : ⌈ε⁻¹⌉₊ ≤ k := (Nat.ceil_le_floor_add_one ε⁻¹).trans (by omega)
  have hδsmall : δ ≤ 1 / 8646 := hδε.trans hεsmall
  have hNscale : Λ * (P.coreRadius ^ 2)⁻¹ < (1 - 4323 * δ) * N.scale := by
    rw [hscale]
    nlinarith [mul_le_mul_of_nonneg_right hδsmall hQpos.le]
  have hNpos : N.center ∈ P.horn c e '' (_root_.Set.univ ×ˢ _root_.Set.Ioi (0 : ℝ)) := by
    rw [hcenter]
    exact ⟨(y,t),⟨mem_univ _,ht⟩,rfl⟩
  obtain ⟨Θ,hΘ,hmap⟩ := P.exists_neck_coordinates_in_horn_of_base_scalar_bound c e N
    hk2 (by linarith) hNpos hNscale
  obtain ⟨p,R,hR,hfrontl,hfrontr,hcll,hclr,hfullcompact,hcompact,hlo,hhi,hband⟩ :=
    hseparate P hεeta c e N hδε hkε Θ hΘ hmap
  have hprefix : ∀ s ∈ _root_.Set.Icc 0 t, ∀ z : Sphere 2,
      metricScalarAt D.terminal.metric (P.horn c e (z,s)) ≤ Q := by
    intro s hs z
    rcases hs.2.eq_or_lt with rfl | hlt
    · exact hlevel z
    · exact (hbefore s ⟨hs.1,hlt⟩ z).le
  let S := _root_.Set.range (fun q : Sphere 2 => Θ ⟨(q,0),_root_.Set.mem_univ _,
    neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)
  have hSbound : ∀ x ∈ S, metricScalarAt D.terminal.metric (P.horn c e x.val) ≤ 3 * Q / 2 := by
    rintro x ⟨z,rfl⟩
    rw [hmap]
    have hb := (normalized_neck_scalar_bounds_of_small N hk2 hδsmall
      (TopologicalSpace.Opens.inclusion (neckCentralOpen_le_buffer δ)
        ⟨(z,0),_root_.Set.mem_univ _,neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)
      (by change -δ⁻¹ ≤ 0 ∧ 0 ≤ δ⁻¹; constructor <;> linarith [inv_pos.mpr N.delta_pos])).2
    simpa only [hscale] using hb
  refine ⟨t,ht,y,δ,k,N,hcenter,hscale,hδ,hk,hbefore,hprefix,Θ,hΘ,hmap,
    p,R,hR,hcll,hclr,hfullcompact,hlo,hhi,?_⟩
  intro x hx
  rw [hcll] at hx
  rcases hx with hx | hx
  · by_contra hnot
    have hxhigh : 3 * Q < metricScalarAt D.terminal.metric (P.horn c e x.val) := lt_of_not_ge hnot
    have hxpos : P.horn c e x.val ∈ P.horn c e '' (_root_.Set.univ ×ˢ _root_.Set.Ioi (0 : ℝ)) :=
      ⟨x.val,x.property,rfl⟩
    have hxin : P.horn c e x.val ∈
        interior (_root_.Set.range (fun q : HalfNeckCylinder => P.horn c e q.val)) := by
      apply (P.isOpen_positive_horn c e).subset_interior_iff.mpr ?_ hxpos
      rintro z ⟨q,hq,rfl⟩
      exact ⟨⟨q,hq.2.le⟩,rfl⟩
    obtain ⟨δx,kx,Nx,hNxcenter,hδx,hkx⟩ := P.horn_spatial_neck c e _ hxin
    have hNxscale : Nx.scale = metricScalarAt D.terminal.metric (P.horn c e x.val) := by
      rw [Nx.scale_scalar,hNxcenter]
    have hkx2 : 2 ≤ kx := by omega
    have hδxsmall : δx ≤ 1 / 8646 := hδx.trans hεsmall
    have hNxscalegap : Λ * (P.coreRadius ^ 2)⁻¹ < (1 - 4323 * δx) * Nx.scale := by
      have hb := mul_le_mul_of_nonneg_right hδxsmall Nx.scale_pos.le
      rw [hNxscale] at *
      nlinarith
    obtain ⟨Θx,hΘx,hmapx⟩ := P.exists_neck_coordinates_in_horn_of_base_scalar_bound c e Nx
      hkx2 (by linarith) (hNxcenter.symm ▸ hxpos) hNxscalegap
    obtain ⟨px,Rx,hRx,hxfrontl,hxfrontr,hxcll,hxclr,hxfullcompact,hxcompact,hxlo,hxhi,hxband⟩ :=
      hseparate P hεeta c e Nx hδx ((Nat.ceil_le_floor_add_one ε⁻¹).trans hkx) Θx hΘx hmapx
    let T := _root_.Set.range (fun q : Sphere 2 => Θx ⟨(q,0),_root_.Set.mem_univ _,
      neg_lt_zero.mpr (inv_pos.mpr Nx.delta_pos),inv_pos.mpr Nx.delta_pos⟩)
    have hTbound : ∀ z ∈ T, 3 * Q / 2 < metricScalarAt D.terminal.metric (P.horn c e z.val) := by
      rintro z ⟨w,rfl⟩
      rw [hmapx]
      have hb := (normalized_neck_scalar_bounds_of_small Nx hkx2 hδxsmall
        (TopologicalSpace.Opens.inclusion (neckCentralOpen_le_buffer δx)
          ⟨(w,0),_root_.Set.mem_univ _,neg_lt_zero.mpr (inv_pos.mpr Nx.delta_pos),inv_pos.mpr Nx.delta_pos⟩)
        (by change -δx⁻¹ ≤ 0 ∧ 0 ≤ δx⁻¹; constructor <;> linarith [inv_pos.mpr Nx.delta_pos])).1
      rw [hNxscale] at hb
      linarith
    have hTx : x ∈ T := by
      refine ⟨Nx.sphereMark,?_⟩
      apply (P.horn_interior_embedding c e).isEmbedding.injective
      exact (hmapx _).trans (Nx.marked.trans hNxcenter)
    have hTconn : IsPreconnected T :=
      (isConnected_range (hΘx.contMDiff.continuous.comp
        ((continuous_id.prodMk continuous_const).subtype_mk _))).isPreconnected
    have hTS : T ⊆ Sᶜ := by
      intro z hz hzS
      exact (not_lt_of_ge (hSbound z hzS)) (hTbound z hz)
    have hTleft : T ⊆ p.left := by
      rcases p.subset_left_or_subset_right hTconn hTS with h | h
      · exact h
      · exact False.elim (p.disjoint.le_bot ⟨hx,h hTx⟩)
    have hrightmeet : (p.right ∩ px.right).Nonempty := by
      let r := _root_.Max.max (Real.exp R) (Real.exp Rx) + 1
      have hr : 0 < r := by dsimp [r]; positivity
      refine ⟨⟨(y,r),_root_.Set.mem_univ _,hr⟩,hhi _ ?_,hxhi _ ?_⟩
      · dsimp only [r]; linarith [le_max_left (Real.exp R) (Real.exp Rx)]
      · dsimp only [r]; linarith [le_max_right (Real.exp R) (Real.exp Rx)]
    have hSright : S ⊆ px.right :=
      p.sphere_subset_right_of_sphere_subset_left px
        (by rw [hclr]; exact _root_.Set.subset_union_right) hTleft hrightmeet
    have hTafter : ∀ z ∈ T, t < z.val.2 := by
      intro z hz
      by_contra hn
      have hb := hprefix z.val.2 ⟨z.property.2.le,le_of_not_gt hn⟩ z.val.1
      have hb' := hTbound z hz
      linarith
    have hprefixleft := px.lower_band_subset_left_of_separator_above
      (Real.exp_pos (-Rx)) hxlo hTafter
    have hyS : (⟨(y,t),_root_.Set.mem_univ _,ht⟩ : positiveHornDomain) ∈ S := by
      refine ⟨N.sphereMark,?_⟩
      apply (P.horn_interior_embedding c e).isEmbedding.injective
      exact (hmap _).trans (N.marked.trans hcenter)
    exact px.disjoint.le_bot ⟨hprefixleft _ le_rfl,hSright hyS⟩
  · have hb := hSbound x hx
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_horn_first_scalar_level_inner_scalar_bound_tolerance_of_fineCutNecks then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_horn_first_scalar_level_inner_scalar_bound_tolerance_of_fineCutNecks"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_horn_first_scalar_level_inner_scalar_bound_tolerance_of_fineCutNecks ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_horn_first_scalar_level_inner_scalar_bound_tolerance_of_fineCutNecks

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section
open _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Topology.SphereSeparation

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u
variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

theorem exists_horn_first_scalar_level_reparametrized_scalar_bound_tolerance_of_fineCutNecks :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {εc Qc : ℝ}, 0 < εc → εc ≤ ε → P.FineCutNecks εc Qc →
        ∀ (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
          {Q : ℝ}, 2 * (Λ * (P.coreRadius ^ 2)⁻¹) < Q → Qc ≤ Q →
          ∃ t : ℝ, 0 < t ∧ ∃ (y : Sphere 2) (δ : ℝ) (k : ℕ)
            (N : NormalizedNeck D.terminal.metric δ k),
            N.center = P.horn c e (y,t) ∧ N.scale = Q ∧ δ ≤ εc ∧
            ⌊εc⁻¹⌋₊ + 1 ≤ k ∧
            (∀ s ∈ _root_.Set.Ico 0 t, ∀ z : Sphere 2,
              metricScalarAt D.terminal.metric (P.horn c e (z,s)) < Q) ∧
            ∀ (F : NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
              (a r : ℝ), 0 < r →
              (∀ q : NeckCylinder, q.2 ≤ r → F q = q) →
              (∀ w : Sphere 2, ∃ z : Sphere 2,
                P.horn c e (F (z,a)) = N.chart ⟨(w,0),by
                  have hp := inv_pos.mpr N.delta_pos
                  constructor <;> linarith⟩) →
              ∀ z : Sphere 2, ∀ s ∈ _root_.Set.Icc (0 : ℝ) a,
                metricScalarAt D.terminal.metric (P.horn c e (F (z,s))) ≤ 3 * Q := by
  obtain ⟨eta, heta, hinner⟩ :=
    exists_horn_first_scalar_level_inner_scalar_bound_tolerance_of_fineCutNecks.{u}
  refine ⟨eta, heta, ?_⟩
  intro D ε Λ P hε εc Qc hεc hεcε hfine c e Q hQ hQc
  obtain ⟨t, ht, y, δ, k, N, hcenter, hscale, hδ, hk, hbefore, hprefix,
    Θ, hΘ, hmap, p, R, hR, hcl, hcr, hcompact, hlo, hhi, hbound⟩ :=
    hinner P hε hεc hεcε hfine c e hQ hQc
  refine ⟨t, ht, y, δ, k, N, hcenter, hscale, hδ, hk, hbefore, ?_⟩
  intro F a r hr hfix hmatch z s hs
  have hfix0 : ∀ q : NeckCylinder, q.2 ≤ 0 → F q = q :=
    fun q hq => hfix q (hq.trans hr.le)
  have hbase : 0 < Λ * (P.coreRadius ^ 2)⁻¹ :=
    mul_pos (zero_lt_one.trans_le P.Lambda_ge_one) (inv_pos.mpr (sq_pos_of_pos P.coreRadius_pos))
  have hQpos : 0 < Q := by linarith
  by_cases hs0 : s = 0
  · subst s
    rw [hfix (z,0) hr.le]
    have hb := P.horn_base_scalar c e z
    linarith
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    apply reparametrized_prefix_scalar_le P c e F hr (Real.exp_pos (-R)) hfix p hlo ?_ hbound z s
      ⟨hspos,hs.2⟩
    rintro x ⟨w, rfl⟩
    obtain ⟨z, hz⟩ := hmatch w
    refine ⟨z, ?_⟩
    have hFa : 0 < (F (z,a)).2 := by
      by_contra hn
      have hfixa := hfix0 (F (z,a)) (le_of_not_gt hn)
      have hza : F (z,a) = (z,a) := F.injective hfixa
      have hale : a ≤ 0 := by rw [hza] at hn; exact le_of_not_gt hn
      have hslt := hspos.trans_le hs.2
      linarith
    let qw : neckCentralOpen δ := ⟨(w,0),_root_.Set.mem_univ _,
      neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩
    have hTheta : 0 < (Θ qw).val.2 := (Θ qw).property.2
    exact P.horn_injOn c e
      (show F (z,a) ∈ _root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ) from ⟨mem_univ _,hFa.le⟩)
      (show (Θ qw).val ∈ _root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ) from ⟨mem_univ _,hTheta.le⟩)
      (hz.trans (hmap qw).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.exists_horn_first_scalar_level_reparametrized_scalar_bound_tolerance_of_fineCutNecks then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.exists_horn_first_scalar_level_reparametrized_scalar_bound_tolerance_of_fineCutNecks"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.exists_horn_first_scalar_level_reparametrized_scalar_bound_tolerance_of_fineCutNecks ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.exists_horn_first_scalar_level_reparametrized_scalar_bound_tolerance_of_fineCutNecks


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

end

end


set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Submission.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u
variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab target :: scope.openDecls } }

private theorem exists_common_deep_coordinates_of_fine_neck_family
    {β εc : ℝ} (hεc : 0 < εc) (hε : εc ≤ 1 / 8646) (hεβ : εc < β) (hβ1 : β < 1)
    {Q : ℝ} (hQ : 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q)
    (δ₀ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
    (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e))
    (hδε : ∀ c e, δ₀ c e ≤ εc)
    (hkN : ∀ c e, ⌊εc⁻¹⌋₊ + 1 ≤ k c e)
    (hcenter : ∀ c e, (N c e).center ∈ P.horn c e '' (_root_.Set.univ ×ˢ _root_.Set.Ioi (0 : ℝ)))
    (hscale : ∀ c e, (N c e).scale = Q) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (hδ : ∀ c e, δ₀ c e ≤ β),
      ∃ (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
        (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
        (lambda : ℝ) (hlambda : 0 < lambda),
        let P' := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
        ∃ Θ : ∀ c, P.hornIndex c → neckCentralOpen β → positiveHornDomain,
          (∀ c e, _root_.Manifold.IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ (Θ c e)) ∧
          (∀ c e q, P'.horn c e (Θ c e q).val =
            ((N c e).monoDelta (hδ c e) hβ1).chart
              (Opens.inclusion (neckCentralOpen_le_buffer β) q)) ∧
          ∀ c e q, (P'.hornCollar c e).radius + R + 3 < (Θ c e q).val.2 := by
  have hbase : 0 < Λ * (P.coreRadius ^ 2)⁻¹ :=
    mul_pos (zero_lt_one.trans_le P.Lambda_ge_one) (inv_pos.mpr (sq_pos_of_pos P.coreRadius_pos))
  have hδ : ∀ c e, δ₀ c e ≤ β := fun c e => (hδε c e).trans hεβ.le
  have hcoords (c) (e : P.hornIndex c) :
      ∃ Θ : neckCentralOpen β → positiveHornDomain,
        _root_.Manifold.IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ ∧
        (∀ q, P.horn c e (Θ q).val =
          ((N c e).monoDelta (hδ c e) hβ1).chart
            (Opens.inclusion (neckCentralOpen_le_buffer β) q)) ∧
        ∃ m : ℝ, 0 < m ∧ ∀ q, m ≤ (Θ q).val.2 := by
    have hk : 2 ≤ k c e := by
      have hlarge : (1 : ℝ) ≤ εc⁻¹ := by
        rw [inv_eq_one_div]
        exact (le_div_iff₀ hεc).mpr (by linarith)
      have hi : 1 ≤ ⌊εc⁻¹⌋₊ := Nat.le_floor (by exact_mod_cast hlarge)
      have hh := hkN c e
      omega
    have hδε := hδε c e
    have hcenter := hcenter c e
    have hscale : Λ * (P.coreRadius ^ 2)⁻¹ < (1 - 4323 * δ₀ c e) * (N c e).scale := by
      rw [hscale c e]
      have hf : (1 / 2 : ℝ) ≤ 1 - 4323 * δ₀ c e := by linarith [hδε.trans hε]
      have hp : 0 < Q := by nlinarith
      nlinarith
    exact P.exists_neck_coordinates_with_positive_height_of_base_scalar_bound c e (N c e)
      hk ((hδε.trans hε).trans (by norm_num)) (hδ c e) hβ1
      ((inv_lt_inv₀ (hεc.trans hεβ) (N c e).delta_pos).mpr (hδε.trans_lt hεβ))
      hcenter hscale
  classical
  choose Θ hΘ hmap height hheight hbound using hcoords
  obtain ⟨r,hr,hle,lambda,hlambda,F,hF,hFmap,hFdepth⟩ :=
    exists_common_deep_coordinates_after_rescaling P k
      (fun c e => (N c e).monoDelta (hδ c e) hβ1) Θ hΘ hmap
      height hheight hbound R hR
  exact ⟨hδ,r,hr,hle,lambda,hlambda,F,hF,hFmap,hFdepth⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.exists_common_deep_coordinates_of_fine_neck_family
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.exists_common_deep_coordinates_of_fine_neck_family target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

end

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Submission.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab {D : OneStepIncoming.{u}} : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab target :: scope.openDecls } }

private theorem exists_common_scale_horn_matching_of_fine_neck_family :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {εc : ℝ}, 0 < εc → εc ≤ ε →
        ∀ {δ : ℝ}, 0 < δ → δ⁻¹ + 1 < (2 * εc)⁻¹ →
        ∀ {Q : ℝ}, 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q →
        ∀ (δ₀ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
          (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e)),
          (∀ c e, δ₀ c e ≤ εc) →
          (∀ c e, ⌊εc⁻¹⌋₊ + 1 ≤ k c e) →
          (∀ c e, (N c e).center ∈ P.horn c e '' (_root_.Set.univ ×ˢ _root_.Set.Ioi (0 : ℝ))) →
          (∀ c e, (N c e).scale = Q) →
          ∃ (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
            (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
            (lambda : ℝ) (hlambda : 0 < lambda),
            let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
            ∃ (hδ : ∀ c e, δ₀ c e ≤ 2 * εc) (hε1 : 2 * εc < 1),
              ∀ c e, ∃ (a : ℝ) (β : Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2) (σ : ℝ),
                (Padapt.hornCollar c e).radius + δ⁻¹ < a ∧
                (β = Diffeomorph.refl (𝓡 2) (Sphere 2) ∞ ∨
                  β = sphereAntipodalDiffeomorph (n := 2)) ∧ (σ = 1 ∨ σ = -1) ∧
                ∃ F : NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder,
                  (∀ (q : Sphere 2) (s : ℝ), |s| ≤ δ⁻¹ →
                    ∃ hq : (β q,σ*s) ∈ neckBuffer (2 * εc),
                      0 < (F (q,a+s)).2 ∧
                      Padapt.horn c e (F (q,a+s)) =
                        ((N c e).monoDelta (hδ c e) hε1).chart ⟨(β q,σ*s),hq⟩) ∧
                  ∃ K : Set NeckCylinder, IsCompact K ∧
                    K ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioi (Padapt.hornCollar c e).radius ∧
                    EqOn F id Kᶜ ∧ _root_.Set.EqOn F.symm id Kᶜ := by
  obtain ⟨eta,heta,hmatch⟩ := exists_horn_neck_collar_matching_of_deep_coordinates
  refine ⟨min (eta / 2) (1 / 17292),lt_min (by positivity) (by norm_num),?_⟩
  intro D ε Λ P hε εc hεc hεcε δ hδ hfit Q hQ δ₀ k N hδε hkN hcenter hscale
  have hβeta : 2 * ε ≤ eta := by linarith [hε.trans (min_le_left _ _)]
  have hεsmall : εc ≤ 1 / 8646 :=
    (hεcε.trans (hε.trans (min_le_right _ _))).trans (by norm_num)
  have hεβ : εc < 2 * εc := by linarith
  have hβ1 : 2 * εc < 1 := by linarith [hε.trans (min_le_right _ _)]
  have hεε : ε ≤ 2 * ε := by linarith [P.epsilon_pos]
  obtain ⟨hδ₀,r,hr,hle,lambda,hlambda,Θ,hΘ,hmap,hdepth⟩ :=
    P.exists_common_deep_coordinates_of_fine_neck_family hεc hεsmall hεβ hβ1 hQ δ₀ k N hδε hkN
      hcenter hscale δ⁻¹ (inv_nonneg.mpr hδ.le)
  let Padapt := TerminalCorePresentation.monoEpsilon
    ((P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda) hεε
  refine ⟨r,hr,hle,lambda,hlambda,hδ₀,hβ1,?_⟩
  intro c e
  have hk : ⌈(2 * ε)⁻¹⌉₊ ≤ k c e := by
    have hi : (2 * ε)⁻¹ ≤ εc⁻¹ := inv_anti₀ hεc (by linarith)
    exact (Nat.ceil_mono hi).trans ((Nat.ceil_le_floor_add_one εc⁻¹).trans (hkN c e))
  obtain ⟨a,ha,β,σ,hβ,hσ,F,hF,K,hK,hKr,hfix,hfixi⟩ :=
    hmatch Padapt hβeta c e ((N c e).monoDelta (hδ₀ c e) hβ1) (by linarith) hk
      (Θ c e) (hΘ c e) (hmap c e) (ρ := (Padapt.hornCollar c e).radius)
      (Padapt.hornCollar c e).radius_pos.le hδ hfit (hdepth c e)
  exact ⟨a,β,σ,ha,hβ,hσ,F,hF,K,hK,hKr,hfix,hfixi⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_common_scale_horn_matching_of_fine_neck_family
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_common_scale_horn_matching_of_fine_neck_family target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Submission.Function _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.Topology.Manifold

universe u

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab_1 {D : OneStepIncoming.{u}} : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab_1 target :: scope.openDecls } }

private theorem exists_reparametrized_horn_matching_of_fine_neck_family :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {εc : ℝ}, 0 < εc → εc ≤ ε →
        ∀ {δ : ℝ}, 0 < δ → δ⁻¹ + 1 < (2 * εc)⁻¹ →
        ∀ {Q : ℝ}, 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q →
        ∀ (δ₀ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
          (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e)),
          (∀ c e, δ₀ c e ≤ εc) →
          (∀ c e, ⌊εc⁻¹⌋₊ + 1 ≤ k c e) →
          (∀ c e, (N c e).center ∈ P.horn c e '' (_root_.Set.univ ×ˢ _root_.Set.Ioi (0 : ℝ))) →
          (∀ c e, (N c e).scale = Q) →
          ∃ (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
            (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
            (lambda : ℝ) (hlambda : 0 < lambda),
            let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
            ∃ (hδ : ∀ c e, δ₀ c e ≤ 2 * εc) (hε1 : 2 * εc < 1)
              (a : ∀ c, P.hornIndex c → ℝ)
              (β : ∀ c, P.hornIndex c → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
              (γ : ∀ c, P.hornIndex c → ℝ)
              (F : ∀ c, P.hornIndex c →
                NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
              (K : ∀ c, P.hornIndex c → Set NeckCylinder)
              (hK : ∀ c e, IsCompact (K c e))
              (hfix : ∀ c e q, q.2 ≤ (Padapt.hornCollar c e).radius → F c e q = q)
              (hF : ∀ c e, _root_.Set.EqOn (F c e) id (K c e)ᶜ),
              let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
              ∀ c e, (Padapt.hornCollar c e).radius + δ⁻¹ < a c e ∧
                (β c e = Diffeomorph.refl (𝓡 2) (Sphere 2) ∞ ∨
                  β c e = sphereAntipodalDiffeomorph (n := 2)) ∧
                (γ c e = 1 ∨ γ c e = -1) ∧
                (_root_.Set.range (fun q : HalfNeckCylinder => P'.horn c e q.val) =
                  _root_.Set.range (fun q : HalfNeckCylinder => Padapt.horn c e q.val)) ∧
                ∀ q : Sphere 2, ∀ s : ℝ, |s| ≤ δ⁻¹ →
                  ∃ hq : (β c e q, γ c e * s) ∈ neckBuffer (2 * εc),
                    P'.horn c e (q, a c e - s) =
                      ((N c e).monoDelta (hδ c e) hε1).chart ⟨(β c e q,γ c e*s),hq⟩ := by
  obtain ⟨eta,heta,hmatch⟩ := exists_common_scale_horn_matching_of_fine_neck_family
  refine ⟨eta,heta,?_⟩
  intro D ε Λ P hε εc hεc hεcε δ hδpos hfit Q hQ δ₀ k N hδε hk hcenter hscale
  obtain ⟨r,hr,hle,lambda,hlambda,hδ,hε1,hmatching⟩ :=
    hmatch P hε hεc hεcε hδpos hfit hQ δ₀ k N hδε hk hcenter hscale
  let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
  classical
  choose a β σ ha hβ hσ F hchart K hK hKρ hfix hfixi using hmatching
  let γ : ∀ c, P.hornIndex c → ℝ := fun c e => -(σ c e)
  have hfixed (c) (e : P.hornIndex c) (q : NeckCylinder)
      (hq : q.2 ≤ (Padapt.hornCollar c e).radius) : F c e q = q :=
    hfix c e (fun hqK => (not_lt_of_ge hq) (hKρ c e hqK).2)
  refine ⟨r,hr,hle,lambda,hlambda,hδ,hε1,a,β,γ,F,K,hK,hfixed,hfix,?_⟩
  dsimp only
  intro c e
  refine ⟨ha c e,hβ c e,?_,
    Padapt.reparametrizeHornsOfCompactSupport_range F hfixed K hK hfix c e,?_⟩
  · rcases hσ c e with h | h
    · exact Or.inr (congrArg Neg.neg h)
    · exact Or.inl (by dsimp only [γ]; rw [h]; norm_num)
  · intro q s hs
    obtain ⟨hq,hpos,heq⟩ := hchart c e q (-s) (by simpa only [abs_neg] using hs)
    have hsign : σ c e * (-s) = γ c e * s := by dsimp only [γ]; ring
    have hq' : (β c e q,γ c e * s) ∈ neckBuffer (2 * εc) := hsign ▸ hq
    refine ⟨hq',?_⟩
    change Padapt.horn c e (F c e (q,a c e-s)) = _
    have hsub : (⟨(β c e q,σ c e*(-s)),hq⟩ : neckBuffer (2 * εc)) =
        ⟨(β c e q,γ c e*s),hq'⟩ := Subtype.ext (Prod.ext rfl hsign)
    change Padapt.horn c e (F c e (q,a c e + -s)) = _ at heq
    simpa only [sub_eq_add_neg] using heq.trans
      (congrArg ((N c e).monoDelta (hδ c e) hε1).chart hsub)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_reparametrized_horn_matching_of_fine_neck_family
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_reparametrized_horn_matching_of_fine_neck_family target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u

private theorem exists_fine_neck_family_first_scalar_level_reparametrized_bound :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {εc Qc : ℝ}, 0 < εc → εc ≤ ε → P.FineCutNecks εc Qc →
        ∀ {Q : ℝ}, 2 * (Λ * (P.coreRadius ^ 2)⁻¹) < Q → Qc ≤ Q →
        ∃ (t : ∀ c, P.hornIndex c → ℝ) (y : ∀ c, P.hornIndex c → Sphere 2)
          (δ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
          (N : ∀ c e, NormalizedNeck D.terminal.metric (δ c e) (k c e)),
          ∀ c e, 0 < t c e ∧ (N c e).center = P.horn c e (y c e, t c e) ∧
            (N c e).scale = Q ∧ δ c e ≤ εc ∧ ⌊εc⁻¹⌋₊ + 1 ≤ k c e ∧
            (∀ s ∈ _root_.Set.Ico 0 (t c e), ∀ z : Sphere 2,
              metricScalarAt D.terminal.metric (P.horn c e (z, s)) < Q) ∧
            ∀ (F : NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
              (a r : ℝ), 0 < r →
              (∀ q : NeckCylinder, q.2 ≤ r → F q = q) →
              (∀ w : Sphere 2, ∃ z : Sphere 2,
                P.horn c e (F (z, a)) = (N c e).chart ⟨(w, 0), by
                  have hp := inv_pos.mpr (N c e).delta_pos
                  constructor <;> linarith⟩) →
              ∀ z : Sphere 2, ∀ s ∈ _root_.Set.Icc (0 : ℝ) a,
                metricScalarAt D.terminal.metric (P.horn c e (F (z, s))) ≤ 3 * Q := by
  obtain ⟨eta, heta, hchoose⟩ :=
    exists_horn_first_scalar_level_reparametrized_scalar_bound_tolerance_of_fineCutNecks.{u}
  refine ⟨eta, heta, ?_⟩
  intro D ε Λ P hε εc Qc hεc hεcε hfine Q hQ hQc
  classical
  choose t ht y δ k N hcenter hscale hδ hk hbefore hprefix using
    fun c e => hchoose P hε hεc hεcε hfine c e hQ hQc
  exact ⟨t, y, δ, k, N, fun c e =>
    ⟨ht c e, hcenter c e, hscale c e, hδ c e, hk c e, hbefore c e, hprefix c e⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.exists_fine_neck_family_first_scalar_level_reparametrized_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.exists_fine_neck_family_first_scalar_level_reparametrized_bound target :: scope.openDecls } }
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab_2 {D : OneStepIncoming.{u}} : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab_2 target :: scope.openDecls } }

private theorem exists_first_hit_reparametrized_horn_matching_of_fineCutNecks :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {εc Qc : ℝ}, 0 < εc → εc ≤ ε → P.FineCutNecks εc Qc →
        ∀ {δ : ℝ}, 0 < δ → δ⁻¹ + 1 < (2 * εc)⁻¹ →
        ∀ {Q coreBound : ℝ}, 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q → Qc ≤ Q →
        (∀ c ∈ P.component, ∀ x ∈ P.core c, metricScalarAt D.terminal.metric x ≤ coreBound) →
          ∃ (δ₀ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
            (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e))
            (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
            (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
            (lambda : ℝ) (hlambda : 0 < lambda),
            let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
            ∃ (hδ : ∀ c e, δ₀ c e ≤ 2 * εc) (hε1 : 2 * εc < 1)
              (a : ∀ c, P.hornIndex c → ℝ)
              (β : ∀ c, P.hornIndex c → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
              (γ : ∀ c, P.hornIndex c → ℝ)
              (F : ∀ c, P.hornIndex c →
                NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
              (K : ∀ c, P.hornIndex c → Set NeckCylinder)
              (hK : ∀ c e, IsCompact (K c e))
              (hfix : ∀ c e q, q.2 ≤ (Padapt.hornCollar c e).radius → F c e q = q)
              (hF : ∀ c e, _root_.Set.EqOn (F c e) id (K c e)ᶜ),
              let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
              (∀ c e, (N c e).scale = Q ∧ δ₀ c e ≤ εc ∧ ⌊εc⁻¹⌋₊ + 1 ≤ k c e) ∧
              (∀ c e, (Padapt.hornCollar c e).radius + δ⁻¹ < a c e ∧
                (β c e = Diffeomorph.refl (𝓡 2) (Sphere 2) ∞ ∨
                  β c e = sphereAntipodalDiffeomorph (n := 2)) ∧
                (γ c e = 1 ∨ γ c e = -1) ∧
                (_root_.Set.range (fun q : HalfNeckCylinder => P'.horn c e q.val) =
                  _root_.Set.range (fun q : HalfNeckCylinder => Padapt.horn c e q.val)) ∧
                ∀ q : Sphere 2, ∀ s : ℝ, |s| ≤ δ⁻¹ →
                  ∃ hq : (β c e q, γ c e * s) ∈ neckBuffer (2 * εc),
                    P'.horn c e (q, a c e - s) =
                      ((N c e).monoDelta (hδ c e) hε1).chart ⟨(β c e q,γ c e*s),hq⟩) ∧
              ∀ x ∈ P'.truncatedRegion a,
                metricScalarAt D.terminal.metric x ≤ _root_.Max.max coreBound (3 * Q) := by
  obtain ⟨eta₀, heta₀, hchoose⟩ :=
    TerminalCorePresentation.exists_fine_neck_family_first_scalar_level_reparametrized_bound.{u}
  obtain ⟨eta₁, heta₁, hmatch⟩ := exists_reparametrized_horn_matching_of_fine_neck_family.{u}
  refine ⟨min eta₀ eta₁, lt_min heta₀ heta₁, ?_⟩
  intro D ε Λ P hε εc Qc hεc hεcε hfine δ hδpos hfit Q coreBound hQ hQc hcore
  obtain ⟨t, y, δ₀, k, N, hN⟩ := hchoose P (hε.trans (min_le_left _ _)) hεc hεcε hfine (Q := Q)
    (by simpa only [mul_assoc] using hQ) hQc
  have hδε := fun c e => (hN c e).2.2.2.1
  have hk := fun c e => (hN c e).2.2.2.2.1
  have hcenter : ∀ c e, (N c e).center ∈ P.horn c e '' (_root_.Set.univ ×ˢ _root_.Set.Ioi (0 : ℝ)) := by
    intro c e
    rw [(hN c e).2.1]
    exact ⟨(y c e,t c e),⟨mem_univ _,(hN c e).1⟩,rfl⟩
  have hscale := fun c e => (hN c e).2.2.1
  obtain ⟨r,hr,hle,lambda,hlambda,hδ,hε1,a,β,γ,F,K,hK,hfix,hF,hmatching⟩ :=
    hmatch P (hε.trans (min_le_right _ _)) hεc hεcε hδpos hfit hQ δ₀ k N hδε hk hcenter hscale
  let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
  let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
  refine ⟨δ₀,k,N,r,hr,hle,lambda,hlambda,hδ,hε1,a,β,γ,F,K,hK,hfix,hF,
    (fun c e => ⟨hscale c e,hδε c e,hk c e⟩),hmatching,?_⟩
  apply scalar_le_on_rescaled_reparametrized_truncatedRegion P δ₀ k N
    (fun c e => (hN c e).2.2.2.2.2.2) hcore r hr hle lambda hlambda F a K hK hfix hF
  intro c e w
  obtain ⟨hw,hval⟩ := (hmatching c e).2.2.2.2 ((β c e).symm w) 0
    (by simp [inv_nonneg.mpr hδpos.le])
  refine ⟨(β c e).symm w, ?_⟩
  change P'.horn c e ((β c e).symm w,a c e) = _
  simp only [sub_zero, _root_.MulZeroClass.mul_zero, (β c e).apply_symm_apply] at hval
  exact hval.trans (by rfl)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_first_hit_reparametrized_horn_matching_of_fineCutNecks
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_first_hit_reparametrized_horn_matching_of_fineCutNecks target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab_3 {D : OneStepIncoming.{u}} : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab_3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFiniteHornCutIndex {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ) :
    Finite P.HornCutIndex := by
  let : Finite P.component := P.component_finite.to_subtype
  let (c : P.component) : Finite (P.hornIndex c.val) := P.hornIndex_finite c.val
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFiniteHornCutIndex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFiniteHornCutIndex target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2+1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }

private theorem exists_first_hit_oriented_horn_necks_of_fineCutNecks :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {εc Qc : ℝ}, 0 < εc → εc ≤ ε → P.FineCutNecks εc Qc →
        ∀ {δ : ℝ} (_ : 2 * εc ≤ δ) (hδ1 : δ < 1), δ⁻¹+2 < (2 * εc)⁻¹ →
        ∀ Q coreBound : ℝ, 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q → Qc ≤ Q →
        (∀ c ∈ P.component, ∀ x ∈ P.core c, metricScalarAt D.terminal.metric x ≤ coreBound) →
        ∃ (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
          (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
          (lambda : ℝ) (hlambda : 0 < lambda),
        let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
          ∃ (δ₀ : ∀ c, Padapt.hornIndex c → ℝ) (k : ∀ c, Padapt.hornIndex c → ℕ)
            (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e))
            (hδ : ∀ c e, δ₀ c e ≤ δ)
            (a : ∀ c, Padapt.hornIndex c → ℝ)
            (F : ∀ c, Padapt.hornIndex c → NeckCylinder ≃ₘ⟮NeckCylinderModel,
              NeckCylinderModel⟯ NeckCylinder)
            (K : ∀ c, Padapt.hornIndex c → Set NeckCylinder)
            (hK : ∀ c e, IsCompact (K c e))
            (hfix : ∀ c e (q : NeckCylinder),
              q.2 ≤ (Padapt.hornCollar c e).radius → F c e q = q)
            (hF : ∀ c e, _root_.Set.EqOn (F c e) id (K c e)ᶜ),
            let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
            let N' := fun j : P'.HornCutIndex =>
              (N j.1.val j.2).monoDelta (hδ j.1.val j.2) hδ1
            P'.core = Padapt.core ∧
            (∀ c e, (N c e).scale = Q ∧ δ₀ c e ≤ 2 * εc ∧ ⌊εc⁻¹⌋₊+1 ≤ k c e) ∧
            (∀ x ∈ P'.truncatedRegion a,
              metricScalarAt D.terminal.metric x ≤ _root_.Max.max coreBound (3 * Q)) ∧
            ∃ (e : P'.HornCutIndex → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
              (he : ∀ j, sphereDiffeo (n := 2) (e j) spherePoint = (N' j).sphereMark)
              (side : P'.HornCutIndex → Bool)
              (ν : P'.HornCutIndex → Sphere 2 ≃ Sphere 2),
              let d := fun j => (N' j).rotatedDatum (e j) (he j) (side j)
              (∀ j, LinearMap.det (e j).toLinearMap = 1) ∧
              (∀ c e, δ⁻¹+1 < a c e) ∧
              (∀ j (q : bufferedCylinder δ),
                (d j).oriented.map q =
                  P'.horn j.1.val j.2 (ν j q.val.1, a j.1.val j.2 - q.val.2)) ∧
              let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j).oriented
              ∃ (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
                (hd : Pairwise fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j))),
                (∀ j side,
                  cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd (j,side) ∈
                  scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
                    (P'.coreRadius^2)⁻¹ ↔
                  side = _root_.Bool.true) ∧
                _root_.Set.MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
                  (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen
                    D.terminal.metric f
                    (P'.coreRadius^2)⁻¹)) D.slab.terminalRegularOpen := by
  obtain ⟨eta,heta,hmatching⟩ := exists_first_hit_reparametrized_horn_matching_of_fineCutNecks
  refine ⟨eta,heta,?_⟩
  intro D ε Λ P hε εc Qc hεc hεcε hfine δ hεδ hδ1 hfit Q coreBound hQ hQc hcorebound
  have hδpos : 0 < δ := (mul_pos (by norm_num) hεc).trans_le hεδ
  let δw := (δ⁻¹+1)⁻¹
  have hδw : 0 < δw := inv_pos.mpr (by positivity)
  have hδwi : δw⁻¹ = δ⁻¹+1 := inv_inv _
  have hfitw : δw⁻¹+1 < (2 * εc)⁻¹ := by rw [hδwi]; linarith
  obtain ⟨δraw,k,Nraw,r,hr,hle,lambda,hlambda,hraw,hε1,a,β,γ,F,K,hK,hfix,hF,hNraw,hmatch,
    hscalar⟩ := hmatching P hε hεc hεcε hfine hδw hfitw hQ hQc hcorebound
  let δ₀ := fun (_c : ConnectedComponents D.slab.terminalRegularOpen) (_e : P.hornIndex _c) =>
    2 * εc
  let N := fun c e => (Nraw c e).monoDelta (hraw c e) hε1
  have hdata : ∀ c e,
      (N c e).scale = Q ∧ δ₀ c e ≤ 2 * εc ∧ ⌊εc⁻¹⌋₊ + 1 ≤ k c e :=
    fun c e => ⟨(hNraw c e).1, le_rfl, (hNraw c e).2.2⟩
  let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
  let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
  let hδ : ∀ c e, δ₀ c e ≤ δ := fun _ _ => hεδ
  have ham (c) (e : P'.hornIndex c) : δ⁻¹+1 < a c e := by
    have hh := (hmatch c e).1
    rw [hδwi] at hh
    have hp := (Padapt.hornCollar c e).radius_pos
    linarith
  obtain ⟨e,he,side,ν,hdet,hm,hgeometry⟩ := exists_oriented_horn_neck_data_of_matching
    P' hδpos hδ1 hδwi δ₀ k N hδ a ham β γ
      (fun c e => (hmatch c e).2.2.1)
      (fun c e => (hmatch c e).2.2.2.2)
  exact ⟨r,hr,hle,lambda,hlambda,δ₀,k,N,hδ,a,F,K,hK,hfix,hF,rfl,hdata,hscalar,
    e,he,side,ν,hdet,ham,hm,hgeometry⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_first_hit_oriented_horn_necks_of_fineCutNecks
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_first_hit_oriented_horn_necks_of_fineCutNecks target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Submission.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab_4 {D : OneStepIncoming.{u}} : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab_4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab_4 target :: scope.openDecls } }

private theorem exists_finite_first_hit_oriented_horn_neck_data_of_fineCutNecks :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {εc Qc : ℝ}, 0 < εc → εc ≤ ε → P.FineCutNecks εc Qc →
        ∀ {δ : ℝ} (_ : 2 * εc ≤ δ) (hδ1 : δ < 1), δ⁻¹ + 2 < (2 * εc)⁻¹ →
        ∀ m : ℕ, m + 6 ≤ ⌊εc⁻¹⌋₊ + 1 →
        ∀ Q coreBound : ℝ, 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q → Qc ≤ Q →
        (∀ c ∈ P.component, ∀ x ∈ P.core c,
          metricScalarAt D.terminal.metric x ≤ coreBound) →
        ∃ (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
          (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
          (lambda : ℝ) (hlambda : 0 < lambda),
        let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda;
          0 < Q ∧
          ∃ (F : ∀ c, Padapt.hornIndex c →
              NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
            (K : ∀ c, Padapt.hornIndex c → Set NeckCylinder)
            (hK : ∀ c e, IsCompact (K c e))
            (hfix : ∀ c e (q : NeckCylinder),
              q.2 ≤ (Padapt.hornCollar c e).radius → F c e q = q)
            (hF : ∀ c e, _root_.Set.EqOn (F c e) id (K c e)ᶜ),
            let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
            P'.core = Padapt.core ∧
            ∃ e : Fin (Nat.card P'.HornCutIndex) ≃ P'.HornCutIndex,
              ∃ (a : ∀ c, P'.hornIndex c → ℝ)
                (ν : Fin (Nat.card P'.HornCutIndex) → Sphere 2 ≃ Sphere 2)
                (x₀ : Fin (Nat.card P'.HornCutIndex) → D.slab.terminalRegularOpen)
                (d : ∀ j : Fin (Nat.card P'.HornCutIndex),
                  normalizedDatum D.terminal.metric (x₀ j) δ (m + 6)),
                (∀ j, metricScalarAt D.terminal.metric (x₀ j) = Q) ∧
                (∀ x ∈ P'.truncatedRegion a,
                  metricScalarAt D.terminal.metric x ≤ _root_.Max.max coreBound (3 * Q)) ∧
                (∀ c e, δ⁻¹ + 1 < a c e) ∧
                (∀ j, (d j).retainedSide = _root_.Bool.true) ∧
                (∀ j (q : bufferedCylinder δ),
                  (d j).map q = P'.horn (e j).1.val (e j).2
                    (ν j q.val.1, a (e j).1.val (e j).2 - q.val.2)) ∧
                let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
                ∃ (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
                  (hd : Pairwise fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j))),
                  (∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (f j)) ∧
                  ∃ hRet : _root_.Set.MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
                    (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹))
                    D.slab.terminalRegularOpen,
                  (∀ j side, cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd
                    (j, side) ∈ scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹ ↔ side = _root_.Bool.true) ∧
                  (∀ p : retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹),
                    metricScalarAt D.terminal.metric
                      (retainedCoreDomainMap f
                        (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
                          (P'.coreRadius ^ 2)⁻¹) D.slab.terminalRegularOpen hRet p) ≤
                        _root_.Max.max coreBound (3 * Q)) ∧
                  ∃ (δOriginal : Fin (Nat.card P'.HornCutIndex) → ℝ)
                    (kOriginal : Fin (Nat.card P'.HornCutIndex) → ℕ)
                    (NOriginal : ∀ j, NormalizedNeck D.terminal.metric
                      (δOriginal j) (kOriginal j))
                    (hδOriginal : ∀ j, δOriginal j ≤ δ)
                    (rotation : Fin (Nat.card P'.HornCutIndex) →
                      ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
                    (hmark : ∀ j,
                      DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j) spherePoint =
                      ((NOriginal j).monoDelta (hδOriginal j) hδ1).sphereMark)
                    (side : Fin (Nat.card P'.HornCutIndex) → Bool)
                    (horder : ∀ j, m + 6 ≤ kOriginal j),
                    (∀ j, (NOriginal j).center = x₀ j ∧
                      (NOriginal j).scale = Q ∧ δOriginal j ≤ 2 * εc ∧
                      ⌊εc⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
                    (∀ j, LinearMap.det (rotation j).toLinearMap = 1) ∧
                    ∀ j, HEq (d j)
                      ((((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum
                        (rotation j) (hmark j) (side j)).oriented.lowerOrder (horder j)) := by
  classical
  obtain ⟨eta, heta, hchoose⟩ := exists_first_hit_oriented_horn_necks_of_fineCutNecks.{u}
  refine ⟨eta, heta, ?_⟩
  intro D ε Λ P hε εc Qc hεc hεcε hfine δ hεδ hδ1 hfit m hm Q coreBound hQ hQc hcorebound
  let : SigmaCompactSpace D.slab.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen
        ThreeModel D.slab.terminalRegularOpen.isOpen)
  obtain ⟨r, hr, hle, lambda, hlambda, δ₀, k, N, hδ, a, F, K, hK, hfix, hF,
    hcore, hdata, hscalarTrunc, rot, hrot, side, ν, hdet, ha, hmap, hf, hd, hside, hRet⟩ :=
    hchoose P hε hεc hεcε hfine hεδ hδ1 hfit Q coreBound hQ hQc hcorebound
  let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
  let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
  let Ns := fun j : P'.HornCutIndex => N j.1.val j.2
  let hm' : ∀ j : P'.HornCutIndex, m + 6 ≤ k j.1.val j.2 :=
    fun j => hm.trans (hdata j.1.val j.2).2.2
  obtain ⟨e, hscalar, hsideFin, hmapFin, hfFin, hdFin, hlocalFin, hRetFin, hfacesFin⟩ :=
    exists_finite_oriented_neck_data_of_chosen_family P' hδ1
      (fun j => δ₀ j.1.val j.2) (fun j => k j.1.val j.2) Ns
      (fun j => hδ j.1.val j.2) rot hrot side ν a hm'
      (fun j => (hdata j.1.val j.2).1) hmap hf hd hRet hside
  let d := fun j =>
    (((Ns (e j)).monoDelta (hδ (e j).1.val (e j).2) hδ1).rotatedDatum
      (rot (e j)) (hrot (e j)) (side (e j))).oriented.lowerOrder (hm' (e j))
  let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
  have hQpos : 0 < Q := (mul_pos
    (mul_pos (by norm_num) (zero_lt_one.trans_le P.Lambda_ge_one))
    (inv_pos.mpr (sq_pos_of_pos P.coreRadius_pos))).trans hQ
  have hδpos : 0 < δ := (mul_pos (by norm_num) hεc).trans_le hεδ
  have haPos : ∀ c e, 0 < a c e := by
    intro c e
    have hi := inv_pos.mpr hδpos
    linarith [ha c e]
  have hremoved : ∀ c ∈ P'.component, ∀ ec : P'.hornIndex c, ∀ y : Sphere 2,
      (P'.horn c ec (y, a c ec)).val ∈ ⋃ j, removedSlab (f j) := by
    intro c hc ec y
    obtain ⟨j, hj⟩ := e.surjective (⟨⟨c, hc⟩, ec⟩ : P'.HornCutIndex)
    let q : bufferedCylinder δ := ⟨((ν (e j)).symm y, 0), by
      constructor <;> linarith [inv_pos.mpr hδpos]⟩
    refine mem_iUnion.mpr ⟨j, q, ?_, ?_⟩
    · change (-1 : ℝ) < 0 ∧ (0 : ℝ) < 1
      norm_num
    · change ((d j).map q).val = _
      rw [hmapFin]
      change (P'.horn (e j).1.val (e j).2
        (ν (e j) ((ν (e j)).symm y), a (e j).1.val (e j).2 - 0)).val = _
      rw [(ν (e j)).apply_symm_apply, sub_zero, hj]
  have hboundRet : ∀ x : cutCore f,
      x ∈ retainedCore f
        (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric
          f (P'.coreRadius ^ 2)⁻¹) →
      ∃ p : D.slab.terminalRegularOpen, p.val = x.val ∧
        p ∈ P'.truncatedRegion a ∧ metricScalarAt D.terminal.metric p ≤ _root_.Max.max coreBound (3 * Q) :=
    scalar_le_on_retainedCore_of_truncated_bound P' a haPos hscalarTrunc
      f hremoved
  refine ⟨r, hr, hle, lambda, hlambda, hQpos, F, K, hK, hfix, hF, hcore, e,
    a, ν ∘ e, (fun j => (Ns (e j)).center), d,
    hscalar, hscalarTrunc, ha, hsideFin, hmapFin,
    hfFin, hdFin, hlocalFin, hRetFin, hfacesFin, ?_, ?_⟩
  · intro x
    obtain ⟨p, hp, _, hpbound⟩ := hboundRet x.val x.property
    have heq : p = retainedCoreDomainMap f
        (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric
          f (P'.coreRadius ^ 2)⁻¹)
        D.slab.terminalRegularOpen hRetFin x := Subtype.ext hp
    exact heq ▸ hpbound
  · refine ⟨(fun j => δ₀ (e j).1.val (e j).2),
      (fun j => k (e j).1.val (e j).2), (fun j => Ns (e j)),
      (fun j => hδ (e j).1.val (e j).2), (fun j => rot (e j)),
      (fun j => hrot (e j)), (fun j => side (e j)), (fun j => hm' (e j)),
      ?_, ?_, ?_⟩
    · intro j
      exact ⟨rfl, (hdata (e j).1.val (e j).2).1,
        (hdata (e j).1.val (e j).2).2.1, (hdata (e j).1.val (e j).2).2.2⟩
    · intro j
      exact hdet (e j)
    · intro j
      exact HEq.rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_finite_first_hit_oriented_horn_neck_data_of_fineCutNecks
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_finite_first_hit_oriented_horn_neck_data_of_fineCutNecks target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
