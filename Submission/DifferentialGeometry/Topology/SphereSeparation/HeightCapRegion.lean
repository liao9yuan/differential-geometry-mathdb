import Submission.DifferentialGeometry.Topology.FiberwiseHomeomorph
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric

namespace DifferentialGeometry.Topology.SphereSeparation

def heightCapRegion {E : Type*} [NormedAddCommGroup E]
    (G : ℝ → E → E) (A : E × ℝ → E × ℝ) (a b c r : ℝ) : Set (E × ℝ) :=
  (fun p : E × ℝ => (G p.2 p.1, p.2)) '' (_root_.Metric.closedBall 0 r ×ˢ _root_.Set.Icc a b) ∪
    A '' {p | p.1 ∈ _root_.Metric.closedBall 0 r ∧ p.2 ∈ _root_.Set.Icc b (c - ‖p.1‖ ^ 2 / 2)}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.heightCapRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.heightCapRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.heightCapRegion ``Submission.DifferentialGeometry.Topology.SphereSeparation.heightCapRegion

theorem heightCapRegion_eq_of_image_closedBall_eq
    {E : Type*} [NormedAddCommGroup E] {G H : ℝ → E → E}
    {A : E × ℝ → E × ℝ} {a b c r : ℝ}
    (himage : ∀ t ∈ _root_.Set.Icc a b, G t '' _root_.Metric.closedBall 0 r = H t '' _root_.Metric.closedBall 0 r) :
    heightCapRegion G A a b c r = heightCapRegion H A a b c r := by
  unfold heightCapRegion
  congr 1
  ext z
  constructor
  · rintro ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
    obtain ⟨x, hx, hxy⟩ := (himage t ht).subset ⟨y, hy, rfl⟩
    exact ⟨(x, t), ⟨hx, ht⟩, Prod.ext hxy rfl⟩
  · rintro ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
    obtain ⟨x, hx, hxy⟩ := (himage t ht).symm.subset ⟨y, hy, rfl⟩
    exact ⟨(x, t), ⟨hx, ht⟩, Prod.ext hxy rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.heightCapRegion_eq_of_image_closedBall_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.heightCapRegion_eq_of_image_closedBall_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.heightCapRegion_eq_of_image_closedBall_eq ``Submission.DifferentialGeometry.Topology.SphereSeparation.heightCapRegion_eq_of_image_closedBall_eq

theorem isCompact_heightCapRegion {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {G : ℝ → E → E} {A : E × ℝ → E × ℝ} (a b c r : ℝ)
    (hG : ContinuousOn (fun p : E × ℝ => G p.2 p.1) (_root_.Metric.closedBall 0 r ×ˢ _root_.Set.Icc a b))
    (hA : ContinuousOn A
      {p | p.1 ∈ _root_.Metric.closedBall 0 r ∧ p.2 ∈ _root_.Set.Icc b (c - ‖p.1‖ ^ 2 / 2)}) :
    IsCompact (heightCapRegion G A a b c r) := by
  apply IsCompact.union
  · exact (_root_.ProperSpace.isCompact_closedBall 0 r |>.prod _root_.CompactIccSpace.isCompact_Icc).image_of_continuousOn
      (hG.prodMk continuous_snd.continuousOn)
  · have hclosed : IsClosed {p : E × ℝ |
        p.1 ∈ _root_.Metric.closedBall 0 r ∧ p.2 ∈ _root_.Set.Icc b (c - ‖p.1‖ ^ 2 / 2)} :=
      (isClosed_closedBall.preimage continuous_fst).inter
        ((isClosed_le continuous_const continuous_snd).inter
          (isClosed_le continuous_snd
            (continuous_const.sub ((continuous_fst.norm.pow 2).div_const 2))))
    have hsub : {p : E × ℝ | p.1 ∈ _root_.Metric.closedBall 0 r ∧ p.2 ∈ _root_.Set.Icc b (c - ‖p.1‖ ^ 2 / 2)} ⊆
        closedBall 0 r ×ˢ _root_.Set.Icc b c := by
      intro p hp
      exact ⟨hp.1, hp.2.1, hp.2.2.trans (by linarith [sq_nonneg ‖p.1‖])⟩
    exact IsCompact.image_of_continuousOn
      ((_root_.ProperSpace.isCompact_closedBall 0 r |>.prod _root_.CompactIccSpace.isCompact_Icc).of_isClosed_subset hclosed hsub) hA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isCompact_heightCapRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isCompact_heightCapRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isCompact_heightCapRegion ``Submission.DifferentialGeometry.Topology.SphereSeparation.isCompact_heightCapRegion

private theorem image_cylinder_inter_range {M E : Type*} [NormedAddCommGroup E]
    (f : M → E × ℝ) (G : ℝ → E → E) {a b r : ℝ}
    (hlevels : ∀ t ∈ _root_.Set.Icc a b,
      (G t '' _root_.Metric.closedBall 0 r) ∩ ((fun x => (f x).1) '' {x | (f x).2 = t}) =
        G t '' _root_.Metric.sphere 0 r) :
      ((fun p : E × ℝ => (G p.2 p.1, p.2)) '' (_root_.Metric.closedBall 0 r ×ˢ _root_.Set.Icc a b)) ∩ _root_.Set.range f =
        (fun p : E × ℝ => (G p.2 p.1, p.2)) '' (_root_.Metric.sphere 0 r ×ˢ _root_.Set.Icc a b) :=
  Set.image_prod_inter_range f G hlevels

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.image_cylinder_inter_range
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.image_cylinder_inter_range target :: scope.openDecls } }

private theorem image_quadratic_cap_inter_range {M E : Type*} [NormedAddCommGroup E]
    (f : M → E × ℝ) (A : (E × ℝ) ≃ (E × ℝ))
    {b c r R τ : ℝ} (hb : b = c - r ^ 2 / 2) (hr : 0 ≤ r)
    (hrR : r ≤ R) (hrτ : r ^ 2 / 2 ≤ τ)
    (hgraph : (_root_.Metric.closedBall 0 R ×ˢ _root_.Metric.closedBall c τ) ∩ _root_.Set.range (A.symm ∘ f) =
      (fun y => (y, c - ‖y‖ ^ 2 / 2)) '' _root_.Metric.closedBall 0 R) :
      (A '' {p : E × ℝ | p.1 ∈ _root_.Metric.closedBall 0 r ∧ p.2 ∈ _root_.Set.Icc b (c - ‖p.1‖ ^ 2 / 2)}) ∩ _root_.Set.range f =
        (fun y => A (y, c - ‖y‖ ^ 2 / 2)) '' _root_.Metric.closedBall 0 r := by
  apply Subset.antisymm
  · rintro z ⟨⟨p, hp, rfl⟩, x, hx⟩
    have hpτ : p.2 ∈ _root_.Metric.closedBall c τ := by
      rw [_root_.Metric.mem_closedBall, Real.dist_eq, abs_le]
      have hlo := hp.2.1
      rw [hb] at hlo
      constructor <;> linarith [hp.2.2, sq_nonneg ‖p.1‖]
    have hmem : p ∈ (_root_.Metric.closedBall 0 R ×ˢ _root_.Metric.closedBall c τ) ∩ _root_.Set.range (A.symm ∘ f) :=
      ⟨⟨(_root_.Metric.closedBall_subset_closedBall hrR) hp.1, hpτ⟩,
        x, by simp only [Function.comp_def, hx, A.symm_apply_apply]⟩
    obtain ⟨y, _, hyp⟩ := hgraph.subset hmem
    have hy : y ∈ _root_.Metric.closedBall (0 : E) r := by
      rw [show y = p.1 from congrArg Prod.fst hyp]
      exact hp.1
    exact ⟨y, hy, congrArg A hyp⟩
  · rintro z ⟨y, hy, rfl⟩
    have hyq : b ≤ c - ‖y‖ ^ 2 / 2 := by
      have hn := mem_closedBall_zero_iff.mp hy
      have hsq := (sq_le_sq₀ (norm_nonneg y) hr).mpr hn
      rw [hb]
      linarith
    have hmem := hgraph.symm.subset (_root_.Set.mem_image_of_mem
      (fun y => (y, c - ‖y‖ ^ 2 / 2)) ((_root_.Metric.closedBall_subset_closedBall hrR) hy))
    obtain ⟨x, hx⟩ := hmem.2
    have hf : f x = A (y, c - ‖y‖ ^ 2 / 2) := by
      have h := congrArg A hx
      simpa only [Function.comp_def, A.apply_symm_apply] using h
    exact ⟨mem_image_of_mem A ⟨hy, hyq, le_rfl⟩, x, hf⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.image_quadratic_cap_inter_range
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.image_quadratic_cap_inter_range target :: scope.openDecls } }

theorem heightCapRegion_inter_range {M E : Type*} [NormedAddCommGroup E]
    (f : M → E × ℝ) (G : ℝ → E → E) (A : (E × ℝ) ≃ (E × ℝ))
    {a b c r R τ : ℝ} (hb : b = c - r ^ 2 / 2) (hr : 0 ≤ r)
    (hrR : r ≤ R) (hrτ : r ^ 2 / 2 ≤ τ)
    (hgraph : (_root_.Metric.closedBall 0 R ×ˢ _root_.Metric.closedBall c τ) ∩ _root_.Set.range (A.symm ∘ f) =
      (fun y => (y, c - ‖y‖ ^ 2 / 2)) '' _root_.Metric.closedBall 0 R)
    (hlevels : ∀ t ∈ _root_.Set.Icc a b,
      (G t '' _root_.Metric.closedBall 0 r) ∩ ((fun x => (f x).1) '' {x | (f x).2 = t}) =
        G t '' _root_.Metric.sphere 0 r) :
    heightCapRegion G A a b c r ∩ _root_.Set.range f =
      (fun p : E × ℝ => (G p.2 p.1, p.2)) '' (_root_.Metric.sphere 0 r ×ˢ _root_.Set.Icc a b) ∪
        (fun y => A (y, c - ‖y‖ ^ 2 / 2)) '' _root_.Metric.closedBall 0 r := by
  rw [heightCapRegion, _root_.Set.union_inter_distrib_right,
    image_cylinder_inter_range f G hlevels,
    image_quadratic_cap_inter_range f A hb hr hrR hrτ hgraph]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.heightCapRegion_inter_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.heightCapRegion_inter_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.heightCapRegion_inter_range ``Submission.DifferentialGeometry.Topology.SphereSeparation.heightCapRegion_inter_range

theorem heightCapRegion_sdiff_range {M E : Type*} [NormedAddCommGroup E]
    (f : M → E × ℝ) (G : ℝ → E → E) (A : (E × ℝ) ≃ (E × ℝ))
    {a b c r R τ : ℝ} (hb : b = c - r ^ 2 / 2) (hr : 0 ≤ r)
    (hrR : r ≤ R) (hrτ : r ^ 2 / 2 ≤ τ)
    (hgraph : (_root_.Metric.closedBall 0 R ×ˢ _root_.Metric.closedBall c τ) ∩ _root_.Set.range (A.symm ∘ f) =
      (fun y => (y, c - ‖y‖ ^ 2 / 2)) '' _root_.Metric.closedBall 0 R)
    (hlevels : ∀ t ∈ _root_.Set.Icc a b,
      (G t '' _root_.Metric.closedBall 0 r) ∩ ((fun x => (f x).1) '' {x | (f x).2 = t}) =
        G t '' _root_.Metric.sphere 0 r)
    (hG : ∀ t ∈ _root_.Set.Icc a b, _root_.Set.InjOn (G t) (_root_.Metric.closedBall 0 r)) :
    heightCapRegion G A a b c r \ _root_.Set.range f =
      (fun p : E × ℝ => (G p.2 p.1, p.2)) '' (_root_.Metric.ball 0 r ×ˢ _root_.Set.Icc a b) ∪
        A '' {p | p.1 ∈ _root_.Metric.closedBall 0 r ∧ b ≤ p.2 ∧ p.2 < c - ‖p.1‖ ^ 2 / 2} := by
  have hcyl := image_cylinder_inter_range f G hlevels
  have hcap := image_quadratic_cap_inter_range f A hb hr hrR hrτ hgraph
  rw [heightCapRegion, _root_.Set.union_sdiff_distrib]
  congr 1
  · apply Subset.antisymm
    · rintro z ⟨⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩, hz⟩
      refine ⟨(y, t), ⟨?_, ht⟩, rfl⟩
      rw [← _root_.Metric.closedBall_sdiff_sphere]
      refine ⟨hy, fun hys => hz ?_⟩
      exact (hcyl.symm.subset (_root_.Set.mem_image_of_mem _ ⟨hys, ht⟩)).2
    · rintro z ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
      refine ⟨mem_image_of_mem _ ⟨ball_subset_closedBall hy, ht⟩, fun hz => ?_⟩
      obtain ⟨⟨w, u⟩, ⟨hw, _⟩, hwt⟩ := hcyl.subset
        ⟨mem_image_of_mem _ ⟨ball_subset_closedBall hy, ht⟩, hz⟩
      have hut : u = t := congrArg Prod.snd hwt
      subst u
      have hwy : w = y := hG t ht (_root_.Metric.sphere_subset_closedBall hw)
        (_root_.Metric.ball_subset_closedBall hy) (congrArg Prod.fst hwt)
      exact disjoint_left.mp _root_.Metric.sphere_disjoint_ball (hwy ▸ hw) hy
  · apply Subset.antisymm
    · rintro z ⟨⟨p, hp, rfl⟩, hz⟩
      refine ⟨p, ⟨hp.1, hp.2.1, lt_of_le_of_ne hp.2.2 ?_⟩, rfl⟩
      intro heq
      apply hz
      exact (hcap.symm.subset ⟨p.1, hp.1,
        congrArg A (show (p.1, c - ‖p.1‖ ^ 2 / 2) = p from Prod.ext rfl heq.symm)⟩).2
    · rintro z ⟨p, hp, rfl⟩
      refine ⟨mem_image_of_mem _ ⟨hp.1, hp.2.1, hp.2.2.le⟩, fun hz => ?_⟩
      obtain ⟨y, _, hyp⟩ := hcap.subset
        ⟨mem_image_of_mem _ ⟨hp.1, hp.2.1, hp.2.2.le⟩, hz⟩
      have hyp' := A.injective hyp
      have hy : y = p.1 := congrArg Prod.fst hyp'
      have ht := congrArg Prod.snd hyp'
      rw [hy] at ht
      exact hp.2.2.ne ht.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.heightCapRegion_sdiff_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.heightCapRegion_sdiff_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.heightCapRegion_sdiff_range ``Submission.DifferentialGeometry.Topology.SphereSeparation.heightCapRegion_sdiff_range

end DifferentialGeometry.Topology.SphereSeparation
