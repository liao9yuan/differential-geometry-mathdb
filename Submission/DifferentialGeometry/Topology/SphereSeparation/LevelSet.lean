import Submission.DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation
import Submission.DifferentialGeometry.Topology.Manifold.RegularLevel.Components
import Submission.DifferentialGeometry.Topology.Morse.RegularSublevelBoundary
import Submission.DifferentialGeometry.Topology.Handle.SphereDisk
import Submission.DifferentialGeometry.Topology.SphereSeparation.HeightLevel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set

namespace DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation

variable {X α : Type*} [TopologicalSpace X] [LinearOrder α]

theorem levelSet_eq_of_isPreconnected {S : Set X} (d : TwoSidedSeparation S)
    {f : X → α} {a : α} (hS : S ⊆ {x | f x = a})
    (hlo : IsPreconnected {x | f x < a}) (hhi : IsPreconnected {x | a < f x})
    (hclo : {x | f x = a} ⊆ closure {x | f x < a})
    (hchi : {x | f x = a} ⊆ closure {x | a < f x}) :
    {x | f x = a} = S := by
  have hlS : {x | f x < a} ⊆ Sᶜ := by
    intro x hx hs
    exact (ne_of_lt hx) (hS hs)
  have hhS : {x | a < f x} ⊆ Sᶜ := by
    intro x hx hs
    exact (ne_of_gt hx) (hS hs)
  have hpcl : Disjoint (closure d.positiveSide) d.negativeSide :=
    d.disjoint.closure_left d.isOpen_negativeSide
  have hncl : Disjoint d.positiveSide (closure d.negativeSide) :=
    d.disjoint.closure_right d.isOpen_positiveSide
  have hdifferent (U V : Set X) (hne : V.Nonempty)
      (hdisj : Disjoint (closure U) V)
      (hl : {x | f x < a} ⊆ U) (hh : {x | a < f x} ⊆ U) : False := by
    obtain ⟨x, hx⟩ := hne
    rcases lt_trichotomy (f x) a with hlx | heq | hhx
    · exact disjoint_left.mp hdisj (subset_closure (hl hlx)) hx
    · exact disjoint_left.mp hdisj (closure_mono hl (hclo heq)) hx
    · exact disjoint_left.mp hdisj (subset_closure (hh hhx)) hx
  apply Subset.antisymm ?_ hS
  intro x hx
  by_contra hn
  have hxc : x ∈ d.positiveSide ∪ d.negativeSide := d.union_eq_compl.symm.subset hn
  rcases d.subset_positiveSide_or_subset_negativeSide hlo hlS with hl | hl
  · rcases d.subset_positiveSide_or_subset_negativeSide hhi hhS with hh | hh
    · exact hdifferent _ _ d.nonempty_negativeSide hpcl hl hh
    · rcases hxc with hxp | hxn
      · exact disjoint_left.mp hncl hxp (closure_mono hh (hchi hx))
      · exact disjoint_left.mp hpcl (closure_mono hl (hclo hx)) hxn
  · rcases d.subset_positiveSide_or_subset_negativeSide hhi hhS with hh | hh
    · rcases hxc with hxp | hxn
      · exact disjoint_left.mp hncl hxp (closure_mono hl (hclo hx))
      · exact disjoint_left.mp hpcl (closure_mono hh (hchi hx)) hxn
    · exact hdifferent _ _ d.nonempty_positiveSide hncl.symm hl hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.levelSet_eq_of_isPreconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.levelSet_eq_of_isPreconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.levelSet_eq_of_isPreconnected ``Submission.DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.levelSet_eq_of_isPreconnected

theorem side_subset_gt_of_isPreconnected_lt {S : Set X} (d : TwoSidedSeparation S)
    {f : X → α} {a : α} (hS : S ⊆ {x | f x = a})
    (hlo : IsPreconnected {x | f x < a})
    (hclo : {x | f x = a} ⊆ closure {x | f x < a}) :
    d.positiveSide ⊆ {x | a < f x} ∨ d.negativeSide ⊆ {x | a < f x} := by
  have hlS : {x | f x < a} ⊆ Sᶜ := fun x hx hs => (ne_of_lt hx) (hS hs)
  have hside (U V : Set X) (hdisj : Disjoint (closure U) V)
      (hl : {x | f x < a} ⊆ U) : V ⊆ {x | a < f x} := by
    intro x hx
    rcases lt_trichotomy (f x) a with hlx | heq | hhx
    · exact False.elim (disjoint_left.mp hdisj (subset_closure (hl hlx)) hx)
    · exact False.elim (disjoint_left.mp hdisj (closure_mono hl (hclo heq)) hx)
    · exact hhx
  rcases d.subset_positiveSide_or_subset_negativeSide hlo hlS with hl | hl
  · exact Or.inr (hside _ _ (d.disjoint.closure_left d.isOpen_negativeSide) hl)
  · exact Or.inl (hside _ _ (d.disjoint.symm.closure_left d.isOpen_positiveSide) hl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.side_subset_gt_of_isPreconnected_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.side_subset_gt_of_isPreconnected_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.side_subset_gt_of_isPreconnected_lt ``Submission.DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.side_subset_gt_of_isPreconnected_lt

end DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation

open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem range_eq_levelSet_of_isPreconnected
    {f : SphereTwo → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (hr : ∀ x, f x = a → ¬ Morse.IsCriticalPointAt (𝓡 2) f x)
    {η : AddCircle (1 : ℝ) → SphereTwo}
    (hη : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η)
    (hηf : _root_.Set.range η ⊆ {x | f x = a})
    (hlo : IsPreconnected {x | f x < a}) (hhi : IsPreconnected {x | a < f x}) :
    range η = {x | f x = a} := by
  obtain ⟨b₀, b₁, hb₀, hb₁, hboundary₀, hboundary₁, hcover, hinter⟩ :=
    Handle.exists_two_smooth_disks_sphere_of_circle hη
  let _ : Nonempty (ClosedCell 2) := ⟨⟨0, by simp⟩⟩
  let d := TwoSidedSeparation.ofClosedCover
    (Handle.closure_interior_range_closedCell_sphere 1 hb₀)
    (Handle.closure_interior_range_closedCell_sphere 1 hb₁)
    (_root_.Set.range_nonempty b₀) (_root_.Set.range_nonempty b₁) hcover hinter
    ((Handle.frontier_range_closedCell_sphere 1 hb₀).trans hboundary₀)
    ((Handle.frontier_range_closedCell_sphere 1 hb₁).trans hboundary₁)
  have hneg : ∀ x, (-f) x = -a → ¬ Morse.IsCriticalPointAt (𝓡 2) (-f) x := by
    intro x hx hc
    apply hr x (neg_injective hx)
    change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (-f) x = 0 at hc
    rw [mfderiv_neg] at hc
    unfold Morse.IsCriticalPointAt
    ext v
    have hv := congrArg (fun L => L v) hc
    change -(mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v) = 0 at hv
    exact neg_eq_zero.mp hv
  apply (d.levelSet_eq_of_isPreconnected hηf hlo hhi ?_ ?_).symm
  · rw [Morse.closure_lt_sublevel_eq_sublevel f a hf hr]
    exact fun x hx => hx.le
  · have hupper : closure {x | a < f x} = {x | a ≤ f x} := by
      simpa only [Pi.neg_apply, neg_lt_neg_iff, neg_le_neg_iff] using
        Morse.closure_lt_sublevel_eq_sublevel (-f) (-a) hf.neg hneg
    rw [hupper]
    exact fun x hx => hx.ge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.range_eq_levelSet_of_isPreconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.range_eq_levelSet_of_isPreconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.range_eq_levelSet_of_isPreconnected ``Submission.DifferentialGeometry.Topology.SphereSeparation.range_eq_levelSet_of_isPreconnected

theorem exists_source_height_level_circle_of_isPreconnected
    {e : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, EuclideanThree) ∞ e)
    {a : ℝ} (hne : {x | e x 2 = a}.Nonempty)
    (hr : ∀ x, e x 2 = a → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0)
    (hlo : IsPreconnected {x | e x 2 < a}) (hhi : IsPreconnected {x | a < e x 2}) :
    ∃ η : AddCircle (1 : ℝ) → SphereTwo,
      Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η ∧
      range η = {x | e x 2 = a} := by
  obtain ⟨_, η, hη, _, hcover⟩ := exists_source_height_level_circles he a hr
  obtain ⟨x, hx⟩ := hne
  obtain ⟨C, _⟩ := mem_iUnion.mp (hcover.symm.subset hx)
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun y => e y 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  refine ⟨η C, hη C, range_eq_levelSet_of_isPreconnected hf hr (hη C) ?_ hlo hhi⟩
  exact (_root_.Set.subset_iUnion (fun C => _root_.Set.range (η C)) C).trans hcover.subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_source_height_level_circle_of_isPreconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_source_height_level_circle_of_isPreconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_source_height_level_circle_of_isPreconnected ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_source_height_level_circle_of_isPreconnected

theorem exists_disk_superlevel_component_of_isPreconnected_lt
    {f : SphereTwo → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (hr : ∀ x, f x = a → ¬ Morse.IsCriticalPointAt (𝓡 2) f x)
    {η : AddCircle (1 : ℝ) → SphereTwo}
    (hη : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η)
    (hηf : _root_.Set.range η ⊆ {x | f x = a}) (hlo : IsPreconnected {x | f x < a}) :
    ∃ b : ClosedCell 2 → SphereTwo,
      Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b ∧
      _root_.Set.range (b ∘ cellBoundaryInclusion 2) = _root_.Set.range η ∧
      ∃ p ∈ interior (_root_.Set.range b), a < f p ∧
        interior (_root_.Set.range b) = connectedComponentIn {x | a < f x} p ∧
        range b = closure (connectedComponentIn {x | a < f x} p) := by
  obtain ⟨b₀, b₁, hb₀, hb₁, hboundary₀, hboundary₁, hcover, hinter⟩ :=
    Handle.exists_two_smooth_disks_sphere_of_circle hη
  have hconn₀ := Handle.isConnected_interior_range_closedCell_sphere 1 hb₀
  have hconn₁ := Handle.isConnected_interior_range_closedCell_sphere 1 hb₁
  let _ : Nonempty (ClosedCell 2) := ⟨⟨0, by simp⟩⟩
  let d := TwoSidedSeparation.ofClosedCover
    (Handle.closure_interior_range_closedCell_sphere 1 hb₀)
    (Handle.closure_interior_range_closedCell_sphere 1 hb₁)
    (_root_.Set.range_nonempty b₀) (_root_.Set.range_nonempty b₁) hcover hinter
    ((Handle.frontier_range_closedCell_sphere 1 hb₀).trans hboundary₀)
    ((Handle.frontier_range_closedCell_sphere 1 hb₁).trans hboundary₁)
  have hclo : {x | f x = a} ⊆ closure {x | f x < a} := by
    rw [Morse.closure_lt_sublevel_eq_sublevel f a hf hr]
    exact fun x hx => hx.le
  have hU : {x | a < f x} ⊆ (_root_.Set.range η)ᶜ := fun x hx hηx => (ne_of_gt hx) (hηf hηx)
  rcases d.side_subset_gt_of_isPreconnected_lt hηf hlo hclo with hside | hside
  · obtain ⟨p, hp⟩ := hconn₀.nonempty
    have heq := d.positiveSide_eq_connectedComponentIn hU hconn₀.isPreconnected hside hp
    refine ⟨b₀, hb₀, hboundary₀, p, hp, hside hp, heq, ?_⟩
    rw [← heq]
    exact (Handle.closure_interior_range_closedCell_sphere 1 hb₀).symm
  · obtain ⟨p, hp⟩ := hconn₁.nonempty
    have heq := d.negativeSide_eq_connectedComponentIn hU hconn₁.isPreconnected hside hp
    refine ⟨b₁, hb₁, hboundary₁, p, hp, hside hp, heq, ?_⟩
    rw [← heq]
    exact (Handle.closure_interior_range_closedCell_sphere 1 hb₁).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_disk_superlevel_component_of_isPreconnected_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_disk_superlevel_component_of_isPreconnected_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_disk_superlevel_component_of_isPreconnected_lt ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_disk_superlevel_component_of_isPreconnected_lt

theorem range_eq_of_mem_closure_superlevel_component
    {f : SphereTwo → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (hr : ∀ x, f x = a → ¬ Morse.IsCriticalPointAt (𝓡 2) f x)
    {η₀ η₁ : AddCircle (1 : ℝ) → SphereTwo}
    (hη₀ : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η₀)
    (hη₁ : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η₁)
    (hη₀f : _root_.Set.range η₀ ⊆ {x | f x = a}) (hη₁f : _root_.Set.range η₁ ⊆ {x | f x = a})
    (hlo : IsPreconnected {x | f x < a}) {p x₀ x₁ : SphereTwo}
    (hx₀ : x₀ ∈ _root_.Set.range η₀) (hx₁ : x₁ ∈ _root_.Set.range η₁)
    (hx₀C : x₀ ∈ closure (connectedComponentIn {x | a < f x} p))
    (hx₁C : x₁ ∈ closure (connectedComponentIn {x | a < f x} p)) :
    range η₀ = _root_.Set.range η₁ := by
  obtain ⟨b₀, hb₀, hboundary₀, p₀, _, _, _, hclosure₀⟩ :=
    exists_disk_superlevel_component_of_isPreconnected_lt hf hr hη₀ hη₀f hlo
  obtain ⟨b₁, hb₁, hboundary₁, p₁, _, _, _, hclosure₁⟩ :=
    exists_disk_superlevel_component_of_isPreconnected_lt hf hr hη₁ hη₁f hlo
  have hx₀b : x₀ ∈ _root_.Set.range b₀ := by
    obtain ⟨u, hu⟩ := hboundary₀.symm.subset hx₀
    exact ⟨cellBoundaryInclusion 2 u, hu⟩
  have hx₁b : x₁ ∈ _root_.Set.range b₁ := by
    obtain ⟨u, hu⟩ := hboundary₁.symm.subset hx₁
    exact ⟨cellBoundaryInclusion 2 u, hu⟩
  have hC₀ := DifferentialGeometry.Manifold.RegularLevel.superlevel_connectedComponentIn_eq_of_mem_closure
    (𝓡 2) hf (hη₀f hx₀) (hr x₀ (hη₀f hx₀)) (hclosure₀.subset hx₀b) hx₀C
  have hC₁ := DifferentialGeometry.Manifold.RegularLevel.superlevel_connectedComponentIn_eq_of_mem_closure
    (𝓡 2) hf (hη₁f hx₁) (hr x₁ (hη₁f hx₁)) (hclosure₁.subset hx₁b) hx₁C
  have heq : _root_.Set.range b₀ = _root_.Set.range b₁ := by rw [hclosure₀, hclosure₁, hC₀, hC₁]
  exact ((Handle.frontier_range_closedCell_sphere 1 hb₀).trans hboundary₀).symm.trans
    ((congrArg frontier heq).trans ((Handle.frontier_range_closedCell_sphere 1 hb₁).trans hboundary₁))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.range_eq_of_mem_closure_superlevel_component then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.range_eq_of_mem_closure_superlevel_component"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.range_eq_of_mem_closure_superlevel_component ``Submission.DifferentialGeometry.Topology.SphereSeparation.range_eq_of_mem_closure_superlevel_component

end DifferentialGeometry.Topology.SphereSeparation
