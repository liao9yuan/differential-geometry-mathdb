import Submission.DifferentialGeometry.Topology.VanKampen.TwoSidedCollarRescale
import Mathlib.Topology.Compactness.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

def inl
    {B C X : Type*} [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace X]
    {e : B → X} {f : C → X} (c : TwoSidedCollar (Sum.elim e f)) : TwoSidedCollar e where
  toFun p := c.toFun (Sum.inl p.1, p.2)
  isOpenEmbedding_toFun := c.isOpenEmbedding_toFun.comp
    (_root_.Topology.IsOpenEmbedding.inl.prodMap _root_.Topology.IsOpenEmbedding.id)
  zero_eq b := c.zero_eq (Sum.inl b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.inl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.inl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.inl ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.inl

def inr
    {B C X : Type*} [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace X]
    {e : B → X} {f : C → X} (c : TwoSidedCollar (Sum.elim e f)) : TwoSidedCollar f where
  toFun p := c.toFun (Sum.inr p.1, p.2)
  isOpenEmbedding_toFun := c.isOpenEmbedding_toFun.comp
    (_root_.Topology.IsOpenEmbedding.inr.prodMap _root_.Topology.IsOpenEmbedding.id)
  zero_eq b := c.zero_eq (Sum.inr b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.inr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.inr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.inr ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.inr

theorem exists_subcollar_subset_open
    {B X : Type*} [TopologicalSpace B] [CompactSpace B] [TopologicalSpace X]
    {e : B → X} (c : TwoSidedCollar e) {U : Set X} (hU : IsOpen U)
    (hzero : Set.range e ⊆ U) :
    ∃ d : TwoSidedCollar e, d.range ⊆ U ∧ d.range ⊆ c.range := by
  have hpre : IsOpen (c.toFun ⁻¹' U) := hU.preimage c.isOpenEmbedding_toFun.continuous
  have hprod : (_root_.Set.univ : Set B) ×ˢ ({0} : Set ℝ) ⊆ c.toFun ⁻¹' U := by
    rintro ⟨b, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact hzero ⟨b, (c.zero_eq b).symm⟩
  obtain ⟨A, V, _, hV, hA, h₀, hAV⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hpre hprod
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (h₀ (_root_.Set.mem_singleton 0)))
  let φ : B × _root_.Set.Ioo (-r) r → X := fun p ↦ c.toFun (p.1, p.2.val)
  have hφ : _root_.Topology.IsOpenEmbedding φ :=
    c.isOpenEmbedding_toFun.comp
      (_root_.Topology.IsOpenEmbedding.id.prodMap isOpen_Ioo.isOpenEmbedding_subtypeVal)
  let d := ofOpenInterval hr φ hφ (fun b ↦ c.zero_eq b)
  refine ⟨d, ?_, ?_⟩
  · rintro x ⟨p, rfl⟩
    change c.toFun (p.1, (realHomeomorphIoo r hr p.2).val) ∈ U
    apply hAV
    refine ⟨hA (_root_.Set.mem_univ _), hball ?_⟩
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using (realHomeomorphIoo r hr p.2).property
  · rintro x ⟨p, rfl⟩
    exact ⟨(p.1, (realHomeomorphIoo r hr p.2).val), rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.exists_subcollar_subset_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.exists_subcollar_subset_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.exists_subcollar_subset_open ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.exists_subcollar_subset_open

def sum
    {B C X : Type*} [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace X]
    {e : B → X} {f : C → X} (c : TwoSidedCollar e) (d : TwoSidedCollar f)
    (hd : Disjoint c.range d.range) : TwoSidedCollar (Sum.elim e f) := by
  let φ := Sum.elim c.toFun d.toFun
  have hφinj : Function.Injective φ := by
    intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (c.isOpenEmbedding_toFun.injective hxy)
      | inr y => exact False.elim (disjoint_left.mp hd ⟨x, rfl⟩ ⟨y, hxy.symm⟩)
    | inr x =>
      cases y with
      | inl y => exact False.elim (disjoint_left.mp hd ⟨y, hxy.symm⟩ ⟨x, rfl⟩)
      | inr y => exact congrArg Sum.inr (d.isOpenEmbedding_toFun.injective hxy)
  exact {
    toFun := φ ∘ Homeomorph.sumProdDistrib
    isOpenEmbedding_toFun :=
      (c.isOpenEmbedding_toFun.sumElim d.isOpenEmbedding_toFun hφinj).comp
        Homeomorph.sumProdDistrib.isOpenEmbedding
    zero_eq := fun b ↦ by cases b <;> simp [φ, c.zero_eq, d.zero_eq] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.sum ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.sum

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
