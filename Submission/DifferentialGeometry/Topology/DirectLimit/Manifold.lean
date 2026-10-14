import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Submission.DifferentialGeometry.Topology.DirectLimit.Basic
import Submission.DifferentialGeometry.Bundle.FiberBundleHausdorff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry

open _root_.Set _root_.Topology
open scoped _root_.Manifold _root_.ContDiff

namespace SeqSystem

section Charted

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
  [∀ k, Nonempty (A k)]
variable (S : SeqSystem A)

def inclHomeo (k : ℕ) : OpenPartialHomeomorph (A k) S.Lim :=
  (S.incl_isOpenEmb k).toOpenPartialHomeomorph (S.incl k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.inclHomeo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.inclHomeo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.inclHomeo ``Submission.DifferentialGeometry.SeqSystem.inclHomeo

@[simp] theorem inclHomeo_apply (k : ℕ) (x : A k) : S.inclHomeo k x = S.incl k x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.inclHomeo_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.inclHomeo_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.inclHomeo_apply ``Submission.DifferentialGeometry.SeqSystem.inclHomeo_apply

@[simp] theorem inclHomeo_source (k : ℕ) : (S.inclHomeo k).source = univ :=
  (S.incl_isOpenEmb k).toOpenPartialHomeomorph_source (S.incl k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.inclHomeo_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.inclHomeo_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.inclHomeo_source ``Submission.DifferentialGeometry.SeqSystem.inclHomeo_source

@[simp] theorem inclHomeo_target (k : ℕ) : (S.inclHomeo k).target = _root_.Set.range (S.incl k) :=
  (S.incl_isOpenEmb k).toOpenPartialHomeomorph_target (S.incl k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.inclHomeo_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.inclHomeo_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.inclHomeo_target ``Submission.DifferentialGeometry.SeqSystem.inclHomeo_target

theorem inclHomeo_symm_apply (k : ℕ) (x : A k) :
    (S.inclHomeo k).symm (S.incl k x) = x :=
  (S.incl_isOpenEmb k).toOpenPartialHomeomorph_left_inv (S.incl k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.inclHomeo_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.inclHomeo_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.inclHomeo_symm_apply ``Submission.DifferentialGeometry.SeqSystem.inclHomeo_symm_apply

def limChart (k : ℕ) (a : A k) : OpenPartialHomeomorph S.Lim H :=
  (S.inclHomeo k).symm.trans (chartAt H a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.limChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.limChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.limChart ``Submission.DifferentialGeometry.SeqSystem.limChart

theorem mem_limChart_source (k : ℕ) (a : A k) :
    S.incl k a ∈ (S.limChart (H := H) k a).source := by
  rw [limChart, OpenPartialHomeomorph.trans_source]
  refine ⟨?_, ?_⟩
  · rw [OpenPartialHomeomorph.symm_source, inclHomeo_target]
    exact ⟨a, rfl⟩
  · change (S.inclHomeo k).symm (S.incl k a) ∈ (chartAt H a).source
    rw [inclHomeo_symm_apply]
    exact mem_chart_source H a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.mem_limChart_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.mem_limChart_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.mem_limChart_source ``Submission.DifferentialGeometry.SeqSystem.mem_limChart_source


omit [∀ (k : ℕ), Nonempty (A k)] in
theorem exists_sigma_incl (z : S.Lim) : ∃ p : Σ k, A k, S.incl p.1 p.2 = z := by
  obtain ⟨k, x, hx⟩ := S.exists_incl_eq z
  exact ⟨⟨k, x⟩, hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.exists_sigma_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.exists_sigma_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.exists_sigma_incl ``Submission.DifferentialGeometry.SeqSystem.exists_sigma_incl


def rep (z : S.Lim) : Σ k, A k := (S.exists_sigma_incl z).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.rep then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.rep"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.rep ``Submission.DifferentialGeometry.SeqSystem.rep

omit [∀ (k : ℕ), Nonempty (A k)] in
theorem incl_rep (z : S.Lim) : S.incl (S.rep z).1 (S.rep z).2 = z :=
  (S.exists_sigma_incl z).choose_spec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.incl_rep then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.incl_rep"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.incl_rep ``Submission.DifferentialGeometry.SeqSystem.incl_rep

instance instChartedSpaceLim : ChartedSpace H S.Lim where
  atlas := ⋃ (k : ℕ), ⋃ (a : A k), {S.limChart k a}
  chartAt z := S.limChart (S.rep z).1 (S.rep z).2
  mem_chart_source z := by
    have hz : S.incl (S.rep z).1 (S.rep z).2 = z := S.incl_rep z
    have hmem := S.mem_limChart_source (H := H) (S.rep z).1 (S.rep z).2
    rwa [hz] at hmem
  chart_mem_atlas z := by
    simp only [_root_.Set.mem_iUnion, _root_.Set.mem_singleton_iff]
    exact ⟨(S.rep z).1, (S.rep z).2, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.instChartedSpaceLim then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.instChartedSpaceLim"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.instChartedSpaceLim ``Submission.DifferentialGeometry.SeqSystem.instChartedSpaceLim

theorem chartAt_lim (z : S.Lim) :
    chartAt H z = S.limChart (S.rep z).1 (S.rep z).2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.chartAt_lim then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.chartAt_lim"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.chartAt_lim ``Submission.DifferentialGeometry.SeqSystem.chartAt_lim

theorem limChart_mem_atlas (k : ℕ) (a : A k) : S.limChart k a ∈ atlas H S.Lim := by
  change S.limChart k a ∈ ⋃ (k : ℕ) (a : A k), {S.limChart k a}
  simp only [_root_.Set.mem_iUnion, _root_.Set.mem_singleton_iff]
  exact ⟨k, a, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.limChart_mem_atlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.limChart_mem_atlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.limChart_mem_atlas ``Submission.DifferentialGeometry.SeqSystem.limChart_mem_atlas

theorem mem_atlas_iff {e : OpenPartialHomeomorph S.Lim H} :
    e ∈ atlas H S.Lim ↔ ∃ (k : ℕ) (a : A k), e = S.limChart k a := by
  change e ∈ ⋃ (k : ℕ) (a : A k), {S.limChart k a} ↔ _
  simp only [_root_.Set.mem_iUnion, _root_.Set.mem_singleton_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.mem_atlas_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.mem_atlas_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.mem_atlas_iff ``Submission.DifferentialGeometry.SeqSystem.mem_atlas_iff


instance instSigmaCompactSpaceLim [∀ k, SigmaCompactSpace (A k)] :
    SigmaCompactSpace S.Lim := S.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.instSigmaCompactSpaceLim then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.instSigmaCompactSpaceLim"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.instSigmaCompactSpaceLim ``Submission.DifferentialGeometry.SeqSystem.instSigmaCompactSpaceLim


instance instT2SpaceLim [∀ k, T2Space (A k)] : T2Space S.Lim := S.t2Space

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.instT2SpaceLim then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.instT2SpaceLim"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.instT2SpaceLim ``Submission.DifferentialGeometry.SeqSystem.instT2SpaceLim

instance instNonemptyLim : Nonempty S.Lim :=
  ⟨S.incl 0 (Classical.arbitrary (A 0))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.instNonemptyLim then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.instNonemptyLim"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.instNonemptyLim ``Submission.DifferentialGeometry.SeqSystem.instNonemptyLim

instance instPreconnectedLim [∀ k, PreconnectedSpace (A k)] :
    PreconnectedSpace S.Lim := by
  constructor
  rw [← S.iUnion_range_incl]
  refine isPreconnected_iUnion ⟨S.incl 0 (Classical.arbitrary (A 0)), ?_⟩ fun k => ?_
  · simp only [_root_.Set.mem_iInter]
    intro k
    exact S.range_incl_mono (Nat.zero_le k) ⟨Classical.arbitrary (A 0), rfl⟩
  · have h := (_root_.PreconnectedSpace.isPreconnected_univ (α := A k)).image (S.incl k)
      (S.continuous_incl k).continuousOn
    rwa [Set.image_univ] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.instPreconnectedLim then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.instPreconnectedLim"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.instPreconnectedLim ``Submission.DifferentialGeometry.SeqSystem.instPreconnectedLim

instance instConnectedSpaceLim [∀ k, PreconnectedSpace (A k)] :
    ConnectedSpace S.Lim where
  toPreconnectedSpace := S.instPreconnectedLim
  toNonempty := S.instNonemptyLim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.instConnectedSpaceLim then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.instConnectedSpaceLim"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.instConnectedSpaceLim ``Submission.DifferentialGeometry.SeqSystem.instConnectedSpaceLim

def transitionHomeo (k ℓ : ℕ) : OpenPartialHomeomorph (A k) (A ℓ) :=
  (S.inclHomeo k).trans (S.inclHomeo ℓ).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.transitionHomeo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.transitionHomeo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.transitionHomeo ``Submission.DifferentialGeometry.SeqSystem.transitionHomeo

theorem mem_transitionHomeo_source {k ℓ : ℕ} {w : A k} :
    w ∈ (S.transitionHomeo k ℓ).source ↔ S.incl k w ∈ _root_.Set.range (S.incl ℓ) := by
  rw [transitionHomeo, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    inclHomeo_source, inclHomeo_target, _root_.Set.univ_inter, _root_.Set.mem_preimage, inclHomeo_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.mem_transitionHomeo_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.mem_transitionHomeo_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.mem_transitionHomeo_source ``Submission.DifferentialGeometry.SeqSystem.mem_transitionHomeo_source

theorem transitionHomeo_apply {k ℓ : ℕ} (w : A k) :
    S.transitionHomeo k ℓ w = (S.inclHomeo ℓ).symm (S.incl k w) := by
  rw [transitionHomeo, OpenPartialHomeomorph.trans_apply, inclHomeo_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.transitionHomeo_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.transitionHomeo_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.transitionHomeo_apply ``Submission.DifferentialGeometry.SeqSystem.transitionHomeo_apply

theorem incl_transitionHomeo {k ℓ : ℕ} {w : A k} (hw : w ∈ (S.transitionHomeo k ℓ).source) :
    S.incl ℓ (S.transitionHomeo k ℓ w) = S.incl k w := by
  have hmem : S.incl k w ∈ (S.inclHomeo ℓ).target := by
    rw [inclHomeo_target]; exact (S.mem_transitionHomeo_source).mp hw
  rw [transitionHomeo_apply, ← inclHomeo_apply, OpenPartialHomeomorph.right_inv _ hmem]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.incl_transitionHomeo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.incl_transitionHomeo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.incl_transitionHomeo ``Submission.DifferentialGeometry.SeqSystem.incl_transitionHomeo

theorem limChart_symm_trans (k ℓ : ℕ) (a : A k) (b : A ℓ) :
    (S.limChart k a).symm.trans (S.limChart ℓ b)
      = ((chartAt H a).symm.trans (S.transitionHomeo k ℓ)).trans (chartAt H b) := by
  simp only [limChart, transitionHomeo, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.limChart_symm_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.limChart_symm_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.limChart_symm_trans ``Submission.DifferentialGeometry.SeqSystem.limChart_symm_trans

end Charted

end SeqSystem

structure SmoothSeqSystem
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (A : ℕ → Type u) [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
    [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
    extends SeqSystem A where
  contMDiff_map : ∀ {k ℓ : ℕ} (h : k ≤ ℓ), ContMDiff I I ∞ (toSeqSystem.map h)
  contMDiffOn_invFun_map : ∀ {k ℓ : ℕ} (h : k ≤ ℓ),
    ContMDiffOn I I ∞ (Function.invFun (toSeqSystem.map h)) (Set.range (toSeqSystem.map h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothSeqSystem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothSeqSystem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothSeqSystem ``Submission.DifferentialGeometry.SmoothSeqSystem

theorem modelSpace_contDiffOn
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] [Nonempty H] {I : ModelWithCorners ℝ E H}
    {f : H → H} {s : Set H} (hf : ContMDiffOn I I ∞ f s) :
    ContDiffOn ℝ ∞ (↑I ∘ f ∘ ↑I.symm) (↑I.symm ⁻¹' s ∩ _root_.Set.range ↑I) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty H)
  have hs : s ⊆ (extChartAt I x₀).source := by
    simp only [extChartAt_source, chartAt_self_eq, OpenPartialHomeomorph.refl_source,
      _root_.Set.subset_univ]
  have h2s : _root_.Set.MapsTo f s (extChartAt I x₀).source := by
    simp only [extChartAt_source, chartAt_self_eq, OpenPartialHomeomorph.refl_source]
    exact _root_.Set.mapsTo_univ _ _
  have h := (contMDiffOn_iff_of_subset_source' hs h2s).mp hf
  have hset : extChartAt I x₀ '' s = ↑I.symm ⁻¹' s ∩ _root_.Set.range ↑I := by
    rw [← I.image_eq]
    apply Set.image_congr'
    intro z
    simp only [extChartAt_coe, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
      Function.comp_apply, id_eq]
  rw [hset] at h
  refine h.congr (fun z _ => ?_)
  simp only [Function.comp_apply, extChartAt_coe, extChartAt_coe_symm, chartAt_self_eq,
    OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.modelSpace_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.modelSpace_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.modelSpace_contDiffOn ``Submission.DifferentialGeometry.modelSpace_contDiffOn

namespace SmoothSeqSystem

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
  [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
variable (S : SmoothSeqSystem I A)


omit [∀ (k : ℕ), IsManifold I ∞ (A k)] [∀ (k : ℕ), Nonempty (A k)] in
theorem succMap_contMDiff (f : ∀ k, A k → A (k + 1))
    (hf : ∀ k, ContMDiff I I ∞ (f k)) {k ℓ : ℕ} (h : k ≤ ℓ) :
    ContMDiff I I ∞ (SeqSystem.succMap f h) := by
  induction ℓ, h using Nat.le_induction with
  | base =>
      have hfun : SeqSystem.succMap f (Nat.le_refl k) = id := by
        funext x
        exact Nat.leRecOn_self x
      rw [hfun]
      exact contMDiff_id
  | succ ℓ hkℓ ih =>
      have hfun : SeqSystem.succMap f (Nat.le.step hkℓ) =
          f ℓ ∘ SeqSystem.succMap f hkℓ := by
        funext x
        exact Nat.leRecOn_succ hkℓ x
      rw [hfun]
      exact (hf ℓ).comp ih

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothSeqSystem.succMap_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothSeqSystem.succMap_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothSeqSystem.succMap_contMDiff ``Submission.DifferentialGeometry.SmoothSeqSystem.succMap_contMDiff

omit [∀ (k : ℕ), IsManifold I ∞ (A k)] in
theorem succMap_inv_mdiff (f : ∀ k, A k → A (k + 1))
    (hemb : ∀ k, _root_.Topology.IsOpenEmbedding (f k))
    (hfInv : ∀ k, ContMDiffOn I I ∞ (Function.invFun (f k)) (Set.range (f k)))
    {k ℓ : ℕ} (h : k ≤ ℓ) :
    ContMDiffOn I I ∞ (Function.invFun (SeqSystem.succMap f h))
      (Set.range (SeqSystem.succMap f h)) := by
  induction ℓ, h using Nat.le_induction with
  | base =>
      have hfun : SeqSystem.succMap f (Nat.le_refl k) = id := by
        funext x
        exact Nat.leRecOn_self x
      rw [hfun]
      have hinvId : Function.invFun (id : A k → A k) = id := by
        funext x
        exact Function.leftInverse_invFun Function.injective_id x
      rw [hinvId]
      simpa using
        (contMDiff_id : ContMDiff I I ∞ (id : A k → A k)).contMDiffOn
  | succ ℓ hkℓ ih =>
      let prev : A k → A ℓ := SeqSystem.succMap f hkℓ
      have hfun : SeqSystem.succMap f (Nat.le.step hkℓ) = f ℓ ∘ prev := by
        funext x
        exact Nat.leRecOn_succ hkℓ x
      rw [hfun]
      have hprev : Function.Injective prev :=
        (SeqSystem.succMap_isOpenEmb f hemb hkℓ).injective
      have htotal : Function.Injective (f ℓ ∘ prev) := (hemb ℓ).injective.comp hprev
      have hinvTotal : ContMDiffOn I I ∞ (Function.invFun (f ℓ))
          (Set.range (f ℓ ∘ prev)) := by
        refine (hfInv ℓ).mono ?_
        rintro y ⟨x, rfl⟩
        exact ⟨prev x, rfl⟩
      have hmaps : Set.MapsTo (Function.invFun (f ℓ)) (Set.range (f ℓ ∘ prev))
          (Set.range prev) := by
        rintro y ⟨x, rfl⟩
        simp only [Function.comp_apply]
        rw [Function.leftInverse_invFun (hemb ℓ).injective]
        exact ⟨x, rfl⟩
      have hiPrev : ContMDiffOn I I ∞ (Function.invFun prev) (Set.range prev) := by
        simpa only [prev] using ih
      have hsmooth := hiPrev.comp hinvTotal hmaps
      refine hsmooth.congr (fun y hy => ?_)
      obtain ⟨x, rfl⟩ := hy
      simp only [Function.comp_apply]
      rw [Function.leftInverse_invFun (hemb ℓ).injective,
        Function.leftInverse_invFun hprev]
      change Function.invFun (f ℓ ∘ prev) ((f ℓ ∘ prev) x) = x
      exact Function.leftInverse_invFun htotal x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothSeqSystem.succMap_inv_mdiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothSeqSystem.succMap_inv_mdiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothSeqSystem.succMap_inv_mdiff ``Submission.DifferentialGeometry.SmoothSeqSystem.succMap_inv_mdiff

def ofSucc (f : ∀ k, A k → A (k + 1))
    (hemb : ∀ k, _root_.Topology.IsOpenEmbedding (f k))
    (hf : ∀ k, ContMDiff I I ∞ (f k))
    (hfInv : ∀ k, ContMDiffOn I I ∞ (Function.invFun (f k)) (Set.range (f k))) :
    SmoothSeqSystem I A where
  toSeqSystem := SeqSystem.ofSucc f hemb
  contMDiff_map h := succMap_contMDiff f hf h
  contMDiffOn_invFun_map h := succMap_inv_mdiff f hemb hfInv h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothSeqSystem.ofSucc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothSeqSystem.ofSucc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothSeqSystem.ofSucc ``Submission.DifferentialGeometry.SmoothSeqSystem.ofSucc


@[simp] theorem ofSucc_map_succ (f : ∀ k, A k → A (k + 1))
    (hemb : ∀ k, _root_.Topology.IsOpenEmbedding (f k))
    (hf : ∀ k, ContMDiff I I ∞ (f k))
    (hfInv : ∀ k, ContMDiffOn I I ∞ (Function.invFun (f k)) (Set.range (f k)))
    (k : ℕ) :
    (ofSucc (I := I) f hemb hf hfInv).toSeqSystem.map (Nat.le_succ k) = f k := by
  funext x
  change SeqSystem.succMap f (Nat.le_succ k) x = f k x
  unfold SeqSystem.succMap
  rw [show Nat.le_succ k = Nat.le.step (Nat.le_refl k) by rfl,
    Nat.leRecOn_succ (Nat.le_refl k) x, Nat.leRecOn_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothSeqSystem.ofSucc_map_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothSeqSystem.ofSucc_map_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothSeqSystem.ofSucc_map_succ ``Submission.DifferentialGeometry.SmoothSeqSystem.ofSucc_map_succ

theorem transitionHomeo_contMDiffOn (k ℓ : ℕ) :
    ContMDiffOn I I ∞ (S.toSeqSystem.transitionHomeo k ℓ)
      (S.toSeqSystem.transitionHomeo k ℓ).source := by
  set m := _root_.Max.max k ℓ with hm
  have hkm : k ≤ m := le_max_left k ℓ
  have hℓm : ℓ ≤ m := le_max_right k ℓ
  have hFeq : ∀ w ∈ (S.toSeqSystem.transitionHomeo k ℓ).source,
      S.toSeqSystem.map hℓm (S.toSeqSystem.transitionHomeo k ℓ w) = S.toSeqSystem.map hkm w := by
    intro w hw
    apply S.toSeqSystem.incl_injective m
    rw [S.toSeqSystem.incl_comp hℓm, S.toSeqSystem.incl_comp hkm,
      S.toSeqSystem.incl_transitionHomeo hw]
  have hpt : ∀ w ∈ (S.toSeqSystem.transitionHomeo k ℓ).source,
      S.toSeqSystem.transitionHomeo k ℓ w
        = (Function.invFun (S.toSeqSystem.map hℓm) ∘ S.toSeqSystem.map hkm) w := by
    intro w hw
    change S.toSeqSystem.transitionHomeo k ℓ w = Function.invFun (S.toSeqSystem.map hℓm)
      (S.toSeqSystem.map hkm w)
    rw [← hFeq w hw,
      Function.leftInverse_invFun (S.toSeqSystem.isOpenEmb hℓm).injective]
  have hrange : (S.toSeqSystem.transitionHomeo k ℓ).source ⊆
      S.toSeqSystem.map hkm ⁻¹' _root_.Set.range (S.toSeqSystem.map hℓm) := by
    intro w hw
    exact ⟨S.toSeqSystem.transitionHomeo k ℓ w, hFeq w hw⟩
  refine ContMDiffOn.congr ?_ (fun w hw => hpt w hw)
  exact (S.contMDiffOn_invFun_map hℓm).comp ((S.contMDiff_map hkm).contMDiffOn) hrange

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothSeqSystem.transitionHomeo_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothSeqSystem.transitionHomeo_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothSeqSystem.transitionHomeo_contMDiffOn ``Submission.DifferentialGeometry.SmoothSeqSystem.transitionHomeo_contMDiffOn

instance instIsManifoldLim : IsManifold I ∞ S.toSeqSystem.Lim := by
  have : Nonempty H :=
    ⟨chartAt H (Classical.arbitrary (A 0)) (Classical.arbitrary (A 0))⟩
  apply isManifold_of_contDiffOn I ∞ S.toSeqSystem.Lim
  intro e₁ e₂ h₁ h₂
  obtain ⟨k, a, rfl⟩ := (S.toSeqSystem.mem_atlas_iff).mp h₁
  obtain ⟨ℓ, b, rfl⟩ := (S.toSeqSystem.mem_atlas_iff).mp h₂
  rw [S.toSeqSystem.limChart_symm_trans]
  set T' := ((chartAt H a).symm.trans (S.toSeqSystem.transitionHomeo k ℓ)).trans (chartAt H b)
    with hT'
  apply modelSpace_contDiffOn
  have key : ContMDiffOn I I ∞
      (⇑(chartAt H b) ∘ ⇑(S.toSeqSystem.transitionHomeo k ℓ) ∘ ⇑(chartAt H a).symm)
      (((chartAt H a).target ∩ (chartAt H a).symm ⁻¹' (S.toSeqSystem.transitionHomeo k ℓ).source) ∩
        (⇑(S.toSeqSystem.transitionHomeo k ℓ) ∘ ⇑(chartAt H a).symm) ⁻¹' (chartAt H b).source) :=
    (contMDiffOn_chart).comp' ((S.transitionHomeo_contMDiffOn k ℓ).comp' contMDiffOn_chart_symm)
  have hsrc : T'.source =
      ((chartAt H a).target ∩ (chartAt H a).symm ⁻¹' (S.toSeqSystem.transitionHomeo k ℓ).source) ∩
        (⇑(S.toSeqSystem.transitionHomeo k ℓ) ∘ ⇑(chartAt H a).symm) ⁻¹' (chartAt H b).source := by
    simp only [hT', OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.coe_trans]
  rw [hsrc]
  refine key.congr (fun z _ => ?_)
  rw [hT']
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothSeqSystem.instIsManifoldLim then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothSeqSystem.instIsManifoldLim"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothSeqSystem.instIsManifoldLim ``Submission.DifferentialGeometry.SmoothSeqSystem.instIsManifoldLim

theorem contMDiff_incl (k : ℕ) : ContMDiff I I ∞ (S.toSeqSystem.incl k) := by
  intro a
  have hchart : ContMDiffAt I I ∞ (chartAt H a) a :=
    contMDiffOn_chart.contMDiffAt ((chartAt H a).open_source.mem_nhds (mem_chart_source H a))
  have hlim_max : S.toSeqSystem.limChart k a ∈ IsManifold.maximalAtlas I ∞ S.toSeqSystem.Lim :=
    IsManifold.subset_maximalAtlas (S.toSeqSystem.limChart_mem_atlas k a)
  have htarget : chartAt H a a ∈ (S.toSeqSystem.limChart k a).target := by
    have hmem : S.toSeqSystem.incl k a ∈ (S.toSeqSystem.limChart k a).source :=
      S.toSeqSystem.mem_limChart_source (H := H) k a
    have hval0 : S.toSeqSystem.limChart k a (S.toSeqSystem.incl k a) = chartAt H a a := by
      unfold SeqSystem.limChart
      rw [OpenPartialHomeomorph.trans_apply, SeqSystem.inclHomeo_symm_apply]
    rw [← hval0]
    exact (S.toSeqSystem.limChart k a).map_source hmem
  have hsymm : ContMDiffAt I I ∞ (S.toSeqSystem.limChart k a).symm (chartAt H a a) :=
    contMDiffAt_symm_of_mem_maximalAtlas hlim_max htarget
  refine (hsymm.comp a hchart).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt H a).open_source.mem_nhds (mem_chart_source H a)] with a' ha'
  have hmem : S.toSeqSystem.incl k a' ∈ (S.toSeqSystem.limChart (H := H) k a).source := by
    unfold SeqSystem.limChart
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.symm_source, SeqSystem.inclHomeo_target]; exact ⟨a', rfl⟩
    · change (S.toSeqSystem.inclHomeo k).symm (S.toSeqSystem.incl k a') ∈ (chartAt H a).source
      rw [SeqSystem.inclHomeo_symm_apply]; exact ha'
  have hval : S.toSeqSystem.limChart k a (S.toSeqSystem.incl k a') = chartAt H a a' := by
    unfold SeqSystem.limChart
    rw [OpenPartialHomeomorph.trans_apply, SeqSystem.inclHomeo_symm_apply]
  change S.toSeqSystem.incl k a' = (S.toSeqSystem.limChart k a).symm (chartAt H a a')
  rw [← hval, (S.toSeqSystem.limChart k a).left_inv hmem]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothSeqSystem.contMDiff_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothSeqSystem.contMDiff_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothSeqSystem.contMDiff_incl ``Submission.DifferentialGeometry.SmoothSeqSystem.contMDiff_incl

theorem contMDiffAt_invIncl (k : ℕ) {z : S.toSeqSystem.Lim}
    (hz : z ∈ Set.range (S.toSeqSystem.incl k)) :
    ContMDiffAt I I ∞ (Function.invFun (S.toSeqSystem.incl k)) z := by
  obtain ⟨a, rfl⟩ := hz
  have hchart : ContMDiffAt I I ∞ (S.toSeqSystem.limChart k a) (S.toSeqSystem.incl k a) :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (S.toSeqSystem.limChart_mem_atlas k a))
      (S.toSeqSystem.mem_limChart_source (H := H) k a)
  have hval0 : S.toSeqSystem.limChart k a (S.toSeqSystem.incl k a) = chartAt H a a := by
    unfold SeqSystem.limChart
    rw [OpenPartialHomeomorph.trans_apply, SeqSystem.inclHomeo_symm_apply]
  have hsymm : ContMDiffAt I I ∞ (chartAt H a).symm
      (S.toSeqSystem.limChart k a (S.toSeqSystem.incl k a)) := by
    rw [hval0]
    exact contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a)
      ((chartAt H a).map_source (mem_chart_source H a))
  refine (hsymm.comp _ hchart).congr_of_eventuallyEq ?_
  filter_upwards [(S.toSeqSystem.limChart (H := H) k a).open_source.mem_nhds
    (S.toSeqSystem.mem_limChart_source (H := H) k a)] with z' hz'
  rw [SeqSystem.limChart, OpenPartialHomeomorph.trans_source] at hz'
  obtain ⟨hz'r, hz'c⟩ := hz'
  rw [OpenPartialHomeomorph.symm_source, S.toSeqSystem.inclHomeo_target] at hz'r
  have hz'eq : S.toSeqSystem.incl k ((S.toSeqSystem.inclHomeo k).symm z') = z' := by
    have := (S.toSeqSystem.inclHomeo k).right_inv
      (by rw [S.toSeqSystem.inclHomeo_target]; exact hz'r)
    rwa [← S.toSeqSystem.inclHomeo_apply]
  have hmem_c : (S.toSeqSystem.inclHomeo k).symm z' ∈ (chartAt H a).source := hz'c
  rw [← hz'eq, Function.leftInverse_invFun (S.toSeqSystem.incl_injective k)]
  change (S.toSeqSystem.inclHomeo k).symm z'
    = ((chartAt H a).symm ∘ (S.toSeqSystem.limChart k a)) (S.toSeqSystem.incl k _)
  have hval : S.toSeqSystem.limChart k a
      (S.toSeqSystem.incl k ((S.toSeqSystem.inclHomeo k).symm z'))
        = chartAt H a ((S.toSeqSystem.inclHomeo k).symm z') := by
    unfold SeqSystem.limChart
    rw [OpenPartialHomeomorph.trans_apply, SeqSystem.inclHomeo_symm_apply]
  simp only [Function.comp_apply, hval, (chartAt H a).left_inv hmem_c]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothSeqSystem.contMDiffAt_invIncl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothSeqSystem.contMDiffAt_invIncl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothSeqSystem.contMDiffAt_invIncl ``Submission.DifferentialGeometry.SmoothSeqSystem.contMDiffAt_invIncl

noncomputable def inclPartialDiffeo (k : ℕ) :
    PartialDiffeomorph I I S.toSeqSystem.Lim (A k) (∞ : WithTop ℕ∞) where
  toFun := Function.invFun (S.toSeqSystem.incl k)
  invFun := S.toSeqSystem.incl k
  source := Set.range (S.toSeqSystem.incl k)
  target := Set.univ
  map_source' := fun _ _ => Set.mem_univ _
  map_target' := fun a _ => ⟨a, rfl⟩
  left_inv' := fun _ hz => Function.invFun_eq hz
  right_inv' := fun a _ => Function.leftInverse_invFun (S.toSeqSystem.incl_injective k) a
  open_source := (S.toSeqSystem.incl_isOpenEmb k).isOpen_range
  open_target := isOpen_univ
  contMDiffOn_toFun := fun _ hz => (S.contMDiffAt_invIncl k hz).contMDiffWithinAt
  contMDiffOn_invFun := fun a _ => ((S.contMDiff_incl k) a).contMDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothSeqSystem.inclPartialDiffeo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothSeqSystem.inclPartialDiffeo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothSeqSystem.inclPartialDiffeo ``Submission.DifferentialGeometry.SmoothSeqSystem.inclPartialDiffeo

@[simp] theorem inclPartialDiffeo_source (k : ℕ) :
    (S.inclPartialDiffeo k).source = Set.range (S.toSeqSystem.incl k) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothSeqSystem.inclPartialDiffeo_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothSeqSystem.inclPartialDiffeo_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothSeqSystem.inclPartialDiffeo_source ``Submission.DifferentialGeometry.SmoothSeqSystem.inclPartialDiffeo_source

@[simp] theorem inclPartialDiffeo_apply (k : ℕ) (z : S.toSeqSystem.Lim) :
    S.inclPartialDiffeo k z = Function.invFun (S.toSeqSystem.incl k) z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothSeqSystem.inclPartialDiffeo_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothSeqSystem.inclPartialDiffeo_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothSeqSystem.inclPartialDiffeo_apply ``Submission.DifferentialGeometry.SmoothSeqSystem.inclPartialDiffeo_apply

theorem invIncl_incl_le {j k : ℕ} (hjk : j ≤ k) (a : A j) :
    Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl j a)
      = S.toSeqSystem.map hjk a := by
  conv_lhs => rw [← S.toSeqSystem.incl_comp hjk a]
  exact Function.leftInverse_invFun (S.toSeqSystem.incl_injective k) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothSeqSystem.invIncl_incl_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothSeqSystem.invIncl_incl_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothSeqSystem.invIncl_incl_le ``Submission.DifferentialGeometry.SmoothSeqSystem.invIncl_incl_le

instance instT2SpaceTangentBundleLim [∀ k, T2Space (A k)] :
    T2Space (TangentBundle I S.toSeqSystem.Lim) := by
  have : IsManifold I 1 S.toSeqSystem.Lim :=
    IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothSeqSystem.instT2SpaceTangentBundleLim then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothSeqSystem.instT2SpaceTangentBundleLim"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothSeqSystem.instT2SpaceTangentBundleLim ``Submission.DifferentialGeometry.SmoothSeqSystem.instT2SpaceTangentBundleLim

end SmoothSeqSystem

end DifferentialGeometry
