/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Submission.DifferentialGeometry.Topology.Manifold.CompactSectionExtension
import Submission.DifferentialGeometry.Topology.Manifold.SmoothTransverseSection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Bundle _root_.Filter _root_.Function _root_.Manifold _root_.Set _root_.Topology
open scoped _root_.Bundle _root_.Manifold _root_.ContDiff

noncomputable section

namespace DifferentialGeometry.Topology.SmoothEmbeddingRealNormalAtlas

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G : Type*} [TopologicalSpace G]
    {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
    {A : Type*} [TopologicalSpace A] [ChartedSpace G A] [T2Space A]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [IsManifold J ∞ A]
    {m : ℕ∞} {f : B → A}

set_option backward.isDefEq.respectTransparency false in
theorem exists_compactlySupported_ambientSection
    [CompactSpace B] (C : SmoothEmbeddingRealNormalAtlas I J ∞ f)
    (hf : _root_.Function.Injective f)
    (s : Cₛ^(m : ℕ∞ω)⟮I; F, C.continuousMap *ᵖ (TangentSpace J : A → Type _)⟯) :
    ∃ S : Cₛ^(m : ℕ∞ω)⟮J; F, (TangentSpace J : A → Type _)⟯,
      HasCompactSupport (fun a ↦ S a) ∧ ∀ x, S (f x) = s x := by
  classical
  rcases isEmpty_or_nonempty B with hB | hB
  · refine ⟨0, ?_, fun x ↦ isEmptyElim x⟩
    change IsCompact (closure {a : A | (0 : F) ≠ 0})
    simp
  let R := C.toEmbeddingRealNormalAtlas
  let fMap : C^(m : ℕ∞ω)⟮I, B; J, A⟯ :=
    ⟨C.continuousMap, C.contMDiff.of_le (by simp)⟩
  let : ContMDiffVectorBundle (m : ℕ∞ω) F
      (C.continuousMap *ᵖ (TangentSpace J : A → Type _)) I :=
    ContMDiffVectorBundle.pullback (F := F) (E := (TangentSpace J : A → Type _)) I fMap
  let sA (a : A) : TangentSpace J a := s (_root_.Function.invFun f a)
  have hsA (x : B) : sA (f x) = s x := by
    dsimp [sA]
    rw [_root_.Function.leftInverse_invFun hf]
  have hlocal : ∀ a ∈ _root_.Set.range f, ∃ U ∈ nhds a, ∃ l : ∀ b, TangentSpace J b,
      ContMDiffOn J J.tangent (m : ℕ∞ω)
        (fun b ↦ (⟨b, l b⟩ : TangentBundle J A)) U ∧
      ∀ b ∈ U, b ∈ _root_.Set.range f → l b = sA b := by
    rintro _ ⟨x, rfl⟩
    let c := R.chart x
    let r : A → B := fun a ↦ (c.symm a).1
    have hx := R.mem_baseSet_self x
    have hfx : f x ∈ c.target := by
      rw [← R.apply_zero x hx]
      exact c.map_source (R.zero_mem_source x hx)
    have hrx : r (f x) = x := by
      dsimp [r]
      rw [← R.apply_zero x hx, c.left_inv (R.zero_mem_source x hx)]
    have hr : ContMDiffOn J I (m : ℕ∞ω) r c.target := by
      intro a ha
      exact contMDiffAt_fst.comp_contMDiffWithinAt a
        (((C.contMDiffOn_chart_symm x) a ha).of_le (by simp))
    let e := _root_.FiberBundle.trivializationAt F (TangentSpace J) (f x)
    let ep := e.pullback C.continuousMap
    let : MemTrivializationAtlas ep := ⟨by exact ⟨e, inferInstance, rfl⟩⟩
    let g : B → F := fun y ↦ (ep ⟨y, s y⟩).2
    have hg : ContMDiffOn I (modelWithCornersSelf ℝ F) (m : ℕ∞ω) g
        (f ⁻¹' e.baseSet) := by
      exact ep.contMDiffOn_section_baseSet_iff.mp s.contMDiff.contMDiffOn
    let U := c.target ∩ r ⁻¹' R.baseSet x ∩ e.baseSet ∩ r ⁻¹' (f ⁻¹' e.baseSet)
    have hxe : f x ∈ e.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (f x)
    have hrcont : ContinuousAt r (f x) :=
      (hr.contMDiffAt (c.open_target.mem_nhds hfx)).continuousAt
    have hU : U ∈ nhds (f x) := by
      apply _root_.Filter.inter_mem
      · apply _root_.Filter.inter_mem
        · exact _root_.Filter.inter_mem (c.open_target.mem_nhds hfx)
            (hrcont.preimage_mem_nhds (by rw [hrx]; exact (R.isOpen_baseSet x).mem_nhds hx))
        · exact e.open_baseSet.mem_nhds hxe
      · exact hrcont.preimage_mem_nhds
          (by
            rw [hrx]
            exact C.contMDiff.continuous.continuousAt.preimage_mem_nhds
              (e.open_baseSet.mem_nhds hxe))
    let l (a : A) : TangentSpace J a := e.symm a (g (r a))
    refine ⟨U, hU, l, ?_, ?_⟩
    · intro a ha
      rw [e.contMDiffWithinAt_section U ha.1.2]
      have hgr : ContMDiffOn J (modelWithCornersSelf ℝ F) (m : ℕ∞ω)
          (fun b ↦ g (r b)) U := hg.comp (hr.mono (fun _ hb ↦ hb.1.1.1))
            (fun _ hb ↦ hb.2)
      apply (hgr a ha).congr
      · intro b hb
        change (e ⟨b, e.symm b (g (r b))⟩).2 = g (r b)
        rw [e.apply_mk_symm hb.1.2]
      · change (e ⟨a, e.symm a (g (r a))⟩).2 = g (r a)
        rw [e.apply_mk_symm ha.1.2]
    · intro a ha harange
      have hzero : (c.symm a).2 = 0 := by
        apply (R.range_iff_zero x (c.symm a) (c.map_target ha.1.1.1)).mp
        rwa [c.right_inv ha.1.1.1]
      have hfr : f (r a) = a := by
        calc
          f (r a) = c (r a, 0) := (R.apply_zero x ha.1.1.2).symm
          _ = c (c.symm a) := by congr 1; exact Prod.ext rfl hzero.symm
          _ = a := c.right_inv ha.1.1.1
      have heq : l a = s (r a) := by
        dsimp [l, g, ep]
        simp only [Trivialization.pullback_apply]
        change e.symm a (e (⟨f (r a), s (r a)⟩ : TangentBundle J A)).2 = _
        rw [hfr]
        exact e.symm_apply_apply_mk ha.1.2 _
      rw [heq, ← hsA (r a), hfr]
  obtain ⟨S, hS, heq⟩ := exists_contMDiffSection_eqOn_of_isCompact_of_local
    (I := J) (TangentSpace J : A → Type _) (isCompact_range C.contMDiff.continuous) sA hlocal
  exact ⟨S, hS, fun x ↦ (heq (f x) (_root_.Set.mem_range_self x)).trans (hsA x)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothEmbeddingRealNormalAtlas.exists_compactlySupported_ambientSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothEmbeddingRealNormalAtlas.exists_compactlySupported_ambientSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothEmbeddingRealNormalAtlas.exists_compactlySupported_ambientSection ``Submission.DifferentialGeometry.Topology.SmoothEmbeddingRealNormalAtlas.exists_compactlySupported_ambientSection

end DifferentialGeometry.Topology.SmoothEmbeddingRealNormalAtlas

namespace DifferentialGeometry.Topology.CoorientedSmoothEmbeddingRealNormalAtlas

theorem exists_compactlySupported_transverseField
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G : Type*} [TopologicalSpace G]
    {B : Type*} [TopologicalSpace B] [ChartedSpace H B] [T2Space B] [CompactSpace B]
    {A : Type*} [TopologicalSpace A] [ChartedSpace G A] [T2Space A]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [IsManifold I ∞ B] [IsManifold J ∞ A] {f : B → A}
    (C : CoorientedSmoothEmbeddingRealNormalAtlas I J ∞ f) (hf : _root_.Function.Injective f) :
    ∃ S : Cₛ^∞⟮J; F, (TangentSpace J : A → Type _)⟯,
      HasCompactSupport (fun a ↦ S a) ∧
      (∀ x, S (f x) ∈ C.positiveNormalHalfSpace x) ∧
      (∀ x, S (f x) ∉ _root_.Set.range (mfderiv I J f x)) := by
  obtain ⟨s, hspos, hstrans⟩ := C.exists_contMDiff_transverseSection (m := ⊤) (by simp)
  obtain ⟨S, hS, heq⟩ := C.toSmoothEmbeddingRealNormalAtlas.exists_compactlySupported_ambientSection hf s
  exact ⟨S, hS, fun x ↦ by rw [heq]; exact hspos x,
    fun x ↦ by rw [heq]; exact hstrans x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.CoorientedSmoothEmbeddingRealNormalAtlas.exists_compactlySupported_transverseField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.CoorientedSmoothEmbeddingRealNormalAtlas.exists_compactlySupported_transverseField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.CoorientedSmoothEmbeddingRealNormalAtlas.exists_compactlySupported_transverseField ``Submission.DifferentialGeometry.Topology.CoorientedSmoothEmbeddingRealNormalAtlas.exists_compactlySupported_transverseField

end DifferentialGeometry.Topology.CoorientedSmoothEmbeddingRealNormalAtlas
