/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPiece
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLMap
import Submission.DifferentialGeometry.Topology.Pasting

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open _root_.Classical in
theorem IsPiecewiseAffineOn.piecewise_of_isClosed [FiniteDimensional ℝ E]
    {f g : E → F} {P Q : Set E} (hf : IsPiecewiseAffineOn f P) (hg : IsPiecewiseAffineOn g Q)
    (hP : IsClosed P) (hQ : IsClosed Q) (hfg : _root_.Set.EqOn f g (P ∩ Q)) :
    IsPiecewiseAffineOn (P.piecewise f g) (P ∪ Q) := by
  have hleft : _root_.Set.EqOn (P.piecewise f g) f P := fun x hx => _root_.Set.piecewise_eq_of_mem P f g hx
  have hright : _root_.Set.EqOn (P.piecewise f g) g Q := by
    intro x hx
    by_cases hxP : x ∈ P
    · rw [_root_.Set.piecewise_eq_of_mem P f g hxP]
      exact hfg ⟨hxP, hx⟩
    · exact _root_.Set.piecewise_eq_of_notMem P f g hxP
  exact (hf.congr hleft).union_of_isClosed (hg.congr hright) hP hQ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.piecewise_of_isClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.piecewise_of_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.piecewise_of_isClosed ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.piecewise_of_isClosed

open _root_.Classical in
theorem IsPLOn.piecewise_of_isClosed
    {n m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    {f g : EuclideanSpace ℝ (Fin n) → M}
    {P Q : Set (EuclideanSpace ℝ (Fin n))}
    (hf : IsPLOn n m f P) (hg : IsPLOn n m g Q)
    (hP : IsClosed P) (hQ : IsClosed Q) (hfg : _root_.Set.EqOn f g (P ∩ Q)) :
    IsPLOn n m (P.piecewise f g) (P ∪ Q) := by
  let h := P.piecewise f g
  have hPf : _root_.Set.EqOn h f P := P.piecewise_eqOn f g
  have hQg : _root_.Set.EqOn h g Q := by
    intro x hx
    by_cases hxP : x ∈ P
    · change P.piecewise f g x = g x
      rw [P.piecewise_eq_of_mem f g hxP, hfg ⟨hxP, hx⟩]
    · change P.piecewise f g x = g x
      exact P.piecewise_eq_of_notMem f g hxP
  intro x hx
  by_cases hxP : x ∈ P
  · have hhP : IsPLWithinAt n m h P x :=
      piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem
        (hf x hxP) hPf hxP
    by_cases hxQ : x ∈ Q
    · have hhQ : IsPLWithinAt n m h Q x :=
        piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem
          (hg x hxQ) hQg hxQ
      have hhP' :=
        (StructureGroupoid.liftPropWithinAt_self_source).mp hhP
      have hhQ' :=
        (StructureGroupoid.liftPropWithinAt_self_source).mp hhQ
      apply (StructureGroupoid.liftPropWithinAt_self_source).mpr
      exact ⟨hhP'.1.union hhQ'.1, hhP'.2.union hhQ'.2⟩
    · have hset : (fun y => y ∈ P) =ᶠ[𝓝 x] (fun y => y ∈ P ∪ Q) := by
        filter_upwards [hQ.isOpen_compl.mem_nhds hxQ] with y hy
        apply propext
        exact ⟨Or.inl, fun h => h.resolve_right hy⟩
      exact (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_set hset).mp hhP
  · have hxQ : x ∈ Q := hx.resolve_left hxP
    have hhQ : IsPLWithinAt n m h Q x :=
      piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem
        (hg x hxQ) hQg hxQ
    have hset : (fun y => y ∈ Q) =ᶠ[𝓝 x] (fun y => y ∈ P ∪ Q) := by
      filter_upwards [hP.isOpen_compl.mem_nhds hxP] with y hy
      apply propext
      exact ⟨Or.inr, fun h => h.resolve_left hy⟩
    exact (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_set hset).mp hhQ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.piecewise_of_isClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.piecewise_of_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.piecewise_of_isClosed ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.piecewise_of_isClosed

open _root_.Classical in
theorem exists_piecewiseAffineOn_postcomp_on_polyhedron [FiniteDimensional ℝ E]
    {f : E → F} {P Q : Set E} (hf : IsPiecewiseAffineOn f (P ∪ Q)) (hP : IsPolyhedron P)
    (hQ : IsPolyhedron Q) {h : F → F} (hh : IsPiecewiseAffineOn h _root_.Set.univ)
    (hfix : _root_.Set.EqOn h id (f '' (P ∩ Q))) :
    ∃ g : E → F, IsPiecewiseAffineOn g (P ∪ Q) ∧ _root_.Set.EqOn g (h ∘ f) P ∧ _root_.Set.EqOn g f Q ∧ _root_.Set.EqOn g f Pᶜ := by
  let g := P.piecewise (h ∘ f) f
  have hfP := hf.mono_of_isPolyhedron hP _root_.Set.subset_union_left
  have hfQ := hf.mono_of_isPolyhedron hQ _root_.Set.subset_union_right
  have hhf : IsPiecewiseAffineOn (h ∘ f) P := by
    have hpl := hh.comp hfP
    rwa [_root_.Set.preimage_univ, _root_.Set.inter_univ] at hpl
  have hcommon : _root_.Set.EqOn (h ∘ f) f (P ∩ Q) := fun x hx => hfix ⟨x, hx, rfl⟩
  refine ⟨g, hhf.piecewise_of_isClosed hfQ hP.isClosed hQ.isClosed hcommon,
    fun x hx => _root_.Set.piecewise_eq_of_mem P (h ∘ f) f hx, ?_, fun x hx => _root_.Set.piecewise_eq_of_notMem P (h ∘ f)
        f hx⟩
  intro x hx
  by_cases hxP : x ∈ P
  · rw [show g x = h (f x) from _root_.Set.piecewise_eq_of_mem P (h ∘ f) f hxP]
    exact hfix ⟨x, ⟨hxP, hx⟩, rfl⟩
  · exact _root_.Set.piecewise_eq_of_notMem P (h ∘ f) f hxP

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffineOn_postcomp_on_polyhedron then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffineOn_postcomp_on_polyhedron"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffineOn_postcomp_on_polyhedron ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffineOn_postcomp_on_polyhedron

open _root_.Classical in
theorem exists_piecewiseAffineOn_postcomp_on_polyhedron_of_locallyInjective
    [FiniteDimensional ℝ E] {f : E → F} {P Q : Set E}
    (hf : IsPiecewiseAffineOn f (P ∪ Q)) (hP : IsPolyhedron P) (hQ : IsPolyhedron Q)
    (hloc : IsLocallyInjective ((P ∪ Q).domRestrict f))
    (hcard : ∀ y, ((P ∪ Q) ∩ f ⁻¹' {y}).encard ≤ 2) (hinjP : _root_.Set.InjOn f P)
    {h : F → F} (hh : IsPiecewiseAffineOn h _root_.Set.univ) (hhinj : Function.Injective h) {U : Set F}
    (hfix : _root_.Set.EqOn h id Uᶜ) (hseam : ∀ x ∈ P ∩ Q, f x ∉ closure U)
    (hinjQ : _root_.Set.InjOn f (Q ∩ f ⁻¹' U)) :
    ∃ g : E → F, IsPiecewiseAffineOn g (P ∪ Q) ∧
      IsLocallyInjective ((P ∪ Q).domRestrict g) ∧
      (∀ y, ((P ∪ Q) ∩ g ⁻¹' {y}).encard ≤ 2) ∧
      _root_.Set.EqOn g (h ∘ f) P ∧ _root_.Set.EqOn g f Q ∧ _root_.Set.EqOn g f Pᶜ ∧
      ∀ y ∉ U, g ⁻¹' {y} = f ⁻¹' {y} := by
  let g := P.piecewise (h ∘ f) f
  have hcommon : _root_.Set.EqOn h id (f '' (P ∩ Q)) := by
    rintro y ⟨x, hx, rfl⟩
    exact hfix (fun hfx => hseam x hx (subset_closure hfx))
  have hhf : IsPiecewiseAffineOn (h ∘ f) P := by
    have hc := hh.comp (hf.mono_of_isPolyhedron hP _root_.Set.subset_union_left)
    rwa [_root_.Set.preimage_univ, _root_.Set.inter_univ] at hc
  have hg : IsPiecewiseAffineOn g (P ∪ Q) :=
    hhf.piecewise_of_isClosed (hf.mono_of_isPolyhedron hQ _root_.Set.subset_union_right) hP.isClosed
        hQ.isClosed
      (fun x hx => hcommon ⟨x, hx, rfl⟩)
  have hlocg : IsLocallyInjective ((P ∪ Q).domRestrict g) := by
    apply IsLocallyInjective.piecewise_postcomp_of_isClosed hloc hf.continuousOn
      hP.isClosed hQ.isClosed hhinj
    intro x hx
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds (hseam x hx)] with y hy
    exact hfix (fun hyU => hy (subset_closure hyU))
  have hcardg : ∀ y, ((P ∪ Q) ∩ g ⁻¹' {y}).encard ≤ 2 := by
    apply encard_fiber_piecewise_postcomp_le f (P ∪ Q) P hhinj hfix
      (hinjP.mono _root_.Set.inter_subset_right) (n := 1)
    · simpa only [one_add_one_eq_two] using hcard
    · intro y hy
      apply encard_le_one_iff_subsingleton.mpr
      intro x hx z hz
      have hxQ : x ∈ Q := hx.1.1.resolve_left hx.1.2
      have hzQ : z ∈ Q := hz.1.1.resolve_left hz.1.2
      have hfx : f x = y := hx.2
      have hfz : f z = y := hz.2
      exact hinjQ ⟨hxQ, by change f x ∈ U; rwa [hfx]⟩ ⟨hzQ, by change f z ∈ U; rwa [hfz]⟩ (hfx.trans
          hfz.symm)
  refine ⟨g, hg, hlocg, hcardg, fun x hx => _root_.Set.piecewise_eq_of_mem P (h ∘ f) f hx,
    ?_, fun x hx => _root_.Set.piecewise_eq_of_notMem P (h ∘ f) f hx, ?_⟩
  · intro x hx
    by_cases hxP : x ∈ P
    · rw [show g x = h (f x) from _root_.Set.piecewise_eq_of_mem P (h ∘ f) f hxP]
      exact hcommon ⟨x, ⟨hxP, hx⟩, rfl⟩
    · exact _root_.Set.piecewise_eq_of_notMem P (h ∘ f) f hxP
  · exact fun y hy => piecewise_postcomp_preimage_singleton_of_eqOn_compl P f hhinj hfix hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffineOn_postcomp_on_polyhedron_of_locallyInjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffineOn_postcomp_on_polyhedron_of_locallyInjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffineOn_postcomp_on_polyhedron_of_locallyInjective ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffineOn_postcomp_on_polyhedron_of_locallyInjective

open _root_.Classical in
theorem exists_isPLOn_postcomp_on_polyhedron_of_locallyInjective
    {n m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin m)) X]
    {f : EuclideanSpace ℝ (Fin n) → X} {P Q : Set (EuclideanSpace ℝ (Fin n))}
    (hf : IsPLOn n m f (P ∪ Q)) (hP : IsPolyhedron P) (hQ : IsPolyhedron Q)
    (hloc : IsLocallyInjective ((P ∪ Q).domRestrict f))
    (hcard : ∀ y, ((P ∪ Q) ∩ f ⁻¹' {y}).encard ≤ 2) (hinjP : _root_.Set.InjOn f P)
    {h : X → X} (hh : IsPL m m h) (hhinj : Function.Injective h) {U : Set X}
    (hfix : _root_.Set.EqOn h id Uᶜ) (hseam : ∀ x ∈ P ∩ Q, f x ∉ closure U)
    (hinjQ : _root_.Set.InjOn f (Q ∩ f ⁻¹' U)) :
    ∃ g : EuclideanSpace ℝ (Fin n) → X, IsPLOn n m g (P ∪ Q) ∧
      IsLocallyInjective ((P ∪ Q).domRestrict g) ∧
      (∀ y, ((P ∪ Q) ∩ g ⁻¹' {y}).encard ≤ 2) ∧
      _root_.Set.EqOn g (h ∘ f) P ∧ _root_.Set.EqOn g f Q ∧ _root_.Set.EqOn g f Pᶜ ∧
      ∀ y ∉ U, g ⁻¹' {y} = f ⁻¹' {y} := by
  let g := P.piecewise (h ∘ f) f
  have hcont : ContinuousOn f (P ∪ Q) := fun x hx => (hf x hx).continuousWithinAt
  have hsevent : ∀ x ∈ P ∩ Q, ∀ᶠ z in 𝓝 (f x), h z = z := by
    intro x hx
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds (hseam x hx)] with z hz
    exact hfix (fun hzU => hz (subset_closure hzU))
  have hg : IsPLOn n m g (P ∪ Q) :=
    IsPLOn.piecewise_postcomp_of_isClosed hf hh hP.isClosed hQ.isClosed hsevent
  have hgloc : IsLocallyInjective ((P ∪ Q).domRestrict g) :=
    IsLocallyInjective.piecewise_postcomp_of_isClosed hloc hcont hP.isClosed hQ.isClosed hhinj
        hsevent
  have hgcard : ∀ y, ((P ∪ Q) ∩ g ⁻¹' {y}).encard ≤ 2 := by
    apply encard_fiber_piecewise_postcomp_le f (P ∪ Q) P hhinj hfix
      (hinjP.mono _root_.Set.inter_subset_right) (n := 1)
    · simpa only [one_add_one_eq_two] using hcard
    · intro y hy
      apply encard_le_one_iff_subsingleton.mpr
      intro a ha b hb
      have haQ : a ∈ Q := ha.1.1.resolve_left ha.1.2
      have hbQ : b ∈ Q := hb.1.1.resolve_left hb.1.2
      have hfa : f a = y := ha.2
      have hfb : f b = y := hb.2
      apply hinjQ ⟨haQ, ?_⟩ ⟨hbQ, ?_⟩ (hfa.trans hfb.symm)
      · change f a ∈ U
        rwa [hfa]
      · change f b ∈ U
        rwa [hfb]
  refine ⟨g, hg, hgloc, hgcard, fun x hx => _root_.Set.piecewise_eq_of_mem P (h ∘ f) f hx,
    ?_, fun x hx => _root_.Set.piecewise_eq_of_notMem P (h ∘ f) f hx,
    fun y hy => piecewise_postcomp_preimage_singleton_of_eqOn_compl P f hhinj hfix hy⟩
  intro x hx
  by_cases hxP : x ∈ P
  · rw [show g x = h (f x) from _root_.Set.piecewise_eq_of_mem P (h ∘ f) f hxP]
    exact hfix (fun hfx => hseam x ⟨hxP, hx⟩ (subset_closure hfx))
  · exact _root_.Set.piecewise_eq_of_notMem P (h ∘ f) f hxP

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_postcomp_on_polyhedron_of_locallyInjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_postcomp_on_polyhedron_of_locallyInjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_postcomp_on_polyhedron_of_locallyInjective ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_postcomp_on_polyhedron_of_locallyInjective

end DifferentialGeometry.Topology.PiecewiseLinear
