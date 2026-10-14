import Submission.DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.HalfSpaceExtension
import Submission.DifferentialGeometry.Geometry.Boundary.ModelCollarCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.Topology
open scoped _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Analysis

open _root_.Submission.DifferentialGeometry.Geometry.Boundary
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_contDiffOn_extension_across_range_frontier {f : E → F} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U ∩ _root_.Set.range I) (hf : ContDiffOn ℝ ∞ f (U ∩ _root_.Set.range I)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ g : E → F, ContDiffOn ℝ ∞ g V ∧ _root_.Set.EqOn g f (V ∩ _root_.Set.range I) := by
  by_cases hsm : x ∈ interior (_root_.Set.range I)
  · exact ⟨interior (U ∩ _root_.Set.range I), isOpen_interior,
      mem_interior_iff_mem_nhds.mpr
        (_root_.Filter.mem_of_superset (_root_.Filter.inter_mem (hU.mem_nhds hx.1) (isOpen_interior.mem_nhds hsm))
          (fun y hy => ⟨hy.1, interior_subset hy.2⟩)),
      interior_subset.trans _root_.Set.inter_subset_left, f, hf.mono interior_subset, fun _ _ => rfl⟩
  · obtain ⟨p, hp⟩ : ∃ p : hI.boundaryE, modelBoundaryParam I p = x := by
      have h : x ∈ _root_.Set.range (modelBoundaryParam I) := by
        rw [range_modelBoundaryParam I]
        rw [I.isClosed_range.frontier_eq]
        exact ⟨hx.2, hsm⟩
      exact h
    obtain ⟨e, hpe, he, hei, heq⟩ := exists_modelBoundary_coordinates I p
    let U₁ : Set (hI.boundaryE × ℝ) := e.source ∩ e ⁻¹' U
    have hU₁ : IsOpen U₁ := e.isOpen_inter_preimage hU
    have he0 : e (p, (0 : ℝ)) = x := by
      have h := heq (p, 0)
      rw [zero_smul, add_zero] at h
      exact h.trans hp
    have hp₁ : (p, (0 : ℝ)) ∈ U₁ := ⟨hpe, by rw [Set.mem_preimage, he0]; exact hx.1⟩
    have hΦ₁ : ContDiffOn ℝ ∞ (f ∘ ⇑e) (U₁ ∩ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ))) := by
      refine hf.comp (he.mono (fun z hz => hz.1.1)) ?_
      rintro z ⟨hz, -, hz0⟩
      refine ⟨hz.2, ?_⟩
      rw [heq z]
      exact (modelBoundaryParam_add_mem_range_iff I z.1 z.2).2 hz0
    obtain ⟨V₁, hV₁, hpV₁, hV₁U₁, Ψ, hΨ, hΨeq⟩ :=
      exists_contDiffOn_extension_across_halfSpace_boundary hU₁ hp₁ hΦ₁
    have hV₁sub : V₁ ⊆ e.source := fun z hz => (hV₁U₁ hz).1
    have himage : IsOpen (e '' V₁) := by
      rw [e.image_eq_target_inter_inv_preimage hV₁sub]
      exact e.symm.isOpen_inter_preimage hV₁
    refine ⟨e '' V₁, himage, ⟨(p, 0), hpV₁, he0⟩, ?_, Ψ ∘ ⇑e.symm, ?_, ?_⟩
    · rintro y ⟨z, hz, rfl⟩
      exact (hV₁U₁ hz).2
    · refine hΨ.comp (hei.mono ?_) ?_
      · rintro y ⟨z, hz, rfl⟩
        exact e.map_source (hV₁U₁ hz).1
      · rintro y ⟨z, hz, rfl⟩
        rw [OpenPartialHomeomorph.left_inv _ (hV₁U₁ hz).1]
        exact hz
    · intro y hy
      obtain ⟨⟨z, hz, rfl⟩, hyr⟩ := hy
      have hz0 : 0 ≤ z.2 := by
        have h2 : modelBoundaryParam I z.1 + z.2 • hI.inwardCoordE ∈ _root_.Set.range I := by
          rw [← heq z]
          exact hyr
        exact (modelBoundaryParam_add_mem_range_iff I z.1 z.2).1 h2
      rw [Function.comp_apply, OpenPartialHomeomorph.left_inv _ (hV₁U₁ hz).1]
      exact hΨeq ⟨hz, _root_.Set.mem_univ z.1, hz0⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_contDiffOn_extension_across_range_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_contDiffOn_extension_across_range_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_contDiffOn_extension_across_range_frontier ``Submission.DifferentialGeometry.Analysis.exists_contDiffOn_extension_across_range_frontier

omit [FiniteDimensional ℝ E] in
theorem uniqueDiffWithinAt_of_isOpen_inter_range {U : Set E} {x : E} (hU : IsOpen U)
    (hx : x ∈ U ∩ _root_.Set.range I) : UniqueDiffWithinAt ℝ (U ∩ _root_.Set.range I) x := by
  have hInterior : (interior (_root_.Set.range I)).Nonempty := by
    obtain ⟨ε, hε, h⟩ := hI.inwardCoordE_enters (modelBoundaryParam I (hI.projE 0))
      (by rw [← range_modelBoundaryParam I]; exact _root_.Set.mem_range_self _)
    exact ⟨_, h ε ⟨hε, le_rfl⟩⟩
  rw [_root_.Set.inter_comm]
  exact (uniqueDiffWithinAt_convex I.convex_range hInterior (subset_closure hx.2)).inter'
    (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx.1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.uniqueDiffWithinAt_of_isOpen_inter_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.uniqueDiffWithinAt_of_isOpen_inter_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.uniqueDiffWithinAt_of_isOpen_inter_range ``Submission.DifferentialGeometry.Analysis.uniqueDiffWithinAt_of_isOpen_inter_range

theorem exists_localInverse_of_hasFDerivWithinAt_equiv_of_ne_zero {f : E → F} {U T : Set E}
    {x : E} {A : E ≃L[ℝ] F} (hU : IsOpen U) (hT : T = U ∩ _root_.Set.range I) (hx : x ∈ T)
    (hf : ContDiffOn ℝ ∞ f T) (hd : HasFDerivWithinAt f (A : E →L[ℝ] F) T x) :
    ∃ e : OpenPartialHomeomorph E F, x ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧ _root_.Set.EqOn e f (e.source ∩ T) := by
  subst hT
  by_cases hnhds : U ∩ _root_.Set.range I ∈ 𝓝 x
  · obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hnhds
    obtain ⟨e, hxe, hsub, he, hei, heq⟩ :=
      exists_localInverse_of_hasFDerivAt_equiv_of_ne_zero (𝕜 := ℝ) (n := ∞) (by simp)
        (hf.mono hVU) hVopen hxV (hd.hasFDerivAt hnhds)
    exact ⟨e, hxe, hsub.trans (hVU.trans _root_.Set.inter_subset_left), he, hei, fun y _ => heq y⟩
  · have hxnotint : x ∉ interior (_root_.Set.range I) := fun hc =>
      hnhds (_root_.Filter.mem_of_superset (_root_.Filter.inter_mem (hU.mem_nhds hx.1) (isOpen_interior.mem_nhds hc))
        (fun y hy => ⟨hy.1, interior_subset hy.2⟩))
    have hxfront : x ∈ frontier (_root_.Set.range I) := by
      rw [I.isClosed_range.frontier_eq]
      exact ⟨hx.2, hxnotint⟩
    have hUD : UniqueDiffWithinAt ℝ (U ∩ _root_.Set.range I) x :=
      uniqueDiffWithinAt_of_isOpen_inter_range hU hx
    obtain ⟨V, hV, hxV, hVU, Φ, hΦ, hΦeq⟩ :=
      exists_contDiffOn_extension_across_range_frontier hU hx hf
    have hΦeq' : Φ =ᶠ[𝓝[U ∩ _root_.Set.range I] x] f := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV), self_mem_nhdsWithin]
        with y hy hyT
      exact hΦeq ⟨hy, hyT.2⟩
    have hdΦ : HasFDerivWithinAt Φ (A : E →L[ℝ] F) (U ∩ _root_.Set.range I) x :=
      hd.congr_of_eventuallyEq hΦeq' (hΦeq ⟨hxV, hx.2⟩)
    have hderivΦ : HasFDerivAt Φ (fderiv ℝ Φ x) x :=
      ((hΦ.contDiffAt (hV.mem_nhds hxV)).differentiableAt (by simp)).hasFDerivAt
    have hA : (A : E →L[ℝ] F) = fderiv ℝ Φ x :=
      UniqueDiffWithinAt.eq hUD hdΦ hderivΦ.hasFDerivWithinAt
    obtain ⟨e, hxe, hsub, he, hei, heq⟩ :=
      exists_localInverse_of_hasFDerivAt_equiv_of_ne_zero (𝕜 := ℝ) (n := ∞) (by simp)
        hΦ hV hxV (hA.symm ▸ hderivΦ)
    exact ⟨e, hxe, hsub.trans hVU, he, hei,
      fun y hy => (heq y).trans (hΦeq ⟨hsub hy.1, hy.2.2⟩)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivWithinAt_equiv_of_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivWithinAt_equiv_of_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivWithinAt_equiv_of_ne_zero ``Submission.DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivWithinAt_equiv_of_ne_zero

example (p : hI.boundaryE) :
    ∃ e : OpenPartialHomeomorph E E, modelBoundaryParam I p ∈ e.source ∧ e.source ⊆ _root_.Set.univ ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      EqOn e id (e.source ∩ _root_.Set.range I) := by
  have hp : modelBoundaryParam I p ∈ _root_.Set.range I :=
    I.isClosed_range.closure_subset
      (frontier_subset_closure (by rw [← range_modelBoundaryParam I]; exact _root_.Set.mem_range_self p))
  exact exists_localInverse_of_hasFDerivWithinAt_equiv_of_ne_zero (I := I) (U := _root_.Set.univ)
    (T := _root_.Set.range I) (f := id) (x := modelBoundaryParam I p) (A := 1) isOpen_univ
    (_root_.Set.univ_inter (_root_.Set.range I)).symm hp contDiff_id.contDiffOn (hasFDerivWithinAt_id _ _)

end DifferentialGeometry.Analysis
