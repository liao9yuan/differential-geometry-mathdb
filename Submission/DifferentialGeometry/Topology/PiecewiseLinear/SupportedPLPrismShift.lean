/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SupportedPLPieceConjugate
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedBallHeightMove
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.AdaptedCapSource

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem PLPieceIn.exists_supported_prism_shift {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {W : Set M} (T : PLPieceIn (E × ℝ) n M W)
    {P : Set E} (hP : IsPolyhedron P) (hTP : T.complex.space = P ×ˢ _root_.Set.Icc (-1 : ℝ) 1)
    (hzero : ∀ x ∈ P, T.map (x, 0) ∈ interior W) :
    ∃ (φ : M ≃ₜ M) (β : ℝ → ℝ), IsPL n n φ ∧ IsPL n n φ.symm ∧
      StrictMono β ∧ 0 < β 0 ∧ _root_.Set.BijOn β (_root_.Set.Icc (-1 : ℝ) 1) (_root_.Set.Icc (-1 : ℝ) 1) ∧
      (∀ x ∈ P, ∀ t ∈ _root_.Set.Icc (-1 : ℝ) 1, φ (T.map (x, t)) = T.map (x, β t)) ∧
      EqOn φ id Wᶜ := by
  have hcont : ContinuousOn T.map (P ×ˢ _root_.Set.Icc (-1 : ℝ) 1) := hTP ▸ T.continuousOn
  obtain ⟨a, ha, ha1, hslab⟩ := exists_pos_forall_prod_Icc_mem_of_isCompact
    hP.isCompact hcont isOpen_interior hzero
  let g : E → ℝ := fun _ => a / 4
  let τ := piercingHeightMove g a
  have hg : IsPiecewiseAffineOn g univ :=
    isPiecewiseAffineOn_of_affine (AffineMap.const ℝ E (a / 4)) isOpen_univ
  have hτ : IsPLHomeomorphOn τ T.complex.space T.complex.space := by
    rw [hTP]
    exact isPLHomeomorphOn_piercingHeightMove_self hg ha1 hP
  let K := P ×ˢ _root_.Set.Icc (-a) a
  have hKP : K ⊆ T.complex.space := by
    rw [hTP]
    exact _root_.Set.prod_mono Subset.rfl (_root_.Set.Icc_subset_Icc (by linarith) ha1)
  have hK : IsCompact K := hP.isCompact.prod _root_.CompactIccSpace.isCompact_Icc
  have hKW : T.map '' K ⊆ interior W := by
    rintro y ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact hslab x hx t ht
  have hfix : _root_.Set.EqOn τ id (T.complex.space \ K) := by
    rintro ⟨x, t⟩ ⟨hx, hn⟩
    apply piercingHeightMove_eq_self
    have hxP : x ∈ P := (hTP.subset hx).1
    by_cases hl : t ≤ -a
    · exact Or.inl hl
    · exact Or.inr (le_of_not_gt fun hu => hn ⟨hxP, (lt_of_not_ge hl).le, hu.le⟩)
  obtain ⟨φ, hφ, hφi, hφτ, hφfix⟩ := T.exists_supported_conjugate hτ hK hKP hKW hfix
  let β := fun t => (piercingHeightMove (fun _ : ℝ => a / 4) a (0, t)).2
  have hβ : StrictMono β := piercingHeightMove_strictMono _ _ _
  have hβzero : β 0 = a / 4 := by
    exact congrArg Prod.snd (piercingHeightMove_apply_zero ha.le
      (show |a / 4| ≤ a / 2 by rw [abs_of_pos (by positivity)]; linarith)
        (x := (0 : ℝ)))
  have hβsurj : _root_.Set.SurjOn β (_root_.Set.Icc (-1 : ℝ) 1) (_root_.Set.Icc (-1 : ℝ) 1) := by
    intro t ht
    have himage := piercingHeightMove_image_prism (fun _ : ℝ => a / 4) ha1 ({0} : Set ℝ)
    obtain ⟨⟨x, s⟩, ⟨hx, hs⟩, heq⟩ := himage.symm.subset (show (0, t) ∈
      ({0} : Set ℝ) ×ˢ _root_.Set.Icc (-1 : ℝ) 1 from ⟨rfl, ht⟩)
    have hx0 : x = 0 := hx
    subst x
    exact ⟨s, hs, congrArg Prod.snd heq⟩
  have hβmap : _root_.Set.MapsTo β (_root_.Set.Icc (-1 : ℝ) 1) (_root_.Set.Icc (-1 : ℝ) 1) := by
    intro t ht
    have himage := piercingHeightMove_image_prism (fun _ : ℝ => a / 4) ha1 ({0} : Set ℝ)
    exact (himage.subset ⟨(0, t), ⟨rfl, ht⟩, rfl⟩).2
  refine ⟨φ, β, hφ, hφi, hβ, hβzero ▸ (by positivity),
    ⟨hβmap, hβ.injective.injOn, hβsurj⟩, ?_, ?_⟩
  · intro x hx t ht
    exact hφτ (x, t) (hTP.symm.subset ⟨hx, ht⟩)
  · intro x hx
    exact hφfix fun h => hx (interior_subset (hKW h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_supported_prism_shift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_supported_prism_shift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_supported_prism_shift ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_supported_prism_shift

end DifferentialGeometry.Topology.PiecewiseLinear
