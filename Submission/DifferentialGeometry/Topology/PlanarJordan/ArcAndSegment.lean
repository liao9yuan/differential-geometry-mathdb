import Submission.DifferentialGeometry.External.Schoenflies.Concatenate
import Submission.DifferentialGeometry.External.Schoenflies.Polygonal
import Mathlib.Analysis.InnerProductSpace.PiL2

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set

namespace DifferentialGeometry.Topology.PlanarJordan

theorem exists_simple_closed_curve_of_arc_and_segment
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (_root_.Set.Icc a b)) (hinj : _root_.Set.InjOn γ (_root_.Set.Icc a b))
    (havoid : ∀ t ∈ _root_.Set.Ioo a b, γ t ∉ segment ℝ (γ a) (γ b)) :
    ∃ α : ℝ → ℂ, ContinuousOn α (_root_.Set.Icc 0 1) ∧ α 0 = α 1 ∧
      InjOn α (_root_.Set.Ico 0 1) ∧ α '' _root_.Set.Icc 0 1 = γ '' _root_.Set.Icc a b ∪ segment ℝ (γ a) (γ b) := by
  let l := Complex.orthonormalBasisOneI.repr
  let ρ : ℝ → ℝ := fun t ↦ a + (b - a) * t
  have hρ : _root_.Set.MapsTo ρ (_root_.Set.Icc 0 1) (_root_.Set.Icc a b) := by
    intro t ht
    constructor <;> dsimp [ρ] <;> nlinarith [ht.1, ht.2]
  have hρimage : ρ '' _root_.Set.Icc 0 1 = _root_.Set.Icc a b := by
    apply Subset.antisymm hρ.image_subset
    intro t ht
    refine ⟨(t - a) / (b - a), ⟨div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr hab).le,
      (div_le_one (sub_pos.mpr hab)).mpr (by linarith [ht.2])⟩, ?_⟩
    dsimp [ρ]
    field_simp [(sub_pos.mpr hab).ne']
    ring
  let δ : ℝ → Schoenflies.Plane := fun t ↦ l (γ (ρ t))
  have hδ : ContinuousOn δ (_root_.Set.Icc 0 1) :=
    l.continuous.comp_continuousOn (hγ.comp (by fun_prop) hρ)
  have hδinj : _root_.Set.InjOn δ (_root_.Set.Icc 0 1) := by
    intro s hs t ht he
    have hp := hinj (hρ hs) (hρ ht) (l.injective he)
    dsimp [ρ] at hp
    nlinarith [hab]
  have hδimage : δ '' _root_.Set.Icc 0 1 = l '' (γ '' _root_.Set.Icc a b) := by
    rw [← hρimage, _root_.Set.image_image, _root_.Set.image_image]
  have hend : γ a ≠ γ b := fun h ↦ hab.ne (hinj ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ h)
  have hA : Schoenflies.IsArcBetween (δ '' _root_.Set.Icc 0 1) (l (γ a)) (l (γ b)) :=
    ⟨δ, hδ, hδinj, rfl, by simp [δ, ρ], by simp [δ, ρ]⟩
  have hB := Schoenflies.isArcBetween_segment (l.injective.ne hend.symm)
  have hseg : l '' segment ℝ (γ a) (γ b) = segment ℝ (l (γ b)) (l (γ a)) := by
    rw [show l '' segment ℝ (γ a) (γ b) = segment ℝ (l (γ a)) (l (γ b)) from
      image_segment ℝ l.toContinuousLinearEquiv.toLinearEquiv.toLinearMap.toAffineMap _ _]
    exact segment_symm _ _ _
  have hmeet : ∀ z ∈ δ '' _root_.Set.Icc 0 1,
      z ∈ segment ℝ (l (γ b)) (l (γ a)) → z = l (γ a) ∨ z = l (γ b) := by
    rintro z ⟨t, ht, rfl⟩ hz
    by_cases ha : ρ t = a
    · exact Or.inl (by simp only [δ, ha])
    by_cases hb : ρ t = b
    · exact Or.inr (by simp only [δ, hb])
    have ht' : ρ t ∈ _root_.Set.Ioo a b :=
      ⟨lt_of_le_of_ne (hρ ht).1 (Ne.symm ha), lt_of_le_of_ne (hρ ht).2 hb⟩
    exfalso
    apply havoid (ρ t) ht'
    rw [← hseg] at hz
    obtain ⟨q, hq, heq⟩ := hz
    exact l.injective heq ▸ hq
  obtain ⟨β, hβ, hβimage⟩ := Schoenflies.IsJordanCurve.of_two_arcs hA hB hmeet
  refine ⟨fun t ↦ l.symm (β t), l.symm.continuous.comp_continuousOn hβ.continuousOn,
    congrArg l.symm hβ.closes, fun _ hs _ ht he ↦ hβ.injOn hs ht (l.symm.injective he), ?_⟩
  rw [← _root_.Set.image_image l.symm β (_root_.Set.Icc 0 1), hβimage, _root_.Set.image_union, hδimage,
    ← hseg]
  simp only [_root_.Set.image_image, l.symm_apply_apply, _root_.Set.image_id']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_simple_closed_curve_of_arc_and_segment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_simple_closed_curve_of_arc_and_segment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_simple_closed_curve_of_arc_and_segment ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_simple_closed_curve_of_arc_and_segment

end DifferentialGeometry.Topology.PlanarJordan
