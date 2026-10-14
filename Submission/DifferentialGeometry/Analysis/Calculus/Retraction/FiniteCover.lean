import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Compactness.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission









noncomputable section

open _root_.Set _root_.Filter _root_.Function
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_neighborhood_retraction_of_local {S : Set F} (hS : IsCompact S)
    {ι : Type*} (Φ : ι → F → F) (V : ι → Set F)
    (hΦ : ∀ i, ContDiff ℝ ∞ (Φ i)) (hfix : ∀ i q, q ∈ S → Φ i q = q)
    (hV : ∀ i, IsOpen (V i)) (hmap : ∀ i, _root_.Set.MapsTo (Φ i) (V i) S)
    (hcover : S ⊆ ⋃ i, V i) :
    ∃ (R : F → F) (U : Set F), ContDiff ℝ ∞ R ∧ IsOpen U ∧ S ⊆ U ∧
      MapsTo R U S ∧ ∀ q ∈ S, R q = q := by
  classical
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover V hV hcover
  let C (l : List ι) : F → F := l.foldr (fun i f => Φ i ∘ f) id
  have hC (l : List ι) : ContDiff ℝ ∞ (C l) ∧ (∀ q ∈ S, C l q = q) ∧
      ∀ q ∈ S, (∃ i ∈ l, q ∈ V i) → ∀ᶠ z in 𝓝 q, C l z ∈ S := by
    induction l with
    | nil =>
      refine ⟨contDiff_id, fun _ _ => rfl, ?_⟩
      rintro q hq ⟨i, hi, _⟩
      simp at hi
    | cons a l ih =>
      refine ⟨(hΦ a).comp ih.1, ?_, ?_⟩
      · intro q hq
        change Φ a (C l q) = q
        rw [ih.2.1 q hq, hfix a q hq]
      · rintro q hq ⟨i, hi, hqi⟩
        rcases List.mem_cons.mp hi with hia | hi
        · subst i
          have hcollapse : ∀ᶠ z in 𝓝 q, Φ a z ∈ S := by
            filter_upwards [(hV a).mem_nhds hqi] with z hz
            exact hmap a hz
          have hc : _root_.Filter.Tendsto (C l) (𝓝 q) (𝓝 q) := by
            have hct := ih.1.continuous.continuousAt (x := q)
            change _root_.Filter.Tendsto (C l) (𝓝 q) (𝓝 (C l q)) at hct
            rwa [ih.2.1 q hq] at hct
          exact hc.eventually hcollapse
        · filter_upwards [ih.2.2 q hq ⟨i, hi, hqi⟩] with z hz
          change Φ a (C l z) ∈ S
          rw [hfix a (C l z) hz]
          exact hz
  let R := C t.toList
  let U := interior (R ⁻¹' S)
  refine ⟨R, U, (hC _).1, isOpen_interior, ?_, fun _ hy => (interior_subset (s := R ⁻¹' S)) hy,
    (hC _).2.1⟩
  intro q hq
  obtain ⟨i, hit, hqi⟩ := mem_iUnion₂.mp (ht hq)
  exact mem_interior_iff_mem_nhds.mpr ((hC _).2.2 q hq
    ⟨i, Finset.mem_toList.mpr hit, hqi⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_smooth_neighborhood_retraction_of_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_smooth_neighborhood_retraction_of_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_smooth_neighborhood_retraction_of_local ``Submission.DifferentialGeometry.Analysis.exists_smooth_neighborhood_retraction_of_local

end DifferentialGeometry.Analysis
