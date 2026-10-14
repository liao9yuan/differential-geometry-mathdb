import Submission.DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Set
open scoped _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.CheegerGromovCompactness

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem MapCInfConvergenceOnCompacts.pullbackForm_comp_fderiv_locally
    {U : Set E} {V : Set F} (hV : IsOpen V)
    {A : ℕ → E → F} {Ainf : E → F}
    {B : ℕ → F → F →L[ℝ] F →L[ℝ] ℝ} {Binf : F → F →L[ℝ] F →L[ℝ] ℝ}
    (hA : MapCInfConvergenceOnCompacts U A Ainf)
    (hB : MapCInfConvergenceOnCompacts V B Binf)
    (hAc : ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
        ∀ᶠ k in _root_.Filter.atTop, ContDiffOn ℝ ∞ (A k) W ∧ _root_.Set.MapsTo (A k) W V)
    (hAinfC : ContDiffOn ℝ ∞ Ainf U)
    (hBc : ∀ k, ContDiffOn ℝ ∞ (B k) V)
    (hBinfC : ContDiffOn ℝ ∞ Binf V)
    (hmap : _root_.Set.MapsTo Ainf U V) :
    MapCInfConvergenceOnCompacts U
      (fun k z => _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.pullbackForm
        (B k (A k z), fderiv ℝ (A k) z))
      (fun z => _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.pullbackForm
        (Binf (Ainf z), fderiv ℝ Ainf z)) := by
  classical
  let : ProperSpace F := FiniteDimensional.proper ℝ F
  let : ProperSpace ((F →L[ℝ] F →L[ℝ] ℝ) × (E →L[ℝ] F)) :=
    FiniteDimensional.proper ℝ _
  intro K hK hKU p
  obtain ⟨W, hW, hKW, hWU, hev⟩ := hAc K hK hKU
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  let A' : ℕ → E → F := fun k => if N ≤ k then A k else Ainf
  have hAeq : ∀ᶠ k in _root_.Filter.atTop, _root_.Set.EqOn (A' k) (A k) W := by
    filter_upwards [_root_.Filter.eventually_ge_atTop N] with k hk
    intro z _
    simp only [A', if_pos hk]
  have hAW : MapCInfConvergenceOnCompacts W A Ainf :=
    fun L hL hLW => hA L hL (hLW.trans hWU)
  have hA' : MapCInfConvergenceOnCompacts W A' Ainf :=
    hAW.congr_eventually hW hAeq (fun _ _ => rfl)
  have hA'c : ∀ k, ContDiffOn ℝ ∞ (A' k) W := by
    intro k
    by_cases hk : N ≤ k
    · simpa only [A', if_pos hk] using (hN k hk).1
    · simpa only [A', if_neg hk] using hAinfC.mono hWU
  have hA'map : ∀ k, _root_.Set.MapsTo (A' k) W V := by
    intro k
    by_cases hk : N ≤ k
    · simpa only [A', if_pos hk] using (hN k hk).2
    · simpa only [A', if_neg hk] using hmap.mono_left hWU
  have hP := hA'.pullbackForm_comp_fderiv hW hV hB hA'c
    (hAinfC.mono hWU) hBc hBinfC (hmap.mono_left hWU) hA'map
  have hPeq : ∀ᶠ k in _root_.Filter.atTop,
      _root_.Set.EqOn (fun z => _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.pullbackForm
        (B k (A k z), fderiv ℝ (A k) z))
        (fun z => _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.pullbackForm
          (B k (A' k z), fderiv ℝ (A' k) z)) W := by
    filter_upwards [_root_.Filter.eventually_ge_atTop N] with k hk
    intro z _
    simp only [A', if_pos hk]
  exact (hP.congr_eventually hW hPeq (fun _ _ => rfl)) K hK hKW p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts.pullbackForm_comp_fderiv_locally then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts.pullbackForm_comp_fderiv_locally"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts.pullbackForm_comp_fderiv_locally ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts.pullbackForm_comp_fderiv_locally

end DifferentialGeometry.CheegerGromovCompactness

end

end
