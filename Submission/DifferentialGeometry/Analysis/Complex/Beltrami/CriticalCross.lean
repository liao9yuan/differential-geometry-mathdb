import Submission.DifferentialGeometry.Analysis.Complex.AnalyticCoordinates
import Submission.DifferentialGeometry.Analysis.Complex.Beltrami.AnalyticCoordinates
import Submission.DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.LocalCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Filter
open scoped _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis

theorem exists_alternating_cross_of_beltrami_critical
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) Ω)
    (hpos : ∀ z ∈ Ω, (A z).PosDef) (hdet : ∀ z ∈ Ω, (A z).det = 1)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℝ f Ω)
    (hBel : ∀ z ∈ Ω, complexAntilinearPart (fderiv ℝ f z) =
      beltramiCoefficient (A z 1 1) (A z 0 0) (-A z 0 1) *
        complexLinearPart (fderiv ℝ f z))
    (hnon : ¬ ∃ c : ℂ, _root_.Set.EqOn f (fun _ => c) Ω)
    {p : ℂ} (hp : p ∈ Ω) (hcrit : fderiv ℝ f p = 0) :
    ∃ E : OpenPartialHomeomorph (ℝ × ℝ) ℂ,
      (0 : ℝ × ℝ) ∈ E.source ∧ E (0, 0) = p ∧
      ∃ η : ℝ, 0 < η ∧
        (∀ t : ℝ, 0 < |t| → |t| < η → (f p).re < (f (E (t, 0))).re) ∧
        ∀ t : ℝ, 0 < |t| → |t| < η → (f (E (0, t))).re < (f p).re := by
  have hcoords (q : ℂ) (hq : q ∈ Ω) : ∃ e : OpenPartialHomeomorph ℂ ℂ,
      q ∈ e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      AnalyticOnNhd ℂ (fun z => f (e.symm z)) e.target := by
    obtain ⟨e, heq, heΩ, _, he, hei, hedet, heB⟩ :=
      exists_local_isothermal_coordinates hΩ A hA hpos hdet hq
    exact ⟨e, heq, hei, analyticOnNhd_comp_symm_of_same_beltrami hf hBel e heΩ
      (he.differentiableOn (by simp)) (fun z hz => (hedet z hz).ne') heB⟩
  have hatlas : ∀ q ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ ℂ,
      q ∈ e.source ∧ AnalyticOnNhd ℂ (fun z => f (e.symm z)) e.target := by
    intro q hq
    obtain ⟨e, heq, _, heA⟩ := hcoords q hq
    exact ⟨e, heq, heA⟩
  obtain ⟨e, hep, hei, heA⟩ := hcoords p hp
  exact exists_alternating_cross_in_analytic_coordinates hc hatlas hnon hp
    (hf.differentiableAt (hΩ.mem_nhds hp)) hcrit e hep (heA _ (e.map_source hep))
    ((hei.differentiableOn (by simp)).differentiableAt (e.open_target.mem_nhds (e.map_source hep)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_alternating_cross_of_beltrami_critical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_alternating_cross_of_beltrami_critical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_alternating_cross_of_beltrami_critical ``Submission.DifferentialGeometry.Analysis.exists_alternating_cross_of_beltrami_critical

end DifferentialGeometry.Analysis

end

end
