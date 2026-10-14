import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.EulerLagrange
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Existence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_weakly_harmonic_dirichlet_minimizer
    {ι : Type*} [Fintype ι] (hd : 2 ≤ d) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {b : E → EuclideanSpace ℝ ι}
    (hb : ∀ i, DeGiorgi.MemW1p 2 (fun x => b x i) Ω) :
    ∃ (u : E → EuclideanSpace ℝ ι),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => u x i - b x i) Ω) ∧
      ∃ hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω,
        (∀ (v : E → EuclideanSpace ℝ ι),
          (∀ i, DeGiorgi.MemW01p 2 (fun x => v x i - b x i) Ω) →
          ∀ hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω,
            (∑ i, ∫ x in Ω, ‖(hu i).weakGrad x‖ ^ 2) ≤
              ∑ i, ∫ x in Ω, ‖(hv i).weakGrad x‖ ^ 2) ∧
        ∀ i (φ : E → ℝ), DeGiorgi.IsSmoothTestOn Ω φ →
          (∫ x in Ω, _root_.Inner.inner ℝ ((hu i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0 := by
  let _ : NeZero d := ⟨by omega⟩
  have hb0 (i : ι) : DeGiorgi.MemW01p 2 (fun x => b x i - b x i) Ω := by
    simpa only [sub_self] using
      DeGiorgi.smoothTest_memH01 hΩ (DeGiorgi.IsSmoothTestOn.zero (Ω := Ω))
  obtain ⟨u, hu0, _, hu, hmin⟩ := exists_dirichlet_integral_minimizer hd hΩ hΩb hb
    (K := Set.univ) isClosed_univ ⟨b, hb0, Filter.Eventually.of_forall fun _ => _root_.Set.mem_univ _⟩
  have hmin' : ∀ (v : E → EuclideanSpace ℝ ι),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => v x i - b x i) Ω) →
      ∀ hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω,
        (∑ i, ∫ x in Ω, ‖(hu i).weakGrad x‖ ^ 2) ≤
          ∑ i, ∫ x in Ω, ‖(hv i).weakGrad x‖ ^ 2 := by
    intro v hv0 hv
    exact hmin v hv0 (Filter.Eventually.of_forall fun _ => _root_.Set.mem_univ _) hv
  exact ⟨u, hu0, hu, hmin', fun i φ hφ =>
    integral_inner_weakGrad_smoothGrad_eq_zero_of_dirichlet_minimizer hΩ hu hu0 hmin' i hφ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_weakly_harmonic_dirichlet_minimizer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_weakly_harmonic_dirichlet_minimizer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_weakly_harmonic_dirichlet_minimizer ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_weakly_harmonic_dirichlet_minimizer

end DifferentialGeometry.Analysis.Sobolev.Euclidean
