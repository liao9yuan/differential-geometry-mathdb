import Submission.DifferentialGeometry.Topology.Simplex.HomotopyExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Simplex

variable {X : Type*} [TopologicalSpace X]

theorem exists_continuous_extension_of_nullhomotopic (n : ℕ)
    (f : C(boundary (Fin (n + 1)), X)) (hf : f.Nullhomotopic) :
    ∃ F : C(stdSimplex ℝ (Fin (n + 1)), X),
      ∀ p : boundary (Fin (n + 1)), F p.val = f p := by
  obtain ⟨x, ⟨H⟩⟩ := hf
  obtain ⟨F, hF, hside⟩ := exists_continuous_homotopy_extension n
    (ContinuousMap.const _ x) H.symm.toContinuousMap (fun p => H.symm.apply_zero p)
  refine ⟨F.comp ⟨fun p => (1, p), continuous_const.prodMk continuous_id⟩, ?_⟩
  intro p
  exact (hside 1 p).trans (H.symm.apply_one p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.exists_continuous_extension_of_nullhomotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.exists_continuous_extension_of_nullhomotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.exists_continuous_extension_of_nullhomotopic ``Submission.DifferentialGeometry.Simplex.exists_continuous_extension_of_nullhomotopic

end DifferentialGeometry.Simplex
