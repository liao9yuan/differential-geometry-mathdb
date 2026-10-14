import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactlySupportedCohomology.OpenEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

theorem integralCompactlySupportedCohomologyPushforward_homeomorph_bijective
    (n : ℕ) (e : X ≃ₜ Y) :
    Function.Bijective (integralCompactlySupportedCohomologyPushforward n
      ⟨e, e.continuous⟩ e.isOpenEmbedding) := by
  let : T2Space X := e.symm.t2Space
  let f : ContinuousMap X Y := ⟨e, e.continuous⟩
  let g : ContinuousMap Y X := ⟨e.symm, e.symm.continuous⟩
  have hgf : g.comp f = ContinuousMap.id X := ContinuousMap.ext e.symm_apply_apply
  have hfg : f.comp g = ContinuousMap.id Y := ContinuousMap.ext e.apply_symm_apply
  have hl : Function.LeftInverse
      (integralCompactlySupportedCohomologyPushforward n g e.symm.isOpenEmbedding)
      (integralCompactlySupportedCohomologyPushforward n f e.isOpenEmbedding) := by
    intro a
    have h := LinearMap.congr_fun (integralCompactlySupportedCohomologyPushforward_comp n
      f g e.isOpenEmbedding e.symm.isOpenEmbedding) a
    simpa only [hgf, integralCompactlySupportedCohomologyPushforward_id,
      LinearMap.comp_apply, LinearMap.id_apply] using h.symm
  have hr : Function.RightInverse
      (integralCompactlySupportedCohomologyPushforward n g e.symm.isOpenEmbedding)
      (integralCompactlySupportedCohomologyPushforward n f e.isOpenEmbedding) := by
    intro a
    have h := LinearMap.congr_fun (integralCompactlySupportedCohomologyPushforward_comp n
      g f e.symm.isOpenEmbedding e.isOpenEmbedding) a
    simpa only [hfg, integralCompactlySupportedCohomologyPushforward_id,
      LinearMap.comp_apply, LinearMap.id_apply] using h.symm
  exact ⟨hl.injective, hr.surjective⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_homeomorph_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_homeomorph_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_homeomorph_bijective ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_homeomorph_bijective

end DifferentialGeometry.Topology
