import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelMotionTransport
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSupportedModification

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.isPLOn_symm_of_supported_homeomorph {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hP : IsPLBall 3 P) (ψ : M ≃ₜ M) {K : Set M}
    (hK : IsClosed K) (hKP : K ⊆ interior (u '' P)) (hfix : _root_.Set.EqOn ψ id Kᶜ)
    (hψ : IsPLOn 3 3 ψ (interior (u '' P))) : IsPLOn 3 3 ψ.symm (interior (u '' P)) := by
  obtain ⟨r, hr⟩ := hP
  have hψu := hu.postcomp_of_supported_isPLOn (isPLCellOn_id_of_isPLBall hr) ψ hψ
    isOpen_interior hK hKP hfix
  have hψP : ψ '' (u '' P) = u '' P :=
    image_eq_of_homeomorph_eqOn_compl_of_subset ψ hfix (hKP.trans interior_subset)
  let τ := Function.invFunOn u P
  have hleft : _root_.Set.LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : _root_.Set.RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hψsP : _root_.Set.MapsTo ψ.symm (u '' P) (u '' P) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hψP.symm.subset hx
    rw [← hyx, ψ.symm_apply_apply]
    exact hy
  have hgleft : _root_.Set.LeftInvOn (τ ∘ ψ.symm) (ψ ∘ u) P := by
    intro x hx
    change τ (ψ.symm (ψ (u x))) = x
    rw [ψ.symm_apply_apply]
    exact hleft hx
  have hg : IsPLOn 3 3 (τ ∘ ψ.symm) (u '' P) := by
    have hg := hψu.isPLOn_inverse hgleft
    rwa [_root_.Set.image_comp, hψP] at hg
  have hmap : _root_.Set.MapsTo (τ ∘ ψ.symm) (u '' P) P :=
    hu.injOn.bijOn_image.surjOn.mapsTo_invFunOn.comp hψsP
  have hinv : IsPLOn 3 3 ψ.symm (u '' P) := (hu.isPLOn.comp_of_mapsTo hg hmap).congr
    (fun x hx => (hright (hψsP hx)).symm)
  exact hinv.mono_of_isOpen isOpen_interior interior_subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.isPLOn_symm_of_supported_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.isPLOn_symm_of_supported_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.isPLOn_symm_of_supported_homeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.isPLOn_symm_of_supported_homeomorph

end DifferentialGeometry.Topology.PiecewiseLinear
