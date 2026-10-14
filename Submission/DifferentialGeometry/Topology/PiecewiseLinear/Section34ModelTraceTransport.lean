import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelMotionTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.inter_image_eq_of_model_conjugacy {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (ψ : M ≃ₜ M) (hφP : φ '' P = P) (hconj : ∀ x ∈ P, ψ (u x) = u (φ x))
    {A B : Set M} (hAP : A ⊆ u '' P) :
    A ∩ ψ '' B = u '' ((Function.invFunOn u P '' A) ∩ φ '' (P ∩ u ⁻¹' B)) := by
  let τ := Function.invFunOn u P
  have hleft : _root_.Set.LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : _root_.Set.RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hφmap : _root_.Set.MapsTo φ P P := fun _ hx => hφP ▸ _root_.Set.mem_image_of_mem φ hx
  have hψP : ψ '' (u '' P) = u '' P := by
    rw [_root_.Set.image_image]
    calc
      (ψ ∘ u) '' P = (u ∘ φ) '' P := _root_.Set.image_congr hconj
      _ = u '' P := by rw [_root_.Set.image_comp, hφP]
  ext x
  constructor
  · rintro ⟨hxA, y, hyB, hyx⟩
    have hyP : y ∈ u '' P := by
      obtain ⟨z, hz, hzx⟩ := hψP.symm ▸ hAP hxA
      exact (ψ.injective (hzx.trans hyx.symm)) ▸ hz
    obtain ⟨z, hz, rfl⟩ := hyP
    have hzx : u (φ z) = x := (hconj z hz).symm.trans hyx
    refine ⟨φ z, ⟨?_, ⟨z, ⟨hz, hyB⟩, rfl⟩⟩, hzx⟩
    exact ⟨x, hxA, by rw [← hzx]; exact hleft (hφmap hz)⟩
  · rintro ⟨y, ⟨⟨a, ha, hay⟩, ⟨z, hz, hzy⟩⟩, rfl⟩
    have hya : u y = a := hay ▸ hright (hAP ha)
    refine ⟨hya.symm ▸ ha, u z, hz.2, ?_⟩
    exact (hconj z hz.1).trans (congrArg u hzy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.inter_image_eq_of_model_conjugacy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.inter_image_eq_of_model_conjugacy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.inter_image_eq_of_model_conjugacy ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.inter_image_eq_of_model_conjugacy

end DifferentialGeometry.Topology.PiecewiseLinear
