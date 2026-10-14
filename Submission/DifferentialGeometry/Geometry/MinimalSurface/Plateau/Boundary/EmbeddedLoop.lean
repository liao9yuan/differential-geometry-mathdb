import Submission.DifferentialGeometry.Geometry.Metric.LoopEmbedding
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothTraceLift
import Submission.DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import Submission.DifferentialGeometry.Topology.Manifold.Quotient
import Submission.DifferentialGeometry.Analysis.Calculus.Periodic.Derivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.ContDiff _root_.NNReal _root_.Topology

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem contMDiff_loop_of_smooth_lift {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle))) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ := by
  apply AddCircle.isLocalDiffeomorph_coe.contMDiff_of_comp_of_surjective
    QuotientAddGroup.mk_surjective
  exact hγ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.contMDiff_loop_of_smooth_lift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.contMDiff_loop_of_smooth_lift target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem exists_lipschitz_antilipschitz_embedded_loop
    {Φ : M → F} (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    (hΦemb : _root_.Topology.IsEmbedding Φ)
    (hΦimm : ∀ p, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) Φ p))
    {γ : freeLoop M} (hγ : IsSmoothEmbeddedLoop (E := E) γ) :
    ∃ K J : ℝ≥0,
      LipschitzWith K (fun t : ℝ => Φ (γ (t : loopCircle))) ∧
      AntilipschitzWith J (fun θ : loopCircle => Φ (γ θ)) := by
  let Γ : loopCircle → F := Φ ∘ γ
  have hΓ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) ∞ Γ :=
    hΦ.comp (contMDiff_loop_of_smooth_lift hγ.smooth)
  have hΓimm : ∀ θ, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) Γ θ) := by
    intro θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    have hγc := contMDiff_loop_of_smooth_lift hγ.smooth
    have hchain := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))
      (I'' := 𝓘(ℝ, F)) (t : loopCircle)
      (hΦ.mdifferentiableAt (by simp)) (hγc.mdifferentiableAt (by simp))
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (Φ ∘ γ) (t : loopCircle))
    rw [hchain]
    apply (hΦimm _).comp
    have hlift : Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        (fun s : ℝ => γ (s : loopCircle)) t) :=
      realContinuousLinearMap_injective_of_one_ne_zero _ (hγ.immersed t)
    have hc := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, E)) t
      (hγc.mdifferentiableAt (x := (t : loopCircle)) (by simp))
      (AddCircle.contMDiff_coe.mdifferentiableAt (x := t) (by simp))
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (γ ∘ (fun s : ℝ => (s : loopCircle))) t) at hlift
    rw [hc] at hlift
    change Function.Injective ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (t : loopCircle)) ∘
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s : loopCircle)) t)) at hlift
    exact Function.Injective.of_comp_right hlift (AddCircle.bijective_mfderiv_coe t).2
  obtain ⟨J, hJ⟩ := exists_antilipschitzWith_of_smooth_loop_embedding
    hΓ (hΦemb.comp hγ.embedding) hΓimm
  have hΓreal : ContDiff ℝ ∞ (fun t : ℝ => Φ (γ (t : loopCircle))) :=
    (hΦ.comp hγ.smooth).contDiff
  have hp : Function.Periodic (fun t : ℝ => Φ (γ (t : loopCircle))) 1 := by
    intro t
    simp only [AddCircle.coe_add, AddCircle.coe_period, add_zero]
  obtain ⟨B, hB, hb⟩ := Analysis.exists_bound_of_continuous_unit_periodic
    (hΓreal.continuous_fderiv (by simp)) hp.fderiv
  refine ⟨⟨B, hB.le⟩, J, ?_, hJ⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (hΓreal.differentiable (by simp))
  intro t
  exact_mod_cast hb t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_lipschitz_antilipschitz_embedded_loop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_lipschitz_antilipschitz_embedded_loop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_lipschitz_antilipschitz_embedded_loop ``Submission.DifferentialGeometry.Geometry.exists_lipschitz_antilipschitz_embedded_loop

end DifferentialGeometry.Geometry

end
