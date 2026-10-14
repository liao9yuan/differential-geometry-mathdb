import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry

open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance instCompleteSpaceE_keystone : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.instCompleteSpaceE_keystone
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.instCompleteSpaceE_keystone target :: scope.openDecls } }

theorem jointContMDiff_toModel_continuous_slice
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (x : M) :
    ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x)) S := by
  have hmap : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => (x, t)) :=
    (contMDiff_const).prodMk contMDiff_id
  have hmaps : Set.MapsTo (fun t : ℝ => (x, t)) S ((Set.univ : Set M) ×ˢ S) :=
    fun t ht => ⟨Set.mem_univ _, ht⟩
  have hslice : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun t : ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x ((Φ t).toSection x)) S :=
    hjoint.comp hmap.contMDiffOn hmaps
  have hcont_total : ContinuousOn (fun t : ℝ =>
      TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x ((Φ t).toSection x)) S :=
    hslice.continuousOn
  set e := _root_.FiberBundle.trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x with he
  have hxbase : x ∈ e.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x
  have hcoord : ContinuousOn (fun t : ℝ =>
      (e (TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x ((Φ t).toSection x))).2) S :=
    continuous_snd.comp_continuousOn (e.continuousOn_toFun.comp hcont_total
      (fun t _ => e.mem_source.mpr hxbase))
  have hfibre : ContinuousOn (fun t : ℝ => (Φ t).toSection x) S := by
    have hkey : ∀ t : ℝ, (Φ t).toSection x =
        (e.continuousLinearEquivAt ℝ x hxbase).symm
          ((e (TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x
            ((Φ t).toSection x))).2) := by
      intro t
      have hp := Trivialization.apply_eq_prod_continuousLinearEquivAt
        (R := ℝ) (e := e) (b := x) hxbase ((Φ t).toSection x)
      have hsnd := congrArg Prod.snd hp
      simp only at hsnd
      rw [hsnd, ContinuousLinearEquiv.symm_apply_apply]
    have hrhs : ContinuousOn (fun t : ℝ =>
        (e.continuousLinearEquivAt ℝ x hxbase).symm
          ((e (TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x
            ((Φ t).toSection x))).2)) S :=
      (e.continuousLinearEquivAt ℝ x hxbase).symm.continuous.comp_continuousOn hcoord
    exact hrhs.congr (fun t _ => hkey t)
  exact Tensor0SBundle.TensorRSSpace.toModel_continuous.comp_continuousOn hfibre

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.jointContMDiff_toModel_continuous_slice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.jointContMDiff_toModel_continuous_slice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.jointContMDiff_toModel_continuous_slice ``Submission.DifferentialGeometry.jointContMDiff_toModel_continuous_slice

end DifferentialGeometry
