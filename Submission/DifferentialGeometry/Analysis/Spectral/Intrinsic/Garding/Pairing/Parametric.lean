import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Pairing.Balanced
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.Parametric.ApplicationJetBound
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.Parametric.ScalarSmulJet

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

theorem iterL_pair_uniform (g : SmoothRiemannianMetric I M) (s n : ℕ)
    (Φ : ℝ → SmoothCcTensor g (s + 1) s) {S K : Set ℝ}
    (hK : IsCompact K) (hKS : K ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel (s + 1) s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel (s + 1) s ℝ E)
        (E := fun z : M => TensorRSSpace (s + 1) s I z) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, t ∈ K → ∀ U : SmoothCcTensor g 0 s,
      |tensorL2Inner (I := I) (M := M) g 0 s
          (oneMinusConnLapSmoothIter (I := I) g 0 s n U).toFun
          (operatorFieldApply (I := I) (M := M) g (s + 1) s (Φ t)
            (covGrad (I := I) (M := M) g 0 s U)).toFun| ≤
        C * ((∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g 0 s j U‖) *
          (∑ j ∈ Finset.range (n + 2),
            ‖iteratedCovGrad (I := I) g 0 s j U‖)) := by
  obtain ⟨CG, hCG_nn, hCG⟩ :=
    param_app_jet (I := I) (M := M) g (s + 1) s Φ hK hKS hjoint
  exact iterL_pair_jet_of (I := I) (M := M) g s n Φ K CG hCG_nn hCG

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.iterL_pair_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.iterL_pair_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.iterL_pair_uniform ``Submission.DifferentialGeometry.Analysis.Spectral.iterL_pair_uniform

theorem iterL_smul_uniform (g : SmoothRiemannianMetric I M) (n : ℕ)
    (zeta : ℝ → C^∞⟮I, M; ℝ⟯) {S K : Set ℝ}
    (hK : IsCompact K) (hKS : K ⊆ S)
    (hzeta : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => (zeta p.2 : M → ℝ) p.1)
      ((Set.univ : Set M) ×ˢ S)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, t ∈ K → ∀ U : SmoothCcTensor g 0 0,
      |tensorL2Inner (I := I) (M := M) g 0 0
          (oneMinusConnLapSmoothIter (I := I) g 0 0 n U).toFun
          (scalarSmul (I := I) (M := M) g 0 0 (zeta t) U).toFun| ≤
        C * ((∑ j ∈ Finset.range (n + 2),
            ‖iteratedCovGrad (I := I) g 0 0 j U‖) *
          (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g 0 0 j U‖)) := by
  classical
  obtain ⟨cY, hcY_nn, hcY⟩ :=
    smul_jet_uniform (I := I) (M := M) g zeta hK hKS hzeta
  obtain ⟨C, hC_nn, hC⟩ :=
    iterL_window_pair (I := I) (M := M) g 0 0 n (n / 2) 0 0
      (n + 1) n (by omega) (by omega) (by omega)
      (fun _ => 1) cY (fun _ => zero_le_one) hcY_nn
  refine ⟨C, hC_nn, fun t ht U => ?_⟩
  refine hC U U
    (scalarSmul (I := I) (M := M) g 0 0 (zeta t) U) ?_ (hcY t ht U)
  intro p
  rw [one_mul]
  refine Finset.single_le_sum
    (f := fun j : ℕ => ‖iteratedCovGrad (I := I) g 0 0 j U‖)
    (fun j _ => norm_nonneg _) ?_
  rw [Finset.mem_range]
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.iterL_smul_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.iterL_smul_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.iterL_smul_uniform ``Submission.DifferentialGeometry.Analysis.Spectral.iterL_smul_uniform

end Spectral
end Analysis
end DifferentialGeometry

end
