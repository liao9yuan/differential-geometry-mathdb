import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Scalar.Nonautonomous.SobolevBound
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLaplacianDifference.L2Bound
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Scalar.LaplacianDifferenceCore

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }

theorem lapDiffHs_eq_A20
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) :
    ∀ᶠ s in 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ),
      ∀ u : TensorHs (I := I) (M := M) (g_fam (T : ℝ)) 0 0 2,
        TensorHs.castEquiv (I := I) (M := M)
            (g := g_fam (T : ℝ)) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) = 0)
            (lapDiffHs (I := I) (M := M) (g_fam (T : ℝ))
              (g_fam ((T : ℝ) - s)) 0
              (TensorHs.castEquiv (I := I) (M := M)
                (g := g_fam (T : ℝ)) (r := 0) (s := 0)
                (by norm_num : (2 : ℝ) = ((0 : ℕ) : ℝ) + 2) u)) =
          lapDiffA20 (I := I) (M := M) g_fam T s u := by
  classical
  obtain ⟨tau, htau, _, _, hHs⟩ :=
    exists_uniform_lapDiffHs_apply_ccTensorToHs (I := I) (M := M) g_fam hG T
  have hIcc : Set.Icc (0 : ℝ) tau ∈ 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ) :=
    Icc_mem_nhdsGE htau
  have hle : 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ) ≤ 𝓝 (0 : ℝ) :=
    nhdsWithin_le_nhds
  have hA20 :=
    (eventually_lapDiffA20_apply_scalarH2Core (I := I) (M := M) g_fam hG T).filter_mono
      hle
  filter_upwards [hIcc, hA20] with s hs hsA20
  let q : SmoothRiemannianMetric I M := g_fam (T : ℝ)
  let h : SmoothRiemannianMetric I M := g_fam ((T : ℝ) - s)
  let J : TensorHs (I := I) (M := M) q 0 0 2 →L[ℝ]
      TensorHs (I := I) (M := M) q 0 0 (((0 : ℕ) : ℝ) + 2) :=
    (TensorHs.castEquiv (I := I) (M := M)
      (g := q) (r := 0) (s := 0)
      (by norm_num : (2 : ℝ) = ((0 : ℕ) : ℝ) + 2)).toContinuousLinearEquiv.toContinuousLinearMap
  let K : TensorHs (I := I) (M := M) q 0 0 ((0 : ℕ) : ℝ) →L[ℝ]
      TensorHs (I := I) (M := M) q 0 0 0 :=
    (TensorHs.castEquiv (I := I) (M := M)
      (g := q) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) = 0)).toContinuousLinearEquiv.toContinuousLinearMap
  let L := K.comp ((lapDiffHs (I := I) (M := M) q h 0).comp J)
  let R := lapDiffA20 (I := I) (M := M) g_fam T s
  intro u
  change L u = R u
  have hdense : DenseRange
      (ScalarH2Core (I := I) (M := M) q).subtype :=
    (tensorHsFiniteSupportSubmodule_dense
      (I := I) (M := M) (g := q) (r := 0) (s := 0) (σ := 2)).denseRange_val
  have heq :
      L ∘ (ScalarH2Core (I := I) (M := M) q).subtype =
        R ∘ (ScalarH2Core (I := I) (M := M) q).subtype := by
    funext v
    let U : SmoothCcTensor q 0 0 :=
      tensorHsSmoothRepr (I := I) (M := M) v.1 v.2
    have hrepr :
        ccTensorToHs (I := I) (M := M) q 0 2 U = v.1 := by
      simpa only [U, ccToHsLin_apply] using
        (ccToHsLin_repr (I := I) (M := M) q 0
          (show (0 : ℝ) ≤ 2 by norm_num) v.1 v.2)
    change L v.1 = R v.1
    rw [← hrepr]
    have hJ :
        J (ccTensorToHs (I := I) (M := M) q 0 2 U) =
          ccTensorToHs (I := I) (M := M) q 0 (((0 : ℕ) : ℝ) + 2) U := by
      apply TensorHs.ext
      funext i
      rfl
    rw [show L (ccTensorToHs (I := I) (M := M) q 0 2 U) =
        ccTensorToHs (I := I) (M := M) q 0 0
          (scalarLapDiffCc (I := I) q h U) by
      change K (lapDiffHs (I := I) (M := M) q h 0
          (J (ccTensorToHs (I := I) (M := M) q 0 2 U))) = _
      rw [hJ]
      rw [hHs 0 s hs U]
      apply TensorHs.ext
      funext i
      rfl]
    apply TensorHs.ext
    funext i
    rw [ccTensorToHs_coeff]
    have hc := congrArg
      (fun Z : TensorL2 0 0 q =>
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator
            (I := I) (M := M) q 0 0) Z i)
      (hsA20 v)
    simp only [tensorHsZeroEquivL2_tensorL2Coeff] at hc
    rw [lapDiffCore_eq_cc (I := I) (M := M)] at hc
    simpa only [R, q, h, U, hrepr] using hc.symm
  have hfun := hdense.equalizer L.continuous R.continuous heq
  exact congr_fun hfun u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffHs_eq_A20 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffHs_eq_A20"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffHs_eq_A20 ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffHs_eq_A20

end DifferentialGeometry.Analysis.Spectral

end
