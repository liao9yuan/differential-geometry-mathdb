import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.RicciTrace.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.MovingFrame.CurvatureTraceSmoothness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
theorem orthonormalFrame_parseval_expand
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (u : TangentSpace I x) :
    u = ∑ a : Fin n, g.inner x (e a) u • e a := by
  classical
  have hfinrank_eq : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  have : Nonempty (Fin n) := by
    refine ⟨⟨0, ?_⟩⟩
    rw [hn, hfinrank_eq]
    exact Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs,
        g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (e k)).map_smul (c j) (e j), smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk; rw [if_neg (fun h => hjk h.symm), _root_.MulZeroClass.mul_zero]
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]; exact hn
  set bse : Module.Basis (Fin n) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse_eq : ∀ i, bse i = e i := by
    intro i; rw [hbse_def]
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i
  conv_lhs => rw [← bse.sum_repr u]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [hbse_eq a]
  congr 1
  have hrepr : g.inner x (e a) u =
      ∑ b : Fin n, bse.repr u b * g.inner x (e a) (e b) := by
    conv_lhs => rw [show u = ∑ b : Fin n,
      bse.repr u b • bse b from (bse.sum_repr u).symm]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [(g.inner x (e a)).map_smul (bse.repr u b) (bse b), smul_eq_mul, hbse_eq b]
  rw [hrepr, Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, mul_one]
  · intro b _ hba; rw [horth a b, if_neg (fun h => hba h.symm), _root_.MulZeroClass.mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.orthonormalFrame_parseval_expand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.orthonormalFrame_parseval_expand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.orthonormalFrame_parseval_expand ``Submission.DifferentialGeometry.Geometry.Curvature.orthonormalFrame_parseval_expand

omit [CompactSpace M] in
theorem pointwiseTensorCurv_toSection_eq_genuine_add_bracket_ofOrthonormal
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (w : TangentSpace I x) (m : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x w) m) =
      genuineThirdCurvFieldFib (I := I) (M := M) g s S x e w m +
        bracketThirdCurvFieldFib (I := I) (M := M) g s S x e w m := by
  classical
  have hexp : ∀ u : TangentSpace I x, u = ∑ a : Fin n,
      g.inner x (e a) u • e a := fun u =>
    orthonormalFrame_parseval_expand (I := I) (M := M) g x e hn horth u
  rw [tensor0S_uncurry_cons_eval_orthonormal (I := I) (M := M) g
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) e hexp w m]
  rw [genuineThirdCurvFieldFib, bracketThirdCurvFieldFib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction
    (I := I) (M := M) g s S x (e a)]
  rw [Tensor0SSpace.toModel_add, add_apply, smul_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_toSection_eq_genuine_add_bracket_ofOrthonormal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_toSection_eq_genuine_add_bracket_ofOrthonormal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_toSection_eq_genuine_add_bracket_ofOrthonormal ``Submission.DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_toSection_eq_genuine_add_bracket_ofOrthonormal

noncomputable def genuineCurvPureRSubtracted
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  pointwiseTensorCurv (I := I) (M := M) g s S - genuineCurvatureOnlySection (I := I) (M := M) g s S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineCurvPureRSubtracted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineCurvPureRSubtracted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineCurvPureRSubtracted ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvPureRSubtracted

@[simp] lemma genuineCurvPureRSubtracted_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    (genuineCurvPureRSubtracted (I := I) (M := M) g s S).toSection =
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection -
        (genuineCurvatureOnlySection (I := I) (M := M) g s S).toSection := by
  rw [genuineCurvPureRSubtracted, SmoothCcTensor.toSection_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineCurvPureRSubtracted_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineCurvPureRSubtracted_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineCurvPureRSubtracted_toSection ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvPureRSubtracted_toSection

theorem genuineCurvPureRSubtracted_toSection_eq_covDeriv_add_bracket
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (w : TangentSpace I x) (m : Fin s → E),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (genuineCurvPureRSubtracted (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x))
              (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x w) m) =
          genuineThirdCurvFieldFibCovDeriv (I := I) (M := M) g s S x e w m +
            bracketThirdCurvFieldFib (I := I) (M := M) g s S x e w m := by
  classical
  obtain ⟨n, e, hn, horth, hGcurv⟩ :=
    GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x
  refine ⟨n, e, hn, horth, fun w m => ?_⟩
  have hsub : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (genuineCurvPureRSubtracted (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x w) m) =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
            (unitZeroSec (I := I) (M := M) x))
            (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x w) m) -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (genuineCurvatureOnlySection (I := I) (M := M) g s S).toSection x)
            (unitZeroSec (I := I) (M := M) x))
            (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x w) m) := by
    rw [genuineCurvPureRSubtracted_toSection]
    rw [show ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection -
        (genuineCurvatureOnlySection (I := I) (M := M) g s S).toSection) x =
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x -
        (genuineCurvatureOnlySection (I := I) (M := M) g s S).toSection x from rfl]
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x -
            (genuineCurvatureOnlySection (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (genuineCurvatureOnlySection (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x) from
      sub_apply _ _ _]
    rw [Tensor0SSpace.toModel_sub, sub_apply]
  rw [hsub]
  rw [pointwiseTensorCurv_toSection_eq_genuine_add_bracket_ofOrthonormal
    (I := I) (M := M) g s S x e hn horth w m]
  rw [genuineThirdCurvFieldFib_eq_pureR_add_covDeriv (I := I) (M := M) g s S x e w m]
  rw [hGcurv w m]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineCurvPureRSubtracted_toSection_eq_covDeriv_add_bracket then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineCurvPureRSubtracted_toSection_eq_covDeriv_add_bracket"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineCurvPureRSubtracted_toSection_eq_covDeriv_add_bracket ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvPureRSubtracted_toSection_eq_covDeriv_add_bracket

noncomputable def movingFrameRemainderSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  pointwiseTensorCurv (I := I) (M := M) g s S - genuineCurvatureOnlySection (I := I) (M := M) g s S
    -
    genuineDiffCurvSection (I := I) (M := M) g s S - ricTraceSection (I := I) (M := M) g s S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.movingFrameRemainderSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.movingFrameRemainderSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.movingFrameRemainderSection ``Submission.DifferentialGeometry.Geometry.Curvature.movingFrameRemainderSection

@[simp] lemma movingFrameRemainderSection_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    (movingFrameRemainderSection (I := I) (M := M) g s S).toSection =
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection -
          (genuineCurvatureOnlySection (I := I) (M := M) g s S).toSection -
          (genuineDiffCurvSection (I := I) (M := M) g s S).toSection -
        (ricTraceSection (I := I) (M := M) g s S).toSection := by
  rw [movingFrameRemainderSection, SmoothCcTensor.toSection_sub,
    SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.movingFrameRemainderSection_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.movingFrameRemainderSection_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.movingFrameRemainderSection_toSection ``Submission.DifferentialGeometry.Geometry.Curvature.movingFrameRemainderSection_toSection

theorem movingFrameRemainderSection_eq_pureRSubtracted_sub_genuineDiff_ricTrace
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    movingFrameRemainderSection (I := I) (M := M) g s S =
      genuineCurvPureRSubtracted (I := I) (M := M) g s S -
        (genuineDiffCurvSection (I := I) (M := M) g s S +
          ricTraceSection (I := I) (M := M) g s S) := by
  rw [movingFrameRemainderSection, genuineCurvPureRSubtracted]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.movingFrameRemainderSection_eq_pureRSubtracted_sub_genuineDiff_ricTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.movingFrameRemainderSection_eq_pureRSubtracted_sub_genuineDiff_ricTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.movingFrameRemainderSection_eq_pureRSubtracted_sub_genuineDiff_ricTrace ``Submission.DifferentialGeometry.Geometry.Curvature.movingFrameRemainderSection_eq_pureRSubtracted_sub_genuineDiff_ricTrace

end Curvature
end Geometry
end DifferentialGeometry
