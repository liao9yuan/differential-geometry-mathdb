import Submission.DifferentialGeometry.Topology.Manifold.MFDeriv.ModelTransport
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Cross
import Submission.DifferentialGeometry.Topology.Manifold.ModelWithCorners

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.SmoothRiemannianMetric

open scoped _root_.Manifold _root_.ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

def transContinuousLinearEquiv
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F) :
    SmoothRiemannianMetric (I.transContinuousLinearEquiv e) M :=
  Diffeomorph.pullbackMetricCross g (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.transContinuousLinearEquiv ``Submission.DifferentialGeometry.SmoothRiemannianMetric.transContinuousLinearEquiv

omit [FiniteDimensional ℝ E] in
theorem transContinuousLinearEquiv_inner
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F)
    (x : M) (v w : TangentSpace (I.transContinuousLinearEquiv e) x) :
    (g.transContinuousLinearEquiv e).inner x v w =
      g.inner x (e.symm v) (e.symm w) := by
  have h := Diffeomorph.pullbackMetricCross_inner g
    (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e).symm x v w
  change _ = g.inner x (mfderiv (I.transContinuousLinearEquiv e) I id x v)
    (mfderiv (I.transContinuousLinearEquiv e) I id x w) at h
  rw [DifferentialGeometry.Manifold.mfderiv_id_transContinuousLinearEquiv] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.transContinuousLinearEquiv_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.transContinuousLinearEquiv_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.transContinuousLinearEquiv_inner ``Submission.DifferentialGeometry.SmoothRiemannianMetric.transContinuousLinearEquiv_inner

theorem pullback_transContinuousLinearEquiv
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F) :
    Diffeomorph.pullbackMetricCross (g.transContinuousLinearEquiv e)
      (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e) = g := by
  rw [transContinuousLinearEquiv, Diffeomorph.pullbackMetricCross_trans]
  have hΦ : (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e).trans
      (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e).symm =
        Diffeomorph.refl I M ∞ := by ext x; rfl
  rw [hΦ, Diffeomorph.pullbackMetricCross_refl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.pullback_transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.pullback_transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.pullback_transContinuousLinearEquiv ``Submission.DifferentialGeometry.SmoothRiemannianMetric.pullback_transContinuousLinearEquiv

theorem restrictOpen_transContinuousLinearEquiv
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F) (U : TopologicalSpace.Opens M) :
    (g.transContinuousLinearEquiv e).restrictOpen U = (g.restrictOpen U).transContinuousLinearEquiv e := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hL := g.transContinuousLinearEquiv_inner e x.val v w
  have hR := (g.restrictOpen U).transContinuousLinearEquiv_inner e x v w
  exact hL.trans hR.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.restrictOpen_transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.restrictOpen_transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.restrictOpen_transContinuousLinearEquiv ``Submission.DifferentialGeometry.SmoothRiemannianMetric.restrictOpen_transContinuousLinearEquiv

end

end DifferentialGeometry.SmoothRiemannianMetric

namespace DifferentialGeometry

open scoped _root_.Manifold _root_.ContDiff

variable {E E' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

omit [FiniteDimensional ℝ F] in
theorem Diffeomorph.pullbackMetricCross_transContinuousLinearEquiv_of_coe_eq
    (g : SmoothRiemannianMetric J N) (e : E ≃L[ℝ] E') (f : F ≃L[ℝ] F')
    (Phi : M ≃ₘ⟮I, J⟯ N)
    (Psi : M ≃ₘ⟮I.transContinuousLinearEquiv e, J.transContinuousLinearEquiv f⟯ N)
    (h : (Psi : M → N) = Phi) :
    Diffeomorph.pullbackMetricCross (g.transContinuousLinearEquiv f) Psi =
      (Diffeomorph.pullbackMetricCross g Phi).transContinuousLinearEquiv e := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hL := Diffeomorph.pullbackMetricCross_inner (g.transContinuousLinearEquiv f) Psi x v w
  have hL' := g.transContinuousLinearEquiv_inner f (Psi x)
    (mfderiv (I.transContinuousLinearEquiv e) (J.transContinuousLinearEquiv f) Psi x v)
    (mfderiv (I.transContinuousLinearEquiv e) (J.transContinuousLinearEquiv f) Psi x w)
  have hR := (Diffeomorph.pullbackMetricCross g Phi).transContinuousLinearEquiv_inner e x v w
  have hR' := Diffeomorph.pullbackMetricCross_inner g Phi x (e.symm v) (e.symm w)
  apply (hL.trans hL').trans
  apply Eq.trans ?_ (hR.trans hR').symm
  rw [h]
  have hd := DifferentialGeometry.Manifold.mfderiv_transContinuousLinearEquiv_naturality e f
    (Phi.mdifferentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0) x)
  have hv := congrArg (fun T => T v) hd
  have hw := congrArg (fun T => T w) hd
  exact congrArg₂ (fun a b : F => g.inner (Phi x) a b) hv hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackMetricCross_transContinuousLinearEquiv_of_coe_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackMetricCross_transContinuousLinearEquiv_of_coe_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackMetricCross_transContinuousLinearEquiv_of_coe_eq ``Submission.DifferentialGeometry.Diffeomorph.pullbackMetricCross_transContinuousLinearEquiv_of_coe_eq

end DifferentialGeometry
