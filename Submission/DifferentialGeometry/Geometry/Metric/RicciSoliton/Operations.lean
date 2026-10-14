import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import Submission.DifferentialGeometry.Geometry.Curvature.Product
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciNaturalityCross
import Submission.DifferentialGeometry.Geometry.Metric.Product
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.Defs
import Submission.DifferentialGeometry.Geometry.Operator.Pullback
import Submission.DifferentialGeometry.Geometry.Operator.Product

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem gradientRicciSoliton_scaleMetric
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ)
    (c : Real) (hc : 0 < c) :
    gradientRicciSoliton (I := I) (scaleMetric (I := I) c hc g) f (σ / c) := by
  intro x v w
  rw [Curvature.ricciTensor_scaleMetric, Operator.hessFun_scaleMetric,
    scaleMetric_inner, h x v w]
  field_simp [ne_of_gt hc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_scaleMetric ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_scaleMetric

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
variable [T2Space M] [I.Boundaryless] [T2Space N] [J.Boundaryless]

theorem gradientRicciSoliton_pullbackCross
    {g : SmoothRiemannianMetric J N} {f : C^∞⟮J, N; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := J) g f σ)
    (Φ : M ≃ₘ⟮I, J⟯ N) :
    gradientRicciSoliton (I := I)
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Φ)
      (f.comp Φ.toContMDiffMap) σ := by
  intro x v w
  rw [Curvature.ricciTensor_pullbackCross, Operator.hessFun_pullbackCross,
    Diffeomorph.pullbackMetricCross_inner]
  exact h (Φ x) (mfderiv I J (Φ : M → N) x v)
    (mfderiv I J (Φ : M → N) x w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_pullbackCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_pullbackCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_pullbackCross ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_pullbackCross

theorem gradientRicciSoliton_localPullMetric
    [SigmaCompactSpace M] [SigmaCompactSpace N]
    {g : SmoothRiemannianMetric J N} {f : C^∞⟮J, N; Real⟯}
    {Phi : M → N} {sigma : Real}
    (hsol : gradientRicciSoliton (I := J) g f sigma)
    (hPhi : IsLocalDiffeomorph I J ∞ Phi) :
    gradientRicciSoliton (I := I) (localPullMetric g Phi hPhi)
      (f.comp ⟨Phi, hPhi.contMDiff⟩) sigma := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let _ : CompleteSpace F := FiniteDimensional.complete Real F
  intro x v w
  change ricciTensor (localPullMetric g Phi hPhi) x v w +
    hessFun (localPullMetric g Phi hPhi) (f ∘ Phi) x v w =
      (sigma / 2) * (localPullMetric g Phi hPhi).inner x v w
  rw [ricciTensor_localPull, hessFun_localPull, localPullMetric_inner]
  exact hsol (Phi x) (mfderiv I J Phi x v) (mfderiv I J Phi x w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_localPullMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_localPullMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_localPullMetric ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_localPullMetric

theorem gradientRicciSoliton_of_surjective_localPullMetric
    [SigmaCompactSpace M] [SigmaCompactSpace N]
    {h : SmoothRiemannianMetric I M} {Fpot : C^∞⟮I, M; Real⟯}
    {g : SmoothRiemannianMetric J N} {f : C^∞⟮J, N; Real⟯}
    {Phi : M → N} {sigma : Real}
    (hsol : gradientRicciSoliton (I := I) h Fpot sigma)
    (hPhi : IsLocalDiffeomorph I J ∞ Phi)
    (hsurj : Function.Surjective Phi)
    (hpull : localPullMetric (I := I) (J := J) g Phi hPhi = h)
    (hpotential : ∀ x : M, Fpot x = f (Phi x)) :
    gradientRicciSoliton (I := J) g f sigma := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let _ : CompleteSpace F := FiniteDimensional.complete Real F
  have hpotentialEq : (Fpot : M → Real) = f ∘ Phi :=
    funext hpotential
  intro y a b
  obtain ⟨x, rfl⟩ := hsurj y
  let e : TangentSpace I x ≃L[Real] TangentSpace J (Phi x) :=
    hPhi.mfderivToContinuousLinearEquiv (by simp) x
  let v : TangentSpace I x := e.symm a
  let w : TangentSpace I x := e.symm b
  have hsource := hsol x v w
  rw [← hpull, hpotentialEq,
    Curvature.ricciTensor_localPull (I := I) (J := J) g Phi hPhi,
    Operator.hessFun_localPull (I := I) (J := J) g Phi hPhi,
    localPullMetric_inner] at hsource
  have he_apply (z : TangentSpace I x) :
      e z = mfderiv I J Phi x z := by
    have hco := hPhi.mfderivToContinuousLinearEquiv_coe
      (x := x) (by simp)
    exact congrArg
      (fun L : TangentSpace I x →L[Real] TangentSpace J (Phi x) ↦ L z) hco
  have hv : mfderiv I J Phi x v = a := by
    rw [← he_apply]
    exact e.apply_symm_apply a
  have hw : mfderiv I J Phi x w = b := by
    rw [← he_apply]
    exact e.apply_symm_apply b
  simpa only [hv, hw] using hsource

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_of_surjective_localPullMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_of_surjective_localPullMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_of_surjective_localPullMetric ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_of_surjective_localPullMetric

theorem gradientRicciSoliton_prod
    [BoundarylessManifold I M] [BoundarylessManifold J N]
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric J N}
    {f : C^∞⟮I, M; Real⟯} {k : C^∞⟮J, N; Real⟯} {σ : Real}
    (hg : gradientRicciSoliton (I := I) g f σ)
    (hh : gradientRicciSoliton (I := J) h k σ) :
    gradientRicciSoliton (I := I.prod J) (g.prod h)
      (f.comp ContMDiffMap.fst + k.comp ContMDiffMap.snd) σ := by
  intro x u v
  let uM : TangentSpace I x.1 := u.1
  let uN : TangentSpace J x.2 := u.2
  let vM : TangentSpace I x.1 := v.1
  let vN : TangentSpace J x.2 := v.2
  change Curvature.ricciTensor (I := I.prod J) (g.prod h) x u v +
      Operator.hessFun (I := I.prod J) (g.prod h)
        (fun q : M × N => f q.1 + k q.2) x u v =
    (σ / 2) * (g.prod h).inner x u v
  rw [Curvature.ricciTensor_productMetric, Operator.hessFun_prod,
    SmoothRiemannianMetric.prod_inner]
  change Curvature.ricciTensor (I := I) g x.1 uM vM +
        Curvature.ricciTensor (I := J) h x.2 uN vN +
      (Operator.hessFun (I := I) g f x.1 uM vM +
        Operator.hessFun (I := J) h k x.2 uN vN) =
    (σ / 2) * (g.inner x.1 uM vM + h.inner x.2 uN vN)
  calc
    _ = (Curvature.ricciTensor (I := I) g x.1 uM vM +
          Operator.hessFun (I := I) g f x.1 uM vM) +
        (Curvature.ricciTensor (I := J) h x.2 uN vN +
          Operator.hessFun (I := J) h k x.2 uN vN) := by ring
    _ = (σ / 2) * g.inner x.1 uM vM +
        (σ / 2) * h.inner x.2 uN vN := by
      rw [hg x.1 uM vM, hh x.2 uN vN]
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_prod ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_prod

end DifferentialGeometry.Geometry
