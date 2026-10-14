import Submission.DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature.CovariantDerivative

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

private theorem metricRm04StdAt_eq_inner_riemannOp
    (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    metricRm04StandardAt (I := I) g x X Y Z W =
      g.inner x W (riemannOp (cov := LeviCivita (I := I) g) x X Y Z) := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  rw [metricRm04StandardAt_apply,
    show metricRm04At (I := I) g x =
        riemannCurvature04At g (metricCov (I := I) g) (metricCov_smooth (I := I) g) x
      from rfl,
    riemannCurvature04At_apply_const]
  have : CovariantDerivative.ContMDiffCovariantDerivative (metricCov (I := I) g) ∞ :=
    LeviCivita_isContMDiff g
  rw [connectionRiemannCurvatureField_tangentConst_eq_riemannOp (metricCov (I := I) g)
      (metricCov_smooth (I := I) g) x X Y Z,
    show riemannOp (cov := metricCov (I := I) g) x X Y Z =
        riemannOp (cov := LeviCivita (I := I) g) x X Y Z from rfl]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.metricRm04StdAt_eq_inner_riemannOp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.metricRm04StdAt_eq_inner_riemannOp target :: scope.openDecls } }

theorem ricciTensor_pullbackCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Φ) x v w =
      ricciTensor (I := J) g (Φ x)
        (mfderiv I J (Φ : M → N) x v)
        (mfderiv I J (Φ : M → N) x w) := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let _ : CompleteSpace F := FiniteDimensional.complete Real F
  classical
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Φ) x
  let dΦ : TangentSpace I x ≃L[Real] TangentSpace J (Φ x) :=
    Diffeomorph.mfderivToContinuousLinearEquiv Φ (by simp) x
  let idxEquiv :
      Fin (Module.finrank Real (TangentSpace I x)) ≃
        Fin (Module.finrank Real (TangentSpace J (Φ x))) :=
    finCongr dΦ.toLinearEquiv.finrank_eq
  let basis' :
      Module.Basis (Fin (Module.finrank Real (TangentSpace J (Φ x))))
        Real (TangentSpace J (Φ x)) :=
    (basis.map dΦ.toLinearEquiv).reindex idxEquiv
  have hdΦ_apply : ∀ u : TangentSpace I x,
      dΦ u = mfderiv I J (Φ : M → N) x u := by
    intro u
    have hco := Diffeomorph.mfderivToContinuousLinearEquiv_coe
      (Φ := Φ) (x := x) (by simp)
    exact congrArg
      (fun L : TangentSpace I x →L[Real] TangentSpace J (Φ x) => L u) hco
  have hbasis'_apply : ∀ j,
      basis' j = mfderiv I J (Φ : M → N) x (basis (idxEquiv.symm j)) := by
    intro j
    change ((basis.map dΦ.toLinearEquiv).reindex idxEquiv) j = _
    rw [Module.Basis.reindex_apply, Module.Basis.map_apply]
    change dΦ (basis (idxEquiv.symm j)) =
      mfderiv I J (Φ : M → N) x (basis (idxEquiv.symm j))
    exact hdΦ_apply _
  have hON' : ∀ i j,
      g.inner (Φ x) (basis' i) (basis' j) =
        if i = j then (1 : Real) else 0 := by
    intro i j
    rw [hbasis'_apply i, hbasis'_apply j,
      ← Diffeomorph.pullbackMetricCross_inner
        (I := I) (J := J) g Φ x
        (basis (idxEquiv.symm i)) (basis (idxEquiv.symm j))]
    simpa using hON (idxEquiv.symm i) (idxEquiv.symm j)
  rw [ricciTensor_eq_orthonormal_trace
        (I := I) (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Φ)
        x v w (fun i => basis i) hON,
      ricciTensor_eq_orthonormal_trace
        (I := J) g (Φ x)
        (mfderiv I J (Φ : M → N) x v)
        (mfderiv I J (Φ : M → N) x w)
        (fun i => basis' i) hON']
  refine Fintype.sum_equiv idxEquiv _ _ ?_
  intro i
  have hbasis'_comp :
      basis' (idxEquiv i) = mfderiv I J (Φ : M → N) x (basis i) := by
    simpa using hbasis'_apply (idxEquiv i)
  rw [hbasis'_comp]
  rw [(Diffeomorph.pullbackMetricCross (I := I) (J := J) g Φ).symm x
        (riemannOp
          (cov := LeviCivita (I := I)
            (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Φ))
          x (basis i) v w) (basis i),
      ← metricRm04StdAt_eq_inner_riemannOp
        (I := I) (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Φ)
        x (basis i) v w (basis i),
      metricRm04Standard_pullbackCross
        (I := I) (J := J) g Φ x (basis i) v w (basis i),
      metricRm04StdAt_eq_inner_riemannOp
        (I := J) g (Φ x)
        (mfderiv I J (Φ : M → N) x (basis i))
        (mfderiv I J (Φ : M → N) x v)
        (mfderiv I J (Φ : M → N) x w)
        (mfderiv I J (Φ : M → N) x (basis i)),
      g.symm (Φ x)
        (mfderiv I J (Φ : M → N) x (basis i))
        (riemannOp (cov := LeviCivita (I := J) g) (Φ x)
          (mfderiv I J (Φ : M → N) x (basis i))
          (mfderiv I J (Φ : M → N) x v)
          (mfderiv I J (Φ : M → N) x w))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciTensor_pullbackCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciTensor_pullbackCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciTensor_pullbackCross ``Submission.DifferentialGeometry.Geometry.Curvature.ricciTensor_pullbackCross

end DifferentialGeometry.Geometry.Curvature
