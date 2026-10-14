import Submission.DifferentialGeometry.Geometry.Coordinates.Frame.ChangeOfBasis
import Submission.DifferentialGeometry.Geometry.Coordinates.Connection.Christoffel
import Submission.DifferentialGeometry.Geometry.Connection.LocalFrameRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {ι κ : Type*} [Fintype ι]

theorem christoffelSymbolInFrame_change_basis
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : _root_.Bundle.Trivialization E (π E (TangentSpace I : M → Type _)))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (c : Module.Basis κ ℝ E)
    {x : M} (hx : x ∈ e.baseSet) (i j k : κ) :
    christoffelSymbolInFrame cov (e.localFrame c)
      (e.isLocalFrameOn_localFrame_baseSet I 1 c) x i j k =
      ∑ a, ∑ d, ∑ m,
        (b.repr (c j) a * b.repr (c i) d * c.repr (b m) k) *
          christoffelSymbolInFrame cov (e.localFrame b)
            (e.isLocalFrameOn_localFrame_baseSet I 1 b) x d a m := by
  classical
  have hdiff (a : ι) : MDiffAt (T% (e.localFrame b a)) x :=
    ((e.isLocalFrameOn_localFrame_baseSet I 1 b).contMDiffAt
      e.open_baseSet hx a).mdifferentiableAt one_ne_zero
  have hterm (a : ι) :
      MDiffAt (T% (b.repr (c j) a • e.localFrame b a)) x :=
    mdifferentiableAt_const.smul_section (hdiff a)
  have hcov : (cov (e.localFrame c j) x) (e.localFrame c i x) =
      ∑ a, ∑ d, (b.repr (c j) a * b.repr (c i) d) •
        (cov (e.localFrame b a) x) (e.localFrame b d x) := by
    rw [localFrame_eq_sum_repr e b c j]
    rw [covariantDerivative_finset_sum_tangent cov Finset.univ _ _ hterm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [cov.isCovariantDerivativeOnUniv.smul_const _ (hdiff a)]
    simp only [smul_apply]
    rw [congrFun (localFrame_eq_sum_repr e b c i) x]
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, Finset.smul_sum,
      smul_smul]
  change e.localFrameCoeff I c k x
    ((cov (e.localFrame c j) x) (e.localFrame c i x)) = _
  rw [hcov, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [covariantDerivative_eq_sum_christoffel cov (e.localFrame b)
    (e.isLocalFrameOn_localFrame_baseSet I 1 b) hx d a]
  simp only [Finset.smul_sum, map_sum, map_smul, smul_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  change (b.repr (c j) a * b.repr (c i) d *
      christoffelSymbolInFrame cov (e.localFrame b)
        (e.isLocalFrameOn_localFrame_baseSet I 1 b) x d a m) *
      e.localFrameCoeff I c k x (e.localFrame b m x) = _
  rw [localFrame_coeff_localFrame e b c hx]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame_change_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame_change_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame_change_basis ``Submission.DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame_change_basis

end DifferentialGeometry.Tensor.Coordinates
