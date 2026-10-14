import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section


universe u uE uH

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

open _root_.Module _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.RealInnerProductSpace

section Normed

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

noncomputable def normalBasis (g : SmoothRiemannianMetric I M) (x : M) :
    Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x) := by
  let D := (tangentMetricData (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  have hdim : Module.finrank Real (TangentSpace I x) = Module.finrank Real E := by
    change Module.finrank Real E = Module.finrank Real E
    rfl
  exact ((stdOrthonormalBasis Real (TangentSpace I x)).reindex (finCongr hdim)).toBasis

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalBasis ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalBasis

theorem normalBasis_inner (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank Real E)) :
    g.inner x (normalBasis (I := I) g x i) (normalBasis (I := I) g x j) =
      if i = j then (1 : Real) else 0 := by
  let D := (tangentMetricData (I := I) g x).metric
  let : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  let : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  have hdim : Module.finrank Real (TangentSpace I x) = Module.finrank Real E := by
    change Module.finrank Real E = Module.finrank Real E
    rfl
  let ob := (stdOrthonormalBasis Real (TangentSpace I x)).reindex (finCongr hdim)
  have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
    MetricFiberData.toCore_inner D (ob i) (ob j)
  have hob := ob.inner_eq_ite i j
  change g.inner x (ob i) (ob j) = if i = j then (1 : Real) else 0
  rw [← TangentMetricData.inner_eq
    (tangentMetricData (I := I) g x) (ob i) (ob j)]
  change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
  rw [← hinner]
  exact hob

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalBasis_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalBasis_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalBasis_inner ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalBasis_inner

noncomputable def euclideanNormalFrame (g : SmoothRiemannianMetric I M) (x : M) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃L[ℝ] TangentSpace I x := by
  let _ : T2Space (TangentSpace I x) := by
    change T2Space E
    infer_instance
  exact ((EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.equiv
    (normalBasis (I := I) g x) (Equiv.refl _)).toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.euclideanNormalFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.euclideanNormalFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.euclideanNormalFrame ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.euclideanNormalFrame

@[simp] theorem euclideanNormalFrame_single (g : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    euclideanNormalFrame g x (EuclideanSpace.single i 1) =
      normalBasis g x i := by
  rw [← EuclideanSpace.basisFun_apply]
  simp only [euclideanNormalFrame, LinearEquiv.coe_toContinuousLinearEquiv']
  exact Module.Basis.equiv_apply _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.euclideanNormalFrame_single then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.euclideanNormalFrame_single"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.euclideanNormalFrame_single ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.euclideanNormalFrame_single

theorem euclideanNormalFrame_inner (g : SmoothRiemannianMetric I M) (x : M)
    (v w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    g.inner x (euclideanNormalFrame g x v) (euclideanNormalFrame g x w) = _root_.Inner.inner ℝ v w := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let L := (euclideanNormalFrame (I := I) g x).toContinuousLinearMap
  let G : F →L[ℝ] F →L[ℝ] ℝ :=
    (ContinuousLinearMap.precomp ℝ L).comp ((g.inner x).comp L)
  have hG : G = (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) := by
    let b := (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis
    apply LinearMap.toLinearMap_injective
    apply b.ext
    intro i
    apply LinearMap.toLinearMap_injective
    apply b.ext
    intro j
    change g.inner x
      (euclideanNormalFrame g x (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ i))
      (euclideanNormalFrame g x (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ j)) =
      _root_.Inner.inner ℝ (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ i)
        (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ j)
    have hb (k : Fin (Module.finrank ℝ E)) :
        euclideanNormalFrame g x
          (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ k) = normalBasis g x k := by
      simpa only [EuclideanSpace.basisFun_apply] using euclideanNormalFrame_single g x k
    rw [hb i, hb j, normalBasis_inner]
    exact ((EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).inner_eq_ite i j).symm
  exact congrArg (fun B : F →L[ℝ] F →L[ℝ] ℝ => B v w) hG

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.euclideanNormalFrame_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.euclideanNormalFrame_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.euclideanNormalFrame_inner ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.euclideanNormalFrame_inner

theorem euclideanNormalFrame_sqrt (g : SmoothRiemannianMetric I M) (x : M)
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    Real.sqrt (g.inner x (euclideanNormalFrame g x v) (euclideanNormalFrame g x v)) = ‖v‖ := by
  rw [euclideanNormalFrame_inner, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg v)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.euclideanNormalFrame_sqrt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.euclideanNormalFrame_sqrt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.euclideanNormalFrame_sqrt ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.euclideanNormalFrame_sqrt

end Normed

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]


noncomputable def normalFrame (g : SmoothRiemannianMetric I M) (x : M) :
    E ≃L[Real] TangentSpace I x := by
  let _ : T2Space (TangentSpace I x) := by
    change T2Space E
    infer_instance
  exact
  ((stdOrthonormalBasis Real E).toBasis.equiv
    (normalBasis (I := I) g x)
    (Equiv.refl (Fin (Module.finrank Real E)))).toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame

@[simp] theorem normalFrame_basis (g : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank Real E)) :
    normalFrame (I := I) g x ((stdOrthonormalBasis Real E) i) =
      normalBasis (I := I) g x i := by
  simp only [normalFrame, LinearEquiv.coe_toContinuousLinearEquiv',     ]
  change ((stdOrthonormalBasis Real E).toBasis.equiv
      (normalBasis (I := I) g x) (Equiv.refl (Fin (Module.finrank Real E))))
        ((stdOrthonormalBasis Real E).toBasis i) = normalBasis (I := I) g x i
  exact Basis.equiv_apply _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_basis ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_basis

noncomputable def frameMetric (g : SmoothRiemannianMetric I M) (x : M) :
    E →L[Real] E →L[Real] Real :=
  let L := (normalFrame (I := I) g x).toContinuousLinearMap
  (ContinuousLinearMap.precomp Real L).comp ((g.inner x).comp L)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.frameMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.frameMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.frameMetric ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.frameMetric

theorem frameMetric_apply (g : SmoothRiemannianMetric I M) (x : M) (v w : E) :
    frameMetric (I := I) g x v w =
      g.inner x (normalFrame (I := I) g x v) (normalFrame (I := I) g x w) := by
  simp [frameMetric]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.frameMetric_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.frameMetric_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.frameMetric_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.frameMetric_apply

theorem frameMetric_eq (g : SmoothRiemannianMetric I M) (x : M) :
    frameMetric (I := I) g x = (innerSL Real : E →L[Real] E →L[Real] Real) := by
  classical
  let b := (stdOrthonormalBasis Real E).toBasis
  apply LinearMap.toLinearMap_injective
  apply b.ext
  intro i
  apply LinearMap.toLinearMap_injective
  apply b.ext
  intro j
  change frameMetric (I := I) g x (b i) (b j) =
    (innerSL Real : E →L[Real] E →L[Real] Real) (b i) (b j)
  dsimp only [b]
  change g.inner x
      (normalFrame (I := I) g x ((stdOrthonormalBasis Real E) i))
      (normalFrame (I := I) g x ((stdOrthonormalBasis Real E) j)) =
    Inner.inner Real ((stdOrthonormalBasis Real E) i)
      ((stdOrthonormalBasis Real E) j)
  rw [normalFrame_basis, normalFrame_basis, normalBasis_inner]
  exact ((stdOrthonormalBasis Real E).inner_eq_ite i j).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.frameMetric_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.frameMetric_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.frameMetric_eq ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.frameMetric_eq

theorem normalFrame_inner (g : SmoothRiemannianMetric I M) (x : M) (v w : E) :
    g.inner x (normalFrame (I := I) g x v) (normalFrame (I := I) g x w) =
      Inner.inner Real v w := by
  rw [← frameMetric_apply (I := I) g x, frameMetric_eq (I := I) g x]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_inner ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_inner

theorem normalFrame_normSq (g : SmoothRiemannianMetric I M) (x : M) (v : E) :
    g.inner x (normalFrame (I := I) g x v) (normalFrame (I := I) g x v) =
      ‖v‖ ^ 2 := by
  rw [normalFrame_inner, real_inner_self_eq_norm_sq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_normSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_normSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_normSq ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_normSq

theorem normalFrame_sqrt (g : SmoothRiemannianMetric I M) (x : M) (v : E) :
    Real.sqrt
        (g.inner x (normalFrame (I := I) g x v)
          (normalFrame (I := I) g x v)) =
      ‖v‖ := by
  rw [normalFrame_normSq, Real.sqrt_sq (norm_nonneg v)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_sqrt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_sqrt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_sqrt ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_sqrt

theorem normalFrame_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    (x : U) (v : E) :
    (normalFrame (g.restrictOpen U) x v : E) = (normalFrame g (x : M) v : E) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_restrictOpen ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.normalFrame_restrictOpen

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry
