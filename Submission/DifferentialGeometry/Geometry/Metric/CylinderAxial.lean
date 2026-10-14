import Submission.DifferentialGeometry.Geometry.Metric.Cylinder
import Submission.DifferentialGeometry.Geometry.Metric.DerivativeENorm
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

def cylinderAxialDiffeomorph (a σ : ℝ) (hσ : σ ^ 2 = 1) :
    (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ), I.prod 𝓘(ℝ)⟯ (M × ℝ) where
  toFun x := (x.1, a + σ * x.2)
  invFun x := (x.1, σ * (x.2 - a))
  left_inv x := by
    refine Prod.ext (by rfl) ?_
    change σ * (a + σ * x.2 - a) = x.2
    calc
      _ = σ ^ 2 * x.2 := by ring
      _ = x.2 := by rw [hσ, one_mul]
  right_inv x := by
    refine Prod.ext (by rfl) ?_
    change a + σ * (σ * (x.2 - a)) = x.2
    calc
      _ = a + σ ^ 2 * (x.2 - a) := by ring
      _ = x.2 := by rw [hσ]; ring
  contMDiff_toFun :=
    contMDiff_fst.prodMk (contMDiff_const.add (contMDiff_const.mul contMDiff_snd))
  contMDiff_invFun :=
    contMDiff_fst.prodMk (contMDiff_const.mul (contMDiff_snd.sub contMDiff_const))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph ``Submission.DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph

@[simp] theorem cylinderAxialDiffeomorph_apply (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (x : M × ℝ) :
    cylinderAxialDiffeomorph (I := I) a σ hσ x = (x.1, a + σ * x.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph_apply ``Submission.DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph_apply

@[simp] theorem cylinderAxialDiffeomorph_symm_apply (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (x : M × ℝ) :
    (cylinderAxialDiffeomorph (I := I) a σ hσ).symm x = (x.1, σ * (x.2 - a)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph_symm_apply

theorem cylinderAxialDiffeomorph_mfderiv (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (x : M × ℝ) (v : TangentSpace (I.prod 𝓘(ℝ)) x) :
    mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
      (cylinderAxialDiffeomorph (I := I) a σ hσ) x v = (v.1, σ * v.2) := by
  change mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
    (Prod.map (id : M → M) (fun z : ℝ => a + σ * z)) x v = _
  have hd : HasDerivAt (fun z : ℝ => a + σ * z) σ x.2 := by
    simpa using ((hasDerivAt_id x.2).const_mul σ).const_add a
  rw [mfderiv_prodMap mdifferentiableAt_id hd.differentiableAt.mdifferentiableAt,
    mfderiv_id, mfderiv_eq_fderiv, hd.hasFDerivAt.fderiv]
  change (v.1, v.2 * σ) = (v.1, σ * v.2)
  rw [mul_comm v.2 σ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph_mfderiv ``Submission.DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph_mfderiv

def cylinderAxialImage (a σ : ℝ) (hσ : σ ^ 2 = 1) (U : _root_.TopologicalSpace.Opens (M × ℝ)) :
    Opens (M × ℝ) :=
  ⟨cylinderAxialDiffeomorph (I := I) a σ hσ '' (U : Set (M × ℝ)),
    (cylinderAxialDiffeomorph (I := I) a σ hσ).toHomeomorph.isOpenMap _ U.isOpen⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.cylinderAxialImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.cylinderAxialImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.cylinderAxialImage ``Submission.DifferentialGeometry.Geometry.Metric.cylinderAxialImage

@[simp] theorem mem_cylinderAxialImage (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (U : _root_.TopologicalSpace.Opens (M × ℝ)) (x : M × ℝ) :
    x ∈ cylinderAxialImage (I := I) a σ hσ U ↔ (x.1, σ * (x.2 - a)) ∈ U := by
  change x ∈ cylinderAxialDiffeomorph (I := I) a σ hσ '' (U : Set (M × ℝ)) ↔ _
  rw [Diffeomorph.image_eq_preimage_symm]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.mem_cylinderAxialImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.mem_cylinderAxialImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.mem_cylinderAxialImage ``Submission.DifferentialGeometry.Geometry.Metric.mem_cylinderAxialImage

def cylinderAxialRestrict (a σ : ℝ) (hσ : σ ^ 2 = 1) (U : _root_.TopologicalSpace.Opens (M × ℝ)) :
    U ≃ₘ⟮I.prod 𝓘(ℝ), I.prod 𝓘(ℝ)⟯ cylinderAxialImage (I := I) a σ hσ U :=
  PartialDiffeomorph.toOpensDiffeo
    (cylinderAxialDiffeomorph (I := I) a σ hσ).toPartialDiffeomorph
    (fun _ _ => _root_.Set.mem_univ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.cylinderAxialRestrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.cylinderAxialRestrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.cylinderAxialRestrict ``Submission.DifferentialGeometry.Geometry.Metric.cylinderAxialRestrict

@[simp] theorem cylinderAxialRestrict_apply (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (U : _root_.TopologicalSpace.Opens (M × ℝ)) (x : U) :
    (cylinderAxialRestrict (I := I) a σ hσ U x : M × ℝ) = (x.val.1, a + σ * x.val.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.cylinderAxialRestrict_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.cylinderAxialRestrict_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.cylinderAxialRestrict_apply ``Submission.DifferentialGeometry.Geometry.Metric.cylinderAxialRestrict_apply

@[simp] theorem cylinderAxialRestrict_symm_apply (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (U : _root_.TopologicalSpace.Opens (M × ℝ)) (x : cylinderAxialImage (I := I) a σ hσ U) :
    ((cylinderAxialRestrict (I := I) a σ hσ U).symm x : M × ℝ) =
      (x.val.1, σ * (x.val.2 - a)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.cylinderAxialRestrict_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.cylinderAxialRestrict_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.cylinderAxialRestrict_symm_apply ``Submission.DifferentialGeometry.Geometry.Metric.cylinderAxialRestrict_symm_apply

theorem cylinderAxialRestrict_mfderiv (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (U : _root_.TopologicalSpace.Opens (M × ℝ)) (x : U) (v : TangentSpace (I.prod 𝓘(ℝ)) x) :
    mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
      (cylinderAxialRestrict (I := I) a σ hσ U) x v = (v.1, σ * v.2) :=
  (PartialDiffeomorph.mfderiv_toOpensDiffeo
    (cylinderAxialDiffeomorph (I := I) a σ hσ).toPartialDiffeomorph
    (fun _ _ => _root_.Set.mem_univ _) x v).trans
      (cylinderAxialDiffeomorph_mfderiv a σ hσ (x : M × ℝ) v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.cylinderAxialRestrict_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.cylinderAxialRestrict_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.cylinderAxialRestrict_mfderiv ``Submission.DifferentialGeometry.Geometry.Metric.cylinderAxialRestrict_mfderiv

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M]

theorem pullback_cylinderMetric_cylinderAxialDiffeomorph
    (g : SmoothRiemannianMetric I M) (a σ : ℝ) (hσ : σ ^ 2 = 1) :
    Diffeomorph.pullbackMetric (cylinderMetric g) (cylinderAxialDiffeomorph (I := I) a σ hσ) =
      cylinderMetric g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have heq : (σ * v.2) * (σ * w.2) = v.2 * w.2 := by
    calc
      _ = σ ^ 2 * (v.2 * w.2) := by ring
      _ = _ := by rw [hσ, one_mul]
  rw [Diffeomorph.pullbackMetric_inner]
  calc
    _ = g.inner (cylinderAxialDiffeomorph (I := I) a σ hσ x).1
        (mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
          (cylinderAxialDiffeomorph (I := I) a σ hσ) x v).1
        (mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
          (cylinderAxialDiffeomorph (I := I) a σ hσ) x w).1 +
        (mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
          (cylinderAxialDiffeomorph (I := I) a σ hσ) x v).2 *
        (mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
          (cylinderAxialDiffeomorph (I := I) a σ hσ) x w).2 :=
      cylinderMetric_inner g _ _ _
    _ = g.inner x.1 v.1 w.1 + (σ * v.2) * (σ * w.2) := by
      rw [cylinderAxialDiffeomorph_mfderiv, cylinderAxialDiffeomorph_mfderiv]
      rfl
    _ = g.inner x.1 v.1 w.1 + v.2 * w.2 := by rw [heq]
    _ = (cylinderMetric g).inner x v w := (cylinderMetric_inner g x v w).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.pullback_cylinderMetric_cylinderAxialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.pullback_cylinderMetric_cylinderAxialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.pullback_cylinderMetric_cylinderAxialDiffeomorph ``Submission.DifferentialGeometry.Geometry.Metric.pullback_cylinderMetric_cylinderAxialDiffeomorph

theorem metricDerivNorm_pullback_cylinderAxialDiffeomorph
    (g : SmoothRiemannianMetric I M)
    (gk gInf : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (M × ℝ))
    (a σ : ℝ) (hσ : σ ^ 2 = 1) (j : ℕ) (x : M × ℝ) :
    metricDerivNorm j
      (Diffeomorph.pullbackMetric gk (cylinderAxialDiffeomorph (I := I) a σ hσ))
      (Diffeomorph.pullbackMetric gInf (cylinderAxialDiffeomorph (I := I) a σ hσ))
      (cylinderMetric g) x =
    metricDerivNorm j gk gInf (cylinderMetric g) (cylinderAxialDiffeomorph (I := I) a σ hσ x) := by
  simpa only [pullback_cylinderMetric_cylinderAxialDiffeomorph] using
    metricDerivNorm_pullback gk gInf (cylinderMetric g) (cylinderAxialDiffeomorph (I := I) a σ hσ) j x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricDerivNorm_pullback_cylinderAxialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricDerivNorm_pullback_cylinderAxialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricDerivNorm_pullback_cylinderAxialDiffeomorph ``Submission.DifferentialGeometry.Geometry.Metric.metricDerivNorm_pullback_cylinderAxialDiffeomorph

theorem metricDerivENormSupOn_pullback_cylinderAxialDiffeomorph
    (g : SmoothRiemannianMetric I M)
    (gk gInf : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (M × ℝ))
    (a σ : ℝ) (hσ : σ ^ 2 = 1) (K : Set (M × ℝ)) (p : ℕ) :
    metricDerivENormSupOn K p
      (Diffeomorph.pullbackMetric gk (cylinderAxialDiffeomorph (I := I) a σ hσ))
      (Diffeomorph.pullbackMetric gInf (cylinderAxialDiffeomorph (I := I) a σ hσ))
      (cylinderMetric g) =
    metricDerivENormSupOn (cylinderAxialDiffeomorph (I := I) a σ hσ '' K) p
      gk gInf (cylinderMetric g) := by
  simp only [metricDerivENormSupOn, metricDerivNorm_pullback_cylinderAxialDiffeomorph, iSup_image]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_pullback_cylinderAxialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_pullback_cylinderAxialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_pullback_cylinderAxialDiffeomorph ``Submission.DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_pullback_cylinderAxialDiffeomorph

theorem pullback_cylinderMetric_cylinderAxialRestrict
    (g : SmoothRiemannianMetric I M) (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (U : _root_.TopologicalSpace.Opens (M × ℝ)) :
    Diffeomorph.pullbackMetric
      ((cylinderMetric g).restrictOpen (cylinderAxialImage (I := I) a σ hσ U))
      (cylinderAxialRestrict (I := I) a σ hσ U) = (cylinderMetric g).restrictOpen U := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hglobal := congrArg
    (fun k : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (M × ℝ) => k.inner (x : M × ℝ) v w)
    (pullback_cylinderMetric_cylinderAxialDiffeomorph g a σ hσ)
  have hambient := (Diffeomorph.pullbackMetric_inner (cylinderMetric g)
    (cylinderAxialDiffeomorph (I := I) a σ hσ) (x : M × ℝ) v w).symm.trans hglobal
  rw [Diffeomorph.pullbackMetric_inner]
  change (cylinderMetric g).inner (cylinderAxialDiffeomorph (I := I) a σ hσ (x : M × ℝ))
    (mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (cylinderAxialRestrict (I := I) a σ hσ U) x v)
    (mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (cylinderAxialRestrict (I := I) a σ hσ U) x w) =
    (cylinderMetric g).inner (x : M × ℝ) v w
  have hdv : mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
      (cylinderAxialRestrict (I := I) a σ hσ U) x v =
      mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
        (cylinderAxialDiffeomorph (I := I) a σ hσ) (x : M × ℝ) v :=
    PartialDiffeomorph.mfderiv_toOpensDiffeo
      (cylinderAxialDiffeomorph (I := I) a σ hσ).toPartialDiffeomorph
      (fun _ _ => _root_.Set.mem_univ _) x v
  have hdw : mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
      (cylinderAxialRestrict (I := I) a σ hσ U) x w =
      mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
        (cylinderAxialDiffeomorph (I := I) a σ hσ) (x : M × ℝ) w :=
    PartialDiffeomorph.mfderiv_toOpensDiffeo
      (cylinderAxialDiffeomorph (I := I) a σ hσ).toPartialDiffeomorph
      (fun _ _ => _root_.Set.mem_univ _) x w
  rw [hdv, hdw]
  exact hambient

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.pullback_cylinderMetric_cylinderAxialRestrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.pullback_cylinderMetric_cylinderAxialRestrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.pullback_cylinderMetric_cylinderAxialRestrict ``Submission.DifferentialGeometry.Geometry.Metric.pullback_cylinderMetric_cylinderAxialRestrict

theorem metricDerivNorm_pullback_cylinderAxialRestrict
    (g : SmoothRiemannianMetric I M) (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (U : _root_.TopologicalSpace.Opens (M × ℝ))
    (gk gInf : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (cylinderAxialImage (I := I) a σ hσ U))
    (j : ℕ) (x : U) :
    metricDerivNorm j
      (Diffeomorph.pullbackMetric gk (cylinderAxialRestrict (I := I) a σ hσ U))
      (Diffeomorph.pullbackMetric gInf (cylinderAxialRestrict (I := I) a σ hσ U))
      ((cylinderMetric g).restrictOpen U) x =
    metricDerivNorm j gk gInf
      ((cylinderMetric g).restrictOpen (cylinderAxialImage (I := I) a σ hσ U))
      (cylinderAxialRestrict (I := I) a σ hσ U x) := by
  simpa only [pullback_cylinderMetric_cylinderAxialRestrict] using
    metricDerivNorm_pullback gk gInf
      ((cylinderMetric g).restrictOpen (cylinderAxialImage (I := I) a σ hσ U))
      (cylinderAxialRestrict (I := I) a σ hσ U) j x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricDerivNorm_pullback_cylinderAxialRestrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricDerivNorm_pullback_cylinderAxialRestrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricDerivNorm_pullback_cylinderAxialRestrict ``Submission.DifferentialGeometry.Geometry.Metric.metricDerivNorm_pullback_cylinderAxialRestrict

theorem metricDerivENormSupOn_pullback_cylinderAxialRestrict
    (g : SmoothRiemannianMetric I M) (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (U : _root_.TopologicalSpace.Opens (M × ℝ))
    (gk gInf : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (cylinderAxialImage (I := I) a σ hσ U))
    (K : Set U) (p : ℕ) :
    metricDerivENormSupOn K p
      (Diffeomorph.pullbackMetric gk (cylinderAxialRestrict (I := I) a σ hσ U))
      (Diffeomorph.pullbackMetric gInf (cylinderAxialRestrict (I := I) a σ hσ U))
      ((cylinderMetric g).restrictOpen U) =
    metricDerivENormSupOn (cylinderAxialRestrict (I := I) a σ hσ U '' K) p gk gInf
      ((cylinderMetric g).restrictOpen (cylinderAxialImage (I := I) a σ hσ U)) := by
  simp only [metricDerivENormSupOn, metricDerivNorm_pullback_cylinderAxialRestrict, iSup_image]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_pullback_cylinderAxialRestrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_pullback_cylinderAxialRestrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_pullback_cylinderAxialRestrict ``Submission.DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_pullback_cylinderAxialRestrict

end DifferentialGeometry.Geometry.Metric
