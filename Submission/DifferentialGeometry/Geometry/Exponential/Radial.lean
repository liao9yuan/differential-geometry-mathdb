import Submission.DifferentialGeometry.Geometry.Geodesic.Maximal.Rescaling
import Submission.DifferentialGeometry.Geometry.Geodesic.Flow.CrossVectorFieldReduction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem smul_mem_expDomain_iff
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p} {c : ℝ} :
    c • v ∈ expDomain g p ↔ c ∈ maximalGeodesicInterval g p v := by
  change (1 : ℝ) ∈ maximalGeodesicInterval g p (c • v) ↔
    c ∈ maximalGeodesicInterval g p v
  simpa only [mul_one] using mem_maximalGeodesicInterval_smul_iff (g := g) (p := p)
    (v := v) (c := c) (t := 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.smul_mem_expDomain_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.smul_mem_expDomain_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.smul_mem_expDomain_iff ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.smul_mem_expDomain_iff

theorem expMap_smul [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (c : ℝ) :
    expMap g p (c • v) = maximalGeodesic g p v c := by
  change maximalGeodesic g p (c • v) 1 = maximalGeodesic g p v c
  simpa only [mul_one] using maximalGeodesic_smul g p v c 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.expMap_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.expMap_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.expMap_smul ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.expMap_smul

theorem smul_mem_expDomain
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p} {c : ℝ}
    (hv : v ∈ expDomain g p) (hc : c ∈ _root_.Set.Icc (0 : ℝ) 1) :
    c • v ∈ expDomain g p := by
  obtain ⟨γ, J, hJ, hconn, h0, h1, hγ⟩ := hv
  exact smul_mem_expDomain_iff.mpr
    ⟨γ, J, hJ, hconn, h0, hconn.ordConnected.out h0 h1 hc, hγ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.smul_mem_expDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.smul_mem_expDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.smul_mem_expDomain ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.smul_mem_expDomain

theorem starConvex_expDomain (g : SmoothRiemannianMetric I M) (p : M) :
    StarConvex ℝ (0 : TangentSpace I p) (expDomain g p) := by
  rw [starConvex_zero_iff]
  exact fun _ hv _ hc0 hc1 => smul_mem_expDomain hv ⟨hc0, hc1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.starConvex_expDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.starConvex_expDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.starConvex_expDomain ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.starConvex_expDomain

theorem exists_isGeodesicOnWithInitial_eqOn_expMap [T2Space (TangentBundle I M)]
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p} {r : ℝ}
    (hr : r • v ∈ expDomain g p) :
    ∃ (γ : ℝ → M) (J : Set ℝ), IsOpen J ∧ IsPreconnected J ∧ _root_.Set.uIcc 0 r ⊆ J ∧
      IsGeodesicOnWithInitial g γ J p v ∧ _root_.Set.EqOn γ (fun t => expMap g p (t • v)) J := by
  obtain ⟨γ, J, hJ, hconn, h0, hrJ, hγ⟩ := smul_mem_expDomain_iff.mp hr
  have hsub : _root_.Set.uIcc 0 r ⊆ J := hconn.ordConnected.uIcc_subset h0 hrJ
  refine ⟨γ, J, hJ, hconn, hsub, hγ, ?_⟩
  intro t ht
  exact (maximalGeodesic_eqOn g hJ hconn h0 hγ ht).symm.trans
    (expMap_smul g p v t).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.exists_isGeodesicOnWithInitial_eqOn_expMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.exists_isGeodesicOnWithInitial_eqOn_expMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.exists_isGeodesicOnWithInitial_eqOn_expMap ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.exists_isGeodesicOnWithInitial_eqOn_expMap

theorem hasGeodesicEquationAt_expMap_smul [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) {t : ℝ}
    (ht : t • v ∈ expDomain g p) :
    HasGeodesicEquationAt g (fun s : ℝ => expMap g p (s • v)) t := by
  obtain ⟨γ, J, hJ, _, hsub, hγ, heq⟩ := exists_isGeodesicOnWithInitial_eqOn_expMap ht
  have hJt : J ∈ 𝓝 t := hJ.mem_nhds (hsub _root_.Set.right_mem_uIcc)
  have hEq : (fun s => expMap g p (s • v)) =ᶠ[𝓝 t] γ :=
    _root_.Filter.eventuallyEq_of_mem hJt (fun s hs => (heq hs).symm)
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at hEq.eq_of_nhds hEq
    ((hγ.isGeodesicAt hJt).hasGeodesicEquationAt g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.hasGeodesicEquationAt_expMap_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.hasGeodesicEquationAt_expMap_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.hasGeodesicEquationAt_expMap_smul ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.hasGeodesicEquationAt_expMap_smul

end DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def radialCurve (g : SmoothRiemannianMetric I M) (p : M)
    (x : E) (t : ℝ) : M :=
  expMap (I := I) g p (show TangentSpace I p from (t • x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialCurve ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialCurve

@[simp] lemma radialCurve_apply
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) (t : ℝ) :
    radialCurve (I := I) g p x t =
      expMap (I := I) g p (show TangentSpace I p from (t • x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialCurve_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialCurve_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialCurve_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialCurve_apply

lemma radialCurve_one
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    radialCurve (I := I) g p x 1 =
      expMap (I := I) g p (show TangentSpace I p from x) := by
  simp [radialCurve]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialCurve_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialCurve_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialCurve_one ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialCurve_one

lemma radialCurve_zero [I.Boundaryless] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    radialCurve (I := I) g p x 0 = p := by
  unfold radialCurve
  rw [zero_smul]
  exact expMap_zero (I := I) g p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialCurve_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialCurve_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialCurve_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialCurve_zero

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
