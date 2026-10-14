import Submission.DifferentialGeometry.Topology.Manifold.ModelChangeRoundtrip
import Submission.DifferentialGeometry.Geometry.Metric.ModelChange
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import Submission.DifferentialGeometry.Bundle.FiberBundleHausdorff
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.ModelChange

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

universe u uE uF uH

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2

def PointedRiemannianManifold.transContinuousLinearEquiv
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) (e : E ≃L[ℝ] F) :
    PointedRiemannianManifold.{u, uF, uH} (I := I.transContinuousLinearEquiv e) where
  M := P.M
  topology := P.topology
  charted := P.charted
  smooth := inferInstance
  sigmaCompact := P.sigmaCompact
  t2 := P.t2
  t2TangentBundle := inferInstance
  basepoint := P.basepoint
  metric := P.metric.transContinuousLinearEquiv e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv

@[simp]
theorem PointedRiemannianManifold.transContinuousLinearEquiv_carrier
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) (e : E ≃L[ℝ] F) :
    (P.transContinuousLinearEquiv e).M = P.M := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_carrier ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_carrier

@[simp]
theorem PointedRiemannianManifold.transContinuousLinearEquiv_basepoint
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) (e : E ≃L[ℝ] F) :
    (P.transContinuousLinearEquiv e).basepoint = P.basepoint := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_basepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_basepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_basepoint ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_basepoint

@[simp]
theorem PointedRiemannianManifold.transContinuousLinearEquiv_metric
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) (e : E ≃L[ℝ] F) :
    (P.transContinuousLinearEquiv e).metric = P.metric.transContinuousLinearEquiv e := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_metric ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_metric

def PointedRiemannianSeq.transContinuousLinearEquiv
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) (e : E ≃L[ℝ] F) :
    PointedRiemannianSeq.{u, uF, uH} (I := I.transContinuousLinearEquiv e) where
  obj k := (X.obj k).transContinuousLinearEquiv e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.transContinuousLinearEquiv ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.transContinuousLinearEquiv

@[simp]
theorem PointedRiemannianSeq.transContinuousLinearEquiv_obj
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) (e : E ≃L[ℝ] F) (k : ℕ) :
    (X.transContinuousLinearEquiv e).obj k = (X.obj k).transContinuousLinearEquiv e := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.transContinuousLinearEquiv_obj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.transContinuousLinearEquiv_obj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.transContinuousLinearEquiv_obj ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.transContinuousLinearEquiv_obj

def PointedRiemannianConvergenceMaps.transContinuousLinearEquiv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps X P subseq) (e : E ≃L[ℝ] F) :
    PointedRiemannianConvergenceMaps (X.transContinuousLinearEquiv e)
      (P.transContinuousLinearEquiv e) subseq where
  partialDiffeomorph k :=
    { toPartialEquiv := (Phi.partialDiffeomorph k).toPartialEquiv
      open_source := (Phi.partialDiffeomorph k).open_source
      open_target := (Phi.partialDiffeomorph k).open_target
      contMDiffOn_toFun :=
        (e.contMDiffOn_transContinuousLinearEquiv_left).mpr
          ((e.contMDiffOn_transContinuousLinearEquiv_right).mpr
            (Phi.partialDiffeomorph k).contMDiffOn_toFun)
      contMDiffOn_invFun :=
        (e.contMDiffOn_transContinuousLinearEquiv_left).mpr
          ((e.contMDiffOn_transContinuousLinearEquiv_right).mpr
            (Phi.partialDiffeomorph k).contMDiffOn_invFun) }
  source_exhausts := Phi.source_exhausts
  base_mem := Phi.base_mem
  basepoint_map := Phi.basepoint_map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv

@[simp]
theorem PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_partialEquiv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps X P subseq) (e : E ≃L[ℝ] F) (k : ℕ) :
    ((Phi.transContinuousLinearEquiv e).partialDiffeomorph k).toPartialEquiv =
      (Phi.partialDiffeomorph k).toPartialEquiv := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_partialEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_partialEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_partialEquiv ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_partialEquiv

@[simp]
theorem PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps X P subseq) (e : E ≃L[ℝ] F) (k : ℕ) :
    (Phi.transContinuousLinearEquiv e).source k = Phi.source k := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_source ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_source

@[simp]
theorem PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_target
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps X P subseq) (e : E ≃L[ℝ] F) (k : ℕ) :
    (Phi.transContinuousLinearEquiv e).target k = Phi.target k := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_target ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_target

@[simp]
theorem PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_map
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps X P subseq) (e : E ≃L[ℝ] F) (k : ℕ) :
    (Phi.transContinuousLinearEquiv e).map k = Phi.map k := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_map ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_map

@[simp]
theorem PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_symm
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps X P subseq) (e : E ≃L[ℝ] F) (k : ℕ) :
    (((Phi.transContinuousLinearEquiv e).partialDiffeomorph k).symm :
      (X.obj (subseq k)).M → P.M) = (Phi.partialDiffeomorph k).symm := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_symm ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_symm

section InverseManifold

variable [FiniteDimensional ℝ E]

def PointedRiemannianManifold.ofTransContinuousLinearEquiv
    (e : E ≃L[ℝ] F) (P : PointedRiemannianManifold.{u, uF, uH} (I.transContinuousLinearEquiv e)) :
    PointedRiemannianManifold.{u, uE, uH} I := by
  let _ : IsManifold I ∞ P.M :=
    (ContinuousLinearEquiv.isManifold_transContinuousLinearEquiv_iff (I := I) (M := P.M) (n := ∞) e).mp P.smooth
  exact {
    M := P.M
    topology := P.topology
    charted := P.charted
    smooth := inferInstance
    t2 := P.t2
    sigmaCompact := P.sigmaCompact
    t2TangentBundle := inferInstance
    basepoint := P.basepoint
    metric := Diffeomorph.pullbackMetricCross P.metric
      (ContinuousLinearEquiv.toTransContinuousLinearEquiv I P.M e) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.ofTransContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.ofTransContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.ofTransContinuousLinearEquiv ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.ofTransContinuousLinearEquiv

theorem PointedRiemannianManifold.transContinuousLinearEquiv_ofTransContinuousLinearEquiv
    (e : E ≃L[ℝ] F) (P : PointedRiemannianManifold.{u, uF, uH} (I.transContinuousLinearEquiv e)) :
    (P.ofTransContinuousLinearEquiv e).transContinuousLinearEquiv e = P := by
  rcases P with @⟨M, topology, charted, smooth, sigmaCompact, t2, t2Tangent, base, g⟩
  let _ := topology
  let _ := charted
  let _ := smooth
  let _ := sigmaCompact
  let _ := t2
  let _ : IsManifold I ∞ M :=
    (ContinuousLinearEquiv.isManifold_transContinuousLinearEquiv_iff (I := I) (M := M) (n := ∞) e).mp smooth
  have hg : (Diffeomorph.pullbackMetricCross g
      (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e)).transContinuousLinearEquiv e = g := by
    rw [SmoothRiemannianMetric.transContinuousLinearEquiv, Diffeomorph.pullbackMetricCross_trans]
    have heq : (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e).symm.trans
        (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e) =
          _root_.Diffeomorph.refl (I.transContinuousLinearEquiv e) M ∞ := by ext x; rfl
    rw [heq, Diffeomorph.pullbackMetricCross_refl]
  dsimp only [PointedRiemannianManifold.ofTransContinuousLinearEquiv,
    PointedRiemannianManifold.transContinuousLinearEquiv]
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_ofTransContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_ofTransContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_ofTransContinuousLinearEquiv ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_ofTransContinuousLinearEquiv


theorem PointedRiemannianManifold.ofTransContinuousLinearEquiv_transContinuousLinearEquiv
    (P : PointedRiemannianManifold.{u, uE, uH} I) (e : E ≃L[ℝ] F) :
    (P.transContinuousLinearEquiv e).ofTransContinuousLinearEquiv e = P := by
  rcases P with @⟨M, topology, charted, smooth, sigmaCompact, t2, t2Tangent, base, g⟩
  let _ := topology
  let _ := charted
  let _ := smooth
  let _ := sigmaCompact
  let _ := t2
  have hg := g.pullback_transContinuousLinearEquiv e
  dsimp only [PointedRiemannianManifold.ofTransContinuousLinearEquiv,
    PointedRiemannianManifold.transContinuousLinearEquiv]
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.ofTransContinuousLinearEquiv_transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.ofTransContinuousLinearEquiv_transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.ofTransContinuousLinearEquiv_transContinuousLinearEquiv ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.ofTransContinuousLinearEquiv_transContinuousLinearEquiv

theorem PointedRiemannianManifold.transContinuousLinearEquiv_surjective
    (e : E ≃L[ℝ] F) :
    Function.Surjective (fun P : PointedRiemannianManifold.{u, uE, uH} I =>
      P.transContinuousLinearEquiv e) :=
  fun P => ⟨P.ofTransContinuousLinearEquiv e, P.transContinuousLinearEquiv_ofTransContinuousLinearEquiv e⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_surjective ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.transContinuousLinearEquiv_surjective


end InverseManifold

section InverseMaps

variable {X : PointedRiemannianSeq.{u, uE, uH} I}
  {P : PointedRiemannianManifold.{u, uE, uH} I} {phi : ℕ → ℕ}

def PointedRiemannianConvergenceMaps.ofTransContinuousLinearEquiv (e : E ≃L[ℝ] F)
    (Phi : PointedRiemannianConvergenceMaps (X.transContinuousLinearEquiv e)
      (P.transContinuousLinearEquiv e) phi) : PointedRiemannianConvergenceMaps X P phi where
  partialDiffeomorph k := (Phi.partialDiffeomorph k).ofTransContinuousLinearEquiv e e
  source_exhausts := Phi.source_exhausts
  base_mem := Phi.base_mem
  basepoint_map := Phi.basepoint_map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofTransContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofTransContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofTransContinuousLinearEquiv ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofTransContinuousLinearEquiv

@[simp] theorem PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_ofTransContinuousLinearEquiv
    (e : E ≃L[ℝ] F)
    (Phi : PointedRiemannianConvergenceMaps (X.transContinuousLinearEquiv e)
      (P.transContinuousLinearEquiv e) phi) :
    (Phi.ofTransContinuousLinearEquiv e).transContinuousLinearEquiv e = Phi := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_ofTransContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_ofTransContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_ofTransContinuousLinearEquiv ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_ofTransContinuousLinearEquiv

@[simp] theorem PointedRiemannianConvergenceMaps.ofTransContinuousLinearEquiv_transContinuousLinearEquiv
    (Phi : PointedRiemannianConvergenceMaps X P phi) (e : E ≃L[ℝ] F) :
    (Phi.transContinuousLinearEquiv e).ofTransContinuousLinearEquiv e = Phi := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofTransContinuousLinearEquiv_transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofTransContinuousLinearEquiv_transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofTransContinuousLinearEquiv_transContinuousLinearEquiv ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofTransContinuousLinearEquiv_transContinuousLinearEquiv


end InverseMaps

end DifferentialGeometry.CheegerGromovCompactness
