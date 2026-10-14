import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletFormCompletion
import Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.FormBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.InnerProductSpace _root_.Manifold _root_.RealInnerProductSpace _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.I_half
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.I_half target :: scope.openDecls } }

private local instance smoothDualSeminormedAddCommGroup (q : SmoothRiemannianMetric (I_half n) M) :
    SeminormedAddCommGroup (SmoothScalarDirichlet q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (E := SmoothScalarDirichlet q) (F := ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothDualSeminormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothDualSeminormedAddCommGroup target :: scope.openDecls } }

private local instance smoothBilinearNorm (q : SmoothRiemannianMetric (I_half n) M) :
    Norm (SmoothScalarDirichlet q →L[ℝ] SmoothScalarDirichlet q →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ) (E := SmoothScalarDirichlet q) (F := SmoothScalarDirichlet q →L[ℝ] ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothBilinearNorm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothBilinearNorm target :: scope.openDecls } }

private local instance completedDualSeminormedAddCommGroup (q : SmoothRiemannianMetric (I_half n) M) :
    SeminormedAddCommGroup (H1ComplDirichlet q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (E := H1ComplDirichlet q) (F := ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.completedDualSeminormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.completedDualSeminormedAddCommGroup target :: scope.openDecls } }

private local instance completedBilinearNorm (q : SmoothRiemannianMetric (I_half n) M) :
    Norm (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ) (E := H1ComplDirichlet q) (F := H1ComplDirichlet q →L[ℝ] ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.completedBilinearNorm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.completedBilinearNorm target :: scope.openDecls } }

noncomputable def dirichletMassVariationSmooth
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (B : ℝ)
    (htrace : ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
        (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    SmoothScalarDirichlet q →L[ℝ] SmoothScalarDirichlet q →L[ℝ] ℝ := by
  refine LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun u v => dirichletMassVariation G.metric t u v)
      (dirichletMassVariation_add_left hG ht)
      (dirichletMassVariation_smul_left hG ht)
      (dirichletMassVariation_add_right hG ht)
      (dirichletMassVariation_smul_right hG ht))
    ((1 / 2) * _root_.Max.max B 0 * (Cv.toReal * Cg)) ?_
  intro u v
  rw [Real.norm_eq_abs]
  exact abs_dirichletMassVariation_le_of_metric_and_volume G.metric t B htrace
    hCg hequiv Cv hCv0 hCvtop hvol u v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationSmooth ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationSmooth

theorem dirichletMassVariationSmooth_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (B : ℝ)
    (htrace : ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
        (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : SmoothScalarDirichlet q) :
    dirichletMassVariationSmooth hG ht B htrace hCg hequiv
        Cv hCv0 hCvtop hvol u v =
      dirichletMassVariation G.metric t u v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationSmooth_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationSmooth_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationSmooth_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationSmooth_apply

theorem norm_dirichletMassVariationSmooth_le
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (B : ℝ)
    (htrace : ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
        (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ‖dirichletMassVariationSmooth hG ht B htrace hCg hequiv
      Cv hCv0 hCvtop hvol‖ ≤
        (1 / 2) * _root_.Max.max B 0 * (Cv.toReal * Cg) := by
  apply LinearMap.mkContinuous₂_norm_le
  exact mul_nonneg
    (mul_nonneg (by norm_num) (le_max_right B 0))
    (mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassVariationSmooth_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassVariationSmooth_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassVariationSmooth_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassVariationSmooth_le

noncomputable def dirichletMassVariationCompl
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (B : ℝ)
    (htrace : ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
        (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
  DifferentialGeometry.Analysis.bilinearFromCompletion (X := SmoothScalarDirichlet q)
    (dirichletMassVariationSmooth hG ht B htrace hCg hequiv
      Cv hCv0 hCvtop hvol)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationCompl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationCompl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationCompl ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationCompl

theorem dirichletMassVariationCompl_apply_smooth
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (B : ℝ)
    (htrace : ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
        (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : SmoothScalarDirichlet q) :
    dirichletMassVariationCompl hG ht B htrace hCg hequiv
        Cv hCv0 hCvtop hvol
        (smoothToH1ComplDirichlet q u) (smoothToH1ComplDirichlet q v) =
      dirichletMassVariation G.metric t u v := by
  change DifferentialGeometry.Analysis.bilinearFromCompletion
      (dirichletMassVariationSmooth hG ht B htrace hCg hequiv Cv hCv0 hCvtop hvol)
      (u : UniformSpace.Completion (SmoothScalarDirichlet q))
      (v : UniformSpace.Completion (SmoothScalarDirichlet q)) = _
  rw [DifferentialGeometry.Analysis.bilinearFromCompletion_apply_coe,
    dirichletMassVariationSmooth_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationCompl_apply_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationCompl_apply_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationCompl_apply_smooth ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationCompl_apply_smooth

theorem norm_dirichletMassVariationCompl_le
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (B : ℝ)
    (htrace : ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
        (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ‖dirichletMassVariationCompl hG ht B htrace hCg hequiv
      Cv hCv0 hCvtop hvol‖ ≤
        (1 / 2) * _root_.Max.max B 0 * (Cv.toReal * Cg) := by
  rw [dirichletMassVariationCompl]
  apply DifferentialGeometry.Analysis.norm_bilinearFromCompletion_le
  · exact mul_nonneg
      (mul_nonneg (by norm_num) (le_max_right B 0))
      (mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg))
  · intro u v
    rw [dirichletMassVariationSmooth_apply, Real.norm_eq_abs]
    exact abs_dirichletMassVariation_le_of_metric_and_volume G.metric t B htrace
      hCg hequiv Cv hCv0 hCvtop hvol u v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassVariationCompl_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassVariationCompl_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassVariationCompl_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassVariationCompl_le

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
