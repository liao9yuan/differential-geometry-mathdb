import Submission.DifferentialGeometry.Analysis.DenseExtension
import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletFormBounds

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

noncomputable def dirichletMassLp
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (Cv : ℝ≥0∞) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q) →L[ℝ] ℝ :=
  let L := Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := 2) hCvtop hvol
  (innerSL ℝ).bilinearComp L L

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp

theorem dirichletMassLp_apply_eq_integral
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (Cv : ℝ≥0∞) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q)) :
    dirichletMassLp h Cv hCvtop hvol u v =
      ∫ x, u x * v x ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h) := by
  rw [dirichletMassLp, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply,
    L2.inner_def]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hCvtop hvol u,
    Lp.coeFn_LpToLpOfMeasureLeSMul hCvtop hvol v] with x hu hv
  rw [hu, hv, Real.inner_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp_apply_eq_integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp_apply_eq_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp_apply_eq_integral ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp_apply_eq_integral

theorem dirichletMassLp_apply_smooth
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (Cv : ℝ≥0∞) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : SmoothScalarDirichlet q) :
    dirichletMassLp h Cv hCvtop hvol
        (smoothToLpDirichlet q u) (smoothToLpDirichlet q v) =
      dirichletMass h u v := by
  rw [dirichletMassLp_apply_eq_integral]
  apply _root_.MeasureTheory.integral_congr_ae
  have hac : riemannianVolumeMeasure (I := I_half n) (M := M) h ≪
      riemannianVolumeMeasure (I := I_half n) (M := M) q :=
    Measure.absolutelyContinuous_of_le_smul hvol
  have hu : (smoothToLpDirichlet q u : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I_half n) (M := M) q] u.toFun :=
    MemLp.coeFn_toLp u.memLp_two
  have hv : (smoothToLpDirichlet q v : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I_half n) (M := M) q] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  filter_upwards [hac.ae_eq hu, hac.ae_eq hv] with x hux hvx
  rw [hux, hvx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp_apply_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp_apply_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp_apply_smooth ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp_apply_smooth

theorem dirichletMassLp_self_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    (Cv : ℝ≥0∞) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q)) :
    dirichletMassLp q Cv hCvtop hvol u v = _root_.Inner.inner ℝ u v := by
  let L := Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := 2) hCvtop hvol
  change _root_.Inner.inner ℝ (L u) (L v) = _root_.Inner.inner ℝ u v
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hCvtop hvol u,
    Lp.coeFn_LpToLpOfMeasureLeSMul hCvtop hvol v] with x hu hv
  rw [hu, hv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp_self_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp_self_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp_self_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp_self_apply

theorem dirichletMassLp_self_riesz_eq_resolventDirichlet
    {q : SmoothRiemannianMetric (I_half n) M}
    (Cv : ℝ≥0∞) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q)) :
    (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm
        ((dirichletMassLp q Cv hCvtop hvol u).comp
          (H1ComplDirichletToLp q)) =
      resolventDirichlet q u := by
  apply ext_inner_right ℝ
  intro v
  rw [InnerProductSpace.toDual_symm_apply,
    ContinuousLinearMap.comp_apply,
    dirichletMassLp_self_apply,
    resolventDirichlet_inner_eq_lpFunctional,
    real_inner_comm u]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp_self_riesz_eq_resolventDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp_self_riesz_eq_resolventDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp_self_riesz_eq_resolventDirichlet ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassLp_self_riesz_eq_resolventDirichlet

private noncomputable def dirichletExtend
    (q : SmoothRiemannianMetric (I_half n) M)
    (F : SmoothScalarDirichlet q →L[ℝ] SmoothScalarDirichlet q →L[ℝ] ℝ) :
    H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
  DifferentialGeometry.Analysis.bilinearFromCompletion
    (X := SmoothScalarDirichlet q) F

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletExtend
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletExtend target :: scope.openDecls } }

private theorem dirichletExtend_apply_smooth
    (q : SmoothRiemannianMetric (I_half n) M)
    (F : SmoothScalarDirichlet q →L[ℝ] SmoothScalarDirichlet q →L[ℝ] ℝ)
    (u v : SmoothScalarDirichlet q) :
    dirichletExtend q F (smoothToH1ComplDirichlet q u)
        (smoothToH1ComplDirichlet q v) = F u v := by
  change dirichletExtend q F
      (u : UniformSpace.Completion (SmoothScalarDirichlet q))
      (v : UniformSpace.Completion (SmoothScalarDirichlet q)) = F u v
  exact DifferentialGeometry.Analysis.bilinearFromCompletion_apply_coe
    (X := SmoothScalarDirichlet q) F u v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletExtend_apply_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletExtend_apply_smooth target :: scope.openDecls } }

noncomputable def dirichletMassSmooth
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    SmoothScalarDirichlet q →L[ℝ] SmoothScalarDirichlet q →L[ℝ] ℝ := by
  refine LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun u v => dirichletMass h u v)
      (dirichletMass_add_left h)
      (dirichletMass_smul_left h)
      (dirichletMass_add_right h)
      (dirichletMass_smul_right h))
    (Cv.toReal * Cg) ?_
  intro u v
  rw [Real.norm_eq_abs]
  exact abs_dirichletMass_le_of_metric_and_volume h hCg hequiv
    Cv hCv0 hCvtop hvol u v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassSmooth ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassSmooth

theorem dirichletMassSmooth_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : SmoothScalarDirichlet q) :
    dirichletMassSmooth h hCg hequiv Cv hCv0 hCvtop hvol u v =
      dirichletMass h u v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassSmooth_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassSmooth_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassSmooth_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassSmooth_apply

theorem norm_dirichletMassSmooth_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ‖dirichletMassSmooth h hCg hequiv Cv hCv0 hCvtop hvol‖ ≤
      Cv.toReal * Cg := by
  apply LinearMap.mkContinuous₂_norm_le
  exact mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassSmooth_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassSmooth_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassSmooth_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassSmooth_le

noncomputable def dirichletMassCompl
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
  dirichletExtend q
    (dirichletMassSmooth h hCg hequiv Cv hCv0 hCvtop hvol)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassCompl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassCompl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassCompl ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassCompl

theorem dirichletMassCompl_apply_smooth
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : SmoothScalarDirichlet q) :
    dirichletMassCompl h hCg hequiv Cv hCv0 hCvtop hvol
        (smoothToH1ComplDirichlet q u) (smoothToH1ComplDirichlet q v) =
      dirichletMass h u v := by
  rw [dirichletMassCompl, dirichletExtend_apply_smooth,
    dirichletMassSmooth_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassCompl_apply_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassCompl_apply_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassCompl_apply_smooth ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassCompl_apply_smooth

theorem dirichletMassCompl_self_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ q.inner x v v ∧
        q.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : H1ComplDirichlet q) :
    dirichletMassCompl q hCg hequiv Cv hCv0 hCvtop hvol u v =
      inner ℝ (H1ComplDirichletToLp q u) (H1ComplDirichletToLp q v) := by
  let mass := dirichletMassCompl q hCg hequiv Cv hCv0 hCvtop hvol
  have hsmooth (u₀ : SmoothScalarDirichlet q) :
      (fun v => mass (smoothToH1ComplDirichlet q u₀) v) =
        fun v => _root_.Inner.inner ℝ (H1ComplDirichletToLp q
          (smoothToH1ComplDirichlet q u₀))
          (H1ComplDirichletToLp q v) := by
    apply DenseRange.equalizer (denseRange_smoothToH1ComplDirichlet q)
      (mass (smoothToH1ComplDirichlet q u₀)).continuous
      (continuous_const.inner (H1ComplDirichletToLp q).continuous)
    funext v₀
    simp only [Function.comp_apply]
    dsimp only [mass]
    rw [H1ComplDirichletToLp_smoothToH1ComplDirichlet,
      H1ComplDirichletToLp_smoothToH1ComplDirichlet,
      dirichletMassCompl_apply_smooth, MeasureTheory.L2.inner_def]
    unfold dirichletMass
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp u₀.memLp_two,
      MemLp.coeFn_toLp v₀.memLp_two] with x hu hv
    rw [smoothToLpDirichlet,
      DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpInterior_apply q u₀,
      DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpInterior_apply q v₀,
      hu, hv]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  have hall : (fun u => mass u v) =
      fun u => _root_.Inner.inner ℝ (H1ComplDirichletToLp q u)
        (H1ComplDirichletToLp q v) := by
    apply DenseRange.equalizer (denseRange_smoothToH1ComplDirichlet q)
      (mass.flip v).continuous
      ((H1ComplDirichletToLp q).continuous.inner continuous_const)
    funext u₀
    exact congrFun (hsmooth u₀) v
  exact congrFun hall u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassCompl_self_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassCompl_self_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassCompl_self_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassCompl_self_apply

theorem dirichletMassCompl_self_riesz_eq_resolventDirichlet
    {q : SmoothRiemannianMetric (I_half n) M}
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ q.inner x v v ∧
        q.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u : H1ComplDirichlet q) :
    (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm
        (dirichletMassCompl q hCg hequiv Cv hCv0 hCvtop hvol u) =
      resolventDirichlet q (H1ComplDirichletToLp q u) := by
  apply ext_inner_right ℝ
  intro v
  rw [InnerProductSpace.toDual_symm_apply,
    dirichletMassCompl_self_apply,
    resolventDirichlet_inner_eq_lpFunctional,
    real_inner_comm (H1ComplDirichletToLp q u)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassCompl_self_riesz_eq_resolventDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassCompl_self_riesz_eq_resolventDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassCompl_self_riesz_eq_resolventDirichlet ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassCompl_self_riesz_eq_resolventDirichlet

theorem norm_dirichletMassCompl_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ‖dirichletMassCompl h hCg hequiv Cv hCv0 hCvtop hvol‖ ≤
      Cv.toReal * Cg := by
  rw [dirichletMassCompl, dirichletExtend]
  apply DifferentialGeometry.Analysis.norm_bilinearFromCompletion_le
  · exact mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg)
  · intro u v
    rw [dirichletMassSmooth_apply, Real.norm_eq_abs]
    exact abs_dirichletMass_le_of_metric_and_volume h hCg hequiv
      Cv hCv0 hCvtop hvol u v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassCompl_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassCompl_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassCompl_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassCompl_le

noncomputable def dirichletWeakFormSmooth
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a B : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    SmoothScalarDirichlet q →L[ℝ] SmoothScalarDirichlet q →L[ℝ] ℝ := by
  refine LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun u v => dirichletWeakForm h X a u v)
      (dirichletWeakForm_add_left h X a)
      (dirichletWeakForm_smul_left h X a)
      (dirichletWeakForm_add_right h X a)
      (dirichletWeakForm_smul_right h X a))
    ((1 + Real.sqrt (_root_.Max.max B 0) + |a|) * (Cv.toReal * Cg)) ?_
  intro u v
  rw [Real.norm_eq_abs]
  exact abs_dirichletWeakForm_le_of_metric_and_volume h X a B hX
    hCg hequiv Cv hCv0 hCvtop hvol u v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormSmooth ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormSmooth

theorem dirichletWeakFormSmooth_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a B : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : SmoothScalarDirichlet q) :
    dirichletWeakFormSmooth h X a B hX hCg hequiv Cv hCv0 hCvtop hvol u v =
      dirichletWeakForm h X a u v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormSmooth_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormSmooth_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormSmooth_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormSmooth_apply

theorem norm_dirichletWeakFormSmooth_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a B : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ‖dirichletWeakFormSmooth h X a B hX hCg hequiv Cv hCv0 hCvtop hvol‖ ≤
      (1 + Real.sqrt (_root_.Max.max B 0) + |a|) * (Cv.toReal * Cg) := by
  apply LinearMap.mkContinuous₂_norm_le
  exact mul_nonneg
    (add_nonneg
      (add_nonneg zero_le_one (Real.sqrt_nonneg (_root_.Max.max B 0))) (abs_nonneg a))
    (mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletWeakFormSmooth_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletWeakFormSmooth_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletWeakFormSmooth_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletWeakFormSmooth_le

noncomputable def dirichletWeakFormCompl
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a B : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
  dirichletExtend q
    (dirichletWeakFormSmooth h X a B hX hCg hequiv Cv hCv0 hCvtop hvol)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormCompl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormCompl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormCompl ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormCompl

theorem dirichletWeakFormCompl_apply_smooth
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a B : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : SmoothScalarDirichlet q) :
    dirichletWeakFormCompl h X a B hX hCg hequiv Cv hCv0 hCvtop hvol
        (smoothToH1ComplDirichlet q u) (smoothToH1ComplDirichlet q v) =
      dirichletWeakForm h X a u v := by
  rw [dirichletWeakFormCompl, dirichletExtend_apply_smooth,
    dirichletWeakFormSmooth_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormCompl_apply_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormCompl_apply_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormCompl_apply_smooth ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormCompl_apply_smooth

theorem norm_dirichletWeakFormCompl_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a B : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ‖dirichletWeakFormCompl h X a B hX hCg hequiv Cv hCv0 hCvtop hvol‖ ≤
      (1 + Real.sqrt (_root_.Max.max B 0) + |a|) * (Cv.toReal * Cg) := by
  rw [dirichletWeakFormCompl, dirichletExtend]
  apply DifferentialGeometry.Analysis.norm_bilinearFromCompletion_le
  · exact mul_nonneg
      (add_nonneg
        (add_nonneg zero_le_one (Real.sqrt_nonneg (_root_.Max.max B 0))) (abs_nonneg a))
      (mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg))
  · intro u v
    rw [dirichletWeakFormSmooth_apply, Real.norm_eq_abs]
    exact abs_dirichletWeakForm_le_of_metric_and_volume h X a B hX
      hCg hequiv Cv hCv0 hCvtop hvol u v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletWeakFormCompl_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletWeakFormCompl_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletWeakFormCompl_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletWeakFormCompl_le

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end

noncomputable section

open _root_.Manifold _root_.MeasureTheory
open scoped _root_.ContDiff _root_.ENNReal _root_.InnerProductSpace _root_.Manifold _root_.RealInnerProductSpace _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem dirichletWeakFormCompl_self_zero_apply
    (q : SmoothRiemannianMetric I_hs M)
    (B : ℝ) (hX : ∀ x : M, q.inner x (0 : TangentSpace I_hs x) 0 ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x v v ≤ q.inner x v v ∧
        q.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_hs) (M := M) q ≤
      Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (u v : H1ComplDirichlet q) :
    dirichletWeakFormCompl q 0 0 B hX hCg hequiv Cv hCv0 hCvtop hvol u v =
      ⟪H1ComplDirichletToLp q u, H1ComplDirichletToLp q v⟫_ℝ - ⟪u, v⟫_ℝ := by
  let F := dirichletWeakFormCompl q 0 0 B hX hCg hequiv Cv hCv0 hCvtop hvol
  have hsmooth (u₀ : SmoothScalarDirichlet q) :
      (fun v => F (smoothToH1ComplDirichlet q u₀) v) =
        fun v => ⟪H1ComplDirichletToLp q (smoothToH1ComplDirichlet q u₀),
          H1ComplDirichletToLp q v⟫_ℝ - ⟪smoothToH1ComplDirichlet q u₀, v⟫_ℝ := by
    apply DenseRange.equalizer (denseRange_smoothToH1ComplDirichlet q)
      (F (smoothToH1ComplDirichlet q u₀)).continuous
      ((continuous_const.inner (H1ComplDirichletToLp q).continuous).sub
        (continuous_const.inner continuous_id))
    funext v₀
    simp only [Function.comp_apply, Pi.sub_apply, id_eq]
    dsimp only [F]
    rw [dirichletWeakFormCompl_apply_smooth,
      H1ComplDirichletToLp_smoothToH1ComplDirichlet,
      H1ComplDirichletToLp_smoothToH1ComplDirichlet]
    have hm := dirichletMassLp_apply_smooth q Cv hCvtop hvol u₀ v₀
    rw [dirichletMassLp_self_apply] at hm
    rw [hm]
    have hi : ⟪smoothToH1ComplDirichlet q u₀,
        smoothToH1ComplDirichlet q v₀⟫_ℝ = interiorSmoothScalarH1Inner u₀ v₀ :=
      inner_smoothToH1ComplInterior_smoothToH1ComplInterior u₀ v₀
    rw [hi]
    simp [dirichletWeakForm, dirichletDrift, dirichletMass, dirichletEnergy,
      interiorSmoothScalarH1Inner]
  have hall : (fun u => F u v) = fun u =>
      ⟪H1ComplDirichletToLp q u, H1ComplDirichletToLp q v⟫_ℝ - ⟪u, v⟫_ℝ := by
    apply DenseRange.equalizer (denseRange_smoothToH1ComplDirichlet q)
      (F.flip v).continuous
      (((H1ComplDirichletToLp q).continuous.inner continuous_const).sub
        (continuous_id.inner continuous_const))
    funext u₀
    exact congrFun (hsmooth u₀) v
  exact congrFun hall u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormCompl_self_zero_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormCompl_self_zero_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormCompl_self_zero_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormCompl_self_zero_apply

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
