import Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.FormCompletion
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.InnerProductSpace _root_.Manifold _root_.RealInnerProductSpace _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
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

private local instance completedDualSeminormedAddCommGroup (q : SmoothRiemannianMetric (I_half n) M) :
    SeminormedAddCommGroup (H1ComplDirichlet q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (E := H1ComplDirichlet q) (F := ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.completedDualSeminormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.completedDualSeminormedAddCommGroup target :: scope.openDecls } }

private local instance completedBilinearSeminormedAddCommGroup (q : SmoothRiemannianMetric (I_half n) M) :
    SeminormedAddCommGroup (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ) (E := H1ComplDirichlet q) (F := H1ComplDirichlet q →L[ℝ] ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.completedBilinearSeminormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.completedBilinearSeminormedAddCommGroup target :: scope.openDecls } }

noncomputable def dirichletMassComplOnIcc
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (g t).inner x v v ∧
          (g t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
  fun t ↦ if ht : t ∈ _root_.Set.Icc (0 : ℝ) T then
    dirichletMassCompl (g t) hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht)
  else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassComplOnIcc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassComplOnIcc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassComplOnIcc ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassComplOnIcc

theorem dirichletMassComplOnIcc_apply_smooth
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (g t).inner x v v ∧
          (g t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) T)
    (u v : SmoothScalarDirichlet q) :
    dirichletMassComplOnIcc g hCg hequiv Cv hCv0 hCvtop hvol t
        (smoothToH1ComplDirichlet q u) (smoothToH1ComplDirichlet q v) =
      dirichletMass (g t) u v := by
  rw [dirichletMassComplOnIcc, dif_pos ht,
    dirichletMassCompl_apply_smooth]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassComplOnIcc_apply_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassComplOnIcc_apply_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassComplOnIcc_apply_smooth ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassComplOnIcc_apply_smooth

theorem norm_dirichletMassComplOnIcc_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (g t).inner x v v ∧
          (g t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (t : ℝ) :
    ‖dirichletMassComplOnIcc g hCg hequiv Cv hCv0 hCvtop hvol t‖ ≤
      Cv.toReal * Cg := by
  by_cases ht : t ∈ _root_.Set.Icc (0 : ℝ) T
  · rw [dirichletMassComplOnIcc, dif_pos ht]
    exact norm_dirichletMassCompl_le (g t) hCg (hequiv t ht)
      Cv hCv0 hCvtop (hvol t ht)
  · rw [dirichletMassComplOnIcc, dif_neg ht, norm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassComplOnIcc_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassComplOnIcc_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassComplOnIcc_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassComplOnIcc_le

theorem dirichletMassComplOnIcc_aestronglyMeasurable
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T Cg : ℝ} (hreg : _root_.Set.Icc (0 : ℝ) T ⊆ D.regular)
    (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : H1ComplDirichlet q) :
    _root_.MeasureTheory.AEStronglyMeasurable
      (fun t ↦ dirichletMassComplOnIcc G.metric hCg hequiv
        Cv hCv0 hCvtop hvol t u v) (timeMeasure T) := by
  apply AEStronglyMeasurable.clm_apply₂_of_denseRange
    (denseRange_smoothToH1ComplDirichlet q)
    (denseRange_smoothToH1ComplDirichlet q)
  intro u₀ v₀
  unfold timeMeasure
  have hraw := dirichletMass_time_cont G.metric _root_.CompactIccSpace.isCompact_Icc
    (fun x₀ i j ↦ hG.chartGramMatrix_continuousOn hreg x₀ i j) u₀ v₀
  refine (hraw.aestronglyMeasurable measurableSet_Icc).congr ?_
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
  exact (dirichletMassComplOnIcc_apply_smooth G.metric hCg hequiv
    Cv hCv0 hCvtop hvol ht u₀ v₀).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassComplOnIcc_aestronglyMeasurable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassComplOnIcc_aestronglyMeasurable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassComplOnIcc_aestronglyMeasurable ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassComplOnIcc_aestronglyMeasurable

noncomputable def dirichletMassVariationComplOnIco
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hreg : _root_.Set.Icc (0 : ℝ) T ⊆ D.regular)
    (B : ℝ)
    (htrace : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
  fun t ↦ if ht : t ∈ _root_.Set.Ico (0 : ℝ) T then
    dirichletMassVariationCompl hG (hreg ⟨ht.1, ht.2.le⟩) B
      (htrace t ht) hCg (hequiv t ⟨ht.1, ht.2.le⟩)
      Cv hCv0 hCvtop (hvol t ⟨ht.1, ht.2.le⟩)
  else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationComplOnIco then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationComplOnIco"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationComplOnIco ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationComplOnIco

theorem dirichletMassVariationComplOnIco_apply_smooth
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hreg : _root_.Set.Icc (0 : ℝ) T ⊆ D.regular)
    (B : ℝ)
    (htrace : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    {t : ℝ} (ht : t ∈ _root_.Set.Ico (0 : ℝ) T)
    (u v : SmoothScalarDirichlet q) :
    dirichletMassVariationComplOnIco hG hreg B htrace hCg hequiv
        Cv hCv0 hCvtop hvol t
        (smoothToH1ComplDirichlet q u) (smoothToH1ComplDirichlet q v) =
      dirichletMassVariation G.metric t u v := by
  rw [dirichletMassVariationComplOnIco, dif_pos ht,
    dirichletMassVariationCompl_apply_smooth]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationComplOnIco_apply_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationComplOnIco_apply_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationComplOnIco_apply_smooth ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationComplOnIco_apply_smooth

theorem norm_dirichletMassVariationComplOnIco_le
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hreg : _root_.Set.Icc (0 : ℝ) T ⊆ D.regular)
    (B : ℝ)
    (htrace : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (t : ℝ) :
    ‖dirichletMassVariationComplOnIco hG hreg B htrace hCg hequiv
      Cv hCv0 hCvtop hvol t‖ ≤
        (1 / 2) * _root_.Max.max B 0 * (Cv.toReal * Cg) := by
  by_cases ht : t ∈ _root_.Set.Ico (0 : ℝ) T
  · rw [dirichletMassVariationComplOnIco, dif_pos ht]
    exact norm_dirichletMassVariationCompl_le hG
      (hreg ⟨ht.1, ht.2.le⟩) B (htrace t ht) hCg
      (hequiv t ⟨ht.1, ht.2.le⟩) Cv hCv0 hCvtop
      (hvol t ⟨ht.1, ht.2.le⟩)
  · rw [dirichletMassVariationComplOnIco, dif_neg ht, norm_zero]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (le_max_right B 0))
      (mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassVariationComplOnIco_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassVariationComplOnIco_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassVariationComplOnIco_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletMassVariationComplOnIco_le

theorem dirichletMassVariationComplOnIco_aestronglyMeasurable
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hreg : _root_.Set.Icc (0 : ℝ) T ⊆ D.regular)
    (B : ℝ)
    (htrace : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : H1ComplDirichlet q) :
    _root_.MeasureTheory.AEStronglyMeasurable
      (fun t ↦ dirichletMassVariationComplOnIco hG hreg B htrace
        hCg hequiv Cv hCv0 hCvtop hvol t u v) (timeMeasure T) := by
  apply AEStronglyMeasurable.clm_apply₂_of_denseRange
    (denseRange_smoothToH1ComplDirichlet q)
    (denseRange_smoothToH1ComplDirichlet q)
  intro u₀ v₀
  unfold timeMeasure
  have hIco : ∀ᵐ t ∂(volume.restrict (_root_.Set.Icc (0 : ℝ) T)),
      t ∈ _root_.Set.Ico (0 : ℝ) T := by
    refine (_root_.MeasureTheory.ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [(_root_.MeasureTheory.Ico_ae_eq_Icc :
      _root_.Set.Ico (0 : ℝ) T =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] _root_.Set.Icc (0 : ℝ) T)] with t ht
    intro htIcc
    exact Eq.mpr ht htIcc
  let f : ℝ → ℝ := fun t ↦ dirichletMass (G.metric t) u₀ v₀
  refine (aestronglyMeasurable_deriv f
    (volume.restrict (_root_.Set.Icc (0 : ℝ) T))).congr ?_
  filter_upwards [hIco] with t ht
  have hderiv := (hasDerivAt_dirichletMass hG
    (hreg ⟨ht.1, ht.2.le⟩) u₀ v₀).deriv
  rw [show deriv f t = dirichletMassVariation G.metric t u₀ v₀ from hderiv]
  exact (dirichletMassVariationComplOnIco_apply_smooth hG hreg B htrace
    hCg hequiv Cv hCv0 hCvtop hvol ht u₀ v₀).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationComplOnIco_aestronglyMeasurable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationComplOnIco_aestronglyMeasurable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationComplOnIco_aestronglyMeasurable ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMassVariationComplOnIco_aestronglyMeasurable

noncomputable def dirichletWeakFormComplOnIco
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T : ℝ}
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → ℝ) (B : ℝ)
    (hX : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      (g t).inner x (X t x) (X t x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (g t).inner x v v ∧
          (g t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q) :
    ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
  fun t ↦ if ht : t ∈ _root_.Set.Ico (0 : ℝ) T then
    dirichletWeakFormCompl (g t) (X t) (a t) B (hX t ht)
      hCg (hequiv t ⟨ht.1, ht.2.le⟩) Cv hCv0 hCvtop
      (hvol t ⟨ht.1, ht.2.le⟩)
  else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormComplOnIco then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormComplOnIco"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormComplOnIco ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormComplOnIco

theorem dirichletWeakFormComplOnIco_apply_smooth
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T : ℝ}
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → ℝ) (B : ℝ)
    (hX : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      (g t).inner x (X t x) (X t x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (g t).inner x v v ∧
          (g t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    {t : ℝ} (ht : t ∈ _root_.Set.Ico (0 : ℝ) T)
    (u v : SmoothScalarDirichlet q) :
    dirichletWeakFormComplOnIco g X a B hX hCg hequiv
        Cv hCv0 hCvtop hvol t
        (smoothToH1ComplDirichlet q u) (smoothToH1ComplDirichlet q v) =
      dirichletWeakForm (g t) (X t) (a t) u v := by
  rw [dirichletWeakFormComplOnIco, dif_pos ht,
    dirichletWeakFormCompl_apply_smooth]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormComplOnIco_apply_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormComplOnIco_apply_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormComplOnIco_apply_smooth ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormComplOnIco_apply_smooth

theorem norm_dirichletWeakFormComplOnIco_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T : ℝ}
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → ℝ) (A B : ℝ)
    (hA : 0 ≤ A)
    (ha : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, |a t| ≤ A)
    (hX : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      (g t).inner x (X t x) (X t x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (g t).inner x v v ∧
          (g t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (t : ℝ) :
    ‖dirichletWeakFormComplOnIco g X a B hX hCg hequiv
      Cv hCv0 hCvtop hvol t‖ ≤
        (1 + Real.sqrt (_root_.Max.max B 0) + A) * (Cv.toReal * Cg) := by
  by_cases ht : t ∈ _root_.Set.Ico (0 : ℝ) T
  · rw [dirichletWeakFormComplOnIco, dif_pos ht]
    exact (norm_dirichletWeakFormCompl_le (g t) (X t) (a t) B
      (hX t ht) hCg (hequiv t ⟨ht.1, ht.2.le⟩)
      Cv hCv0 hCvtop (hvol t ⟨ht.1, ht.2.le⟩)).trans (by
        gcongr
        exact ha t ht)
  · rw [dirichletWeakFormComplOnIco, dif_neg ht, norm_zero]
    exact mul_nonneg
      (add_nonneg
        (add_nonneg zero_le_one (Real.sqrt_nonneg (_root_.Max.max B 0)))
        hA)
      (mul_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hCg))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletWeakFormComplOnIco_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletWeakFormComplOnIco_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletWeakFormComplOnIco_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.norm_dirichletWeakFormComplOnIco_le

theorem dirichletWeakFormComplOnIco_aestronglyMeasurable
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hreg : _root_.Set.Icc (0 : ℝ) T ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (_root_.Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (a : ℝ → ℝ) (hacont : ContinuousOn a (_root_.Set.Icc (0 : ℝ) T))
    (B : ℝ)
    (hX : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : H1ComplDirichlet q) :
    _root_.MeasureTheory.AEStronglyMeasurable
      (fun t ↦ dirichletWeakFormComplOnIco G.metric X a B hX
        hCg hequiv Cv hCv0 hCvtop hvol t u v) (timeMeasure T) := by
  apply AEStronglyMeasurable.clm_apply₂_of_denseRange
    (denseRange_smoothToH1ComplDirichlet q)
    (denseRange_smoothToH1ComplDirichlet q)
  intro u₀ v₀
  unfold timeMeasure
  have hIco : ∀ᵐ t ∂(volume.restrict (_root_.Set.Icc (0 : ℝ) T)),
      t ∈ _root_.Set.Ico (0 : ℝ) T := by
    refine (_root_.MeasureTheory.ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [(_root_.MeasureTheory.Ico_ae_eq_Icc :
      _root_.Set.Ico (0 : ℝ) T =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] _root_.Set.Icc (0 : ℝ) T)] with t ht
    intro htIcc
    exact Eq.mpr ht htIcc
  have hraw := dirichletWeakForm_time_cont hG _root_.CompactIccSpace.isCompact_Icc hreg
    X hXcont a hacont u₀ v₀
  refine (hraw.aestronglyMeasurable measurableSet_Icc).congr ?_
  filter_upwards [hIco] with t ht
  exact (dirichletWeakFormComplOnIco_apply_smooth G.metric X a B hX
    hCg hequiv Cv hCv0 hCvtop hvol ht u₀ v₀).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormComplOnIco_aestronglyMeasurable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormComplOnIco_aestronglyMeasurable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormComplOnIco_aestronglyMeasurable ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakFormComplOnIco_aestronglyMeasurable

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
