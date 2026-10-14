import Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakFormIntegration
import Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.SmoothTimeTest
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1IntegrationByParts
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Steklov

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.InnerProductSpace _root_.Manifold _root_.NNReal
  RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator.WithBoundary
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

theorem IsWeakEvolutionSolution.integral_timeH1_test
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : _root_.Set.Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (_root_.Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (_root_.Set.Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : _root_.MeasureTheory.Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      hX htrace f₀ u) :
    ∃ Cg : ℝ, ∃ Cv : ℝ≥0∞,
      ∃ hCg : 1 ≤ Cg,
      ∃ hequiv : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ x : M,
        ∀ v : TangentSpace I_hs x,
          Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
            (G.metric t).inner x v v ≤ Cg * q.inner x v v,
      ∃ hCv0 : Cv ≠ 0, ∃ hCvtop : Cv ≠ ⊤,
      ∃ hvol : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
        riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t) ≤
          Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q,
      ∀ v : timeH1 (H1ComplDirichlet q) T, v.toFun T = 0 →
        (∫ t, dirichletMassComplOnIcc G.metric hCg hequiv Cv hCv0 hCvtop hvol
          t (u t) (v.deriv t) ∂timeMeasure T) +
        (∫ t, dirichletMassVariationComplOnIco hG hreg Bv htrace
            hCg hequiv Cv hCv0 hCvtop hvol t (u t) (v.toFun t) +
          dirichletWeakFormComplOnIco G.metric X a Bx hX
            hCg hequiv Cv hCv0 hCvtop hvol t (u t) (v.toFun t) ∂timeMeasure T) =
        -dirichletMassLp (G.metric 0) Cv hCvtop (hvol 0 ⟨le_rfl, hT⟩)
          f₀ (H1ComplDirichletToLp q v.initial) := by
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, w, hwi, hwm, hwd⟩ :=
    hu.exists_mass_timeH1 hXcont hacont
  refine ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, ?_⟩
  intro v hv
  have h := w.integration_by_parts_integral v hT
  rw [hv, inner_zero_right, zero_sub, w.toFun_zero, v.toFun_zero, hwi,
    InnerProductSpace.toDual_symm_apply] at h
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [h]
  apply congrArg₂ (fun a b : ℝ => a + b)
  · apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hwm] with t ht
    rw [← ht]
    exact InnerProductSpace.toDual_symm_apply.symm
  · apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hwd] with t ht
    rw [ht, real_inner_comm, InnerProductSpace.toDual_symm_apply]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_timeH1_test then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_timeH1_test"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_timeH1_test ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_timeH1_test

theorem IsWeakEvolutionSolution.integral_timeH1_test_eq_integral
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : _root_.Set.Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (_root_.Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (_root_.Set.Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : _root_.MeasureTheory.Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      hX htrace f₀ u)
    (w : timeH1 (H1ComplDirichlet q) T) (v : ℝ → SmoothScalarDirichlet q)
    (v' : ℝ → M → ℝ)
    (hwv : ∀ᵐ t ∂timeMeasure T,
      H1ComplDirichletToLp q (w.toFun t) =ᵐ[
        riemannianVolumeMeasure (I := I_hs) (M := M) q] (v t).toFun)
    (hwd : ∀ᵐ t ∂timeMeasure T,
      H1ComplDirichletToLp q (w.deriv t) =ᵐ[
        riemannianVolumeMeasure (I := I_hs) (M := M) q] v' t)
    (hwi : H1ComplDirichletToLp q w.initial =ᵐ[
      riemannianVolumeMeasure (I := I_hs) (M := M) q] (v 0).toFun)
    (hwT : w.toFun T = 0) :
    (∫ t, ∫ x, H1ComplDirichletToLp q (u t) x * v' t x
      ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t)) ∂timeMeasure T) +
    (∫ t, (∫ x, (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t x *
        (H1ComplDirichletToLp q (u t) x * (v t).toFun x)
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t))) +
      ∫ x, H1ComplDirichletToLp q (u t) x *
        (ΔGWithBoundary (I := I_hs) (G.metric t) (v t).smooth (v t).interior_support x -
          tangentSectionAction (I := I_hs) (X t) (v t).toFun x -
          divergence (I := I_hs) (leviCivitaConnectionOfMetric (I := I_hs) (G.metric t))
            (X t) x * (v t).toFun x - a t * (v t).toFun x)
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t)) ∂timeMeasure T) =
      -(∫ x, f₀ x * (v 0).toFun x
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric 0))) := by
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, htest⟩ :=
    hu.integral_timeH1_test hXcont hacont
  have hac (t : ℝ) (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
      riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t) ≪
        riemannianVolumeMeasure (I := I_hs) (M := M) q :=
    Measure.absolutelyContinuous_of_le_smul (hvol t ht)
  have hv : ∀ᵐ t ∂timeMeasure T,
      w.toFun t = smoothToH1ComplDirichlet q (v t) := by
    filter_upwards [hwv] with t ht
    apply H1ComplDirichletToLp_injective q
    apply Lp.ext
    exact ht.trans (by
      rw [H1ComplDirichletToLp_smoothToH1ComplDirichlet]
      exact (MemLp.coeFn_toLp (v t).memLp_two).symm)
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ _root_.Set.Ico (0 : ℝ) T := by
    unfold timeMeasure
    rw [← _root_.MeasureTheory.restrict_Ico_eq_restrict_Icc]
    exact _root_.MeasureTheory.ae_restrict_mem measurableSet_Ico
  have hfirst :
      (∫ t, dirichletMassComplOnIcc G.metric hCg hequiv Cv hCv0 hCvtop hvol
        t (u t) (w.deriv t) ∂timeMeasure T) =
      ∫ t, ∫ x, H1ComplDirichletToLp q (u t) x * v' t x
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t)) ∂timeMeasure T := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hwd, hmem] with t ht htm
    have htc : t ∈ _root_.Set.Icc (0 : ℝ) T := ⟨htm.1, htm.2.le⟩
    rw [dirichletMassComplOnIcc, dif_pos htc, dirichletMassCompl_apply_eq_integral]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [(hac t htc).ae_eq ht] with x hx
    rw [hx]
  have hsecond :
      (∫ t, dirichletMassVariationComplOnIco hG hreg Bv htrace
          hCg hequiv Cv hCv0 hCvtop hvol t (u t) (w.toFun t) +
        dirichletWeakFormComplOnIco G.metric X a Bx hX
          hCg hequiv Cv hCv0 hCvtop hvol t (u t) (w.toFun t) ∂timeMeasure T) =
      (∫ t, (∫ x, (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t x *
          (H1ComplDirichletToLp q (u t) x * (v t).toFun x)
          ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t))) +
        ∫ x, H1ComplDirichletToLp q (u t) x *
          (ΔGWithBoundary (I := I_hs) (G.metric t) (v t).smooth (v t).interior_support x -
            tangentSectionAction (I := I_hs) (X t) (v t).toFun x -
            divergence (I := I_hs) (leviCivitaConnectionOfMetric (I := I_hs) (G.metric t))
              (X t) x * (v t).toFun x - a t * (v t).toFun x)
          ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t)) ∂timeMeasure T) := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hv, hmem] with t ht htm
    rw [ht, dirichletMassVariationComplOnIco, dif_pos htm,
      dirichletWeakFormComplOnIco, dif_pos htm,
      dirichletMassVariationCompl_apply_eq_integral,
      dirichletWeakFormCompl_apply_eq_integral_adjoint]
  have hin : dirichletMassLp (G.metric 0) Cv hCvtop (hvol 0 ⟨le_rfl, hT⟩)
      f₀ (H1ComplDirichletToLp q w.initial) =
      ∫ x, f₀ x * (v 0).toFun x
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric 0)) := by
    rw [dirichletMassLp_apply_eq_integral]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [(hac 0 ⟨le_rfl, hT⟩).ae_eq hwi] with x hx
    rw [hx]
  simpa only [hfirst, hsecond, hin] using htest w hwT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_timeH1_test_eq_integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_timeH1_test_eq_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_timeH1_test_eq_integral ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_timeH1_test_eq_integral

theorem IsWeakEvolutionSolution.integral_smooth_time_test
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : _root_.Set.Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (_root_.Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (_root_.Set.Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : _root_.MeasureTheory.Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      hX htrace f₀ u)
    (v v' : ℝ → SmoothScalarDirichlet q)
    {J : Set ℝ} (hJ : IsOpen J)
    (hv : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (v p.1).toFun p.2) (J ×ˢ _root_.Set.univ))
    (hv' : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (v' p.1).toFun p.2) (J ×ˢ _root_.Set.univ))
    (hd : ∀ t ∈ J, ∀ x, HasDerivAt (fun s => (v s).toFun x) ((v' t).toFun x) t)
    {K : Set M} (hK : IsClosed K) (hKi : K ⊆ (I_hs).interior M)
    (hv'K : ∀ t ∈ J, tsupport (v' t).toFun ⊆ K)
    (hTJ : _root_.Set.Icc (0 : ℝ) T ⊆ J) (hvT : v T = 0) :
    (∫ t, ∫ x, H1ComplDirichletToLp q (u t) x * (v' t).toFun x
      ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t)) ∂timeMeasure T) +
    (∫ t, (∫ x, (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t x *
        (H1ComplDirichletToLp q (u t) x * (v t).toFun x)
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t))) +
      ∫ x, H1ComplDirichletToLp q (u t) x *
        (ΔGWithBoundary (I := I_hs) (G.metric t) (v t).smooth (v t).interior_support x -
          tangentSectionAction (I := I_hs) (X t) (v t).toFun x -
          divergence (I := I_hs) (leviCivitaConnectionOfMetric (I := I_hs) (G.metric t))
            (X t) x * (v t).toFun x - a t * (v t).toFun x)
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t)) ∂timeMeasure T) =
      -(∫ x, f₀ x * (v 0).toFun x
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric 0))) := by
  obtain ⟨w, hwv, hwd, hwi, hwT⟩ :=
    exists_timeH1_smoothToH1ComplDirichlet q v v' hJ hv hv' hd hK hKi hv'K hT hTJ hvT
  apply hu.integral_timeH1_test_eq_integral hXcont hacont w v (fun t => (v' t).toFun)
    (hwT := hwT)
  · filter_upwards [_root_.MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with t ht
    rw [hwv ht, H1ComplDirichletToLp_smoothToH1ComplDirichlet]
    exact MemLp.coeFn_toLp (v t).memLp_two
  · filter_upwards [hwd] with t ht
    rw [ht, H1ComplDirichletToLp_smoothToH1ComplDirichlet]
    exact MemLp.coeFn_toLp (v' t).memLp_two
  · rw [hwi, H1ComplDirichletToLp_smoothToH1ComplDirichlet]
    exact MemLp.coeFn_toLp (v 0).memLp_two

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_smooth_time_test then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_smooth_time_test"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_smooth_time_test ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_smooth_time_test

theorem IsWeakEvolutionSolution.integral_steklovAverage_test
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : _root_.Set.Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (_root_.Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (_root_.Set.Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv hX htrace f₀ u)
    (v : timeL2 (H1ComplDirichlet q) T) {h : ℝ} (hh : 0 ≤ h) :
    let V := (_root_.Set.Icc (0 : ℝ) T).indicator (fun t => v t)
    ∃ Cg : ℝ, ∃ Cv : ℝ≥0∞,
      ∃ hCg : 1 ≤ Cg,
      ∃ hequiv : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ x : M,
        ∀ v : TangentSpace I_hs x,
          Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
            (G.metric t).inner x v v ≤ Cg * q.inner x v v,
      ∃ hCv0 : Cv ≠ 0, ∃ hCvtop : Cv ≠ ⊤,
      ∃ hvol : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
        riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t) ≤
          Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q,
      (∫ t, dirichletMassComplOnIcc G.metric hCg hequiv Cv hCv0 hCvtop hvol
        t (u t) (h⁻¹ • (V (t + h) - V t)) ∂timeMeasure T) +
      (∫ t, dirichletMassVariationComplOnIco hG hreg Bv htrace
          hCg hequiv Cv hCv0 hCvtop hvol t (u t) (steklovAverage h V t) +
        dirichletWeakFormComplOnIco G.metric X a Bx hX
          hCg hequiv Cv hCv0 hCvtop hvol t (u t) (steklovAverage h V t) ∂timeMeasure T) =
      -dirichletMassLp (G.metric 0) Cv hCvtop (hvol 0 ⟨le_rfl, hT⟩)
        f₀ (H1ComplDirichletToLp q (steklovAverage h V 0)) := by
  obtain ⟨w, hw, hwd, hwT⟩ := exists_timeH1_steklovAverage_timeL2_terminal_zero hT v hh
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, htest⟩ :=
    hu.integral_timeH1_test hXcont hacont
  refine ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, ?_⟩
  have hid := htest w hwT
  have hinit : w.initial = steklovAverage h ((_root_.Set.Icc (0 : ℝ) T).indicator v) 0 :=
    w.toFun_zero.symm.trans (hw 0 ⟨le_rfl, hT⟩)
  rw [hinit] at hid
  rw [← hid]
  apply congrArg₂ (fun a b : ℝ => a + b)
  · apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hwd] with t ht
    rw [ht]
  · apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    rw [hw t ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_steklovAverage_test then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_steklovAverage_test"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_steklovAverage_test ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_steklovAverage_test

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
