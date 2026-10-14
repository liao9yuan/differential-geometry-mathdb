import Submission.DifferentialGeometry.Analysis.ODE.Flow.BundleLinearODE
import Submission.DifferentialGeometry.Bundle.Equiv
import Submission.DifferentialGeometry.Bundle.Hom
import Submission.DifferentialGeometry.Geometry.Curvature.RicciSharpSmooth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

theorem exists_gauge_with_fixed_ricci_generator
    (g : SmoothRiemannianMetric I M) (b : ℝ)
    (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap)) :
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι b x = ι₀ x) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
          (E := fun x => V x →L[ℝ] TangentSpace I x)
          (ι p.1 p.2).toContinuousLinearMap) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] F) p.2
          (E := fun x => TangentSpace I x →L[ℝ] V x)
          (ι p.1 p.2).symm.toContinuousLinearMap) ∧
      ∀ x v t, HasDerivAt (fun s => ι s x v)
        (ricciSharp (I := I) g x (ι t x v)) t := by
  have hR : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E) p.2
        (E := fun x => TangentSpace I x →L[ℝ] TangentSpace I x) (ricciSharp g p.2)) :=
    (ricciSharp_contMDiff g).comp contMDiff_snd
  obtain ⟨Φ, hΦ₀, hΦsmooth, _, hΦderiv, _, hΦinv, _⟩ :=
    Analysis.ODE.Flow.exists_fiberwise_linear_ode_solution_on_interval
      (I := I) (F := E) (V := TangentSpace I) (J := _root_.Set.univ) (t₀ := b)
      _root_.Set.ordConnected_univ (_root_.Set.mem_univ b) (fun _ x => ricciSharp g x) hR.contMDiffOn
  let Ψ : ℝ → ∀ x, TangentSpace I x ≃L[ℝ] TangentSpace I x := fun t x =>
    ContinuousLinearEquiv.equivOfInverse (Φ t x) (Φ t x).inverse
      (fun v => (hΦinv t (_root_.Set.mem_univ t) x v).1)
      (fun v => (hΦinv t (_root_.Set.mem_univ t) x v).2)
  let ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x := fun t x => (ι₀ x).trans (Ψ t x)
  have hι (t : ℝ) (x : M) (v : V x) : ι t x v = Φ t x (ι₀ x v) := rfl
  have hιinit : ∀ x, ι b x = ι₀ x := by
    intro x
    ext v
    rw [hι, hΦ₀]
    rfl
  have hΦglobal : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E) p.2
        (E := fun x => TangentSpace I x →L[ℝ] TangentSpace I x) (Φ p.1 p.2)) := by
    simpa only [_root_.Set.univ_prod_univ, contMDiffOn_univ] using hΦsmooth
  have hιsmooth : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
        (E := fun x => V x →L[ℝ] TangentSpace I x)
        (ι p.1 p.2).toContinuousLinearMap) := by
    intro p
    exact (hΦglobal p).clm_bundle_comp ((hι₀.comp contMDiff_snd) p)
  refine ⟨ι, hιinit, hιsmooth, ?_, ?_⟩
  · let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
    simpa only [ContinuousLinearMap.inverse_equiv] using
      hιsmooth.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
  · intro x v t
    simpa only [hι] using (hΦderiv x (ι₀ x v) t (_root_.Set.mem_univ t)).hasDerivAt (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exists_gauge_with_fixed_ricci_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exists_gauge_with_fixed_ricci_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exists_gauge_with_fixed_ricci_generator ``Submission.DifferentialGeometry.exists_gauge_with_fixed_ricci_generator

end DifferentialGeometry
