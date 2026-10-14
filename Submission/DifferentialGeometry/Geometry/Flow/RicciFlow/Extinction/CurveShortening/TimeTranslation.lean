import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set
open scoped _root_.Manifold _root_.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem smoothOn_time_translate {c : CurveMap M} {J K : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (τ : ℝ)
    (hmap : _root_.Set.MapsTo (fun t : ℝ => t + τ) K J) :
    CurveMap.SmoothOn (I := I) (fun z t => c z (t + τ)) K := by
  have hshift : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun p : ℝ × ℝ => (p.1, p.2 + τ)) :=
    (contDiff_fst.prodMk (contDiff_snd.add contDiff_const)).contMDiff
  exact hc.comp hshift.contMDiffOn (fun p hp => ⟨hp.1, hmap hp.2⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.smoothOn_time_translate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.smoothOn_time_translate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.smoothOn_time_translate ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.smoothOn_time_translate

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem velocity_time_translate {c : CurveMap M} {J K : Set ℝ}
    (τ : ℝ) (hmap : _root_.Set.MapsTo (fun t : ℝ => t + τ) K J)
    {x t : ℝ}
    (houter : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (c.lift x) J (t + τ))
    (hK : UniqueDiffWithinAt ℝ K t) :
    CurveMap.velocity (I := I) (fun z s => c z (s + τ)) K x t =
      c.velocity (I := I) J x (t + τ) := by
  have hinner : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun s : ℝ => s + τ) K t :=
    ((show ContDiff ℝ ∞ (fun s : ℝ => s + τ) from
      contDiff_id.add contDiff_const).contMDiff.contMDiffAt.contMDiffWithinAt).mdifferentiableWithinAt
        (by simp)
  have huniq : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) K t :=
    uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr hK
  have hchain := mfderivWithin_comp t houter hinner hmap huniq
  have hdiff : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s + τ) K t =
      (1 : ℝ →L[ℝ] ℝ) := by
    rw [mfderivWithin_eq_fderivWithin]
    exact ((hasFDerivAt_id t).add_const τ).hasFDerivWithinAt.fderivWithin hK
  change (mfderivWithin 𝓘(ℝ, ℝ) I (c.lift x ∘ (fun s : ℝ => s + τ)) K t) 1 = _
  rw [hchain, hdiff]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.velocity_time_translate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.velocity_time_translate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.velocity_time_translate ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.velocity_time_translate

theorem IsSolutionOn.time_translate {c : CurveMap M}
    {g : ℝ → SmoothRiemannianMetric I M} {J K : Set ℝ}
    (hc : c.IsSolutionOn (I := I) g J) (τ : ℝ)
    (hmap : _root_.Set.MapsTo (fun t : ℝ => t + τ) K J) (hK : UniqueDiffOn ℝ K) :
    CurveMap.IsSolutionOn (I := I) (fun z t => c z (t + τ))
      (fun t => g (t + τ)) K := by
  refine ⟨smoothOn_time_translate hc.smooth τ hmap, ?_, ?_⟩
  · intro x t ht
    exact hc.immersed x (t + τ) (hmap ht)
  · intro x t ht
    have htime := (c.time_slice_contMDiffWithinAt J hc.smooth x
      (t + τ) (hmap ht)).mdifferentiableWithinAt (by simp)
    rw [velocity_time_translate τ hmap htime (hK t ht)]
    exact hc.equation x (t + τ) (hmap ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.time_translate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.time_translate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.time_translate ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.time_translate

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem parabolic_equation_time_translate {c : CurveMap M}
    {g : ℝ → SmoothRiemannianMetric I M} {J K : Set ℝ}
    (hc : c.SmoothOn (I := I) J)
    (heq : ∀ x t, t ∈ J → c.velocity (I := I) J x t =
      c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t)
    (τ : ℝ) (hmap : _root_.Set.MapsTo (fun t : ℝ => t + τ) K J)
    (hK : UniqueDiffOn ℝ K) :
    ∀ x t, t ∈ K →
      CurveMap.velocity (I := I) (fun z s => c z (s + τ)) K x t =
        CurveMap.speed (I := I) (fun z s => c z (s + τ))
            (fun s => g (s + τ)) x t ^ (-2 : ℤ) •
          CurveMap.Dx (I := I) (fun z s => c z (s + τ))
            (fun s => g (s + τ))
            (CurveMap.X (I := I) (fun z s => c z (s + τ))) x t := by
  intro x t ht
  have htime := (c.time_slice_contMDiffWithinAt J hc x
    (t + τ) (hmap ht)).mdifferentiableWithinAt (by simp)
  rw [velocity_time_translate τ hmap htime (hK t ht)]
  exact heq x (t + τ) (hmap ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.parabolic_equation_time_translate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.parabolic_equation_time_translate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.parabolic_equation_time_translate ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.parabolic_equation_time_translate

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end
