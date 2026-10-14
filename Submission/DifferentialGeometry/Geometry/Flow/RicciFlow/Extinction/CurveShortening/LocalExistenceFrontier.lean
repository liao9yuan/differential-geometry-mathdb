import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    {D : RealTimeInterval} {a b : ℝ}

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [IsManifold I ∞ M] in
theorem CurveMap.velocity_congr_set {c : CurveMap M} {J J' : Set ℝ} {x t : ℝ}
    (h : J =ᶠ[𝓝[{t}ᶜ] t] J') :
    c.velocity (I := I) J x t = c.velocity (I := I) J' x t := by
  simp only [CurveMap.velocity]
  rw [mfderivWithin_congr_set' (I := 𝓘(ℝ, ℝ)) (I' := I) t h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.velocity_congr_set then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.velocity_congr_set"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.velocity_congr_set ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.velocity_congr_set

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [IsManifold I ∞ M] in
theorem CurveMap.velocity_Icc_of_lt {c : CurveMap M} {t₀ σ τ : ℝ}
    (hσ : 0 < σ) (hστ : σ < τ)
    (hsm : c.SmoothOn (I := I) (_root_.Set.Icc t₀ (t₀ + τ))) {x t : ℝ}
    (ht : t ∈ _root_.Set.Icc t₀ (t₀ + σ)) :
    c.velocity (I := I) (_root_.Set.Icc t₀ (t₀ + σ)) x t = c.velocity (I := I) (_root_.Set.Icc t₀ (t₀ + τ)) x t := by
  simp only [CurveMap.velocity]
  rcases eq_or_lt_of_le ht.1 with rfl | htlt
  · rw [mfderivWithin_congr_set' (I := 𝓘(ℝ, ℝ)) (I' := I) t₀ ?_]
    refine eventually_nhdsWithin_iff.mpr ?_
    filter_upwards [isOpen_Iio.mem_nhds (by linarith : t₀ < t₀ + σ)] with u hu hune
    exact propext ⟨fun h' => ⟨h'.1, le_trans h'.2 (by linarith)⟩, fun h' => ⟨h'.1, le_of_lt hu⟩⟩
  · by_cases hright : t = t₀ + σ
    · subst hright
      have hfar : t₀ + σ < t₀ + τ := by linarith
      have hnb : _root_.Set.Icc t₀ (t₀ + τ) ∈ 𝓝 (t₀ + σ) := Icc_mem_nhds (by linarith) hfar
      have hslice : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun s => c.lift x s) (_root_.Set.Icc t₀ (t₀ + τ)) :=
        c.time_slice_contMDiffOn (_root_.Set.Icc t₀ (t₀ + τ)) hsm x
      have hd : MDifferentiableAt 𝓘(ℝ, ℝ) I (c.lift x) (t₀ + σ) :=
        (hslice.contMDiffAt hnb).mdifferentiableAt (by simp)
      have hU : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (_root_.Set.Icc t₀ (t₀ + σ)) (t₀ + σ) :=
        uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr
          ((uniqueDiffOn_Icc (by linarith : t₀ < t₀ + σ)) (t₀ + σ) ⟨by linarith, le_rfl⟩)
      rw [mfderivWithin_eq_mfderiv hU hd,
        mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℝ)) (I' := I) hnb]
    · have hlt : t < t₀ + σ := lt_of_le_of_ne ht.2 hright
      have hfar : t < t₀ + τ := by linarith
      rw [mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℝ)) (I' := I) (Icc_mem_nhds htlt hlt),
        mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℝ)) (I' := I) (Icc_mem_nhds htlt hfar)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.velocity_Icc_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.velocity_Icc_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.velocity_Icc_of_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.velocity_Icc_of_lt

def CurveShorteningSmoothSolution (B : SmoothMetricWindow (I := I) (M := M) D a b) : Prop :=
  ∀ t₀ ∈ _root_.Set.Ico a b, ∀ c₀ : SmoothImmersion (I := I) (M := M),
    ∃ τ > 0, t₀ + τ ≤ b ∧ ∃ c : CurveMap M,
      c.SmoothOn (I := I) (_root_.Set.Icc t₀ (t₀ + τ)) ∧
      (∀ z, c z t₀ = c₀.map z) ∧
      (∀ x t, t ∈ _root_.Set.Icc t₀ (t₀ + τ) →
        c.velocity (I := I) (_root_.Set.Icc t₀ (t₀ + τ)) x t = c.curvatureVector B.family.metric x t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveShorteningSmoothSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveShorteningSmoothSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveShorteningSmoothSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveShorteningSmoothSolution

def CurveShorteningImmersedPersistence : Prop :=
  ∀ ⦃t₀ T : ℝ⦄, t₀ < T → ∀ c : CurveMap M, c.SmoothOn (I := I) (_root_.Set.Icc t₀ T) →
    (∀ x, c.X (I := I) x t₀ ≠ 0) →
    ∃ τ, 0 < τ ∧ τ ≤ T - t₀ ∧ c.ImmersedOn (I := I) (_root_.Set.Icc t₀ (t₀ + τ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveShorteningImmersedPersistence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveShorteningImmersedPersistence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveShorteningImmersedPersistence ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveShorteningImmersedPersistence

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem curveShorteningLocalExistence_of_smoothSolution
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (h : CurveShorteningSmoothSolution (I := I) (M := M) B)
    (hp : CurveShorteningImmersedPersistence (I := I) (M := M)) :
    curveShorteningLocalExistence (I := I) (M := M) B := by
  intro t₀ ht₀ c₀
  obtain ⟨τ, hτ, hb, c, hsm, hinit, heq⟩ := h t₀ ht₀ c₀
  have hX₀ : ∀ x, c.X (I := I) x t₀ ≠ 0 := by
    intro x
    have hpoint : c.X (I := I) x t₀ =
        mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => c₀.map (y : AddCircle (1 : ℝ))) x (1 : ℝ) := by
      have hfun : (fun y : ℝ => c.lift y t₀) =
          fun y : ℝ => c₀.map (y : AddCircle (1 : ℝ)) := by
        funext y
        rw [CurveMap.lift, hinit]
      simp only [CurveMap.X]
      exact congrArg (fun f : ℝ → M => (mfderiv 𝓘(ℝ, ℝ) I f x) (1 : ℝ)) hfun
    rw [hpoint]
    exact c₀.immersed x
  obtain ⟨τ', hτ'pos, hτ'le, himm⟩ := hp (by linarith : t₀ < t₀ + τ) c hsm hX₀
  have hτ'τ : τ' ≤ τ := by linarith
  have hsub : _root_.Set.Icc t₀ (t₀ + τ' / 2) ⊆ _root_.Set.Icc t₀ (t₀ + τ) :=
    fun t ht => ⟨ht.1, by linarith [ht.2, hτ'τ]⟩
  have hsub' : _root_.Set.Icc t₀ (t₀ + τ' / 2) ⊆ _root_.Set.Icc t₀ (t₀ + τ') :=
    fun t ht => ⟨ht.1, by linarith [ht.2]⟩
  refine ⟨τ' / 2, by linarith, by linarith, c, ?_, hinit⟩
  refine ⟨hsm.mono (Set.prod_mono Subset.rfl hsub),
    fun x t ht => himm x t (hsub' ht), ?_⟩
  intro x t ht
  rw [CurveMap.velocity_Icc_of_lt (t₀ := t₀) (σ := τ' / 2) (τ := τ)
    (by linarith : 0 < τ' / 2) (by linarith : τ' / 2 < τ) hsm ht]
  exact heq x t (hsub ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalExistence_of_smoothSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalExistence_of_smoothSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalExistence_of_smoothSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalExistence_of_smoothSolution

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
