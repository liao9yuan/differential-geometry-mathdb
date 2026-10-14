import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistenceFrontier
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistenceDimensionOne
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ImmersedPersistence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    {D : RealTimeInterval} {a b : ℝ}

def curveShorteningParabolicGaugeLocalExistence
    (B : SmoothMetricWindow (I := I) (M := M) D a b) : Prop :=
  ∀ t₀ ∈ _root_.Set.Ico a b, ∀ c₀ : SmoothImmersion (I := I) (M := M),
    ∃ τ : ℝ, 0 < τ ∧ t₀ + τ ≤ b ∧
      ∃ c : CurveMap M,
        c.SmoothOn (I := I) (_root_.Set.Icc t₀ (t₀ + τ)) ∧
        (∀ z, c z t₀ = c₀.map z) ∧
        (∀ x t, t ∈ _root_.Set.Icc t₀ (t₀ + τ) →
          c.velocity (I := I) (_root_.Set.Icc t₀ (t₀ + τ)) x t =
            (c.speed B.family.metric x t) ^ (-2 : ℤ) • c.Dx B.family.metric c.X x t -
              (deriv (fun y => c.speed B.family.metric y t) x /
                c.speed B.family.metric x t ^ 3) • c.X x t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningParabolicGaugeLocalExistence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningParabolicGaugeLocalExistence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningParabolicGaugeLocalExistence ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningParabolicGaugeLocalExistence

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem curveShorteningSmoothSolution_of_parabolicGaugeLocalExistence [I.Boundaryless]
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (h : curveShorteningParabolicGaugeLocalExistence (I := I) (M := M) B) :
    CurveShorteningSmoothSolution (I := I) (M := M) B := by
  intro t₀ ht₀ c₀
  obtain ⟨τ, hτ, hτb, c, hcT, hinit, heq⟩ := h t₀ ht₀ c₀
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
  obtain ⟨τ', hτ'pos, hτ'le, himm'⟩ :=
    curveShorteningImmersedPersistence (I := I) (M := M)
      (by linarith : t₀ < t₀ + τ) c hcT hX₀
  let τ'' : ℝ := τ' / 2
  have hτ''pos : 0 < τ'' := by dsimp [τ'']; linarith
  have hτ''τ' : τ'' < τ' := by dsimp [τ'']; linarith
  have hτ'τ : τ' ≤ τ := by linarith
  have hτ''τ : τ'' < τ := lt_of_lt_of_le hτ''τ' hτ'τ
  have hτ''b : t₀ + τ'' ≤ b := by linarith
  have hc'' : c.SmoothOn (I := I) (_root_.Set.Icc t₀ (t₀ + τ'')) :=
    hcT.mono (Set.prod_mono Subset.rfl (_root_.Set.Icc_subset_Icc le_rfl (by linarith)))
  refine ⟨τ'', hτ''pos, hτ''b, c, hc'', hinit, ?_⟩
  intro x t ht
  have htT : t ∈ _root_.Set.Icc t₀ (t₀ + τ) := ⟨ht.1, le_trans ht.2 (by linarith : t₀ + τ'' ≤ t₀ + τ)⟩
  have ht' : t ∈ _root_.Set.Icc t₀ (t₀ + τ') :=
    ⟨ht.1, le_trans ht.2 (by linarith : t₀ + τ'' ≤ t₀ + τ')⟩
  have hvel₁ : c.velocity (I := I) (_root_.Set.Icc t₀ (t₀ + τ'')) x t =
      c.velocity (I := I) (_root_.Set.Icc t₀ (t₀ + τ)) x t :=
    CurveMap.velocity_Icc_of_lt (t₀ := t₀) (σ := τ'') (τ := τ)
      hτ''pos hτ''τ hcT ht
  have hc' : c.SmoothOn (I := I) (_root_.Set.Icc t₀ (t₀ + τ')) :=
    hcT.mono (Set.prod_mono Subset.rfl (_root_.Set.Icc_subset_Icc le_rfl (by linarith)))
  have hpar := parabolic_gauge_velocity (I := I) B.family.metric c hc' himm' x t ht'
  have hgauge :
      (c.speed B.family.metric x t) ^ (-2 : ℤ) • c.Dx B.family.metric c.X x t -
        (deriv (fun y => c.speed B.family.metric y t) x /
          c.speed B.family.metric x t ^ 3) • c.X x t =
      c.curvatureVector B.family.metric x t := by
    rw [hpar.2, add_sub_cancel_right]
  calc
    c.velocity (I := I) (_root_.Set.Icc t₀ (t₀ + τ'')) x t =
        c.velocity (I := I) (_root_.Set.Icc t₀ (t₀ + τ)) x t := hvel₁
    _ = (c.speed B.family.metric x t) ^ (-2 : ℤ) • c.Dx B.family.metric c.X x t -
          (deriv (fun y => c.speed B.family.metric y t) x /
            c.speed B.family.metric x t ^ 3) • c.X x t := heq x t htT
    _ = c.curvatureVector B.family.metric x t := hgauge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningSmoothSolution_of_parabolicGaugeLocalExistence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningSmoothSolution_of_parabolicGaugeLocalExistence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningSmoothSolution_of_parabolicGaugeLocalExistence ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningSmoothSolution_of_parabolicGaugeLocalExistence

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem curveShorteningLocalExistence_of_parabolicGaugeLocalExistence [I.Boundaryless]
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (h : curveShorteningParabolicGaugeLocalExistence (I := I) (M := M) B) :
    curveShorteningLocalExistence (I := I) (M := M) B :=
  curveShorteningLocalExistence_of_smoothSolution B
    (curveShorteningSmoothSolution_of_parabolicGaugeLocalExistence B h)
    curveShorteningImmersedPersistence

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalExistence_of_parabolicGaugeLocalExistence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalExistence_of_parabolicGaugeLocalExistence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalExistence_of_parabolicGaugeLocalExistence ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalExistence_of_parabolicGaugeLocalExistence

theorem curveShorteningParabolicGaugeLocalExistence_of_finrank_eq_one [I.Boundaryless]
    (hE : Module.finrank ℝ E = 1)
    (B : SmoothMetricWindow (I := I) (M := M) D a b) :
    curveShorteningParabolicGaugeLocalExistence (I := I) (M := M) B := by
  intro t₀ ht₀ c₀
  let J : Set ℝ := _root_.Set.Icc t₀ (t₀ + (b - t₀))
  refine ⟨b - t₀, sub_pos.mpr ht₀.2, by linarith, staticCurve c₀.map, ?_, ?_, ?_⟩
  · exact staticCurve_smoothOn c₀.map c₀.smooth J
  · intro z
    rfl
  · intro x t ht
    have hc : (staticCurve c₀.map).SmoothOn (I := I) J :=
      staticCurve_smoothOn c₀.map c₀.smooth J
    have hi : (staticCurve c₀.map).ImmersedOn (I := I) J :=
      staticCurve_immersedOn c₀.map J c₀.immersed
    have hpar := parabolic_gauge_velocity (I := I) B.family.metric (staticCurve c₀.map)
      hc hi x t ht
    rw [staticCurve_velocity]
    calc
      0 = (staticCurve c₀.map).curvatureVector B.family.metric x t :=
        (curvatureVector_eq_zero_of_finrank_eq_one hE B.family.metric hc hi ht).symm
      _ = (staticCurve c₀.map).speed B.family.metric x t ^ (-2 : ℤ) •
            (staticCurve c₀.map).Dx B.family.metric (staticCurve c₀.map).X x t -
          (deriv (fun y => (staticCurve c₀.map).speed B.family.metric y t) x /
            (staticCurve c₀.map).speed B.family.metric x t ^ 3) •
            (staticCurve c₀.map).X x t := by
        rw [hpar.2]
        abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningParabolicGaugeLocalExistence_of_finrank_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningParabolicGaugeLocalExistence_of_finrank_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningParabolicGaugeLocalExistence_of_finrank_eq_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningParabolicGaugeLocalExistence_of_finrank_eq_one

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
