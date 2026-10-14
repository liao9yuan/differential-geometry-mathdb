import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.TerminalEndpoint
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ContinuationFrontier
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolutionCorrespondence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {D : RealTimeInterval} {a b : ℝ}

namespace ProductCurve

def LocalExistence (B : SmoothMetricWindow (I := I) (M := M) D a b) (lambda : ℝ) : Prop :=
  ∀ t₀ ∈ _root_.Set.Ico a b, ∀ c₀ : ProductCurve M, c₀.SmoothOn (I := I) {t₀} →
    c₀.ImmersedOn (I := I) {t₀} →
    ∃ τ > 0, t₀ + τ ≤ b ∧ ∃ c : ProductCurve M,
      c.IsSolutionOn (I := I) B.family.metric lambda (_root_.Set.Icc t₀ (t₀ + τ)) ∧
      ∀ z, c.map z t₀ = c₀.map z t₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.LocalExistence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.LocalExistence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.LocalExistence ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.LocalExistence

def TerminalClosure [T2Space M]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) : Prop :=
  ∀ (T : ℝ), a < T → T ≤ b → ∀ (c : ProductCurve M) (K : ℝ), 0 ≤ K →
    c.IsSolutionOn (I := I) B.family.metric lambda (_root_.Set.Ico a T) →
    (∀ x t, t ∈ _root_.Set.Ico a T → c.curvature (I := I) B.family.metric lambda x t ≤ K) →
    ∃ closed : ProductCurve M,
      closed.IsSolutionOn (I := I) B.family.metric lambda (_root_.Set.Icc a T) ∧
      ∀ z t, t ∈ _root_.Set.Ico a T → closed.map z t = c.map z t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.TerminalClosure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.TerminalClosure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.TerminalClosure ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.TerminalClosure

def Extension [T2Space M]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) : Prop :=
  ∀ (T : ℝ), a < T → T < b → ∀ (c : ProductCurve M) (K : ℝ), 0 ≤ K →
    c.IsSolutionOn (I := I) B.family.metric lambda (_root_.Set.Ico a T) →
    (∀ x t, t ∈ _root_.Set.Ico a T → c.curvature (I := I) B.family.metric lambda x t ≤ K) →
    ∃ τ > 0, T + τ ≤ b ∧ ∃ extended : ProductCurve M,
      extended.IsSolutionOn (I := I) B.family.metric lambda (_root_.Set.Icc a (T + τ)) ∧
      ∀ z t, t ∈ _root_.Set.Ico a T → extended.map z t = c.map z t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Extension ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Extension

def Continuation [T2Space M]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) : Prop :=
  ∀ (T : ℝ), a < T → T ≤ b → ∀ (c : ProductCurve M) (K : ℝ), 0 ≤ K →
    c.IsSolutionOn (I := I) B.family.metric lambda (_root_.Set.Ico a T) →
    (∀ x t, t ∈ _root_.Set.Ico a T → c.curvature (I := I) B.family.metric lambda x t ≤ K) →
    (∃ closed : ProductCurve M,
        closed.IsSolutionOn (I := I) B.family.metric lambda (_root_.Set.Icc a T) ∧
        ∀ z t, t ∈ _root_.Set.Ico a T → closed.map z t = c.map z t) ∧
      (T < b → ∃ τ > 0, T + τ ≤ b ∧ ∃ extended : ProductCurve M,
        extended.IsSolutionOn (I := I) B.family.metric lambda (_root_.Set.Icc a (T + τ)) ∧
        ∀ z t, t ∈ _root_.Set.Ico a T → extended.map z t = c.map z t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Continuation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Continuation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Continuation ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Continuation

theorem continuation_iff_terminalClosure_and_extension [T2Space M]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) :
    Continuation B lambda ↔ TerminalClosure B lambda ∧ Extension B lambda := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro T haT hTb c K hK hc hcurv
      exact (h T haT hTb c K hK hc hcurv).1
    · intro T haT hTb c K hK hc hcurv
      exact (h T haT hTb.le c K hK hc hcurv).2 hTb
  · rintro ⟨hclose, hext⟩ T haT hTb c K hK hc hcurv
    exact ⟨hclose T haT hTb c K hK hc hcurv,
      fun hlt => hext T haT hlt c K hK hc hcurv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.continuation_iff_terminalClosure_and_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.continuation_iff_terminalClosure_and_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.continuation_iff_terminalClosure_and_extension ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.continuation_iff_terminalClosure_and_extension

omit [CompleteSpace E] in
theorem map_curvature_eq (c : ProductCurve M) (A : QuotientProductAtlas I M) [T2Space M]
    [I.Boundaryless] (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (hU : (c.unitTangent g lambda).SmoothOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.curvature (I := I.prod 𝓘(ℝ, ℝ))
        (fun s => quotientProductMetric A (g s) lambda hlambda) x t =
      c.curvature (I := I) g lambda x t := by
  let := A.charts
  let := A.smoothManifold
  have hvec := c.map_curvatureVector_eq (I := I) A g lambda hlambda hc hU x t ht
  have hprod : (quotientProductMetric A (g t) lambda hlambda).inner
        (productCoverProjection (M := M) (c.coverLift x t))
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
          (c.coverLift x t) (c.curvatureVector g lambda x t))
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
          (c.coverLift x t) (c.curvatureVector g lambda x t)) =
      c.inner g lambda x t (c.curvatureVector g lambda x t)
        (c.curvatureVector g lambda x t) := by
    refine (localPullMetric_inner (quotientProductMetric A (g t) lambda hlambda)
      (productCoverProjection (M := M)) (isLocalDiffeomorph_productCoverProjection A)
      (c.coverLift x t) (c.curvatureVector g lambda x t)
      (c.curvatureVector g lambda x t)).symm.trans ?_
    rw [quotientProductMetric_localPull A (g t) lambda hlambda,
      coverProductMetric_inner (g t) lambda hlambda (c.coverLift x t)
        (c.curvatureVector g lambda x t) (c.curvatureVector g lambda x t)]
    simp only [ProductCurve.inner]
    rfl
  have hstep := (c.coverProjection_lift x t) ▸ hvec ▸ hprod
  have hsq : c.map.curvatureSq (I := I.prod 𝓘(ℝ, ℝ))
        (fun s => quotientProductMetric A (g s) lambda hlambda) x t =
      c.curvatureSq (I := I) g lambda x t := by
    simp only [ProductCurve.curvatureSq, ProductCurve.normSq, CurveMap.curvatureSq,
      CurveMap.normSq]
    exact hstep
  rw [CurveMap.curvature, ProductCurve.curvature, hsq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.map_curvature_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.map_curvature_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.map_curvature_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.map_curvature_eq

omit [CompleteSpace E] in
theorem localExistence_of_quotientCurveLocalExistence (A : QuotientProductAtlas I M)
    [T2Space M] [I.Boundaryless]
    (B : SmoothMetricWindow (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    ∀ (Bhat : SmoothMetricWindow (I := I.prod 𝓘(ℝ, ℝ))
        (M := M × Surgery.Topology.Circle) D a b),
      Bhat.family.metric =
        (fun t => quotientProductMetric A (B.family.metric t) lambda hlambda) →
      curveShorteningLocalExistence (I := I.prod 𝓘(ℝ, ℝ))
        (M := M × Surgery.Topology.Circle) Bhat →
      LocalExistence B lambda := by
  let := A.charts
  let := A.smoothManifold
  intro Bhat hBhat H t₀ ht₀ c₀ hsm₀ himm₀
  have hmap : c₀.map.SmoothOn (I := I.prod 𝓘(ℝ, ℝ)) {t₀} :=
    c₀.smoothOn_map (I := I) A hsm₀
  have himmMap : c₀.map.ImmersedOn (I := I.prod 𝓘(ℝ, ℝ)) {t₀} :=
    (c₀.map_immersedOn_iff (I := I) A hsm₀).mpr himm₀
  let d₀ : SmoothImmersion (I := I.prod 𝓘(ℝ, ℝ))
      (M := M × Surgery.Topology.Circle) :=
    SmoothImmersion.slice (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle)
      c₀.map hmap himmMap t₀ (by simp)
  obtain ⟨τ, hτ, hτb, c, hc, hinit⟩ := H t₀ ht₀ d₀
  have hc' : c.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
      (fun t => quotientProductMetric A (B.family.metric t) lambda hlambda)
      (_root_.Set.Icc t₀ (t₀ + τ)) := by
    rw [← hBhat]
    exact hc
  have hsu : t₀ < t₀ + τ := by linarith
  obtain ⟨ĉ, hĉsol, hĉmap⟩ := product_solution_lift (I := I) (M := M) A
    (fun t => B.family.metric t) lambda hlambda c hsu (_root_.Set.Icc t₀ (t₀ + τ)) (Or.inr rfl) hc'
  exact ⟨τ, hτ, hτb, ĉ, hĉsol,
    fun z => (hĉmap z t₀ ⟨le_rfl, by linarith⟩).trans (hinit z)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.localExistence_of_quotientCurveLocalExistence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.localExistence_of_quotientCurveLocalExistence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.localExistence_of_quotientCurveLocalExistence ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.localExistence_of_quotientCurveLocalExistence

theorem terminalClosure_of_quotient (A : QuotientProductAtlas I M)
    [T2Space M] [CompactSpace M] [I.Boundaryless]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    ∀ (Bhat : RicciBackground (I := I.prod 𝓘(ℝ, ℝ))
        (M := M × Surgery.Topology.Circle) D a b),
      Bhat.family.metric =
        (fun t => quotientProductMetric A (B.family.metric t) lambda hlambda) →
      TerminalClosure B lambda := by
  let := A.charts
  let := A.smoothManifold
  intro Bhat hBhat T haT hTb c K hK hc hcurv
  have H := curveShorteningTerminalClosure_of_ricciBackground Bhat
  have hU : (c.unitTangent B.family.metric lambda).SmoothOn (I := I) (_root_.Set.Ico a T) :=
    c.field_smoothOn_unitTangent (I := I) B.family.metric lambda hlambda hc.smooth hc.immersed
  have hmap : c.map.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
      (fun t => quotientProductMetric A (B.family.metric t) lambda hlambda) (_root_.Set.Ico a T) :=
    c.map_isSolutionOn_of_interval_of_isSolutionOn (I := I) A B.family.metric lambda hlambda
      haT (Or.inl rfl) hc
  have hcurvMap : ∀ x t, t ∈ _root_.Set.Ico a T →
      c.map.curvature (I := I.prod 𝓘(ℝ, ℝ))
        (fun s => quotientProductMetric A (B.family.metric s) lambda hlambda) x t ≤ K :=
    fun x t ht => by
      rw [c.map_curvature_eq (I := I) A B.family.metric lambda hlambda hc.smooth hU x t ht]
      exact hcurv x t ht
  obtain ⟨closed, hsol, hagr⟩ := H T haT hTb c.map K hK (by rw [hBhat]; exact hmap)
    (fun x t ht => by rw [hBhat]; exact hcurvMap x t ht)
  obtain ⟨ĉ, hĉsol, hĉmap⟩ := product_solution_lift (I := I) (M := M) A
    (fun t => B.family.metric t) lambda hlambda closed haT (_root_.Set.Icc a T) (Or.inr rfl)
    (by rw [← hBhat]; exact hsol)
  exact ⟨ĉ, hĉsol, fun z t ht =>
    (hĉmap z t ⟨ht.1, ht.2.le⟩).trans (hagr z t ht)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.terminalClosure_of_quotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.terminalClosure_of_quotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.terminalClosure_of_quotient ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.terminalClosure_of_quotient

theorem extension_of_quotient (A : QuotientProductAtlas I M)
    [T2Space M] [I.Boundaryless]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    ∀ (Bhat : RicciBackground (I := I.prod 𝓘(ℝ, ℝ))
        (M := M × Surgery.Topology.Circle) D a b),
      Bhat.family.metric =
        (fun t => quotientProductMetric A (B.family.metric t) lambda hlambda) →
      curveShorteningExtension (I := I.prod 𝓘(ℝ, ℝ))
        (M := M × Surgery.Topology.Circle) Bhat →
      Extension B lambda := by
  let := A.charts
  let := A.smoothManifold
  intro Bhat hBhat H T haT hTb c K hK hc hcurv
  have hU : (c.unitTangent B.family.metric lambda).SmoothOn (I := I) (_root_.Set.Ico a T) :=
    c.field_smoothOn_unitTangent (I := I) B.family.metric lambda hlambda hc.smooth hc.immersed
  have hmap : c.map.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
      (fun t => quotientProductMetric A (B.family.metric t) lambda hlambda) (_root_.Set.Ico a T) :=
    c.map_isSolutionOn_of_interval_of_isSolutionOn (I := I) A B.family.metric lambda hlambda
      haT (Or.inl rfl) hc
  have hcurvMap : ∀ x t, t ∈ _root_.Set.Ico a T →
      c.map.curvature (I := I.prod 𝓘(ℝ, ℝ))
        (fun s => quotientProductMetric A (B.family.metric s) lambda hlambda) x t ≤ K :=
    fun x t ht => by
      rw [c.map_curvature_eq (I := I) A B.family.metric lambda hlambda hc.smooth hU x t ht]
      exact hcurv x t ht
  obtain ⟨τ, hτ, hτb, extended, hsol, hagr⟩ := H T haT hTb c.map K hK
    (by rw [hBhat]; exact hmap) (fun x t ht => by rw [hBhat]; exact hcurvMap x t ht)
  have hsu : a < T + τ := by linarith
  obtain ⟨ê, hêsol, hêmap⟩ := product_solution_lift (I := I) (M := M) A
    (fun t => B.family.metric t) lambda hlambda extended hsu (_root_.Set.Icc a (T + τ)) (Or.inr rfl)
    (by rw [← hBhat]; exact hsol)
  exact ⟨τ, hτ, hτb, ê, hêsol, fun z t ht =>
    (hêmap z t ⟨ht.1, by linarith [ht.2, hτ]⟩).trans (hagr z t ht)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.extension_of_quotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.extension_of_quotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.extension_of_quotient ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.extension_of_quotient

theorem continuation_of_quotient (A : QuotientProductAtlas I M)
    [T2Space M] [CompactSpace M] [I.Boundaryless]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    ∀ (Bhat : RicciBackground (I := I.prod 𝓘(ℝ, ℝ))
        (M := M × Surgery.Topology.Circle) D a b),
      Bhat.family.metric =
        (fun t => quotientProductMetric A (B.family.metric t) lambda hlambda) →
      curveShorteningContinuation (I := I.prod 𝓘(ℝ, ℝ))
        (M := M × Surgery.Topology.Circle) Bhat →
      Continuation B lambda := by
  let := A.charts
  let := A.smoothManifold
  intro Bhat hBhat H
  have hsplit := (curveShorteningContinuation_iff_terminalClosure_and_extension
    (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle) Bhat).mp H
  exact (continuation_iff_terminalClosure_and_extension
      (I := I) (M := M) B lambda).mpr
    ⟨terminalClosure_of_quotient (I := I) (M := M) A B lambda hlambda Bhat hBhat,
      extension_of_quotient (I := I) (M := M) A B lambda hlambda Bhat hBhat hsplit.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.continuation_of_quotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.continuation_of_quotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.continuation_of_quotient ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.continuation_of_quotient

end ProductCurve

namespace ProductCurve

variable [IsEmpty M]

omit [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
theorem isEmpty_of_isEmpty : IsEmpty (ProductCurve M) :=
  ⟨fun c => (inferInstance : IsEmpty M).elim (c.map 0 0).1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.isEmpty_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.isEmpty_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.isEmpty_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.isEmpty_of_isEmpty

omit [CompleteSpace E] in
theorem localExistence_of_isEmpty
    (B : SmoothMetricWindow (I := I) (M := M) D a b) (lambda : ℝ) :
    LocalExistence B lambda := by
  intro t₀ ht₀ c₀
  exact ((isEmpty_of_isEmpty : IsEmpty (ProductCurve M)).false c₀).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.localExistence_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.localExistence_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.localExistence_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.localExistence_of_isEmpty

theorem terminalClosure_of_isEmpty [T2Space M]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) :
    TerminalClosure B lambda := by
  intro T haT hTb c
  exact ((isEmpty_of_isEmpty : IsEmpty (ProductCurve M)).false c).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.terminalClosure_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.terminalClosure_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.terminalClosure_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.terminalClosure_of_isEmpty

theorem extension_of_isEmpty [T2Space M]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) :
    Extension B lambda := by
  intro T haT hTb c
  exact ((isEmpty_of_isEmpty : IsEmpty (ProductCurve M)).false c).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.extension_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.extension_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.extension_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.extension_of_isEmpty

theorem continuation_of_isEmpty [T2Space M]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) :
    Continuation B lambda := by
  intro T haT hTb c
  exact ((isEmpty_of_isEmpty : IsEmpty (ProductCurve M)).false c).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.continuation_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.continuation_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.continuation_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.continuation_of_isEmpty

end ProductCurve

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
