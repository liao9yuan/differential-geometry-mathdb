import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.BoundaryIsotopy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
  [hNonempty : Nonempty M] [SigmaCompactSpace M]
  {a b : ℝ}

namespace CurveMap

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] hBoundary hT2 hCompact
  hNonempty [SigmaCompactSpace M] in
theorem smoothOn_mono {c : CurveMap M} {J J' : Set ℝ} (h : c.SmoothOn (I := I) J)
    (hsub : J' ⊆ J) : c.SmoothOn (I := I) J' :=
  h.mono fun _ hp => ⟨hp.1, hsub hp.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.smoothOn_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.smoothOn_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.smoothOn_mono ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.smoothOn_mono

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] hBoundary hT2 hCompact
  hNonempty [SigmaCompactSpace M] in
theorem immersedOn_mono {c : CurveMap M} {J J' : Set ℝ} (h : c.ImmersedOn (I := I) J)
    (hsub : J' ⊆ J) : c.ImmersedOn (I := I) J' :=
  fun x t ht => h x t (hsub ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.immersedOn_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.immersedOn_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.immersedOn_mono ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.immersedOn_mono

end CurveMap

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
def HasBoundaryIsotopyVelocityExtension (a b : ℝ) : Prop :=
  ∀ γ : ℝ → ContinuousFreeLoop M,
    (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b) →
    (curveOfLoopFamily γ).ImmersedOn (I := I) (_root_.Set.Icc a b) →
    (∀ t ∈ _root_.Set.Icc a b, Topology.IsEmbedding (γ t)) →
    LoopFamilyVelocityExtension (I := I) a b γ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.HasBoundaryIsotopyVelocityExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.HasBoundaryIsotopyVelocityExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.HasBoundaryIsotopyVelocityExtension ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.HasBoundaryIsotopyVelocityExtension

omit [CompleteSpace E] hNonempty in
theorem rfs_csf_boundary_isotopy_of_hasBoundaryIsotopyVelocityExtension
    (hfront : HasBoundaryIsotopyVelocityExtension (I := I) (M := M) a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (_root_.Set.Icc a b))
    (hemb : ∀ t ∈ _root_.Set.Icc a b, Topology.IsEmbedding (γ t))
    (t₀ : ℝ) (ht₀ : t₀ ∈ _root_.Set.Icc a b) (hab : a < b) :
    ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : M × ℝ => Φ p.2 p.1)
        (_root_.Set.univ ×ˢ (_root_.Set.Icc a b ∩ _root_.Set.Ioo (t₀ - ε) (t₀ + ε))) ∧
      (∀ p, Φ t₀ p = p) ∧
      ∀ t ∈ _root_.Set.Icc a b ∩ _root_.Set.Ioo (t₀ - ε) (t₀ + ε), ∀ z, Φ t (γ t₀ z) = γ t z := by
  let _ := hab
  exact rfs_csf_boundary_isotopy_of_velocityExtension a b γ t₀ ht₀
    (hfront γ hγ hi hemb)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_boundary_isotopy_of_hasBoundaryIsotopyVelocityExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_boundary_isotopy_of_hasBoundaryIsotopyVelocityExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_boundary_isotopy_of_hasBoundaryIsotopyVelocityExtension ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_boundary_isotopy_of_hasBoundaryIsotopyVelocityExtension

omit [CompleteSpace E] hNonempty in
theorem rfs_csf_boundary_isotopy_of_hasBoundaryIsotopyVelocityExtension_subset
    {α β : ℝ} (hfront : HasBoundaryIsotopyVelocityExtension (I := I) (M := M) a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc α β))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (_root_.Set.Icc α β))
    (hemb : ∀ t ∈ _root_.Set.Icc α β, Topology.IsEmbedding (γ t))
    (ha : α ≤ a) (hb : b ≤ β)
    (t₀ : ℝ) (ht₀ : t₀ ∈ _root_.Set.Icc a b) (hab : a < b) :
    ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : M × ℝ => Φ p.2 p.1)
        (_root_.Set.univ ×ˢ (_root_.Set.Icc a b ∩ _root_.Set.Ioo (t₀ - ε) (t₀ + ε))) ∧
      (∀ p, Φ t₀ p = p) ∧
      ∀ t ∈ _root_.Set.Icc a b ∩ _root_.Set.Ioo (t₀ - ε) (t₀ + ε), ∀ z, Φ t (γ t₀ z) = γ t z :=
  rfs_csf_boundary_isotopy_of_hasBoundaryIsotopyVelocityExtension (I := I) (M := M)
    hfront γ (CurveMap.smoothOn_mono hγ (_root_.Set.Icc_subset_Icc ha hb))
    (CurveMap.immersedOn_mono hi (_root_.Set.Icc_subset_Icc ha hb))
    (fun t ht => hemb t (_root_.Set.Icc_subset_Icc ha hb ht)) t₀ ht₀ hab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_boundary_isotopy_of_hasBoundaryIsotopyVelocityExtension_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_boundary_isotopy_of_hasBoundaryIsotopyVelocityExtension_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_boundary_isotopy_of_hasBoundaryIsotopyVelocityExtension_subset ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_boundary_isotopy_of_hasBoundaryIsotopyVelocityExtension_subset

omit [CompleteSpace E] hNonempty in
theorem rfs_csf_boundary_isotopy_of_constantLoopFamily
    (γ : ℝ → ContinuousFreeLoop M) (hconst : ∀ t t' : ℝ, γ t = γ t')
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (_root_.Set.Icc a b))
    (hemb : ∀ t ∈ _root_.Set.Icc a b, Topology.IsEmbedding (γ t))
    (t₀ : ℝ) (ht₀ : t₀ ∈ _root_.Set.Icc a b) (hab : a < b) :
    ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : M × ℝ => Φ p.2 p.1)
        (_root_.Set.univ ×ˢ (_root_.Set.Icc a b ∩ _root_.Set.Ioo (t₀ - ε) (t₀ + ε))) ∧
      (∀ p, Φ t₀ p = p) ∧
      ∀ t ∈ _root_.Set.Icc a b ∩ _root_.Set.Ioo (t₀ - ε) (t₀ + ε), ∀ z, Φ t (γ t₀ z) = γ t z := by
  let _ := hγ
  let _ := hi
  let _ := hemb
  let _ := hab
  exact rfs_csf_boundary_isotopy_of_velocityExtension a b γ t₀ ht₀
    (loopFamilyVelocityExtension_zero a b γ hconst)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_boundary_isotopy_of_constantLoopFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_boundary_isotopy_of_constantLoopFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_boundary_isotopy_of_constantLoopFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_boundary_isotopy_of_constantLoopFamily

omit [CompleteSpace E] hCompact hNonempty [SigmaCompactSpace M] in
theorem loopFamilyVelocityExtension_of_compactSupportFlow
    (γ₀ : ContinuousFreeLoop M) (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v)) (a b : ℝ) :
    LoopFamilyVelocityExtension (I := I) a b
      (fun t : ℝ =>
        (⟨fun x : M => Diffeomorph.compactSupportFlow v hv hsupp t x,
          (Diffeomorph.contMDiff_compactSupportFlow v hv hsupp).continuous.comp
            (continuous_const.prodMk continuous_id)⟩ : C(M, M)).comp γ₀) := by
  refine ⟨fun _ p => v p, hv.comp contMDiff_snd, ?_, ?_⟩
  · intro t _ z
    exact ((Diffeomorph.isMIntegralCurve_compactSupportFlow v hv hsupp (γ₀ z)) t).hasMFDerivWithinAt
  · intro t _ z
    exact ((Diffeomorph.isMIntegralCurve_compactSupportFlow v hv hsupp (γ₀ z)) t).hasMFDerivWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_of_compactSupportFlow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_of_compactSupportFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_of_compactSupportFlow ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_of_compactSupportFlow

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
