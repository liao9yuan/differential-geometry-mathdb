import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.CompactSupportVariation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.SmoothSolutions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Set _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

theorem forward_uniqueness_cutoff_energy_hasDerivAt
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport (χ : M → ℝ))
    {a b : ℝ}
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (_root_.Set.Ico a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (_root_.Set.Ico a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet))
    (hpde₁ : ∀ t ∈ _root_.Set.Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (_root_.Set.Ici a) t)
    (hpde₂ : ∀ t ∈ _root_.Set.Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (_root_.Set.Ici a) t)
    {t : ℝ} (ht : t ∈ _root_.Set.Ioo a b) :
    HasDerivAt
      (fun s => ∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ s x
        ∂riemannianMeasureFamily g₁ s)
      (∫ x, χ x ^ 2 *
        (forwardUniqueDensityDot (I := I) g₁ g₂
          (connSpeed (I := I) g₁ g₂ (forwardUniquenessAvec (I := I) g₁ g₂))
          (rmSpeed (I := I) g₁ g₂ (forwardUniquenessSvec (I := I) g₁ g₂)) t x +
          (1 / 2) * traceTimeDerivMetric (I := I) g₁ t x *
            forwardUniqueDensity (I := I) g₁ g₂ t x)
        ∂riemannianMeasureFamily g₁ t) t := by
  have hab : a < b := ht.1.trans ht.2
  have hg₁ (α : M) (i j : Fin (Module.finrank ℝ E)) :=
    (hjoint₁ α i j).mono (Set.prod_mono _root_.Set.Ioo_subset_Ico_self Subset.rfl)
  have hg₂ (α : M) (i j : Fin (Module.finrank ℝ E)) :=
    (hjoint₂ α i j).mono (Set.prod_mono _root_.Set.Ioo_subset_Ico_self Subset.rfl)
  have hS₁ := forwardUniquenessIsSolution (I := I) g₁ hab hjoint₁ hpde₁
  have hS₂ := forwardUniquenessIsSolution (I := I) g₂ hab hjoint₂ hpde₂
  have hdens (x : M) := density_hasDerivAt (I := I) g₁ g₂
    (connSpeed (I := I) g₁ g₂ (forwardUniquenessAvec (I := I) g₁ g₂))
    (rmSpeed (I := I) g₁ g₂ (forwardUniquenessSvec (I := I) g₁ g₂))
    (fun X Y => pde_hasDerivAt (I := I) g₁ hpde₁ ht x X Y)
    (fun X Y => pde_hasDerivAt (I := I) g₂ hpde₂ ht x X Y)
    (connSpeed_hasDerivAt (I := I) g₁ g₂ (forwardUniquenessAvec (I := I) g₁ g₂)
      (pde_hasDerivAt (I := I) g₁ hpde₁ ht x)
      (forwardUniquenessGamma (I := I) g₁ g₂ hab hjoint₁ hjoint₂ hpde₁ hpde₂ t ht x))
    (rmSpeed_hasDerivAt (I := I) g₁ g₂ (forwardUniquenessSvec (I := I) g₁ g₂)
      (pde_hasDerivAt (I := I) g₁ hpde₁ ht x)
      (forwardUniquenessRm (I := I) g₁ g₂ hS₁ hS₂ hpde₁ hpde₂ t ht x))
  have hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => χ p.2 ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
      (_root_.Set.Ioo a b ×ˢ (_root_.Set.univ : Set M)) :=
    ((χ.contMDiff.comp contMDiff_snd).pow 2).contMDiffOn.mul
      (dens_jointContMDiffOn (I := I) g₁ g₂ hg₁ hg₂)
  have hd := hasDerivAt_integral_riemannianMeasureFamily_of_compact_support
    g₁ isOpen_Ioo hg₁ (fun s x => χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ s x)
    (hf.of_le (by simp)) hχ (fun s _ x hx => by simp [image_eq_zero_of_notMem_tsupport hx]) ht
  convert hd using 1
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  rw [((hdens x).const_mul (χ x ^ 2)).deriv]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_hasDerivAt ``Submission.DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_hasDerivAt

theorem forward_uniqueness_cutoff_energy_hasDerivAt_on_Ioo
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport (χ : M → ℝ))
    {a b : ℝ}
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (_root_.Set.Ioo a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (_root_.Set.Ioo a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet))
    (hpde₁ : ∀ t ∈ _root_.Set.Ioo a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (_root_.Set.Ici a) t)
    (hpde₂ : ∀ t ∈ _root_.Set.Ioo a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (_root_.Set.Ici a) t)
    {t : ℝ} (ht : t ∈ _root_.Set.Ioo a b) :
    HasDerivAt
      (fun s => ∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ s x
        ∂riemannianMeasureFamily g₁ s)
      (∫ x, χ x ^ 2 *
        (forwardUniqueDensityDot (I := I) g₁ g₂
          (connSpeed (I := I) g₁ g₂ (forwardUniquenessAvec (I := I) g₁ g₂))
          (rmSpeed (I := I) g₁ g₂ (forwardUniquenessSvec (I := I) g₁ g₂)) t x +
          (1 / 2) * traceTimeDerivMetric (I := I) g₁ t x *
            forwardUniqueDensity (I := I) g₁ g₂ t x)
        ∂riemannianMeasureFamily g₁ t) t := by
  let a₀ : ℝ := (a + t) / 2
  have haa₀ : a < a₀ := by dsimp only [a₀]; linarith [ht.1]
  have ha₀t : a₀ < t := by dsimp only [a₀]; linarith [ht.1]
  have hsub : _root_.Set.Ico a₀ b ⊆ _root_.Set.Ioo a b := fun s hs => ⟨haa₀.trans_le hs.1, hs.2⟩
  have hpde₁' : ∀ s ∈ _root_.Set.Ico a₀ b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun r => (g₁ r).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ s) x v w) (_root_.Set.Ici a₀) s :=
    fun s hs x v w => (hpde₁ s (hsub hs) x v w).mono fun r hr => haa₀.le.trans hr
  have hpde₂' : ∀ s ∈ _root_.Set.Ico a₀ b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun r => (g₂ r).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ s) x v w) (_root_.Set.Ici a₀) s :=
    fun s hs x v w => (hpde₂ s (hsub hs) x v w).mono fun r hr => haa₀.le.trans hr
  exact forward_uniqueness_cutoff_energy_hasDerivAt (I := I) g₁ g₂ χ hχ
    (fun α i j => (hjoint₁ α i j).mono (Set.prod_mono hsub Subset.rfl))
    (fun α i j => (hjoint₂ α i j).mono (Set.prod_mono hsub Subset.rfl))
    hpde₁' hpde₂' ⟨ha₀t, ht.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_hasDerivAt_on_Ioo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_hasDerivAt_on_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_hasDerivAt_on_Ioo ``Submission.DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_hasDerivAt_on_Ioo

end DifferentialGeometry.PDE.RicciFlow
