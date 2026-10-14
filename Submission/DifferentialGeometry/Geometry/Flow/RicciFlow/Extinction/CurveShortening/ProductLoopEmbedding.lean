import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Product
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Loops
import Submission.DifferentialGeometry.Topology.Embedding.Sphere
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

private theorem isSmoothEmbedding_homeomorphCircle :
    _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (fun z : Surgery.Topology.Circle =>
        (AddCircle.homeomorphCircle one_ne_zero z : ℂ)) := by
  let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by norm_num⟩
  have hc : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 1) ∞ AddCircle.diffeomorphCircle :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
      AddCircle.diffeomorphCircle.isLocalDiffeomorph AddCircle.diffeomorphCircle.injective
  exact (isSmoothEmbedding_coe_sphere (E := ℂ) (n := 1)).comp hc (by simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.isSmoothEmbedding_homeomorphCircle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.isSmoothEmbedding_homeomorphCircle target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def QuotientProductAtlas.smoothLoopEmbedding
    (A : QuotientProductAtlas I M) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    letI := A.charts
    Width.SmoothLoopEmbedding (I := I.prod 𝓘(ℝ, ℝ))
      (Q := M × Surgery.Topology.Circle) (N + 2) := by
  let κ : Surgery.Topology.Circle → ℂ := fun z =>
    (AddCircle.homeomorphCircle one_ne_zero z : ℂ)
  let φ : M × Surgery.Topology.Circle → EuclideanSpace ℝ (Fin N) × ℂ :=
    Prod.map e.map κ
  let L : (EuclideanSpace ℝ (Fin N) × ℂ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (N + 2)) :=
    ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin N))).prodCongr
      Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv).trans
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 2)).symm
  have hκ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ κ :=
    isSmoothEmbedding_homeomorphCircle
  have hκcoe : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (fun t : ℝ => κ (t : Surgery.Topology.Circle)) :=
    hκ.contMDiff.comp AddCircle.contMDiff_coe
  have hκcoe_injective (t : ℝ) : Function.Injective
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
        (fun s : ℝ => κ (s : Surgery.Topology.Circle)) t) := by
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      (κ ∘ fun s : ℝ => (s : Surgery.Topology.Circle)) t)
    rw [mfderiv_comp t (hκ.contMDiff.mdifferentiableAt (by simp))
      (AddCircle.contMDiff_coe.mdifferentiableAt (by simp))]
    exact ((hκ.isImmersion.isImmersionAt (t : Surgery.Topology.Circle)).injective_mfderiv
      (by simp)).comp (AddCircle.bijective_mfderiv_coe t).injective
  have hcover : ContMDiff (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℂ) ∞
      (φ ∘ productCoverProjection (M := M)) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact e.smooth.prodMap hκcoe
  have hcover_injective (p : M × ℝ) : Function.Injective
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℂ)
        (φ ∘ productCoverProjection (M := M)) p) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    change Function.Injective (mfderiv (I.prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin N)).prod 𝓘(ℝ, ℂ))
      (Prod.map e.map (fun t : ℝ => κ (t : Surgery.Topology.Circle))) p)
    rw [mfderiv_prodMap (e.smooth.mdifferentiableAt (by simp))
      (hκcoe.mdifferentiableAt (by simp))]
    intro u v huv
    exact Prod.ext
      (e.injective_mfderiv p.1 (congrArg Prod.fst huv))
      (hκcoe_injective p.2 (congrArg Prod.snd huv))
  letI := A.charts
  letI := A.smoothManifold
  have hφ : ContMDiff (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℂ) ∞ φ :=
    (isLocalDiffeomorph_productCoverProjection A).contMDiff_of_comp_of_surjective
      (surjective_productCoverProjection (M := M)) hcover
  have hφ_injective (q : M × Surgery.Topology.Circle) : Function.Injective
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℂ) φ q) := by
    obtain ⟨p, rfl⟩ := surjective_productCoverProjection (M := M) q
    have h := hcover_injective p
    rw [mfderiv_comp p (hφ.mdifferentiableAt (by simp))
      (A.cover_smooth.mdifferentiableAt (by simp))] at h
    intro u v huv
    obtain ⟨u', rfl⟩ := (A.cover_derivative_bijective p).surjective u
    obtain ⟨v', rfl⟩ := (A.cover_derivative_bijective p).surjective v
    exact congrArg _ (h huv)
  have hclosed : _root_.Topology.IsClosedEmbedding φ :=
    e.isClosedEmbedding.prodMap
      (hκ.contMDiff.continuous.isClosedEmbedding hκ.isEmbedding.injective)
  have hemb : _root_.Manifold.IsSmoothEmbedding (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℂ) ∞ φ :=
    ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv
      (by simp) hφ hφ_injective, hclosed.isEmbedding⟩
  have hLφ := hemb.continuousLinearEquiv_comp L
  exact
    { map := L ∘ φ
      smooth := hLφ.contMDiff
      isClosedEmbedding := L.toHomeomorph.isClosedEmbedding.comp hclosed
      injective_mfderiv := fun q =>
        (hLφ.isImmersion.isImmersionAt q).injective_mfderiv (by simp) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.QuotientProductAtlas.smoothLoopEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.QuotientProductAtlas.smoothLoopEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.QuotientProductAtlas.smoothLoopEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.QuotientProductAtlas.smoothLoopEmbedding

@[simp]
theorem QuotientProductAtlas.smoothLoopEmbedding_map
    (A : QuotientProductAtlas I M) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (q : M × Surgery.Topology.Circle) :
    letI := A.charts
    (A.smoothLoopEmbedding e).map q =
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 2)).symm
        (e.map q.1, Complex.orthonormalBasisOneI.repr
          (AddCircle.homeomorphCircle one_ne_zero q.2 : ℂ)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.QuotientProductAtlas.smoothLoopEmbedding_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.QuotientProductAtlas.smoothLoopEmbedding_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.QuotientProductAtlas.smoothLoopEmbedding_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.QuotientProductAtlas.smoothLoopEmbedding_map

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
