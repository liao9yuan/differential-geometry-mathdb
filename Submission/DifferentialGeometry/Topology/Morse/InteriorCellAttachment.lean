import Submission.DifferentialGeometry.Topology.Morse.Attachment.ModelCell
import Submission.DifferentialGeometry.Topology.Morse.CellAttachment
import Submission.DifferentialGeometry.Topology.Morse.ModelTransport
import Submission.DifferentialGeometry.Topology.Morse.SublevelRestriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Topology.Morse
open _root_.Submission.DifferentialGeometry.Topology.Homotopy
namespace DifferentialGeometry.Morse
variable {m : ℕ} {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]


theorem one_critical_point_cell_attachment_of_interiorSublevel
    (e : E ≃L[ℝ] MorseModel (m + 1))
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) (k : ℕ) (hk : k ≤ m + 1)
    (hnd : IsNondegenerateCriticalPointAt I f p)
    (hindex : sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y))
      (extChartAt I p p)) = k)
    (a : ℝ) (ha : 0 < a)
    (hcompact : IsCompact (f ⁻¹' _root_.Set.Icc (f p - a) (f p + a)))
    (hunique : ∀ x, f x ∈ _root_.Set.Icc (f p - a) (f p + a) →
      x = p ∨ ¬ IsCriticalPointAt I f x)
    (hinterior : sublevel f (f p + a) ⊆ I.interior M) :
    ∃ ε : ℝ, ∃ hε : 0 < ε, ε ≤ a ∧
      ∃ φ : C(CellBoundary k, SublevelSpace f (f p - ε)),
        Nonempty (HomotopyEquivUnder
          (sublevelInclusion f (show f p - ε ≤ f p + ε by linarith))
          (ContinuousMap.mk (adjunctionLower (i := cellBoundaryInclusion k) φ)
            (continuous_adjunctionLower (i := cellBoundaryInclusion k) φ))) := by
  let _ : FiniteDimensional ℝ E := e.symm.toLinearEquiv.finiteDimensional
  let _ : SecondCountableTopology H := I.secondCountableTopology
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞ (by simp) (M := M)
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  have hp : I.IsInteriorPoint p := hinterior (show f p ≤ f p + a by linarith)
  let q : U := ⟨p, hp⟩
  let g : U → ℝ := fun x => f x
  have hgold : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hf.comp contMDiff_subtype_val
  have hndold : IsNondegenerateCriticalPointAt I g q :=
    (isNondegenerateCriticalPointAt_openRestriction I hf q hp).mpr hnd
  let _ := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _ : IsManifold 𝓘(ℝ, E) ∞ U := DifferentialGeometry.Manifold.interiorIsManifold I ∞
  have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g :=
    hgold.comp (DifferentialGeometry.Manifold.contMDiff_interiorAtlas_id I ∞)
  have hndself : IsNondegenerateCriticalPointAt 𝓘(ℝ, E) g q :=
    (isNondegenerateCriticalPointAt_interiorAtlas I hgold q).mpr hndold
  let J := (𝓘(ℝ, E)).transContinuousLinearEquiv e
  let _ : J.Boundaryless := ⟨by
    rw [ModelWithCorners.transContinuousLinearEquiv_range,
      ModelWithCorners.range_eq_univ, _root_.Set.image_univ]
    exact e.surjective.range_eq⟩
  have hgJ : ContMDiff J 𝓘(ℝ, ℝ) ∞ g := by simpa [J] using hg
  have hndJ : IsNondegenerateCriticalPointAt J g q :=
    (isNondegenerateCriticalPointAt_transContinuousLinearEquiv_iff
      𝓘(ℝ, E) e hg BoundarylessManifold.isInteriorPoint).mpr hndself
  have hindexself : sigNeg (chartHessianAt (fun y => g ((extChartAt 𝓘(ℝ, E) q).symm y))
      (extChartAt 𝓘(ℝ, E) q q)) = k := by
    have hQ₁ := chartHessianAt_openRestriction I U f q
    have hQ₂ := chartHessianAt_interiorAtlas I g q
    exact (congrArg sigNeg (hQ₂.trans hQ₁)).trans hindex
  have hindexJ : sigNeg (chartHessianAt (fun y => g ((extChartAt J q).symm y))
      (extChartAt J q q)) = k :=
    (sigNeg_chartHessianAt_transContinuousLinearEquiv 𝓘(ℝ, E) e hg
      BoundarylessManifold.isInteriorPoint hndself.1).trans hindexself
  have hcompactg : IsCompact (g ⁻¹' _root_.Set.Icc (g q - a) (g q + a)) := by
    apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hcompact
    intro x hx
    exact ⟨⟨x, hinterior hx.2⟩, rfl⟩
  have huniqueg : ∀ x : U, g x ∈ _root_.Set.Icc (g q - a) (g q + a) →
      x = q ∨ ¬ IsCriticalPointAt J g x := by
    intro x hx
    rcases hunique x hx with he | hc
    · exact Or.inl (Subtype.ext he)
    · right
      intro hxJ
      have hxs := (isCriticalPointAt_transContinuousLinearEquiv_iff
        𝓘(ℝ, E) e g x).mp hxJ
      have hxo := (isCriticalPointAt_interiorAtlas I hgold x).mp hxs
      exact hc ((isCriticalPointAt_openRestriction I hf x x.property).mp hxo)
  obtain ⟨ε, hε, hεa, φ, ⟨hφ⟩⟩ := one_critical_point_cell_attachment
    J g hgJ q k hk hndJ hindexJ a ha hcompactg huniqueg
  have hlo : sublevel f (f p - ε) ⊆ (U : Set M) := by
    intro x hx
    apply hinterior
    change f x ≤ f p - ε at hx
    change f x ≤ f p + a
    linarith
  have hup : sublevel f (f p + ε) ⊆ (U : Set M) := by
    intro x hx
    apply hinterior
    change f x ≤ f p + ε at hx
    change f x ≤ f p + a
    linarith
  let ea := sublevelRestrictionHomeomorph (U : Set M) f (f p - ε) hlo
  let φ' : C(CellBoundary k, SublevelSpace f (f p - ε)) :=
    (⟨ea, ea.continuous_toFun⟩ : C(SublevelSpace g (g q - ε), SublevelSpace f (f p - ε))).comp φ
  exact ⟨ε, hε, hεa, φ', ⟨cellAttachmentUnderSublevelRestriction
    (U : Set M) f (by linarith) hlo hup φ hφ⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.one_critical_point_cell_attachment_of_interiorSublevel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.one_critical_point_cell_attachment_of_interiorSublevel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.one_critical_point_cell_attachment_of_interiorSublevel ``Submission.DifferentialGeometry.Morse.one_critical_point_cell_attachment_of_interiorSublevel
end DifferentialGeometry.Morse
