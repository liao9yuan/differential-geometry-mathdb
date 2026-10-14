import Submission.DifferentialGeometry.Topology.Morse.SublevelDeformation
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
open _root_.Submission.DifferentialGeometry.Topology.Morse _root_.Submission.DifferentialGeometry.Topology.Homotopy
namespace DifferentialGeometry.Morse
variable {m : ℕ} {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem exists_sublevelHomotopyEquivUnder_of_interiorSublevel
    (e : E ≃L[ℝ] MorseModel (m + 1)) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' _root_.Set.Icc a b))
    (hr : ∀ x ∈ f ⁻¹' _root_.Set.Icc a b, ¬ IsCriticalPointAt I f x)
    (hinterior : sublevel f b ⊆ I.interior M)
    {B : Type*} [TopologicalSpace B] (j : C(B, SublevelSpace f a)) :
    ∃ h : HomotopyEquivUnder ((sublevelInclusion f hab).comp j) j,
      h.invFun = sublevelInclusion f hab := by
  let _ : FiniteDimensional ℝ E := e.symm.toLinearEquiv.finiteDimensional
  let _ : SecondCountableTopology H := I.secondCountableTopology
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞ (by simp) (M := M)
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let g : U → ℝ := fun x => f x
  have hgold : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hf.comp contMDiff_subtype_val
  let _ := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _ : IsManifold 𝓘(ℝ, E) ∞ U := DifferentialGeometry.Manifold.interiorIsManifold I ∞
  have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g :=
    hgold.comp (DifferentialGeometry.Manifold.contMDiff_interiorAtlas_id I ∞)
  let J := (𝓘(ℝ, E)).transContinuousLinearEquiv e
  let _ : J.Boundaryless := ⟨by
    rw [ModelWithCorners.transContinuousLinearEquiv_range,
      ModelWithCorners.range_eq_univ, _root_.Set.image_univ]
    exact e.surjective.range_eq⟩
  have hgJ : ContMDiff J 𝓘(ℝ, ℝ) ∞ g := by simpa [J] using hg
  have hcompactg : IsCompact (g ⁻¹' _root_.Set.Icc a b) := by
    apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hcompact
    intro x hx
    exact ⟨⟨x, hinterior hx.2⟩, rfl⟩
  have hrg : ∀ x ∈ g ⁻¹' _root_.Set.Icc a b, mfderiv J 𝓘(ℝ, ℝ) g x ≠ 0 := by
    intro x hx hc
    have hxs := (isCriticalPointAt_transContinuousLinearEquiv_iff
      𝓘(ℝ, E) e g x).mp hc
    have hxo := (isCriticalPointAt_interiorAtlas I hgold x).mp hxs
    exact hr x hx ((isCriticalPointAt_openRestriction I hf x x.property).mp hxo)
  have hlo : sublevel f a ⊆ (U : Set M) := fun _ hx => hinterior (hx.trans hab)
  let ea := sublevelRestrictionHomeomorph (U : Set M) f a hlo
  let eb := sublevelRestrictionHomeomorph (U : Set M) f b hinterior
  let ja : C(B, SublevelSpace g a) :=
    (⟨ea.symm, ea.symm.continuous_toFun⟩ : C(SublevelSpace f a, SublevelSpace g a)).comp j
  obtain ⟨h, hi⟩ := exists_sublevelHomotopyEquivUnder J hgJ hab hcompactg hrg ja
  let hup := HomotopyEquivUnder.ofHomeomorph
    ((sublevelInclusion f hab).comp j) ((sublevelInclusion g hab).comp ja) eb.symm
    (by ext x; rfl)
  let hlow := HomotopyEquivUnder.ofHomeomorph ja j ea (by ext x; rfl)
  refine ⟨(hup.trans h rfl).trans hlow rfl, ?_⟩
  simp only [HomotopyEquivUnder.trans_invFun, hi]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.exists_sublevelHomotopyEquivUnder_of_interiorSublevel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.exists_sublevelHomotopyEquivUnder_of_interiorSublevel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.exists_sublevelHomotopyEquivUnder_of_interiorSublevel ``Submission.DifferentialGeometry.Morse.exists_sublevelHomotopyEquivUnder_of_interiorSublevel

end DifferentialGeometry.Morse
