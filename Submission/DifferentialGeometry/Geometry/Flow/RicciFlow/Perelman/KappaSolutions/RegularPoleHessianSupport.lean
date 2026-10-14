import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.UpperSupportTrace
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvatureNormalization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.BigOperators _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

theorem Iic_subset_parabolicInterval_regular_of_neg
    (hreg : D.regular = _root_.Set.Iio 0) {b Q : Real}
    (hb : b < 0) (hQ : 0 < Q) (hbmem : b ∈ D.carrier) :
    Iic (0 : Real) ⊆ (parabolicInterval D b Q hbmem).regular := by
  intro s hs
  change parabolicTime b Q s ∈ D.regular
  rw [hreg]
  exact add_neg_of_neg_of_nonpos hb (div_nonpos_of_nonpos_of_nonneg hs hQ.le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.Iic_subset_parabolicInterval_regular_of_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.Iic_subset_parabolicInterval_regular_of_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.Iic_subset_parabolicInterval_regular_of_neg ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.Iic_subset_parabolicInterval_regular_of_neg

theorem exists_contMDiffOn_curvatureNormalizedSolution_redLength_upper_support_hess_trace_lt
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (hregD : D.regular = _root_.Set.Iio 0) (b Q K : Real)
    (hb : b < 0) (hQ : 0 < Q) (hbmem : b ∈ D.carrier)
    (x : M) {Z : TangentSpace I x} {tau : Real}
    (hmin : (Z, tau) ∈ lMinDomain (parabolicSolution S b Q hQ hbmem) 0 x)
    (hRm : ∀ q ∈ _root_.Set.Icc (b - tau / Q) b, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    let Sraw := parabolicSolution S b Q hQ hbmem
    let Sres := curvatureNormalizedSolution S b Q hQ hbmem
    let y := lExp Sraw 0 x Z tau
    ∃ (P : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (lRegularizedCurve Sraw 0 x Z s)) (Omega : Set Real),
      IsOpen Omega ∧ _root_.Set.Icc (0 : Real) (Real.sqrt tau) ⊆ Omega ∧
      (∀ i, ContMDiffOn 𝓘(Real, Real) I.tangent ∞
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (lRegularizedCurve Sraw 0 x Z s) (P i s) : TangentBundle I M)) Omega) ∧
      (∀ i, IsLAdapted Sraw 0 (lRegularizedCurve Sraw 0 x Z) (P i) Omega) ∧
      (∀ i j, (Sres.base.metric (-tau)).inner y
        (P i (Real.sqrt tau)) (P j (Real.sqrt tau)) = if i = j then 1 else 0) ∧
      ∃ U : Set M, IsOpen U ∧ y ∈ U ∧
        ∃ phi : M → Real, ContMDiffOn I 𝓘(Real, Real) ∞ phi U ∧
          phi y = redLength Sres 0 x y tau ∧
          (∀ y ∈ U, redLength Sres 0 x y tau ≤ phi y) ∧
          gradientFun (I := I) (Sres.base.metric (-tau)) phi
            y = (2 * Real.sqrt tau)⁻¹ •
              lVelocity (I := I) (lRegularizedCurve Sraw 0 x Z) (Real.sqrt tau) ∧
          (∑ i : Fin (Module.finrank Real E),
            hessFun (I := I) (Sres.base.metric (-tau)) phi y
              (P i (Real.sqrt tau)) (P i (Real.sqrt tau))) <
            (1 / 2 : Real) * (Sres.base.metric (-tau)).inner y
              (gradientFun (I := I) (Sres.base.metric (-tau)) phi y)
              (gradientFun (I := I) (Sres.base.metric (-tau)) phi y) -
              (1 / 2 : Real) * Sres.scalar (-tau) y +
              ((Module.finrank Real E : Real) -
                redLength Sres 0 x y tau) / (2 * tau) + epsilon := by
  dsimp only
  let Sraw := parabolicSolution S b Q hQ hbmem
  have hraw : IsSolutionOn (I := I) Sraw :=
    parabolicSolution_isSolutionOn S hS b Q hQ hbmem
  have hreg : _root_.Set.Icc (0 - tau) 0 ⊆ (parabolicInterval D b Q hbmem).regular := by
    intro s hs
    exact Iic_subset_parabolicInterval_regular_of_neg hregD hb hQ hbmem hs.2
  have hRmRaw : ∀ s ∈ _root_.Set.Icc (0 - tau) 0, ∀ z : M,
      normSq0S (I := I) (Sraw.base.metric s) z 4 (Sraw.base.rm04 s z) ≤
        Q⁻¹ ^ 2 * K := by
    intro s hs z
    change normSq0S (I := I)
      ((parabolicSolution S b Q hQ hbmem).base.metric s) z 4
      ((parabolicSolution S b Q hQ hbmem).base.rm04 s z) ≤ _
    rw [parabolicRmNormSq]
    have htime : parabolicTime b Q s ∈ _root_.Set.Icc (b - tau / Q) b := by
      constructor
      · have hlo : -(tau / Q) ≤ s / Q := by
          simpa only [zero_sub, neg_div] using
            div_le_div_of_nonneg_right hs.1 hQ.le
        change b - tau / Q ≤ b + s / Q
        linarith
      · exact add_le_of_nonpos_right
          (div_nonpos_of_nonpos_of_nonneg hs.2 hQ.le)
    exact mul_le_mul_of_nonneg_left (hRm _ htime z) (sq_nonneg _)
  have hscalar : (curvatureNormalizedSolution S b Q hQ hbmem).scalar = Sraw.scalar := rfl
  have hredLength : redLength (curvatureNormalizedSolution S b Q hQ hbmem) =
      redLength Sraw := rfl
  obtain ⟨P, Omega, hOmega, hsegment, hPsm, hDP, hON,
      U, hUopen, hyU, phi, hphism, hcontact, hupper, hgrad, htrace⟩ :=
    exists_contMDiffOn_redLength_upper_support_hess_trace_lt
      (I := I) Sraw hraw (Q⁻¹ ^ 2 * K) 0 x hmin hreg hRmRaw hepsilon
  refine ⟨P, Omega, hOmega, hsegment, hPsm, hDP, ?_,
    U, hUopen, hyU, phi, hphism, hcontact, hupper, ?_, ?_⟩
  · simpa only [curvatureNormalizedSolution, SolutionOn.timeRestrict, Sraw, zero_sub]
      using hON
  · simpa only [curvatureNormalizedSolution, SolutionOn.timeRestrict, Sraw, zero_sub]
      using hgrad
  · rw [hscalar, hredLength]
    simpa only [curvatureNormalizedSolution, SolutionOn.timeRestrict, Sraw, zero_sub]
      using htrace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_contMDiffOn_curvatureNormalizedSolution_redLength_upper_support_hess_trace_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_contMDiffOn_curvatureNormalizedSolution_redLength_upper_support_hess_trace_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_contMDiffOn_curvatureNormalizedSolution_redLength_upper_support_hess_trace_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_contMDiffOn_curvatureNormalizedSolution_redLength_upper_support_hess_trace_lt

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
