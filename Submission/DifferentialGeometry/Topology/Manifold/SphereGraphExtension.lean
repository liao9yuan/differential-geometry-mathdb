import Mathlib.Geometry.Manifold.Instances.Sphere
import Submission.DifferentialGeometry.Geometry.Metric.Cylinder
import Submission.DifferentialGeometry.Topology.Diffeomorph.Flow
import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.ForwardIntegralCurveUniqueness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }
private abbrev Cylinder := S2 × ℝ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Cylinder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Cylinder target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

private def verticalGraphField (h : S2 → ℝ) (χ : ℝ → ℝ) (p : Cylinder) : TangentSpace IC p :=
  (χ p.2 * h p.1) • DifferentialGeometry.Geometry.Metric.cylinderAxis p

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.verticalGraphField
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.verticalGraphField target :: scope.openDecls } }

private theorem verticalGraphField_smooth (h : S2 → ℝ) (hh : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ h)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    ContMDiff IC IC.tangent ∞ (fun p => (⟨p, verticalGraphField h χ p⟩ : TangentBundle IC Cylinder)) :=
  ((hχ.contMDiff.comp contMDiff_snd).mul (hh.comp contMDiff_fst)).smul_section
    DifferentialGeometry.Geometry.Metric.contMDiff_cylinderAxis

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.verticalGraphField_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.verticalGraphField_smooth target :: scope.openDecls } }

private theorem verticalGraphField_hasCompactSupport (h : S2 → ℝ) (χ : ℝ → ℝ)
    (hχ : HasCompactSupport χ) : HasCompactSupport (verticalGraphField h χ) := by
  apply HasCompactSupport.intro (isCompact_univ.prod hχ)
  intro p hp
  have hnot : p.2 ∉ tsupport χ := fun hx => hp ⟨mem_univ _, hx⟩
  simp only [verticalGraphField, image_eq_zero_of_notMem_tsupport hnot, _root_.MulZeroClass.zero_mul, zero_smul]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.verticalGraphField_hasCompactSupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.verticalGraphField_hasCompactSupport target :: scope.openDecls } }

private theorem graph_path_integralCurve
    (h : S2 → ℝ) (χ : ℝ → ℝ) (p : S2) (z : ℝ)
    (hχ : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, χ (z + t * h p) = 1) :
    IsMIntegralCurveOn (fun t => (p, z + t * h p)) (verticalGraphField h χ) (_root_.Set.Icc (0 : ℝ) 1) := by
  intro t ht
  have hd : HasDerivAt (fun t : ℝ => z + t * h p) (h p) t := by
    convert (hasDerivAt_const t z).add ((hasDerivAt_id t).mul_const (h p)) using 1 <;> first | rfl | simp
  have hp := (hasMFDerivAt_const (I := 𝓘(ℝ)) (I' := (𝓡 2)) p t).prodMk hd.hasFDerivAt.hasMFDerivAt
  apply hp.hasMFDerivWithinAt.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  simp only [verticalGraphField, hχ t ht, one_mul]
  change ℝ at r
  change ((0 : EuclideanSpace ℝ (Fin 2)), r * h p) = r • (h p • ((0 : EuclideanSpace ℝ (Fin 2)), (1 : ℝ)))
  ext <;> simp [smul_eq_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.graph_path_integralCurve
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.graph_path_integralCurve target :: scope.openDecls } }

theorem exists_supported_diffeomorph_eq_graph_shear
    (h : S2 → ℝ) (hh : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ h)
    (K : Set Cylinder) (hK : IsCompact K) (l u : ℝ)
    (htrack : ∀ p ∈ K, ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, l < p.2 + t * h p.1 ∧ p.2 + t * h p.1 < u) :
    ∃ F : Cylinder ≃ₘ⟮IC, IC⟯ Cylinder,
      (∀ p ∈ K, F p = (p.1, p.2 + h p.1)) ∧
      ∃ S : Set Cylinder, IsCompact S ∧ S ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioo l u ∧
        EqOn F id Sᶜ ∧ _root_.Set.EqOn F.symm id Sᶜ := by
  let B := (fun q : ℝ × Cylinder => q.2.2 + q.1 * h q.2.1) '' (_root_.Set.Icc (0 : ℝ) 1 ×ˢ K)
  have hB : IsCompact B := (isCompact_Icc.prod hK).image
    (continuous_snd.snd.add (continuous_fst.mul (hh.continuous.comp continuous_snd.fst)))
  have hBU : B ⊆ _root_.Set.Ioo l u := by
    rintro y ⟨q, hq, rfl⟩
    exact htrack q.2 hq.2 q.1 hq.1
  obtain ⟨χ, hχ, hcχ, hχone, hχsupp, _⟩ := DifferentialGeometry.Analysis.exists_bump_compact hB isOpen_Ioo hBU
  let V := verticalGraphField h χ
  have hV := verticalGraphField_smooth h hh χ hχ
  have hVc := verticalGraphField_hasCompactSupport h χ hcχ
  let F := Diffeomorph.compactSupportFlow V hV hVc 1
  have hVs : tsupport V ⊆ _root_.Set.univ ×ˢ tsupport χ := by
    apply closure_minimal _ (isClosed_univ.prod isClosed_closure)
    intro p hp
    refine ⟨mem_univ _, ?_⟩
    by_contra hn
    apply hp
    simp only [V, verticalGraphField, image_eq_zero_of_notMem_tsupport hn, _root_.MulZeroClass.zero_mul, zero_smul]
    rfl
  refine ⟨F, ?_, tsupport V, hVc, hVs.trans (_root_.Set.prod_mono subset_rfl hχsupp),
    (Diffeomorph.compactSupportFlow_eqOn_compl_tsupport V hV hVc 1).1,
    (Diffeomorph.compactSupportFlow_eqOn_compl_tsupport V hV hVc 1).2⟩
  intro p hp
  have hχtrack : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, χ (p.2 + t * h p.1) = 1 := by
    intro t ht
    have hmem : p.2 + t * h p.1 ∈ B := ⟨(t, p), ⟨ht, hp⟩, rfl⟩
    exact Filter.EventuallyEq.eq_of_nhds (hχone.filter_mono (nhds_le_nhdsSet hmem))
  have hpath := graph_path_integralCurve h χ p.1 p.2 hχtrack
  have hflow := (Diffeomorph.isMIntegralCurve_compactSupportFlow V hV hVc p).isMIntegralCurveOn (_root_.Set.Icc (0 : ℝ) 1)
  have heq := DifferentialGeometry.Analysis.ODE.isMIntegralCurveOn_Icc_eqOn_left_of_contMDiff
    (hV.of_le (by simp)) hflow hpath (by erw [Diffeomorph.compactSupportFlow_zero]; simp)
  simpa only [one_mul] using heq (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_graph_shear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_graph_shear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_graph_shear ``Submission.DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_graph_shear


theorem exists_supported_diffeomorph_eq_graph_collar
    (h : S2 → ℝ) (hh : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ h)
    (a r l u : ℝ)
    (ha : l < a - r ∧ a + r < u)
    (hhull : ∀ p : S2, l < a - r + h p ∧ a + r + h p < u) :
    ∃ F : Cylinder ≃ₘ⟮IC, IC⟯ Cylinder,
      (∀ (p : S2) (s : ℝ), |s| ≤ r → F (p, a + s) = (p, a + s + h p)) ∧
      ∃ S : Set Cylinder, IsCompact S ∧ S ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioo l u ∧
        EqOn F id Sᶜ ∧ _root_.Set.EqOn F.symm id Sᶜ := by
  obtain ⟨F, hF, S, hS, hSU, hfix, hfixi⟩ :=
    exists_supported_diffeomorph_eq_graph_shear h hh (_root_.Set.univ ×ˢ _root_.Set.Icc (a - r) (a + r))
      (isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc) l u (by
        rintro p ⟨_, hp⟩ t ht
        have hp0 : p.2 ∈ _root_.Set.Ioo l u := ⟨ha.1.trans_le hp.1, hp.2.trans_lt ha.2⟩
        have hp1 : p.2 + h p.1 ∈ _root_.Set.Ioo l u := by
          constructor <;> linarith [(hhull p.1).1, (hhull p.1).2, hp.1, hp.2]
        have hconv := convex_Ioo l u hp0 hp1 (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
        have heq : (1 - t) • p.2 + t • (p.2 + h p.1) = p.2 + t * h p.1 := by
          simp only [smul_eq_mul]
          ring
        exact heq ▸ hconv)
  refine ⟨F, ?_, S, hS, hSU, hfix, hfixi⟩
  intro p s hs
  exact hF (p, a + s) ⟨mem_univ _, by
    constructor <;> linarith [(abs_le.mp hs).1, (abs_le.mp hs).2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_graph_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_graph_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_graph_collar ``Submission.DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_graph_collar

end DifferentialGeometry.Topology.Manifold
