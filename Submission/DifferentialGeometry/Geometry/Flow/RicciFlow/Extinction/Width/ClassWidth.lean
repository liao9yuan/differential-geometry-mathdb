import Mathlib.Topology.Sequences
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.LeastArea
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.AreaTransport
import Mathlib.Topology.Order.Compact
import Submission.DifferentialGeometry.Geometry.Metric.Family.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

local instance sphereTwoNonempty : Nonempty (Sphere 2) :=
  (show (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty from
    NormedSpace.sphere_nonempty.mpr (by norm_num)).coe_sort

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.sphereTwoNonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.sphereTwoNonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.sphereTwoNonempty ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.sphereTwoNonempty

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [finiteDimensionalE : FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [boundarylessI : I.Boundaryless]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [t2Q : T2Space Q] [compactQ : CompactSpace Q] [connectedQ : ConnectedSpace Q]

theorem regularFamily_area_bddAbove (g : SmoothRiemannianMetric I Q)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) :
    BddAbove (Set.range (fun k => regularLeastArea g (Γ k))) :=
  (isCompact_range ((continuous_regularLeastArea g).comp Γ.continuous)).bddAbove

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularFamily_area_bddAbove then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularFamily_area_bddAbove"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularFamily_area_bddAbove ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularFamily_area_bddAbove


def familyMaximum (g : SmoothRiemannianMetric I Q)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) : ℝ :=
  _root_.SupSet.sSup (Set.range (fun k => regularLeastArea g (Γ k)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum

theorem regularLeastArea_le_familyMaximum (g : SmoothRiemannianMetric I Q)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) (k : Sphere 2) :
    regularLeastArea g (Γ k) ≤ familyMaximum g Γ :=
  le_csSup (regularFamily_area_bddAbove g Γ) ⟨k, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_le_familyMaximum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_le_familyMaximum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_le_familyMaximum ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_le_familyMaximum


theorem familyMaximum_attained (g : SmoothRiemannianMetric I Q)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) :
    ∃ k : Sphere 2, familyMaximum g Γ = regularLeastArea g (Γ k) := by
  obtain ⟨k, _, hk⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (((continuous_regularLeastArea g).comp Γ.continuous).continuousOn)
  refine ⟨k, le_antisymm ?_ (regularLeastArea_le_familyMaximum g Γ k)⟩
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨p, rfl⟩
  exact hk (Set.mem_univ p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_attained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_attained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_attained ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_attained

theorem familyMaximum_nonneg (g : SmoothRiemannianMetric I Q)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) : 0 ≤ familyMaximum g Γ := by
  obtain ⟨k, hk⟩ := familyMaximum_attained g Γ
  rw [hk]
  exact regularLeastArea_nonneg g (Γ k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_nonneg


def regularAreaMap (g : SmoothRiemannianMetric I Q) :
    C(ContractibleRegularLoop (I := I) (Q := Q), ℝ) :=
  ⟨regularLeastArea g, continuous_regularLeastArea g⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularAreaMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularAreaMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularAreaMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularAreaMap


theorem familyMaximum_eq_norm (g : SmoothRiemannianMetric I Q)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) :
    familyMaximum g Γ = ‖(regularAreaMap g).comp Γ‖ := by
  apply le_antisymm
  · obtain ⟨k, hk⟩ := familyMaximum_attained g Γ
    rw [hk]
    exact (le_abs_self _).trans (((regularAreaMap g).comp Γ).norm_coe_le_norm k)
  · apply (ContinuousMap.norm_le _ (familyMaximum_nonneg g Γ)).mpr
    intro k
    simpa only [ContinuousMap.comp_apply, regularAreaMap, ContinuousMap.coe_mk,
      Real.norm_eq_abs, abs_of_nonneg (regularLeastArea_nonneg g (Γ k))] using
      regularLeastArea_le_familyMaximum g Γ k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_eq_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_eq_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_eq_norm ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_eq_norm


theorem continuous_familyMaximum (g : SmoothRiemannianMetric I Q) :
    Continuous (familyMaximum g : RegularFamily (I := I) (Q := Q) (Sphere 2) → ℝ) := by
  have h : Continuous (fun Γ : RegularFamily (I := I) (Q := Q) (Sphere 2) =>
      ‖(regularAreaMap g).comp Γ‖) :=
    continuous_norm.comp (ContinuousMap.continuous_postcomp (regularAreaMap g))
  exact h.congr fun Γ => (familyMaximum_eq_norm g Γ).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.continuous_familyMaximum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.continuous_familyMaximum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.continuous_familyMaximum ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.continuous_familyMaximum


def representativeMaxima (g : SmoothRiemannianMetric I Q)
    (ξ : FreeContractibleSphereClass Q) : Set ℝ :=
  Set.range (fun Γ : RegularRepresentative (I := I) ξ => familyMaximum g Γ.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.representativeMaxima then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.representativeMaxima"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.representativeMaxima ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.representativeMaxima

theorem representativeMaxima_nonempty (g : SmoothRiemannianMetric I Q)
    (ξ : FreeContractibleSphereClass Q) : (representativeMaxima g ξ).Nonempty := by
  obtain ⟨Γ⟩ := regularRepresentative_nonempty (I := I) ξ
  exact ⟨familyMaximum g Γ.1, Γ, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.representativeMaxima_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.representativeMaxima_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.representativeMaxima_nonempty ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.representativeMaxima_nonempty

theorem representativeMaxima_bddBelow (g : SmoothRiemannianMetric I Q)
    (ξ : FreeContractibleSphereClass Q) : BddBelow (representativeMaxima g ξ) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨Γ, rfl⟩
  exact familyMaximum_nonneg g Γ.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.representativeMaxima_bddBelow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.representativeMaxima_bddBelow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.representativeMaxima_bddBelow ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.representativeMaxima_bddBelow


def classWidth (g : SmoothRiemannianMetric I Q) (ξ : FreeContractibleSphereClass Q) : ℝ :=
  _root_.InfSet.sInf (representativeMaxima g ξ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth

theorem classWidth_nonneg (g : SmoothRiemannianMetric I Q)
    (ξ : FreeContractibleSphereClass Q) : 0 ≤ classWidth g ξ := by
  apply le_csInf (representativeMaxima_nonempty g ξ)
  rintro _ ⟨Γ, rfl⟩
  exact familyMaximum_nonneg g Γ.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_nonneg

theorem classWidth_le_familyMaximum (g : SmoothRiemannianMetric I Q)
    (ξ : FreeContractibleSphereClass Q) (Γ : RegularRepresentative (I := I) ξ) :
    classWidth g ξ ≤ familyMaximum g Γ.1 :=
  csInf_le (representativeMaxima_bddBelow g ξ) ⟨Γ, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_le_familyMaximum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_le_familyMaximum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_le_familyMaximum ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_le_familyMaximum


theorem familyMaximum_le_mul (g h : SmoothRiemannianMetric I Q) {c : ℝ} (hc : 0 ≤ c)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (hpoint : ∀ k, regularLeastArea h (Γ k) ≤ c * regularLeastArea g (Γ k)) :
    familyMaximum h Γ ≤ c * familyMaximum g Γ := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨k, rfl⟩
  exact (hpoint k).trans
    (mul_le_mul_of_nonneg_left (regularLeastArea_le_familyMaximum g Γ k) hc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_le_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_le_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_le_mul ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_le_mul


theorem classWidth_le_mul (g h : SmoothRiemannianMetric I Q) {c : ℝ} (hc : 0 < c)
    (ξ : FreeContractibleSphereClass Q)
    (hfamily : ∀ Γ : RegularRepresentative (I := I) ξ,
      familyMaximum h Γ.1 ≤ c * familyMaximum g Γ.1) :
    classWidth h ξ ≤ c * classWidth g ξ := by
  have hlower : classWidth h ξ / c ≤ classWidth g ξ := by
    apply le_csInf (representativeMaxima_nonempty g ξ)
    rintro _ ⟨Γ, rfl⟩
    apply (div_le_iff₀ hc).mpr
    simpa only [mul_comm] using (classWidth_le_familyMaximum h ξ Γ).trans (hfamily Γ)
  have h := (div_le_iff₀ hc).mp hlower
  simpa only [mul_comm] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_le_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_le_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_le_mul ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_le_mul


theorem exists_representative_maximum_lt (g : SmoothRiemannianMetric I Q)
    (ξ : FreeContractibleSphereClass Q) {η : ℝ} (hη : 0 < η) :
    ∃ Γ : RegularRepresentative (I := I) ξ, familyMaximum g Γ.1 < classWidth g ξ + η := by
  obtain ⟨a, ⟨Γ, rfl⟩, hΓ⟩ := exists_lt_of_csInf_lt
    (representativeMaxima_nonempty g ξ)
    (show _root_.InfSet.sInf (representativeMaxima g ξ) < classWidth g ξ + η from
      lt_add_of_pos_right _ hη)
  exact ⟨Γ, hΓ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_representative_maximum_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_representative_maximum_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_representative_maximum_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_representative_maximum_lt


def nullFamilyClass (q : Q) : FreeContractibleSphereClass Q :=
  FreeHomotopyClass.mk (ContinuousMap.const (Sphere 2)
    (⟨constantLoops q, isContractibleLoop_constant q⟩ : ContractibleContinuousLoop Q))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.nullFamilyClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.nullFamilyClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.nullFamilyClass ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.nullFamilyClass

def constantRegularRepresentative (q : Q) : RegularRepresentative (I := I) (nullFamilyClass q) :=
  ⟨ContinuousMap.const (Sphere 2) (constantContractibleRegularLoop q), rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.constantRegularRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.constantRegularRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.constantRegularRepresentative ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.constantRegularRepresentative

omit connectedQ in
theorem regularLeastArea_constant (g : SmoothRiemannianMetric I Q) (q : Q) :
    regularLeastArea g (constantContractibleRegularLoop q) = 0 :=
  leastArea_const g q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_constant ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_constant

omit connectedQ in
theorem familyMaximum_constant (g : SmoothRiemannianMetric I Q) (q : Q) :
    familyMaximum g (constantRegularRepresentative (I := I) q).1 = 0 := by
  unfold familyMaximum constantRegularRepresentative
  simp only [ContinuousMap.const_apply, regularLeastArea_constant, Set.range_const, csSup_singleton]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_constant ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.familyMaximum_constant


theorem classWidth_null (g : SmoothRiemannianMetric I Q) (q : Q) :
    classWidth g (nullFamilyClass q) = 0 := by
  apply le_antisymm
  · simpa only [familyMaximum_constant] using
      classWidth_le_familyMaximum g (nullFamilyClass q) (constantRegularRepresentative q)
  · exact classWidth_nonneg g (nullFamilyClass q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_null then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_null"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_null ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_null

theorem rfs_width_finiteness (g : SmoothRiemannianMetric I Q)
    (ξ : FreeContractibleSphereClass Q) {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N) {η : ℝ} (hη : 0 < η) :
    ∃ Γ : RegularRepresentative (I := I) ξ,
      familyMaximum g Γ.1 < classWidth g ξ + η ∧ HasContinuousSmoothLoopJets e Γ.1 := by
  classical
  obtain ⟨Γ, hΓ⟩ := exists_representative_maximum_lt g ξ hη
  let i : C(ContractibleRegularLoop (I := I) (Q := Q), RegularLoop I Q) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let Γr : C(Sphere 2, RegularLoop I Q) := i.comp Γ.1
  obtain ⟨_, _, hsmooth⟩ := rfs_loop_smoothing g e
  obtain ⟨ε₀, hε₀, S, hjets, _, hhom, hregular, _⟩ :=
    hsmooth (Sphere 2) (regularLoopInclusion.comp Γr)
  have hctrS (ε : ℝ) (hε : ε ∈ _root_.Set.Ioo (0 : ℝ) ε₀) (k : Sphere 2) :
      IsContractibleLoop (S ε k).toContinuousLoop := by
    obtain ⟨F, _, hF⟩ := hhom ε hε
    have h := hF k (Γ.1 k).2 1
    exact Eq.mp (congrArg IsContractibleLoop (F.apply_one k)) h
  let T : ℝ → RegularFamily (I := I) (Q := Q) (Sphere 2) := fun ε =>
    if hε : ε ∈ _root_.Set.Ioo (0 : ℝ) ε₀ then
      ⟨fun k => ⟨S ε k, hctrS ε hε k⟩, (S ε).continuous.subtype_mk _⟩
    else Γ.1
  have hevent : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ _root_.Set.Ioo (0 : ℝ) ε₀ := Ioo_mem_nhdsGT hε₀
  have hT : Filter.Tendsto T (𝓝[>] (0 : ℝ)) (𝓝 Γ.1) := by
    apply (ContinuousMap.isInducing_postcomp i IsInducing.subtypeVal).tendsto_nhds_iff.mpr
    have heq : (fun ε => i.comp (T ε)) =ᶠ[𝓝[>] (0 : ℝ)] S := by
      filter_upwards [hevent] with ε hε
      ext k
      simp only [T, dif_pos hε, ContinuousMap.comp_apply, i, ContinuousMap.coe_mk]
    exact ((hregular Γr rfl).1).congr' heq.symm
  have hmax := (continuous_familyMaximum g).continuousAt.tendsto.comp hT
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      familyMaximum g (T ε) < classWidth g ξ + η :=
    hmax.eventually (gt_mem_nhds hΓ)
  obtain ⟨ε, hε, hboundε⟩ := (hevent.and hbound).exists
  obtain ⟨F, _, hF⟩ := hhom ε hε
  have hhomT : ContinuousMap.Homotopic (contractibleRegularLoopInclusion.comp Γ.1)
      (contractibleRegularLoopInclusion.comp (T ε)) := by
    refine ⟨{
      toFun := fun p => ⟨F p, hF p.2 (Γ.1 p.2).2 p.1⟩
      continuous_toFun := (_root_.ContinuousMapClass.map_continuous F).subtype_mk _
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro k
      apply Subtype.ext
      exact F.apply_zero k
    · intro k
      apply Subtype.ext
      change F (1, k) = (T ε k).1.toContinuousLoop
      simpa only [T, dif_pos hε, ContinuousMap.coe_mk] using
        (show F (1, k) = (S ε k).toContinuousLoop from F.apply_one k)
  have hclass : FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (T ε)) = ξ :=
    ((FreeHomotopyClass.mk_eq_mk_iff _ _).mpr hhomT).symm.trans Γ.2
  refine ⟨⟨T ε, hclass⟩, hboundε, ?_⟩
  simpa only [HasContinuousSmoothLoopJets, HasContinuousSmoothJets, T, dif_pos hε,
    ContinuousMap.coe_mk] using hjets ε hε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_width_finiteness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_width_finiteness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_width_finiteness ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_width_finiteness

theorem classWidth_metric_comparison (g h : SmoothRiemannianMetric I Q)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hmetric : ∀ q (v : TangentSpace I q),
      a ^ 2 * g.inner q v v ≤ h.inner q v v ∧ h.inner q v v ≤ b ^ 2 * g.inner q v v)
    (ξ : FreeContractibleSphereClass Q) :
    a ^ 2 * classWidth g ξ ≤ classWidth h ξ ∧
      classWidth h ξ ≤ b ^ 2 * classWidth g ξ := by
  have hb : 0 < b := ha.trans_le hab
  have hupper : classWidth h ξ ≤ b ^ 2 * classWidth g ξ := by
    apply classWidth_le_mul g h (sq_pos_of_pos hb) ξ
    intro Γ
    exact familyMaximum_le_mul g h (sq_nonneg b) Γ.1 fun k =>
      (regularLeastArea_metric_comparison g h ha hab hmetric (Γ.1 k)).2
  have hlower : classWidth g ξ ≤ (a ^ 2)⁻¹ * classWidth h ξ := by
    apply classWidth_le_mul h g (inv_pos.mpr (sq_pos_of_pos ha)) ξ
    intro Γ
    apply familyMaximum_le_mul h g (inv_nonneg.mpr (sq_nonneg a)) Γ.1
    intro k
    have hk := (regularLeastArea_metric_comparison g h ha hab hmetric (Γ.1 k)).1
    exact (le_inv_mul_iff₀ (sq_pos_of_pos ha)).mpr hk
  refine ⟨?_, hupper⟩
  exact (le_inv_mul_iff₀ (sq_pos_of_pos ha)).mp hlower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_metric_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_metric_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_metric_comparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_metric_comparison

theorem classWidth_scale (g : SmoothRiemannianMetric I Q) {c : ℝ} (hc : 0 < c)
    (ξ : FreeContractibleSphereClass Q) :
    classWidth (scaleMetric c hc g) ξ = c * classWidth g ξ := by
  have hmetric : ∀ q (v : TangentSpace I q),
      (Real.sqrt c) ^ 2 * g.inner q v v ≤ (scaleMetric c hc g).inner q v v ∧
      (scaleMetric c hc g).inner q v v ≤ (Real.sqrt c) ^ 2 * g.inner q v v := by
    intro q v
    simp [Real.sq_sqrt hc.le]
  have h := classWidth_metric_comparison g (scaleMetric c hc g)
    (Real.sqrt_pos.mpr hc) (le_refl (Real.sqrt c)) hmetric ξ
  simpa only [Real.sq_sqrt hc.le] using le_antisymm h.2 h.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_scale ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_scale

omit boundarylessI connectedQ in
theorem eventually_uniform_relative_metric_bound
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (g : ℝ → SmoothRiemannianMetric I Q)
    (hg : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn D g)
    (t₀ : D.carrier) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : D.carrier in 𝓝 t₀, ∀ q (v : TangentSpace I q),
      |(g t).inner q v v - (g t₀).inner q v v| ≤ ε * (g t₀).inner q v v := by
  let U := MetricUnitTangent (I := I) (M := Q) (g t₀)
  let : CompactSpace U := isCompact_univ_iff.mp (metricUnit_compact (g t₀))
  let F : D.carrier → C(U, ℝ) := fun t =>
    ⟨fun p => (g t).inner p.1.proj p.1.2 p.1.2,
      (metricQuad_cont (g t)).comp continuous_subtype_val⟩
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : D.carrier × U =>
      (g p.1).inner p.2.1.proj p.2.1.2 p.2.1.2)
    have hquad := DifferentialGeometry.Geometry.Curvature.tensor0SFamily_quadCont hg.metricTensor_cont
    have hc := hquad.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd :
        Continuous (fun p : D.carrier × U => p.2.1)))
    convert hc using 1
    ext p
    simp only [Function.comp_apply, quad02, Tensor0SBundle.metricTensorField_apply]
    rfl
  have hclose := (Metric.tendsto_nhds.mp (hF.tendsto t₀)) ε hε
  filter_upwards [hclose] with t ht
  have heval (q : Q) (v : TangentSpace I q) :
      quad02 (Tensor0SBundle.metricTensorField (g t) q -
        Tensor0SBundle.metricTensorField (g t₀) q) v =
      (g t).inner q v v - (g t₀).inner q v v := by
    unfold quad02
    rw [sub_apply, Tensor0SBundle.metricTensorField_apply,
      Tensor0SBundle.metricTensorField_apply]
  have hall := unitAbsBound_to_all (g t₀)
    (fun q => Tensor0SBundle.metricTensorField (g t) q -
      Tensor0SBundle.metricTensorField (g t₀) q) (C := ε) (by
    intro p
    have hp := (ContinuousMap.dist_apply_le_dist p).trans_lt ht
    rw [heval]
    convert! hp.le using 1)
  simpa only [heval] using hall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.eventually_uniform_relative_metric_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.eventually_uniform_relative_metric_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.eventually_uniform_relative_metric_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.eventually_uniform_relative_metric_bound


theorem classWidth_relative_metric_bound (g h : SmoothRiemannianMetric I Q)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδone : δ < 1)
    (hmetric : ∀ q (v : TangentSpace I q),
      |h.inner q v v - g.inner q v v| ≤ δ * g.inner q v v)
    (ξ : FreeContractibleSphereClass Q) :
    |classWidth h ξ - classWidth g ξ| ≤ δ * classWidth g ξ := by
  have hminus : 0 < 1 - δ := sub_pos.mpr hδone
  have hplus : 0 ≤ 1 + δ := by linarith
  have hquad : ∀ q (v : TangentSpace I q),
      (Real.sqrt (1 - δ)) ^ 2 * g.inner q v v ≤ h.inner q v v ∧
      h.inner q v v ≤ (Real.sqrt (1 + δ)) ^ 2 * g.inner q v v := by
    intro q v
    rw [Real.sq_sqrt hminus.le, Real.sq_sqrt hplus]
    obtain ⟨hl, hu⟩ := abs_le.mp (hmetric q v)
    constructor <;> nlinarith
  have hw := classWidth_metric_comparison g h (Real.sqrt_pos.mpr hminus)
    (Real.sqrt_le_sqrt (by linarith)) hquad ξ
  rw [Real.sq_sqrt hminus.le, Real.sq_sqrt hplus] at hw
  exact abs_le.mpr ⟨by nlinarith [hw.1], by nlinarith [hw.2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_relative_metric_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_relative_metric_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_relative_metric_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.classWidth_relative_metric_bound


omit connectedQ in
theorem leastArea_relative_metric_bound (g h : SmoothRiemannianMetric I Q)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδone : δ < 1)
    (hmetric : ∀ q (v : TangentSpace I q),
      |h.inner q v v - g.inner q v v| ≤ δ * g.inner q v v)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ)
    (hlipg : IsLipschitzLoop g γ) (hliph : IsLipschitzLoop h γ) :
    |leastArea h γ hctr hliph - leastArea g γ hctr hlipg| ≤
      δ * leastArea g γ hctr hlipg := by
  have hminus : 0 < 1 - δ := sub_pos.mpr hδone
  have hplus : 0 ≤ 1 + δ := by linarith
  have hquad : ∀ q (v : TangentSpace I q),
      (Real.sqrt (1 - δ)) ^ 2 * g.inner q v v ≤ h.inner q v v ∧
      h.inner q v v ≤ (Real.sqrt (1 + δ)) ^ 2 * g.inner q v v := by
    intro q v
    rw [Real.sq_sqrt hminus.le, Real.sq_sqrt hplus]
    obtain ⟨hl, hu⟩ := abs_le.mp (hmetric q v)
    constructor <;> nlinarith
  have ha := leastArea_metric_comparison g h (Real.sqrt_pos.mpr hminus)
    (Real.sqrt_le_sqrt (by linarith)) hquad γ hctr hlipg hliph
  rw [Real.sq_sqrt hminus.le, Real.sq_sqrt hplus] at ha
  exact abs_le.mpr ⟨by nlinarith [ha.1], by nlinarith [ha.2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_relative_metric_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_relative_metric_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_relative_metric_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_relative_metric_bound

include finiteDimensionalE boundarylessI t2Q compactQ connectedQ in
theorem continuousOn_classWidth_metricFamily
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (g : ℝ → SmoothRiemannianMetric I Q)
    (hg : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn D g)
    (ξ : FreeContractibleSphereClass Q) :
    ContinuousOn (fun t => classWidth (g t) ξ) D.carrier := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  rw [continuous_iff_continuousAt]
  intro t₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A := classWidth (g t₀) ξ
  have hA : 0 ≤ A := classWidth_nonneg (g t₀) ξ
  let δ := _root_.Min.min (1 / 2 : ℝ) (ε / (A + 1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδone : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδA : δ * A < ε := by
    have hh := (le_div_iff₀ (show 0 < A + 1 by positivity)).mp
      (show δ ≤ ε / (A + 1) from min_le_right _ _)
    nlinarith
  filter_upwards [eventually_uniform_relative_metric_bound D g hg t₀ hδ] with t ht
  rw [Real.dist_eq]
  exact (classWidth_relative_metric_bound (g t₀) (g t) hδ.le hδone ht ξ).trans_lt hδA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.continuousOn_classWidth_metricFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.continuousOn_classWidth_metricFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.continuousOn_classWidth_metricFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.continuousOn_classWidth_metricFamily

omit connectedQ in
include finiteDimensionalE boundarylessI t2Q compactQ in
theorem continuousOn_leastArea_metricFamily
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (g : ℝ → SmoothRiemannianMetric I Q)
    (hg : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn D g)
    (g₀ : SmoothRiemannianMetric I Q) (γ : ContinuousFreeLoop Q)
    (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g₀ γ) :
    ContinuousOn (fun t => leastArea (g t) γ hctr
      ((isLipschitzLoop_metric_iff g₀ (g t) γ).mp hlip)) D.carrier := by
  let hLip (t : ℝ) := (isLipschitzLoop_metric_iff g₀ (g t) γ).mp hlip
  apply continuousOn_iff_continuous_domRestrict.mpr
  rw [continuous_iff_continuousAt]
  intro t₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A := leastArea (g t₀) γ hctr (hLip t₀)
  have hA : 0 ≤ A := leastArea_nonneg (g t₀) γ hctr (hLip t₀)
  let δ := _root_.Min.min (1 / 2 : ℝ) (ε / (A + 1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδone : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδA : δ * A < ε := by
    have hh := (le_div_iff₀ (show 0 < A + 1 by positivity)).mp
      (show δ ≤ ε / (A + 1) from min_le_right _ _)
    nlinarith
  filter_upwards [eventually_uniform_relative_metric_bound D g hg t₀ hδ] with t ht
  rw [Real.dist_eq]
  exact (leastArea_relative_metric_bound (g t₀) (g t) hδ.le hδone ht γ hctr
    (hLip t₀) (hLip t)).trans_lt hδA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.continuousOn_leastArea_metricFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.continuousOn_leastArea_metricFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.continuousOn_leastArea_metricFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.continuousOn_leastArea_metricFamily


omit connectedQ in
theorem regularLeastArea_relative_metric_bound (g h : SmoothRiemannianMetric I Q)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδone : δ < 1)
    (hmetric : ∀ q (v : TangentSpace I q),
      |h.inner q v v - g.inner q v v| ≤ δ * g.inner q v v)
    (γ : ContractibleRegularLoop (I := I) (Q := Q)) :
    |regularLeastArea h γ - regularLeastArea g γ| ≤ δ * regularLeastArea g γ := by
  have hminus : 0 < 1 - δ := sub_pos.mpr hδone
  have hplus : 0 ≤ 1 + δ := by linarith
  have hquad : ∀ q (v : TangentSpace I q),
      (Real.sqrt (1 - δ)) ^ 2 * g.inner q v v ≤ h.inner q v v ∧
      h.inner q v v ≤ (Real.sqrt (1 + δ)) ^ 2 * g.inner q v v := by
    intro q v
    rw [Real.sq_sqrt hminus.le, Real.sq_sqrt hplus]
    obtain ⟨hl, hu⟩ := abs_le.mp (hmetric q v)
    constructor <;> nlinarith
  have harea := regularLeastArea_metric_comparison g h (Real.sqrt_pos.mpr hminus)
    (Real.sqrt_le_sqrt (by linarith)) hquad γ
  rw [Real.sq_sqrt hminus.le, Real.sq_sqrt hplus] at harea
  exact abs_le.mpr ⟨by nlinarith [harea.1], by nlinarith [harea.2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_relative_metric_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_relative_metric_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_relative_metric_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_relative_metric_bound

omit connectedQ in
theorem tendsto_regularLeastArea_of_uniform_metric
    (g : SmoothRiemannianMetric I Q) (gseq : ℕ → SmoothRiemannianMetric I Q)
    (hg : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in Filter.atTop,
      ∀ q (v : TangentSpace I q),
        |(gseq j).inner q v v - g.inner q v v| ≤ ε * g.inner q v v)
    (γ : ContractibleRegularLoop (I := I) (Q := Q))
    (γseq : ℕ → ContractibleRegularLoop (I := I) (Q := Q))
    (hγ : Filter.Tendsto γseq Filter.atTop (𝓝 γ)) :
    Filter.Tendsto (fun j => regularLeastArea (gseq j) (γseq j)) Filter.atTop
      (𝓝 (regularLeastArea g γ)) := by
  let _ : Nonempty Q := ⟨γ.1.toContinuousLoop 0⟩
  have hbase := (continuous_regularLeastArea g).continuousAt.tendsto.comp hγ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let B := regularLeastArea g γ + 1
  have hB : 0 < B := by
    dsimp [B]
    linarith [regularLeastArea_nonneg g γ]
  let δ := _root_.Min.min (1 / 2 : ℝ) (ε / (2 * B))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδone : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδB : δ * B ≤ ε / 2 := by
    calc
      δ * B ≤ (ε / (2 * B)) * B := mul_le_mul_of_nonneg_right (min_le_right _ _) hB.le
      _ = ε / 2 := by field_simp [hB.ne']
  have hsmall : 0 < _root_.Min.min (1 : ℝ) (ε / 2) := lt_min (by norm_num) (by positivity)
  have hclose := (Metric.tendsto_nhds.mp hbase) (_root_.Min.min (1 : ℝ) (ε / 2)) hsmall
  filter_upwards [hg δ hδ, hclose] with j hj hclosej
  rw [Real.dist_eq] at hclosej ⊢
  simp only [Function.comp_apply] at hclosej
  have hBbound : regularLeastArea g (γseq j) ≤ B := by
    have h := (abs_lt.mp (hclosej.trans_le (min_le_left _ _))).2
    dsimp [B]
    linarith
  have hhalf : |regularLeastArea g (γseq j) - regularLeastArea g γ| < ε / 2 :=
    hclosej.trans_le (min_le_right _ _)
  calc
    |regularLeastArea (gseq j) (γseq j) - regularLeastArea g γ| ≤
        |regularLeastArea (gseq j) (γseq j) - regularLeastArea g (γseq j)| +
          |regularLeastArea g (γseq j) - regularLeastArea g γ| := abs_sub_le _ _ _
    _ ≤ δ * regularLeastArea g (γseq j) +
        |regularLeastArea g (γseq j) - regularLeastArea g γ| :=
      add_le_add (regularLeastArea_relative_metric_bound g (gseq j) hδ.le hδone hj
        (γseq j)) le_rfl
    _ < δ * B + ε / 2 :=
      add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hBbound hδ.le) hhalf
    _ ≤ ε := by linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.tendsto_regularLeastArea_of_uniform_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.tendsto_regularLeastArea_of_uniform_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.tendsto_regularLeastArea_of_uniform_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.tendsto_regularLeastArea_of_uniform_metric

omit connectedQ in
include finiteDimensionalE boundarylessI t2Q compactQ in
theorem continuousOn_regularLeastArea_family [Nonempty Q]
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (g : ℝ → SmoothRiemannianMetric I Q)
    (hg : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn D g)
    {s : Set ℝ} (hs : s ⊆ D.regular)
    (Γ : ℝ → ContractibleRegularLoop (I := I) (Q := Q))
    (hΓ : ContinuousOn Γ s) :
    ContinuousOn (fun t => regularLeastArea (g t) (Γ t)) s := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  rw [continuous_iff_continuousAt]
  intro t₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hΓc : ContinuousAt (fun t : s => Γ t.1) t₀ :=
    (continuousOn_iff_continuous_domRestrict.mp hΓ).continuousAt
  have hbase : ContinuousAt (regularLeastArea (g t₀.1)) (Γ t₀.1) :=
    (continuous_regularLeastArea (g t₀.1)).continuousAt
  let A := regularLeastArea (g t₀.1) (Γ t₀.1)
  have hA : 0 ≤ A := regularLeastArea_nonneg (g t₀.1) (Γ t₀.1)
  let δ := _root_.Min.min (1 / 2 : ℝ) (ε / (2 * (A + 2)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδone : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδbound : δ * (A + 2) < ε := by
    have h1 : δ ≤ ε / (2 * (A + 2)) := min_le_right _ _
    have h2 : 0 < 2 * (A + 2) := by linarith
    have h3 := (le_div_iff₀ h2).mp h1
    nlinarith
  have hloop : ∀ᶠ t : s in 𝓝 t₀,
      dist (regularLeastArea (g t₀.1) (Γ t.1)) A < δ :=
    Metric.tendsto_nhds.mp (hbase.tendsto.comp hΓc.tendsto) δ hδ
  have hι : Continuous (fun t : s =>
      (⟨t.1, D.regular_subset (hs t.2)⟩ : D.carrier)) :=
    continuous_subtype_val.subtype_mk fun t => D.regular_subset (hs t.2)
  have hmetric : ∀ᶠ t : s in 𝓝 t₀, ∀ q (v : TangentSpace I q),
      |(g t.1).inner q v v - (g t₀.1).inner q v v| ≤ δ * (g t₀.1).inner q v v :=
    by
      filter_upwards [hι.continuousAt.preimage_mem_nhds
        (eventually_uniform_relative_metric_bound D g hg
          ⟨t₀.1, D.regular_subset (hs t₀.2)⟩ hδ)] with t ht
      simpa using ht
  filter_upwards [hmetric, hloop] with t ht hlt
  rw [Real.dist_eq] at hlt ⊢
  have hloop' : |regularLeastArea (g t₀.1) (Γ t.1) - A| ≤ δ := le_of_lt hlt
  have hbdd : regularLeastArea (g t₀.1) (Γ t.1) ≤ A + 1 := by
    have h := (abs_le.mp hloop').2
    linarith
  have hrel := regularLeastArea_relative_metric_bound (g t₀.1) (g t.1) hδ.le hδone ht
    (Γ t.1)
  calc |regularLeastArea (g t.1) (Γ t.1) - A| ≤
      |regularLeastArea (g t.1) (Γ t.1) - regularLeastArea (g t₀.1) (Γ t.1)| +
        |regularLeastArea (g t₀.1) (Γ t.1) - A| := abs_sub_le _ _ _
    _ ≤ δ * regularLeastArea (g t₀.1) (Γ t.1) + δ := add_le_add hrel hloop'
    _ ≤ δ * (A + 2) := by nlinarith
    _ < ε := hδbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.continuousOn_regularLeastArea_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.continuousOn_regularLeastArea_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.continuousOn_regularLeastArea_family ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.continuousOn_regularLeastArea_family

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

end

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

theorem uniform_regularLeastArea_of_uniform_embeddingFirstJet
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hg : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn D g)
    {a b : ℝ} (hreg : _root_.Set.Icc a b ⊆ D.carrier) {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := M) N)
    (Γ : ℝ → ContractibleRegularLoop (I := I) (Q := M))
    (Γseq : ℕ → ℝ → ContractibleRegularLoop (I := I) (Q := M))
    (hΓ : ContinuousOn Γ (_root_.Set.Icc a b))
    (hjets : ∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t ∈ _root_.Set.Icc a b,
      _root_.Dist.dist (embeddingFirstJet e (Γseq j t).1) (embeddingFirstJet e (Γ t).1) < ε) :
    ∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t ∈ _root_.Set.Icc a b,
      |regularLeastArea (g t) (Γseq j t) - regularLeastArea (g t) (Γ t)| < ε := by
  classical
  let _ : Nonempty M := ⟨(Γ a).1.toContinuousLoop 0⟩
  by_contra h
  push Not at h
  obtain ⟨ε, hε, hbad⟩ := h
  choose k hk t ht hlarge using hbad
  obtain ⟨t₀, ht₀, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq ht
  have hkφ : _root_.Filter.Tendsto (fun n => k (φ n)) _root_.Filter.atTop atTop :=
    _root_.Filter.tendsto_atTop_mono (fun n => hk (φ n)) hφ.tendsto_atTop
  have htime : _root_.Filter.Tendsto (fun n => t (φ n)) _root_.Filter.atTop (𝓝 t₀) := hlim
  have hbase : _root_.Filter.Tendsto (fun n => Γ (t (φ n))) _root_.Filter.atTop (𝓝 (Γ t₀)) :=
    (hΓ t₀ ht₀).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨htime, Eventually.of_forall fun n => ht (φ n)⟩)
  have hjetbase : _root_.Filter.Tendsto (fun n => embeddingFirstJet e (Γ (t (φ n))).1) _root_.Filter.atTop
      (𝓝 (embeddingFirstJet e (Γ t₀).1)) :=
    ((continuous_embeddingFirstJet e).comp continuous_subtype_val).continuousAt.tendsto.comp hbase
  have hdist : _root_.Filter.Tendsto (fun n => _root_.Dist.dist (embeddingFirstJet e (Γ (t (φ n))).1)
      (embeddingFirstJet e (Γseq (k (φ n)) (t (φ n))).1)) _root_.Filter.atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    obtain ⟨j₀, hj₀⟩ := hjets η hη
    filter_upwards [hkφ.eventually_ge_atTop j₀] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, dist_comm]
    exact hj₀ _ hn _ (ht (φ n))
  have hind : Topology.IsInducing (embeddingFirstJet e) :=
    ⟨regularLoop_topology_eq_embedding e⟩
  have happrox : _root_.Filter.Tendsto (fun n => Γseq (k (φ n)) (t (φ n))) _root_.Filter.atTop (𝓝 (Γ t₀)) := by
    apply tendsto_subtype_rng.mpr
    exact hind.tendsto_nhds_iff.mpr (hjetbase.congr_dist hdist)
  have htimeD : _root_.Filter.Tendsto (fun n => (⟨t (φ n), hreg (ht (φ n))⟩ : D.carrier)) _root_.Filter.atTop
      (𝓝 (⟨t₀, hreg ht₀⟩ : D.carrier)) := tendsto_subtype_rng.mpr htime
  have hmetric : ∀ η : ℝ, 0 < η → ∀ᶠ n in _root_.Filter.atTop,
      ∀ q (v : TangentSpace I q),
        |(g (t (φ n))).inner q v v - (g t₀).inner q v v| ≤ η * (g t₀).inner q v v := by
    intro η hη
    exact htimeD.eventually (eventually_uniform_relative_metric_bound D g hg
      ⟨t₀, hreg ht₀⟩ hη)
  have ha := tendsto_regularLeastArea_of_uniform_metric (g t₀) (fun n => g (t (φ n)))
    hmetric (Γ t₀) _ happrox
  have hb := tendsto_regularLeastArea_of_uniform_metric (g t₀) (fun n => g (t (φ n)))
    hmetric (Γ t₀) _ hbase
  have hd := (ha.sub hb).abs
  simp only [sub_self, abs_zero] at hd
  have hsmall := hd.eventually_lt_const hε
  obtain ⟨n, hn⟩ := hsmall.exists
  exact (not_lt_of_ge (hlarge (φ n))) hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.uniform_regularLeastArea_of_uniform_embeddingFirstJet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.uniform_regularLeastArea_of_uniform_embeddingFirstJet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.uniform_regularLeastArea_of_uniform_embeddingFirstJet ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.uniform_regularLeastArea_of_uniform_embeddingFirstJet

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

end
