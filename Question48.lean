/-
  Dow–Tkachuk, Question 4.8 (Eur. J. Math. 11 (2025), Art. No. 5):
  if the closure of every countable subset of `C_p(X)` is pseudocomplete,
  must `X` be a P-space?  Answer: yes (in ZFC, i.e. in Lean + Mathlib).

  Formalization of the argument in "Pseudocompleteness of countable closures in
  spaces of continuous functions".  No axioms beyond Lean's standard ones are used;
  in particular the Aarts–Lutzer characterization is NOT imported: the key lemma
  (a dense pseudocomplete subgroup of a metrizable group is the whole group) is
  proved directly from Oxtoby's definition.

  Checked with Lean 4.34.1 and Mathlib v4.34.1 (no `sorry`; axioms: propext,
  Classical.choice, Quot.sound).
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Set Filter Topology

noncomputable section

namespace Question48

/-! ## Definitions -/

/-- A π-base: a family of nonempty open sets such that every nonempty open set
contains one of its members. -/
def IsPiBase {Y : Type*} [TopologicalSpace Y] (𝓑 : Set (Set Y)) : Prop :=
  (∀ U ∈ 𝓑, IsOpen U ∧ U.Nonempty) ∧
    ∀ V : Set Y, IsOpen V → V.Nonempty → ∃ U ∈ 𝓑, U ⊆ V

/-- Pseudocompleteness in the sense of Oxtoby: there is a sequence of π-bases
`𝓑 n` such that every sequence `U n ∈ 𝓑 n` with `closure (U (n+1)) ⊆ U n`
has nonempty intersection. -/
def Pseudocomplete (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∃ 𝓑 : ℕ → Set (Set Y), (∀ n, IsPiBase (𝓑 n)) ∧
    ∀ U : ℕ → Set Y, (∀ n, U n ∈ 𝓑 n) → (∀ n, closure (U (n + 1)) ⊆ U n) →
      (⋂ n, U n).Nonempty

/-- A P-space: every countable intersection of open sets is open. -/
def IsPSpace (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ U : ℕ → Set X, (∀ n, IsOpen (U n)) → IsOpen (⋂ n, U n)

/-- `C_p(X)`: the continuous real functions on `X`, as a subspace of the product
`X → ℝ` (topology of pointwise convergence). -/
def Cp (X : Type*) [TopologicalSpace X] : Set (X → ℝ) := {g | Continuous g}

/-- Non-degeneracy check of the definition: every compact space is pseudocomplete. -/
theorem Pseudocomplete.of_compactSpace (Y : Type*) [TopologicalSpace Y] [CompactSpace Y] :
    Pseudocomplete Y := by
  refine ⟨fun _ => {U | IsOpen U ∧ U.Nonempty},
    fun _ => ⟨fun U hU => hU, fun V hV hne => ⟨V, ⟨hV, hne⟩, le_rfl⟩⟩, ?_⟩
  intro U hU hcl
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => closure (U (n + 1))) (fun n => (hcl (n + 1)).trans subset_closure)
    (fun n => (hU (n + 1)).2.closure) isClosed_closure.isCompact (fun _ => isClosed_closure)
  exact ⟨y, mem_iInter.2 fun n => hcl n (mem_iInter.1 hy n)⟩

/-! ## Pseudocompleteness is a topological invariant -/

theorem Pseudocomplete.of_homeomorph {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (e : Y ≃ₜ Z) (h : Pseudocomplete Y) : Pseudocomplete Z := by
  obtain ⟨𝓑, hπ, hc⟩ := h
  refine ⟨fun n => (fun U => e '' U) '' 𝓑 n, fun n => ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨U, hU, rfl⟩
    exact ⟨e.isOpenMap U ((hπ n).1 U hU).1, ((hπ n).1 U hU).2.image e⟩
  · intro V hV hne
    obtain ⟨z, hz⟩ := hne
    obtain ⟨U, hU, hUV⟩ := (hπ n).2 (e ⁻¹' V) (hV.preimage e.continuous)
      ⟨e.symm z, by simpa using hz⟩
    refine ⟨e '' U, ⟨U, hU, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hUV hy
  · intro W hW hcl
    choose U hU hUW using hW
    have hUW' : ∀ n, e '' U n = W n := hUW
    have hU' : ∀ n, closure (U (n + 1)) ⊆ U n := by
      intro n
      have h1 := hcl n
      rw [← hUW' n, ← hUW' (n + 1), ← e.image_closure] at h1
      exact (Set.image_subset_image_iff e.injective).1 h1
    obtain ⟨y, hy⟩ := hc U hU hU'
    refine ⟨e y, mem_iInter.2 fun n => ?_⟩
    rw [← hUW' n]
    exact mem_image_of_mem e (mem_iInter.1 hy n)

/-! ## Lemma 2.1: dense pseudocomplete subgroups

We prove: a dense pseudocomplete subgroup `S` of a metrizable topological group `M`
is all of `M`.  (The paper derives this from the Aarts–Lutzer characterization and
the Baire category theorem; here it is proved directly by a simultaneous
nested-sequence construction for `S` and its translate `a + S`.) -/

/-- Auxiliary state of the nested construction. -/
structure St (M S : Type*) where
  U : Set S
  V : Set S
  Ut : Set M
  Vt : Set M

theorem dense_pseudocomplete_subgroup {M : Type*} [TopologicalSpace M]
    [TopologicalSpace.MetrizableSpace M] [AddGroup M] [IsTopologicalAddGroup M]
    (S : Set M) (hsub : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ S) (hd : Dense S)
    (hp : Pseudocomplete S) (a : M) : a ∈ S := by
  let _ : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨𝓑, hπ, hc⟩ := hp
  have hcadd : Continuous fun m : M => a + m := continuous_const.add continuous_id
  have hcneg : Continuous fun m : M => -a + m := continuous_const.add continuous_id
  -- every nonempty open set of `M` meets `S`
  have hne : ∀ W : Set M, IsOpen W → W.Nonempty →
      (Subtype.val ⁻¹' W : Set S).Nonempty := by
    intro W hW hW'
    obtain ⟨x, hxW, hxS⟩ := hd.inter_open_nonempty W hW hW'
    exact ⟨⟨x, hxS⟩, hxW⟩
  -- pick a member of `𝓑 n` inside an open set, together with an ambient open trace
  have hpick : ∀ n (W : Set M), IsOpen W → W.Nonempty →
      ∃ U ∈ 𝓑 n, ∃ Ut : Set M, IsOpen Ut ∧ Ut ⊆ W ∧ Subtype.val ⁻¹' Ut = U := by
    intro n W hW hW'
    obtain ⟨U, hU, hUW⟩ :=
      (hπ n).2 _ (hW.preimage continuous_subtype_val) (hne W hW hW')
    obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 ((hπ n).1 U hU).1
    refine ⟨U, hU, W ∩ O, hW.inter hO, inter_subset_left, ?_⟩
    rw [preimage_inter, hOU]
    exact inter_eq_right.2 hUW
  -- the invariant
  let Inv : ℕ → St M S → Prop := fun n s =>
    s.U ∈ 𝓑 n ∧ s.V ∈ 𝓑 n ∧ IsOpen s.Ut ∧ IsOpen s.Vt ∧
      Subtype.val ⁻¹' s.Ut = s.U ∧ Subtype.val ⁻¹' s.Vt = s.V ∧
      ∀ v ∈ s.Vt, a + v ∈ s.Ut
  -- given `U ∈ 𝓑 n` with open trace `Ut`, choose the matching `V`
  have hVpick : ∀ n (U : Set S) (Ut : Set M), U ∈ 𝓑 n → IsOpen Ut →
      Subtype.val ⁻¹' Ut = U → ∃ s : St M S, s.U = U ∧ s.Ut = Ut ∧ Inv n s := by
    intro n U Ut hU hUt hUe
    obtain ⟨u, hu⟩ := ((hπ n).1 U hU).2
    have hut : (u : M) ∈ Ut := by rw [← hUe] at hu; exact hu
    obtain ⟨V, hV, Vt, hVto, hVtsub, hVte⟩ :=
      hpick n ((fun m => a + m) ⁻¹' Ut) (hUt.preimage hcadd)
        ⟨-a + u, by simpa using hut⟩
    exact ⟨⟨U, V, Ut, Vt⟩, rfl, rfl, hU, hV, hUt, hVto, hUe, hVte, fun v hv => hVtsub hv⟩
  -- initial state
  obtain ⟨s0, -, -, hs0⟩ : ∃ s : St M S, True ∧ True ∧ Inv 0 s := by
    obtain ⟨U, hU, Ut, hUt, -, hUe⟩ := hpick 0 univ isOpen_univ ⟨a, trivial⟩
    obtain ⟨s, -, -, hs⟩ := hVpick 0 U Ut hU hUt hUe
    exact ⟨s, trivial, trivial, hs⟩
  -- the inductive step
  have hstep : ∀ n (s : St M S), Inv n s → ∃ s' : St M S, Inv (n + 1) s' ∧
      closure s'.U ⊆ s.U ∧ closure s'.V ⊆ s.V ∧
      ∃ c : M, s'.Ut ⊆ Metric.ball c (1 / ((n : ℝ) + 1)) := by
    intro n s ⟨_, hV, _, hVo, hUe, hVe, hUV⟩
    obtain ⟨v, hv⟩ := ((hπ n).1 _ hV).2
    have hvt : (v : M) ∈ s.Vt := by rw [← hVe] at hv; exact hv
    set W : Set M := (fun m => -a + m) ⁻¹' s.Vt with hWdef
    have hWo : IsOpen W := hVo.preimage hcneg
    set c : M := a + (v : M) with hcdef
    have hcW : c ∈ W := by simpa [hWdef, hcdef] using hvt
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hWo c hcW
    have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    set r : ℝ := min (ε / 2) (1 / ((n : ℝ) + 1) / 2) with hrdef
    have hr : 0 < r := lt_min (half_pos hε) (half_pos hn)
    have hrε : r < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
    have hrn : r ≤ 1 / ((n : ℝ) + 1) := (min_le_right _ _).trans (half_le_self hn.le)
    have hcl : Metric.closedBall c r ⊆ W :=
      (Metric.closedBall_subset_ball hrε).trans hball
    obtain ⟨U', hU', Ut', hUt'o, hUt'sub, hUt'e⟩ :=
      hpick (n + 1) (Metric.ball c r) Metric.isOpen_ball ⟨c, Metric.mem_ball_self hr⟩
    obtain ⟨s', hs'U, hs'Ut, hs'⟩ := hVpick (n + 1) U' Ut' hU' hUt'o hUt'e
    refine ⟨s', hs', ?_, ?_, c, ?_⟩
    · -- `closure U' ⊆ U`
      rw [hs'U]
      have h1 : U' ⊆ Subtype.val ⁻¹' Metric.closedBall c r := by
        rw [← hUt'e]
        exact preimage_mono (hUt'sub.trans Metric.ball_subset_closedBall)
      refine (closure_minimal h1
        (Metric.isClosed_closedBall.preimage continuous_subtype_val)).trans ?_
      intro y hy
      have h2 : -a + (y : M) ∈ s.Vt := hcl hy
      have h3 := hUV _ h2
      rw [← hUe]
      simpa using h3
    · -- `closure V' ⊆ V`
      obtain ⟨_, _, _, _, _, hVe', hUV'⟩ := hs'
      have h1 : s'.V ⊆ Subtype.val ⁻¹' ((fun m => a + m) ⁻¹' Metric.closedBall c r) := by
        rw [← hVe']
        intro y hy
        have := hUV' _ hy
        rw [hs'Ut] at this
        exact Metric.ball_subset_closedBall (hUt'sub this)
      refine (closure_minimal h1 ((Metric.isClosed_closedBall.preimage hcadd).preimage
        continuous_subtype_val)).trans ?_
      intro y hy
      have h2 : -a + (a + (y : M)) ∈ s.Vt := hcl hy
      rw [← hVe]
      simpa using h2
    · rw [hs'Ut]
      exact hUt'sub.trans (Metric.ball_subset_ball hrn)
  choose! next hnext using hstep
  let sq : ℕ → St M S := fun n => Nat.rec (motive := fun _ => St M S) s0 (fun k s => next k s) n
  have hsq_succ : ∀ n, sq (n + 1) = next n (sq n) := fun n => rfl
  have hsq : ∀ n, Inv n (sq n) := by
    intro n
    induction n with
    | zero => exact hs0
    | succ k ih => rw [hsq_succ]; exact (hnext k _ ih).1
  obtain ⟨d1, hd1⟩ := hc (fun n => (sq n).U) (fun n => (hsq n).1)
    (fun n => by rw [hsq_succ]; exact (hnext n _ (hsq n)).2.1)
  obtain ⟨d2, hd2⟩ := hc (fun n => (sq n).V) (fun n => (hsq n).2.1)
    (fun n => by rw [hsq_succ]; exact (hnext n _ (hsq n)).2.2.1)
  have key : ∀ n : ℕ, dist (d1 : M) (a + d2) < 2 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨c, hcb⟩ := (hnext n _ (hsq n)).2.2.2
    rw [← hsq_succ] at hcb
    obtain ⟨_, _, _, _, hUe, hVe, hUV⟩ := hsq (n + 1)
    have h1 : (d1 : M) ∈ (sq (n + 1)).Ut := by
      have := mem_iInter.1 hd1 (n + 1)
      rw [← hUe] at this
      exact this
    have h2 : a + (d2 : M) ∈ (sq (n + 1)).Ut := by
      have := mem_iInter.1 hd2 (n + 1)
      rw [← hVe] at this
      exact hUV _ this
    have e1 := hcb h1
    have e2 := hcb h2
    rw [Metric.mem_ball] at e1 e2
    have := dist_triangle_right (d1 : M) (a + d2) c
    have h2n : (2 : ℝ) / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by ring
    linarith
  have hdist : dist (d1 : M) (a + d2) = 0 := by
    by_contra hne0
    have hpos : 0 < dist (d1 : M) (a + d2) := lt_of_le_of_ne dist_nonneg (Ne.symm hne0)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hpos)
    have := key n
    have h2n : (2 : ℝ) / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1)) := by ring
    linarith
  have heq : a + (d2 : M) = d1 := (dist_eq_zero.1 hdist).symm
  have : a = (d1 : M) - d2 := eq_sub_of_add_eq heq
  rw [this]
  exact hsub _ d1.2 _ d2.2

/-! ## Zero sets: a non-P-space has a non-open zero set -/

theorem exists_nonopen_zero_set {X : Type*} [TopologicalSpace X] [CompletelyRegularSpace X]
    (h : ¬ IsPSpace X) :
    ∃ f : X → ℝ, Continuous f ∧ (∀ x, 0 ≤ f x) ∧ ¬ IsOpen (f ⁻¹' {0}) := by
  unfold IsPSpace at h
  push Not at h
  obtain ⟨U, hUo, hnot⟩ := h
  rw [isOpen_iff_mem_nhds] at hnot
  push Not at hnot
  obtain ⟨y, hy, hny⟩ := hnot
  have hreg : ∀ n, ∃ g : X → unitInterval, Continuous g ∧ g y = 0 ∧ EqOn g 1 (U n)ᶜ :=
    fun n => CompletelyRegularSpace.completely_regular y _ (hUo n).isClosed_compl
      (by simpa using mem_iInter.1 hy n)
  choose g hgc hgy hg1 using hreg
  have hterm : ∀ n x, 0 ≤ (1 / 2 : ℝ) ^ n * (g n x : ℝ) :=
    fun n x => mul_nonneg (by positivity) (g n x).2.1
  have hterm' : ∀ n x, (1 / 2 : ℝ) ^ n * (g n x : ℝ) ≤ (1 / 2 : ℝ) ^ n :=
    fun n x => mul_le_of_le_one_right (by positivity) (g n x).2.2
  have hsum : ∀ x, Summable fun n => (1 / 2 : ℝ) ^ n * (g n x : ℝ) :=
    fun x => summable_geometric_two.of_nonneg_of_le (hterm · x) (hterm' · x)
  set f : X → ℝ := fun x => ∑' n, (1 / 2 : ℝ) ^ n * (g n x : ℝ) with hfdef
  have hfc : Continuous f :=
    continuous_tsum (fun n => continuous_const.mul (continuous_subtype_val.comp (hgc n)))
      summable_geometric_two (fun n x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hterm n x)]
        exact hterm' n x)
  refine ⟨f, hfc, fun x => tsum_nonneg (hterm · x), fun hopen => hny ?_⟩
  have hyZ : y ∈ f ⁻¹' {0} := by simp [hfdef, hgy]
  refine mem_of_superset (hopen.mem_nhds hyZ) ?_
  intro x hx
  simp only [mem_preimage, mem_singleton_iff] at hx
  rw [mem_iInter]
  intro n
  by_contra hxn
  have h1 : (g n x : ℝ) = 1 := by
    have := hg1 n hxn
    rw [this]
    rfl
  have h2 := (hsum x).le_tsum n (fun j _ => hterm j x)
  rw [h1, mul_one] at h2
  have h3 : (0 : ℝ) < (1 / 2) ^ n := by positivity
  have h4 : f x = ∑' n, (1 / 2 : ℝ) ^ n * (g n x : ℝ) := rfl
  linarith

/-! ## Tent functions on a sequence of levels tending to zero -/

/-- Tent functions: `ψ t 0` rises from `0` at `t 1` to `1` at `t 0` and stays `1`;
`ψ t (k+1)` is the tent supported on `[t (k+2), t k]` with peak `1` at `t (k+1)`.
For a sequence `a`, `∑ a m * ψ t m` is the piecewise linear interpolation `u_a`. -/
def ψ (t : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, τ => max 0 (min 1 ((τ - t 1) / (t 0 - t 1)))
  | k + 1, τ => max 0 (min ((τ - t (k + 2)) / (t (k + 1) - t (k + 2)))
      ((t k - τ) / (t k - t (k + 1))))

section Tents

variable {t : ℕ → ℝ} (hanti : StrictAnti t)
include hanti

omit hanti in
lemma ψ_nonneg (m : ℕ) (τ : ℝ) : 0 ≤ ψ t m τ := by
  cases m <;> exact le_max_left _ _

omit hanti in
lemma ψ_continuous (m : ℕ) : Continuous (ψ t m) := by
  cases m with
  | zero =>
    exact continuous_const.max (continuous_const.min
      ((continuous_id.sub continuous_const).div_const _))
  | succ k =>
    exact continuous_const.max
      (((continuous_id.sub continuous_const).div_const _).min
        ((continuous_const.sub continuous_id).div_const _))

lemma sub_pos_succ (n : ℕ) : 0 < t n - t (n + 1) := sub_pos.2 (hanti (Nat.lt_succ_self n))

/-- `ψ t m` vanishes at and below `t (m+1)`. -/
lemma ψ_vanish_left (m : ℕ) (τ : ℝ) (hτ : τ ≤ t (m + 1)) : ψ t m τ = 0 := by
  cases m with
  | zero =>
    have hx : (τ - t 1) / (t 0 - t 1) ≤ 0 :=
      (div_le_iff₀ (sub_pos_succ hanti 0)).2 (by linarith)
    exact max_eq_left ((min_le_right _ _).trans hx)
  | succ k =>
    have hx : (τ - t (k + 2)) / (t (k + 1) - t (k + 2)) ≤ 0 :=
      (div_le_iff₀ (sub_pos_succ hanti (k + 1))).2 (by linarith)
    exact max_eq_left ((min_le_left _ _).trans hx)

/-- `ψ t (k+1)` vanishes at and above `t k`. -/
lemma ψ_vanish_right (k : ℕ) (τ : ℝ) (hτ : t k ≤ τ) : ψ t (k + 1) τ = 0 := by
  have hx : (t k - τ) / (t k - t (k + 1)) ≤ 0 :=
    (div_le_iff₀ (sub_pos_succ hanti k)).2 (by linarith)
  exact max_eq_left ((min_le_right _ _).trans hx)

lemma ψ_peak (m : ℕ) : ψ t m (t m) = 1 := by
  cases m with
  | zero =>
    simp only [ψ, div_self (sub_pos_succ hanti 0).ne', min_self, max_eq_right zero_le_one]
  | succ k =>
    have h1 : (t (k + 1) - t (k + 2)) / (t (k + 1) - t (k + 2)) = 1 :=
      div_self (sub_pos_succ hanti (k + 1)).ne'
    have h2 : (t k - t (k + 1)) / (t k - t (k + 1)) = 1 :=
      div_self (sub_pos_succ hanti k).ne'
    simp only [ψ, h1, h2, min_self, max_eq_right zero_le_one]

lemma ψ_at (m n : ℕ) : ψ t m (t n) = if m = n then 1 else 0 := by
  split_ifs with h
  · subst h
    exact ψ_peak hanti m
  · rcases lt_or_gt_of_ne h with h | h
    · exact ψ_vanish_left hanti m _ (hanti.antitone (by omega))
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact ψ_vanish_right hanti k _ (hanti.antitone (by omega))

lemma ψ_eventually_zero (hpos : ∀ n, 0 < t n) (hlim : ∀ τ > 0, ∃ N, t N < τ) (τ : ℝ) :
    ∃ N, ∀ m, N ≤ m → ψ t m τ = 0 := by
  rcases le_or_gt τ 0 with hτ | hτ
  · exact ⟨0, fun m _ => ψ_vanish_left hanti m τ (hτ.trans (hpos _).le)⟩
  · obtain ⟨K, hK⟩ := hlim τ hτ
    refine ⟨K + 1, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact ψ_vanish_right hanti k τ ((hanti.antitone (by omega : K ≤ k)).trans hK.le)

/-- On every positive level two consecutive tents add up to at least `1`. -/
lemma ψ_pair_ge_one (hlim : ∀ τ > 0, ∃ N, t N < τ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ n, 1 ≤ ψ t n τ + ψ t (n + 1) τ := by
  rcases le_or_gt (t 0) τ with h0 | h0
  · refine ⟨0, ?_⟩
    have hx : 1 ≤ (τ - t 1) / (t 0 - t 1) :=
      (le_div_iff₀ (sub_pos_succ hanti 0)).2 (by linarith)
    have h1 : ψ t 0 τ = 1 := by
      simp only [ψ, min_eq_left hx, max_eq_right zero_le_one]
    linarith [ψ_nonneg (t := t) 1 τ]
  · classical
    have hex : ∃ N, t N < τ := hlim τ hτ
    set N := Nat.find hex with hNdef
    have hN : t N < τ := Nat.find_spec hex
    have hN0 : N ≠ 0 := by
      intro h
      rw [h] at hN
      linarith
    obtain ⟨n, hn⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hlo : t (n + 1) < τ := hn ▸ hN
    have hhi : τ ≤ t n := by
      have := Nat.find_min hex (show n < N by omega)
      exact not_lt.1 this
    have hd := sub_pos_succ hanti n
    set α : ℝ := (τ - t (n + 1)) / (t n - t (n + 1)) with hαdef
    have hα0 : 0 ≤ α := div_nonneg (by linarith) hd.le
    have hα1 : α ≤ 1 := (div_le_one hd).2 (by linarith)
    -- lower bound for the rising tent
    have hA : α ≤ ψ t n τ := by
      cases n with
      | zero =>
        exact le_max_of_le_right (le_min hα1 le_rfl)
      | succ k =>
        have hβ : 1 ≤ (t k - τ) / (t k - t (k + 1)) :=
          (le_div_iff₀ (sub_pos_succ hanti k)).2 (by linarith)
        exact le_max_of_le_right (le_min le_rfl (hα1.trans hβ))
    -- lower bound for the falling tent
    have hB : 1 - α ≤ ψ t (n + 1) τ := by
      have hγ : 1 ≤ (τ - t (n + 2)) / (t (n + 1) - t (n + 2)) :=
        (le_div_iff₀ (sub_pos_succ hanti (n + 1))).2 (by linarith)
      have hδ : (t n - τ) / (t n - t (n + 1)) = 1 - α := by
        rw [hαdef]
        field_simp
        ring
      refine le_max_of_le_right (le_min (by linarith) hδ.ge)
    exact ⟨n, by linarith⟩

end Tents

/-! ## The interpolation map `T` -/

/-- `T a = u_a ∘ f`, where `u_a = ∑ a m * ψ t m` interpolates `a` at the levels `t`. -/
def Tmap {X : Type*} (t : ℕ → ℝ) (f : X → ℝ) (a : ℕ → ℝ) : X → ℝ :=
  fun x => ∑' m, a m * ψ t m (f x)

/-- A countable dense family of finitely supported sequences in `ℕ → ℝ`. -/
def fs (p : Σ k : ℕ, Fin k → ℚ) : ℕ → ℝ :=
  fun n => if h : n < p.1 then ((p.2 ⟨n, h⟩ : ℚ) : ℝ) else 0

lemma fs_eq_zero (p : Σ k : ℕ, Fin k → ℚ) (m : ℕ) (hm : p.1 ≤ m) : fs p m = 0 := by
  simp [fs, not_lt.2 hm]

lemma dense_range_fs : Dense (range fs) := by
  intro a
  have hq : ∀ k : ℕ, ∀ n, ∃ q : ℚ, a n < q ∧ (q : ℝ) < a n + 1 / ((k : ℝ) + 1) :=
    fun k n => exists_rat_btwn (by linarith [show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity])
  choose q hq1 hq2 using hq
  let b : ℕ → ℕ → ℝ := fun k => fs ⟨k, fun i => q k i⟩
  refine mem_closure_of_tendsto (f := b) (b := atTop) ?_
    (Eventually.of_forall fun k => mem_range_self _)
  rw [tendsto_pi_nhds]
  intro n
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
  refine ⟨max (n + 1) K, fun k hk => ?_⟩
  have hnk : n < k := by have := le_of_max_le_left hk; omega
  have hKk : K ≤ k := le_of_max_le_right hk
  have hbk : b k n = q k n := by simp [b, fs, hnk]
  rw [hbk, Real.dist_eq, abs_of_pos (by linarith [hq1 k n])]
  have : 1 / ((k : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) := by
    gcongr
  linarith [hq2 k n]

/-! ## Main theorem -/

/-- **Answer to Dow–Tkachuk Question 4.8.**  If the closure in `C_p(X)` of every
countable subset of `C_p(X)` is pseudocomplete, then `X` is a P-space. -/
theorem question_4_8 {X : Type*} [TopologicalSpace X] [CompletelyRegularSpace X]
    (h : ∀ A : Set (Cp X), A.Countable → Pseudocomplete (closure A)) : IsPSpace X := by
  by_contra hP
  obtain ⟨f, hfc, hf0, hZ⟩ := exists_nonopen_zero_set hP
  /- Step 1: positive values of `f` accumulate at `0`. -/
  have hsmall : ∀ ε > 0, ∃ x, 0 < f x ∧ f x < ε := by
    intro ε hε
    by_contra hno
    push Not at hno
    apply hZ
    have : f ⁻¹' {0} = f ⁻¹' Iio ε := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_Iio]
      constructor
      · intro hx
        rw [hx]
        exact hε
      · intro hx
        by_contra hne
        exact absurd (hno x (lt_of_le_of_ne (hf0 x) (Ne.symm hne))) (not_le.2 hx)
    rw [this]
    exact isOpen_Iio.preimage hfc
  have hsmall' : ∀ ε : ℝ, ∃ x, 0 < ε → 0 < f x ∧ f x < ε := by
    intro ε
    by_cases hε : 0 < ε
    · obtain ⟨x, hx⟩ := hsmall ε hε
      exact ⟨x, fun _ => hx⟩
    · obtain ⟨x, -⟩ := hsmall 1 one_pos
      exact ⟨x, fun h => absurd h hε⟩
  choose g hg using hsmall'
  have hgpos : ∀ ε, 0 < ε → 0 < f (g ε) := fun ε hε => (hg ε hε).1
  have hglt : ∀ ε, 0 < ε → f (g ε) < ε := fun ε hε => (hg ε hε).2
  /- Step 2: points `x n` with levels `0 < t (n+1) < t n / 2`. -/
  let xs : ℕ → X := fun n => Nat.rec (motive := fun _ => X) (g 1) (fun _ x => g (f x / 2)) n
  set t : ℕ → ℝ := fun n => f (xs n) with htdef
  have htpos : ∀ n, 0 < t n := by
    intro n
    induction n with
    | zero => exact hgpos 1 one_pos
    | succ k ih => exact hgpos _ (half_pos ih)
  have hhalf : ∀ n, t (n + 1) < t n / 2 := fun n => hglt _ (half_pos (htpos n))
  have hdec : ∀ n, t (n + 1) < t n := fun n => (hhalf n).trans (half_lt_self (htpos n))
  have hanti : StrictAnti t := strictAnti_nat_of_succ_lt hdec
  have hbound : ∀ n, t n ≤ t 0 / 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      calc t (k + 1) ≤ t k / 2 := (hhalf k).le
        _ ≤ t 0 / 2 ^ k / 2 := by gcongr
        _ = t 0 / 2 ^ (k + 1) := by ring
  have hlim : ∀ τ > 0, ∃ N, t N < τ := by
    intro τ hτ
    obtain ⟨N, hN⟩ := exists_nat_gt (t 0 / τ)
    refine ⟨N, (hbound N).trans_lt ?_⟩
    have h2N : (N : ℝ) < 2 ^ N := by exact_mod_cast Nat.lt_two_pow_self
    have h1 : t 0 < N * τ := (div_lt_iff₀ hτ).1 hN
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  /- Step 3: the map `T` and its properties. -/
  have hfin := ψ_eventually_zero hanti htpos hlim
  have hrepr : ∀ τ, ∃ N, ∀ a : ℕ → ℝ, Summable (fun m => a m * ψ t m τ) ∧
      ∑' m, a m * ψ t m τ = ∑ m ∈ Finset.range N, a m * ψ t m τ := by
    intro τ
    obtain ⟨N, hN⟩ := hfin τ
    refine ⟨N, fun a => ⟨summable_of_ne_finset_zero (s := Finset.range N) ?_,
      tsum_eq_sum ?_⟩⟩ <;>
    · intro m hm
      simp only [Finset.mem_range, not_lt] at hm
      rw [hN m hm, mul_zero]
  let T := Tmap t f
  have hTc : Continuous T := by
    apply continuous_pi
    intro x
    obtain ⟨N, hN⟩ := hrepr (f x)
    have : (fun a : ℕ → ℝ => T a x) =
        fun a => ∑ m ∈ Finset.range N, a m * ψ t m (f x) :=
      funext fun a => (hN a).2
    rw [this]
    exact continuous_finsetSum _ fun m _ => (continuous_apply m).mul continuous_const
  have hTsub : ∀ a b, T (a - b) = T a - T b := by
    intro a b
    funext x
    obtain ⟨N, hN⟩ := hrepr (f x)
    show ∑' m, (a - b) m * ψ t m (f x) =
      ∑' m, a m * ψ t m (f x) - ∑' m, b m * ψ t m (f x)
    rw [(hN (a - b)).2, (hN a).2, (hN b).2, ← Finset.sum_sub_distrib]
    simp [sub_mul]
  let P : (X → ℝ) → (ℕ → ℝ) := fun g n => g (xs n)
  have hPc : Continuous P := continuous_pi fun n => continuous_apply (xs n)
  have hPT : ∀ a, P (T a) = a := by
    intro a
    funext n
    show ∑' m, a m * ψ t m (t n) = a n
    rw [tsum_eq_single n (fun m hm => by rw [ψ_at hanti, ite_eq_right hm, mul_zero]),
      ψ_at hanti, ite_eq_left rfl, mul_one]
  have hfs_cont : ∀ p, Continuous (T (fs p)) := by
    intro p
    have : T (fs p) = fun x => ∑ m ∈ Finset.range p.1, fs p m * ψ t m (f x) := by
      funext x
      exact tsum_eq_sum fun m hm => by
        simp only [Finset.mem_range, not_lt] at hm
        rw [fs_eq_zero p m hm, zero_mul]
    rw [this]
    exact continuous_finsetSum _ fun m _ =>
      continuous_const.mul ((ψ_continuous m).comp hfc)
  /- Step 4: the countable set `A` and the closed set `L`. -/
  let A : Set (Cp X) := Subtype.val ⁻¹' (T '' range fs)
  have hAc : A.Countable :=
    ((countable_range fs).image T).preimage Subtype.val_injective
  let L : Set (X → ℝ) := {g | T (P g) = g}
  have hLc : IsClosed L := isClosed_eq (hTc.comp hPc) continuous_id
  have hAL : Subtype.val '' A ⊆ L := by
    rintro _ ⟨g, ⟨a, ⟨p, rfl⟩, hga⟩, rfl⟩
    show T (P g.1) = g.1
    rw [← hga, hPT]
  have hclA : ∀ g : Cp X, g ∈ closure A ↔ g.1 ∈ closure (Subtype.val '' A) := by
    intro g
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image A]
    rfl
  /- Step 5: the subgroup `G` and the homeomorphism `G ≃ₜ closure A`. -/
  let G : Set (ℕ → ℝ) := {a | Continuous (T a)}
  have hGsub : ∀ x ∈ G, ∀ y ∈ G, x - y ∈ G := by
    intro x hx y hy
    show Continuous (T (x - y))
    rw [hTsub]
    exact hx.sub hy
  have hGd : Dense G := dense_range_fs.mono (by rintro _ ⟨p, rfl⟩; exact hfs_cont p)
  have htoF : ∀ a : G, (⟨T a.1, a.2⟩ : Cp X) ∈ closure A := by
    intro a
    rw [hclA]
    have h1 : T a.1 ∈ closure (T '' range fs) :=
      map_mem_closure hTc (dense_range_fs a.1) (mapsTo_image T _)
    refine closure_mono ?_ h1
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    exact ⟨⟨T (fs p), hfs_cont p⟩, ⟨fs p, ⟨p, rfl⟩, rfl⟩, rfl⟩
  have hinL : ∀ g : closure A, T (P g.1.1) = g.1.1 := by
    intro g
    have := closure_minimal hAL hLc ((hclA g.1).1 g.2)
    exact this
  have hinvG : ∀ g : closure A, P g.1.1 ∈ G := by
    intro g
    show Continuous (T (P g.1.1))
    rw [hinL g]
    exact g.1.2
  let e : G ≃ₜ closure A :=
    { toFun := fun a => ⟨⟨T a.1, a.2⟩, htoF a⟩
      invFun := fun g => ⟨P g.1.1, hinvG g⟩
      left_inv := fun a => Subtype.ext (hPT a.1)
      right_inv := fun g => Subtype.ext (Subtype.ext (hinL g))
      continuous_toFun :=
        ((hTc.comp continuous_subtype_val).subtype_mk fun a => a.2).subtype_mk fun a => htoF a
      continuous_invFun :=
        (hPc.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk
          fun g => hinvG g }
  have hpG : Pseudocomplete G := (h A hAc).of_homeomorph e.symm
  /- Step 6: `G` is everything, so `T 1` is continuous; but `Z` would then be open. -/
  have h1G : (1 : ℕ → ℝ) ∈ G := dense_pseudocomplete_subgroup G hGsub hGd hpG 1
  have hT1 : ∀ x, T 1 x = ∑' m, ψ t m (f x) := fun x => by
    show ∑' m, (1 : ℕ → ℝ) m * ψ t m (f x) = _
    simp
  apply hZ
  have hZeq : f ⁻¹' {0} = T 1 ⁻¹' Iio (1 / 2) := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_Iio]
    rw [hT1]
    constructor
    · intro hx
      rw [hx]
      have : ∀ m, ψ t m 0 = 0 := fun m => ψ_vanish_left hanti m 0 (htpos (m + 1)).le
      simp [this]
    · intro hx
      by_contra hne
      have hpos : 0 < f x := lt_of_le_of_ne (hf0 x) (Ne.symm hne)
      obtain ⟨n, hn⟩ := ψ_pair_ge_one hanti hlim (f x) hpos
      obtain ⟨N, hN⟩ := hrepr (f x)
      have hs : Summable fun m => ψ t m (f x) := by simpa using (hN 1).1
      have hle := hs.sum_le_tsum {n, n + 1} (fun m _ => ψ_nonneg m (f x))
      rw [Finset.sum_pair (by omega)] at hle
      linarith
  rw [hZeq]
  exact isOpen_Iio.preimage h1G

end Question48

-- Sanity check: the main theorem depends only on the standard axioms.
#print axioms Question48.question_4_8
