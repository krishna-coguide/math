module

public import VeryWellCovered.Defs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset

@[expose] public section

/-! The core is a join of two graphs, each a disjoint union of equal-sized cliques. -/

namespace VeryWellCovered

/-- Disjoint cliques: the first coordinate indexes the clique, the second its vertices. -/
def cliqueFamily (I L : Type*) : SimpleGraph (I × L) where
  Adj x y := x.1 = y.1 ∧ x ≠ y
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

/-- The join retains both induced graphs and includes every edge across the two sides. -/
def graphJoin {A B : Type*} (G : SimpleGraph A) (H : SimpleGraph B) : SimpleGraph (A ⊕ B) where
  Adj
    | .inl a, .inl b => G.Adj a b
    | .inr a, .inr b => H.Adj a b
    | _, _ => True
  symm := ⟨by rintro (a | a) (b | b) h <;> first | exact G.adj_symm h | exact H.adj_symm h | trivial⟩
  loopless := ⟨by rintro (a | b) <;> first | exact G.loopless.irrefl a | exact H.loopless.irrefl b⟩

/-- Vertices of the 7,296-vertex core. -/
abbrev CoreV := (Fin 192 × Fin 30) ⊕ (Fin 768 × Fin 2)

/-- Join of 192 disjoint 30-cliques with 768 disjoint edges. -/
def coreGraph : SimpleGraph CoreV :=
  graphJoin (cliqueFamily (Fin 192) (Fin 30)) (cliqueFamily (Fin 768) (Fin 2))

theorem card_coreV : Fintype.card CoreV = 7296 := by
  simp [CoreV, Fintype.card_sum, Fintype.card_prod]

theorem coreGraph_connected : coreGraph.Connected := by
  have cross (a b) : coreGraph.Reachable (.inl a) (.inr b) :=
    SimpleGraph.Adj.reachable (show coreGraph.Adj (.inl a) (.inr b) from trivial)
  constructor
  rintro (a | a) (b | b)
  · exact (cross a (0, 0)).trans (cross b (0, 0)).symm
  · exact cross a b
  · exact (cross b a).symm
  · exact (cross (0, 0) a).symm.trans (cross (0, 0) b)

private theorem count_eq_card {V : Type*} [Fintype V] (G : SimpleGraph V) (j : ℕ)
    [Fintype {s // G.IsNIndepSet j s}] :
    independentCount G j = Fintype.card {s // G.IsNIndepSet j s} := by
  classical
  exact (Fintype.card_of_subtype _ fun _ => SimpleGraph.mem_indepSetFinset_iff).symm

section Side

variable {I L : Type*}

private theorem indep_cliqueFamily_iff (s : Finset (I × L)) :
    (cliqueFamily I L).IsIndepSet s ↔ Set.InjOn Prod.fst (s : Set (I × L)) := by
  constructor
  · intro h x hx y hy heq
    by_contra hne
    exact h hx hy hne ⟨heq, hne⟩
  · intro h x hx y hy hne hadj
    exact hne (h hx hy hadj.1)

/-- From the occupied indices and a choice of label at each index, recover the vertices. -/
private def labeledSet (t : Finset I) (f : (↑t : Type _) → L) : Finset (I × L) :=
  t.attach.map ⟨fun i => (i.val, f i), fun _ _ h => Subtype.ext (congrArg Prod.fst h)⟩

private theorem mem_labeledSet {t : Finset I} {f : (↑t : Type _) → L} {i : I} {l : L} :
    (i, l) ∈ labeledSet t f ↔ ∃ h : i ∈ t, f ⟨i, h⟩ = l := by
  constructor
  · intro h
    obtain ⟨⟨i', hi'⟩, _, he⟩ := Finset.mem_map.mp h
    change (i', f ⟨i', hi'⟩) = (i, l) at he
    cases he
    exact ⟨hi', rfl⟩
  · rintro ⟨hi, rfl⟩
    exact Finset.mem_map.mpr ⟨⟨i, hi⟩, t.mem_attach _, rfl⟩

private theorem image_labeledSet (t : Finset I) (f : (↑t : Type _) → L) [DecidableEq I] :
    (labeledSet t f).image Prod.fst = t := by
  ext i
  constructor
  · rintro h
    obtain ⟨⟨j, l⟩, hm, rfl⟩ := Finset.mem_image.mp h
    exact (mem_labeledSet.mp hm).choose
  · intro hi
    exact Finset.mem_image.mpr ⟨(i, f ⟨i, hi⟩), mem_labeledSet.mpr ⟨hi, rfl⟩, rfl⟩

private theorem labeledSet_indep (t : Finset I) (f : (↑t : Type _) → L) :
    (cliqueFamily I L).IsIndepSet (labeledSet t f) := by
  rw [indep_cliqueFamily_iff]
  rintro ⟨i, a⟩ hx ⟨j, b⟩ hy (rfl : i = j)
  obtain ⟨hi, rfl⟩ := mem_labeledSet.mp hx
  obtain ⟨hi', rfl⟩ := mem_labeledSet.mp hy
  rfl

/-- A size-`j` transversal consists of a `j`-set of clique indices and one label per index. -/
private abbrev Labels (I L : Type*) (j : ℕ) :=
  (t : {s : Finset I // s.card = j}) × ((↑t.val : Type _) → L)

private def labelMap (j : ℕ) (p : Labels I L j) :
    {s : Finset (I × L) // (cliqueFamily I L).IsNIndepSet j s} :=
  ⟨labeledSet p.1.val p.2, labeledSet_indep _ _, by simp [labeledSet, p.1.property]⟩

private theorem labelMap_bijective (j : ℕ) : Function.Bijective (labelMap (I := I) (L := L) j) := by
  classical
  constructor
  · rintro ⟨⟨t, ht⟩, f⟩ ⟨⟨u, hu⟩, g⟩ he
    have eqs : labeledSet t f = labeledSet u g := congrArg Subtype.val he
    have et : t = u := by simpa only [image_labeledSet] using congrArg (Finset.image Prod.fst) eqs
    subst u
    congr
    funext i
    have h : (i.val, f i) ∈ labeledSet t g := eqs ▸ mem_labeledSet.mpr ⟨i.property, rfl⟩
    exact (mem_labeledSet.mp h).choose_spec.symm
  · rintro ⟨s, hs⟩
    have inj := (indep_cliqueFamily_iff s).mp hs.isIndepSet
    let t := s.image Prod.fst
    have hasLabel (i : t) : ∃ l : L, (i.val, l) ∈ s := by
      obtain ⟨⟨a, l⟩, ha, he⟩ := Finset.mem_image.mp i.property
      exact ⟨l, he ▸ ha⟩
    let f (i : t) := (hasLabel i).choose
    have chosen (i : t) : (i.val, f i) ∈ s := (hasLabel i).choose_spec
    refine ⟨⟨⟨t, (Finset.card_image_of_injOn inj).trans hs.card_eq⟩, f⟩, Subtype.ext ?_⟩
    change labeledSet t f = s
    ext ⟨i, l⟩
    constructor
    · rintro h
      obtain ⟨hi, rfl⟩ := mem_labeledSet.mp h
      exact chosen ⟨i, hi⟩
    · intro h
      have hi : i ∈ t := Finset.mem_image.mpr ⟨(i, l), h, rfl⟩
      exact mem_labeledSet.mpr ⟨hi, congrArg Prod.snd (inj (chosen ⟨i, hi⟩) h rfl)⟩

/-- Choose the occupied cliques and then one label in each. -/
theorem independentCount_cliqueFamily [Fintype I] [Fintype L] (j : ℕ) :
    independentCount (cliqueFamily I L) j = (Fintype.card I).choose j * (Fintype.card L) ^ j := by
  classical
  let e := Equiv.ofBijective _ (labelMap_bijective (I := I) (L := L) j)
  calc
    independentCount (cliqueFamily I L) j = Fintype.card {s // (cliqueFamily I L).IsNIndepSet j s} :=
      count_eq_card _ _
    _ = Fintype.card (Labels I L j) := (Fintype.card_congr e).symm
    _ = _ := by
      have hc (t : {s : Finset I // s.card = j}) : t.val.card = j := t.property
      simp [Labels, hc]

end Side

section Join

variable {A B : Type*} {G : SimpleGraph A} {H : SimpleGraph B} {j : ℕ}

private theorem indep_left_iff (s : Finset A) :
    (graphJoin G H).IsNIndepSet j (s.disjSum ∅) ↔ G.IsNIndepSet j s := by
  simp only [SimpleGraph.isNIndepSet_iff, Finset.card_disjSum, Finset.card_empty, Nat.add_zero]
  simp only [SimpleGraph.isIndepSet_iff, Set.Pairwise, Finset.mem_coe, Sum.forall,
    Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, Finset.notMem_empty, false_implies,
    implies_true, and_true, ne_eq, Sum.inl.injEq, graphJoin]

private theorem indep_right_iff (s : Finset B) :
    (graphJoin G H).IsNIndepSet j ((∅ : Finset A).disjSum s) ↔ H.IsNIndepSet j s := by
  simp only [SimpleGraph.isNIndepSet_iff, Finset.card_disjSum, Finset.card_empty, Nat.zero_add]
  simp only [SimpleGraph.isIndepSet_iff, Set.Pairwise, Finset.mem_coe, Sum.forall,
    Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, Finset.notMem_empty, false_implies,
    implies_true, true_and, ne_eq, Sum.inr.injEq, graphJoin]

private def liftSide :
    ({s // G.IsNIndepSet j s} ⊕ {s // H.IsNIndepSet j s}) →
    {s // (graphJoin G H).IsNIndepSet j s}
  | .inl s => ⟨s.val.disjSum ∅, indep_left_iff _ |>.mpr s.property⟩
  | .inr s => ⟨(∅ : Finset A).disjSum s.val, indep_right_iff _ |>.mpr s.property⟩

private theorem liftSide_bijective (hj : j ≠ 0) : Function.Bijective (liftSide (G := G) (H := H) (j := j)) := by
  constructor
  · rintro (s | s) (t | t) h
    · exact congrArg Sum.inl (Subtype.ext (Finset.disjSum_inj.mp (congrArg Subtype.val h)).1)
    · have he := (Finset.disjSum_inj.mp (congrArg Subtype.val h)).1
      exact (hj (s.property.card_eq.symm.trans (Finset.card_eq_zero.mpr he))).elim
    · have he := (Finset.disjSum_inj.mp (congrArg Subtype.val h)).2
      exact (hj (s.property.card_eq.symm.trans (Finset.card_eq_zero.mpr he))).elim
    · exact congrArg Sum.inr (Subtype.ext (Finset.disjSum_inj.mp (congrArg Subtype.val h)).2)
  · rintro ⟨s, hs⟩
    have split : s.toLeft = ∅ ∨ s.toRight = ∅ := by
      by_contra! h
      obtain ⟨a, ha⟩ := h.1
      obtain ⟨b, hb⟩ := h.2
      exact hs.isIndepSet (Finset.mem_toLeft.mp ha) (Finset.mem_toRight.mp hb) (by simp) trivial
    rcases split with he | he
    · have eqs : (∅ : Finset A).disjSum s.toRight = s := he ▸ Finset.toLeft_disjSum_toRight
      exact ⟨.inr ⟨_, (indep_right_iff _).mp (eqs ▸ hs)⟩, Subtype.ext eqs⟩
    · have eqs : s.toLeft.disjSum (∅ : Finset B) = s := he ▸ Finset.toLeft_disjSum_toRight
      exact ⟨.inl ⟨_, (indep_left_iff _).mp (eqs ▸ hs)⟩, Subtype.ext eqs⟩

/-- An independent set of positive size lies on exactly one side of the join. -/
theorem independentCount_graphJoin [Fintype A] [Fintype B] (hj : j ≠ 0) :
    independentCount (graphJoin G H) j = independentCount G j + independentCount H j := by
  classical
  rw [count_eq_card, count_eq_card G, count_eq_card H,
    ← Fintype.card_sum, Fintype.card_congr (Equiv.ofBijective _ (liftSide_bijective hj)).symm]

end Join

private theorem independentCount_zero {V : Type*} [Fintype V] (G : SimpleGraph V) :
    independentCount G 0 = 1 := by
  classical
  have he : G.indepSetFinset 0 = {∅} := by
    ext s
    simp only [SimpleGraph.mem_indepSetFinset_iff, SimpleGraph.isNIndepSet_iff,
      Finset.card_eq_zero, Finset.mem_singleton]
    constructor
    · exact And.right
    · rintro rfl
      simp [SimpleGraph.isIndepSet_iff]
  simpa [independentCount] using congrArg Finset.card he

/-- All coefficients of the independence polynomial of the core, including the empty set. -/
theorem independentCount_core (j : ℕ) : independentCount coreGraph j = baseCount j := by
  by_cases hj : j = 0
  · subst j
    simp [independentCount_zero, baseCount]
  · simp [coreGraph, independentCount_graphJoin hj, independentCount_cliqueFamily, baseCount, hj]

private theorem le_indepNum_of_count_pos {V : Type*} [Fintype V] {G : SimpleGraph V} {j : ℕ}
    (h : 0 < independentCount G j) : j ≤ G.indepNum := by
  classical
  obtain ⟨s, hs⟩ := Finset.card_pos.mp h
  have hs' : G.IsNIndepSet j s := SimpleGraph.mem_indepSetFinset_iff.mp hs
  exact hs'.card_eq ▸ hs'.isIndepSet.card_le_indepNum

private theorem count_indepNum_pos {V : Type*} [Fintype V] (G : SimpleGraph V) :
    0 < independentCount G G.indepNum := by
  classical
  rw [independentCount_eq_card, Finset.card_pos]
  obtain ⟨s, hs⟩ := SimpleGraph.exists_isNIndepSet_indepNum (G := G)
  exact ⟨s, SimpleGraph.mem_indepSetFinset_iff.mpr hs⟩

theorem coreGraph_indepNum : coreGraph.indepNum = 768 := by
  apply Nat.le_antisymm
  · by_contra! h
    have hp := count_indepNum_pos coreGraph
    rw [independentCount_core, baseCount, ite_eq_right (by omega),
      Nat.choose_eq_zero_of_lt (show 192 < coreGraph.indepNum by omega),
      Nat.choose_eq_zero_of_lt h] at hp
    simp at hp
  · apply le_indepNum_of_count_pos
    rw [independentCount_core, baseCount, ite_eq_right (by decide),
      Nat.choose_eq_zero_of_lt (show 192 < 768 by decide), Nat.choose_self, zero_mul,
      one_mul, zero_add]
    exact pow_pos (by decide) _

theorem five_le_coreGraph_indepNum : 5 ≤ coreGraph.indepNum := by
  rw [coreGraph_indepNum]
  decide

end VeryWellCovered
