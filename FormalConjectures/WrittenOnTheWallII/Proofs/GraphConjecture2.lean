/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-
Development for WOWII GraphConjecture2:
`2 * (averageIndepNeighbors G - 1) ≤ Ls G` for finite nontrivial connected `G`.

Proof structure:
* Lemma A (greedy connected domination + pendant attachment): for every edge `uv`,
  there is a spanning tree with at least `|N(u) ∪ N(v)| - 2` leaves.
* Lemma B (heavy edge): some edge has `n * |N(u) ∪ N(v)| ≥ 2 * ∑ α_v`, proved by
  double counting ordered adjacent pairs, the bound
  `E_x + a_x² + d_x ≤ d_x² + a_x` on adjacent pairs inside neighborhoods,
  and Cauchy–Schwarz.
-/


open Classical SimpleGraph Finset

namespace Gc2Dev

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

/- ### Closed neighborhoods of finsets -/

/-- The closed neighborhood of a `Finset` of vertices, as a `Finset`. -/
def cnf (G : SimpleGraph α) (W : Finset α) : Finset α :=
  W ∪ W.biUnion fun w => G.neighborFinset w

lemma mem_cnf {G : SimpleGraph α} {W : Finset α} {x : α} :
    x ∈ cnf G W ↔ x ∈ W ∨ ∃ w ∈ W, G.Adj w x := by
  simp [cnf, mem_neighborFinset]

lemma subset_cnf {G : SimpleGraph α} {W : Finset α} : W ⊆ cnf G W := by
  intro x hx; exact mem_cnf.mpr (Or.inl hx)

lemma cnf_mono {G : SimpleGraph α} {W W' : Finset α} (h : W ⊆ W') : cnf G W ⊆ cnf G W' := by
  intro x hx
  rcases mem_cnf.mp hx with hx | ⟨w, hw, hadj⟩
  · exact mem_cnf.mpr (Or.inl (h hx))
  · exact mem_cnf.mpr (Or.inr ⟨w, h hw, hadj⟩)

/- ### Greedy growth to a connected dominating subgraph -/

/-- Greedy growth: a connected subgraph grows to a connected subgraph whose closed
neighborhood is everything, adding at most one vertex per newly covered vertex. -/
lemma greedy (G : SimpleGraph α) (hG : G.Connected) :
    ∀ (k : ℕ) (H : G.Subgraph), H.Connected →
      Fintype.card α ≤ (cnf G H.verts.toFinset).card + k →
      ∃ H' : G.Subgraph, H'.Connected ∧
        (∀ x : α, x ∈ cnf G H'.verts.toFinset) ∧
        H'.verts.toFinset.card + (cnf G H.verts.toFinset).card ≤
          H.verts.toFinset.card + Fintype.card α := by
  intro k
  induction k with
  | zero =>
    intro H hHc hcard
    have hall : cnf G H.verts.toFinset = univ := by
      apply Finset.eq_univ_of_card
      exact le_antisymm (Finset.card_le_univ _) (by simpa using hcard)
    refine ⟨H, hHc, fun x => hall ▸ Finset.mem_univ x, ?_⟩
    have h1 := Finset.card_le_univ (cnf G H.verts.toFinset)
    simp only [Finset.card_univ] at h1
    omega
  | succ k ih =>
    intro H hHc hcard
    by_cases hall : cnf G H.verts.toFinset = univ
    · refine ⟨H, hHc, fun x => hall ▸ Finset.mem_univ x, ?_⟩
      have h1 := Finset.card_le_univ (cnf G H.verts.toFinset)
      simp only [Finset.card_univ] at h1
      omega
    · -- there is an uncovered vertex; find a boundary dart
      obtain ⟨y, hy⟩ := not_forall.mp (fun h => hall (Finset.eq_univ_iff_forall.mpr h))
      obtain ⟨w₀, hw₀⟩ := hHc.nonempty
      have hw₀' : w₀ ∈ cnf G H.verts.toFinset :=
        subset_cnf (Set.mem_toFinset.mpr hw₀)
      obtain ⟨p⟩ := hG.preconnected w₀ y
      obtain ⟨d, _, hd1, hd2⟩ :=
        p.exists_boundary_dart (↑(cnf G H.verts.toFinset) : Set α)
          (Finset.mem_coe.mpr hw₀') (fun hc => hy (Finset.mem_coe.mp hc))
      have hdadj : G.Adj d.toProd.1 d.toProd.2 := d.adj
      have hd1' : d.toProd.1 ∈ cnf G H.verts.toFinset := Finset.mem_coe.mp hd1
      have hd2' : d.toProd.2 ∉ cnf G H.verts.toFinset := fun hc => hd2 (Finset.mem_coe.mpr hc)
      -- the source of the dart is adjacent to `H.verts`
      obtain ⟨w', hw', hadjw⟩ : ∃ w' ∈ H.verts.toFinset, G.Adj w' d.toProd.1 := by
        rcases mem_cnf.mp hd1' with h | h
        · exact absurd (mem_cnf.mpr (Or.inr ⟨d.toProd.1, h, hdadj⟩)) hd2'
        · exact h
      -- extend the subgraph by the edge w' - d.1
      set H₂ : G.Subgraph := H ⊔ G.subgraphOfAdj hadjw with hH₂
      have hH₂c : H₂.Connected := by
        refine Subgraph.connected_sup hHc.preconnected
          (Subgraph.subgraphOfAdj_connected hadjw).preconnected ⟨w', ?_⟩
        simp [Subgraph.verts_inf, Set.mem_toFinset.mp hw']
      have hverts₂ : H₂.verts = H.verts ∪ {w', d.toProd.1} := by
        rw [hH₂]
        simp [Subgraph.verts_sup]
      have hsubW : H₂.verts.toFinset ⊆ insert d.toProd.1 H.verts.toFinset := by
        intro z hz
        rw [Set.mem_toFinset, hverts₂] at hz
        rcases hz with hz | hz
        · exact Finset.mem_insert_of_mem (Set.mem_toFinset.mpr hz)
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl
          · exact Finset.mem_insert_of_mem hw'
          · exact Finset.mem_insert_self _ _
      have hcard₂ : H₂.verts.toFinset.card ≤ H.verts.toFinset.card + 1 := by
        calc H₂.verts.toFinset.card ≤ (insert d.toProd.1 H.verts.toFinset).card :=
              Finset.card_le_card hsubW
        _ ≤ H.verts.toFinset.card + 1 := Finset.card_insert_le _ _
      have hWsub₂ : H.verts.toFinset ⊆ H₂.verts.toFinset := by
        intro z hz
        rw [Set.mem_toFinset, hverts₂]
        exact Or.inl (Set.mem_toFinset.mp hz)
      have hcnfsub : cnf G H.verts.toFinset ⊆ cnf G H₂.verts.toFinset := cnf_mono hWsub₂
      have hd2in : d.toProd.2 ∈ cnf G H₂.verts.toFinset := by
        refine mem_cnf.mpr (Or.inr ⟨d.toProd.1, ?_, hdadj⟩)
        rw [Set.mem_toFinset, hverts₂]
        exact Or.inr (Or.inr rfl)
      have hcnfgrow : (cnf G H.verts.toFinset).card + 1 ≤ (cnf G H₂.verts.toFinset).card := by
        have hss : cnf G H.verts.toFinset ⊂ cnf G H₂.verts.toFinset :=
          (Finset.ssubset_iff_of_subset hcnfsub).mpr ⟨d.toProd.2, hd2in, hd2'⟩
        exact Finset.card_lt_card hss
      have hcard₂' : Fintype.card α ≤ (cnf G H₂.verts.toFinset).card + k := by omega
      obtain ⟨H', hH'c, hH'dom, hH'card⟩ := ih H₂ hH₂c hcard₂'
      exact ⟨H', hH'c, hH'dom, by omega⟩

/- ### Pendant attachment: many leaves from a small connected dominating subgraph -/

/-- Transporting `IsTree` along a graph isomorphism. -/
lemma isTree_of_iso {V W : Type*} {G1 : SimpleGraph V} {G2 : SimpleGraph W}
    (e : G1 ≃g G2) (h : G1.IsTree) : G2.IsTree := by
  constructor
  · exact h.isConnected.map e.toHom e.toEquiv.surjective
  · intro v c hc
    exact h.IsAcyclic (c.map e.symm.toHom)
      ((Walk.map_isCycle_iff_of_injective (by exact e.symm.toEquiv.injective)).mpr hc)

/-- From a connected subgraph whose closed neighborhood is everything, we obtain a
spanning tree of `G` in which every vertex outside the subgraph is a leaf. -/
lemma exists_spanning_tree_leaves (G : SimpleGraph α)
    (H : G.Subgraph) (hHc : H.Connected)
    (hdom : ∀ x : α, x ∈ cnf G H.verts.toFinset) :
    ∃ T : G.Subgraph, T.IsSpanning ∧ T.coe.IsTree ∧
      Fintype.card α ≤
        ((Set.toFinset T.verts).filter fun v => T.degree v = 1).card
          + H.verts.toFinset.card := by
  classical
  set W : Set α := H.verts with hW
  -- choose a dominating neighbor for each vertex outside W
  have hchoice : ∀ x : α, x ∉ W → ∃ w, w ∈ W ∧ G.Adj w x := by
    intro x hx
    rcases mem_cnf.mp (hdom x) with h | ⟨w, hw, hadj⟩
    · exact absurd (Set.mem_toFinset.mp h) hx
    · exact ⟨w, Set.mem_toFinset.mp hw, hadj⟩
  choose pend hpendW hpendAdj using hchoice
  -- the pendant-augmented graph
  set G' : SimpleGraph α :=
    { Adj := fun a b => H.spanningCoe.Adj a b ∨
        (∃ h : a ∉ W, pend a h = b) ∨ (∃ h : b ∉ W, pend b h = a)
      symm := by
        rintro a b (h | ⟨ha, e⟩ | ⟨hb, e⟩)
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr ⟨ha, e⟩)
        · exact Or.inr (Or.inl ⟨hb, e⟩)
      loopless := by
        rintro a (h | ⟨ha, e⟩ | ⟨ha, e⟩)
        · exact H.spanningCoe.loopless a h
        · exact ha (e ▸ hpendW a ha)
        · exact ha (e ▸ hpendW a ha) } with hG'
  have hG'le : G' ≤ G := by
    rintro a b (h | ⟨ha, e⟩ | ⟨hb, e⟩)
    · exact H.spanningCoe_le h
    · exact e ▸ (hpendAdj a ha).symm
    · exact e ▸ (hpendAdj b hb)
  -- G' is connected
  obtain ⟨w₀, hw₀⟩ := hHc.nonempty
  have hreach : ∀ x : α, G'.Reachable x w₀ := by
    have hinW : ∀ x : α, x ∈ W → G'.Reachable x w₀ := by
      intro x hx
      have hr : H.coe.Reachable ⟨x, hx⟩ ⟨w₀, hw₀⟩ := hHc.coe.preconnected _ _
      exact hr.map ⟨Subtype.val, fun {a b} hab => Or.inl hab⟩
    intro x
    by_cases hx : x ∈ W
    · exact hinW x hx
    · have hadj : G'.Adj x (pend x hx) := Or.inr (Or.inl ⟨hx, rfl⟩)
      exact hadj.reachable.trans (hinW _ (hpendW x hx))
  have hG'conn : G'.Connected := by
    rw [connected_iff]
    refine ⟨fun a b => (hreach a).trans (hreach b).symm, ⟨w₀⟩⟩
  -- pendant vertices have G'-degree 1
  have hpendNbhd : ∀ (x : α) (hx : x ∉ W), G'.neighborFinset x = {pend x hx} := by
    intro x hx
    ext z
    simp only [mem_neighborFinset, Finset.mem_singleton]
    constructor
    · rintro (h | ⟨hx', e⟩ | ⟨hz, e⟩)
      · exact absurd (H.edge_vert h) hx
      · exact e.symm
      · exact absurd (e ▸ hpendW z hz) hx
    · rintro rfl
      exact Or.inr (Or.inl ⟨hx, rfl⟩)
  -- a spanning tree of G'
  obtain ⟨T', hT'le, hT'tree⟩ := hG'conn.exists_isTree_le
  have hT'leG : T' ≤ G := hT'le.trans hG'le
  refine ⟨SimpleGraph.toSubgraph T' hT'leG, SimpleGraph.toSubgraph.isSpanning T' hT'leG, ?_, ?_⟩
  · -- the coe of the spanning subgraph is a tree
    have e : (SimpleGraph.toSubgraph T' hT'leG).coe ≃g T' :=
      ⟨Equiv.Set.univ α, fun {a b} => Iff.rfl⟩
    exact isTree_of_iso e.symm hT'tree
  · -- vertices outside W are leaves of the tree
    have hleaf : ∀ (x : α), x ∉ W → (SimpleGraph.toSubgraph T' hT'leG).degree x = 1 := by
      intro x hx
      rw [degree_toSubgraph]
      have hle1 : T'.degree x ≤ 1 := by
        have hsub : T'.neighborFinset x ⊆ G'.neighborFinset x := by
          intro z hz
          rw [mem_neighborFinset] at hz ⊢
          exact hT'le hz
        calc T'.degree x = (T'.neighborFinset x).card := rfl
          _ ≤ (G'.neighborFinset x).card := Finset.card_le_card hsub
          _ = 1 := by rw [hpendNbhd x hx, Finset.card_singleton]
      have hge1 : 0 < T'.degree x := by
        rw [degree_pos_iff_exists_adj]
        have hxw : x ≠ w₀ := fun h => hx (h ▸ hw₀)
        obtain ⟨p⟩ := hT'tree.isConnected.preconnected x w₀
        cases p with
        | nil => exact absurd rfl hxw
        | cons h _ => exact ⟨_, h⟩
      omega
    -- count: every vertex is a leaf or in W
    have hcover : (univ : Finset α) ⊆
        (((Set.toFinset (SimpleGraph.toSubgraph T' hT'leG).verts).filter
            fun v => (SimpleGraph.toSubgraph T' hT'leG).degree v = 1) ∪ H.verts.toFinset) := by
      intro x _
      by_cases hx : x ∈ W
      · exact Finset.mem_union_right _ (Set.mem_toFinset.mpr hx)
      · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨?_, hleaf x hx⟩)
        rw [Set.mem_toFinset]
        exact Set.mem_univ x
    calc Fintype.card α = (univ : Finset α).card := (Finset.card_univ).symm
      _ ≤ _ := Finset.card_le_card hcover
      _ ≤ _ := Finset.card_union_le _ _

/- ### Lemma A: a spanning tree with `|N(u) ∪ N(v)| - 2` leaves -/

lemma lemA (G : SimpleGraph α) (hG : G.Connected) {u v : α} (huv : G.Adj u v) :
    ∃ T : G.Subgraph, T.IsSpanning ∧ T.coe.IsTree ∧
      (G.neighborSet u ∪ G.neighborSet v).ncard ≤
        ((Set.toFinset T.verts).filter fun x => T.degree x = 1).card + 2 := by
  classical
  set H₀ : G.Subgraph := G.subgraphOfAdj huv with hH₀
  have hH₀verts : H₀.verts.toFinset = {u, v} := by
    rw [hH₀]
    simp
  have hH₀card : H₀.verts.toFinset.card ≤ 2 := by
    rw [hH₀verts]
    exact (Finset.card_insert_le _ _).trans (by simp)
  have hcnf₀ : cnf G H₀.verts.toFinset = G.neighborFinset u ∪ G.neighborFinset v := by
    ext x
    rw [mem_cnf, hH₀verts]
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, mem_neighborFinset]
    constructor
    · rintro ((rfl | rfl) | ⟨w, (rfl | rfl), hadj⟩)
      · exact Or.inr huv.symm
      · exact Or.inl huv
      · exact Or.inl hadj
      · exact Or.inr hadj
    · rintro (h | h)
      · exact Or.inr ⟨u, Or.inl rfl, h⟩
      · exact Or.inr ⟨v, Or.inr rfl, h⟩
  obtain ⟨H', hH'c, hH'dom, hH'card⟩ :=
    greedy G hG (Fintype.card α) H₀ (Subgraph.subgraphOfAdj_connected huv) (by omega)
  obtain ⟨T, hsp, htree, hcount⟩ := exists_spanning_tree_leaves G H' hH'c hH'dom
  refine ⟨T, hsp, htree, ?_⟩
  have hbridge : (G.neighborSet u ∪ G.neighborSet v).ncard
      = (G.neighborFinset u ∪ G.neighborFinset v).card := by
    rw [Set.ncard_eq_toFinset_card' (G.neighborSet u ∪ G.neighborSet v)]
    congr 1
    ext z
    simp [mem_neighborFinset]
  rw [hbridge]
  rw [hcnf₀] at hH'card
  omega

/- ### Lower bound for `Ls` from a spanning tree with many leaves -/

lemma card_leaves_le_Ls (G : SimpleGraph α) (instD : DecidableRel G.Adj)
    (T : G.Subgraph) (hsp : T.IsSpanning) (htree : T.coe.IsTree) (c : ℕ)
    (hc : c ≤ ((Set.toFinset T.verts).filter fun x => T.degree x = 1).card) :
    (c : ℝ) ≤ @Ls α _ G instD := by
  classical
  unfold Ls
  have hbdd : BddAbove (Set.image
      (fun T'' : G.Subgraph =>
        (((T''.verts.toFinset.filter fun v => T''.degree v = 1)).card : ℝ))
      { T'' : G.Subgraph | T''.IsSpanning ∧ T''.coe.IsTree }) := by
    refine ⟨(Fintype.card α : ℝ), ?_⟩
    rintro y ⟨T'', -, rfl⟩
    dsimp only
    have h1 : (T''.verts.toFinset.filter fun v => T''.degree v = 1).card ≤
        T''.verts.toFinset.card := Finset.card_filter_le _ _
    have h2 : T''.verts.toFinset.card ≤ Fintype.card α := by
      simpa using Finset.card_le_univ T''.verts.toFinset
    exact_mod_cast h1.trans h2
  refine le_trans ?_ (le_csSup hbdd ⟨T, ⟨hsp, htree⟩, rfl⟩)
  dsimp only
  exact_mod_cast hc

/- ### Lemma B: existence of a heavy edge -/

/-- The ordered adjacent pairs of a graph. -/
def adjPairs (G : SimpleGraph α) : Finset (α × α) :=
  univ.filter fun p => G.Adj p.1 p.2

lemma mem_adjPairs {G : SimpleGraph α} {p : α × α} :
    p ∈ adjPairs G ↔ G.Adj p.1 p.2 := by
  simp [adjPairs]

lemma sum_adjPairs {M : Type*} [AddCommMonoid M] (G : SimpleGraph α) (F : α × α → M) :
    ∑ p ∈ adjPairs G, F p = ∑ u, ∑ w ∈ G.neighborFinset u, F (u, w) := by
  classical
  rw [adjPairs, ← Finset.univ_product_univ, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [neighborFinset_eq_filter, Finset.sum_filter]

lemma card_adjPairs (G : SimpleGraph α) : (adjPairs G).card = ∑ u, G.degree u := by
  classical
  rw [Finset.card_eq_sum_ones, sum_adjPairs G (fun _ => 1)]
  refine Finset.sum_congr rfl fun u _ => ?_
  dsimp only
  rw [Finset.sum_const, smul_eq_mul, mul_one]
  rfl

lemma sum_fst_degree (G : SimpleGraph α) :
    ∑ p ∈ adjPairs G, G.degree p.1 = ∑ u, G.degree u * G.degree u := by
  classical
  rw [sum_adjPairs G (fun q => G.degree q.1)]
  refine Finset.sum_congr rfl fun u _ => ?_
  dsimp only
  rw [Finset.sum_const, smul_eq_mul]
  rfl

lemma sum_snd_degree (G : SimpleGraph α) :
    ∑ p ∈ adjPairs G, G.degree p.2 = ∑ u, G.degree u * G.degree u := by
  classical
  rw [← sum_fst_degree]
  refine Finset.sum_equiv (Equiv.prodComm α α) ?_ ?_
  · intro p
    simp [mem_adjPairs, SimpleGraph.adj_comm]
  · intro p _
    rfl

/-- Ordered adjacent pairs inside the neighborhood of `x`. -/
def localPairs (G : SimpleGraph α) (x : α) : Finset (α × α) :=
  ((G.neighborFinset x) ×ˢ (G.neighborFinset x)).filter fun p => G.Adj p.1 p.2

lemma sum_codeg (G : SimpleGraph α) :
    ∑ p ∈ adjPairs G, (G.neighborFinset p.1 ∩ G.neighborFinset p.2).card
      = ∑ x, (localPairs G x).card := by
  classical
  have h1 : ∀ p : α × α,
      (G.neighborFinset p.1 ∩ G.neighborFinset p.2).card
        = ∑ x, if G.Adj p.1 x ∧ G.Adj p.2 x then 1 else 0 := by
    intro p
    rw [show G.neighborFinset p.1 ∩ G.neighborFinset p.2
        = univ.filter (fun x => G.Adj p.1 x ∧ G.Adj p.2 x) by
      ext x; simp [mem_neighborFinset]]
    rw [Finset.card_filter]
  have h2 : ∀ x : α,
      (localPairs G x).card
        = ∑ p ∈ adjPairs G, if G.Adj p.1 x ∧ G.Adj p.2 x then 1 else 0 := by
    intro x
    rw [show localPairs G x = (adjPairs G).filter (fun p => G.Adj p.1 x ∧ G.Adj p.2 x) by
      ext p
      simp only [localPairs, Finset.mem_filter, Finset.mem_product, mem_neighborFinset,
        mem_adjPairs]
      constructor
      · rintro ⟨⟨ha, hb⟩, hc⟩
        exact ⟨hc, ha.symm, hb.symm⟩
      · rintro ⟨hc, ha, hb⟩
        exact ⟨⟨ha.symm, hb.symm⟩, hc⟩]
    rw [Finset.card_filter]
  calc ∑ p ∈ adjPairs G, (G.neighborFinset p.1 ∩ G.neighborFinset p.2).card
      = ∑ p ∈ adjPairs G, ∑ x, if G.Adj p.1 x ∧ G.Adj p.2 x then 1 else 0 :=
        Finset.sum_congr rfl fun p _ => h1 p
    _ = ∑ x, ∑ p ∈ adjPairs G, if G.Adj p.1 x ∧ G.Adj p.2 x then 1 else 0 :=
        Finset.sum_comm
    _ = ∑ x, (localPairs G x).card := Finset.sum_congr rfl fun x _ => (h2 x).symm

lemma exists_indep_in_neighborhood (G : SimpleGraph α) (x : α) :
    ∃ S : Finset α, S ⊆ G.neighborFinset x ∧ S.card = indepNeighborsCard G x ∧
      ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ G.Adj a b := by
  classical
  obtain ⟨s, hs⟩ := (G.induce (G.neighborSet x)).exists_isNIndepSet_indepNum
  refine ⟨s.map ⟨Subtype.val, Subtype.val_injective⟩, ?_, ?_, ?_⟩
  · intro a ha
    rw [Finset.mem_map] at ha
    obtain ⟨b, _, rfl⟩ := ha
    rw [SimpleGraph.mem_neighborFinset]
    exact b.2
  · rw [Finset.card_map, hs.card_eq]
    rfl
  · intro a ha b hb hab hadj
    rw [Finset.mem_map] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have hne : a' ≠ b' := fun h => hab (by rw [h])
    exact hs.isIndepSet (Finset.mem_coe.mpr ha') (Finset.mem_coe.mpr hb') hne
      (by simpa [SimpleGraph.comap_adj] using hadj)

lemma indepNC_le_degree (G : SimpleGraph α) (x : α) :
    indepNeighborsCard G x ≤ G.degree x := by
  obtain ⟨S, hsub, hcard, -⟩ := exists_indep_in_neighborhood G x
  calc indepNeighborsCard G x = S.card := hcard.symm
    _ ≤ (G.neighborFinset x).card := Finset.card_le_card hsub
    _ = G.degree x := rfl

lemma nat_le_sq (n : ℕ) : n ≤ n * n := by
  cases n with
  | zero => simp
  | succ m => exact Nat.le_mul_of_pos_left _ (Nat.succ_pos m)

lemma localPairs_bound (G : SimpleGraph α) (x : α) :
    (localPairs G x).card + indepNeighborsCard G x * indepNeighborsCard G x + G.degree x
      ≤ G.degree x * G.degree x + indepNeighborsCard G x := by
  classical
  obtain ⟨S, hsub, hcard, hindep⟩ := exists_indep_in_neighborhood G x
  have hQsub : localPairs G x ⊆ (G.neighborFinset x).offDiag := by
    intro p hp
    rw [localPairs, Finset.mem_filter, Finset.mem_product] at hp
    exact Finset.mem_offDiag.mpr ⟨hp.1.1, hp.1.2, hp.2.ne⟩
  have hSsub : S.offDiag ⊆ (G.neighborFinset x).offDiag := by
    intro p hp
    rw [Finset.mem_offDiag] at hp ⊢
    exact ⟨hsub hp.1, hsub hp.2.1, hp.2.2⟩
  have hdisj : Disjoint (localPairs G x) S.offDiag := by
    rw [Finset.disjoint_left]
    intro p hp hpS
    rw [localPairs, Finset.mem_filter] at hp
    rw [Finset.mem_offDiag] at hpS
    exact hindep p.1 hpS.1 p.2 hpS.2.1 hpS.2.2 hp.2
  have hunion : (localPairs G x).card + S.offDiag.card
      ≤ ((G.neighborFinset x).offDiag).card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.union_subset hQsub hSsub)
  rw [Finset.offDiag_card, Finset.offDiag_card] at hunion
  have h1 : S.card ≤ S.card * S.card := nat_le_sq _
  have h2 : (G.neighborFinset x).card ≤ (G.neighborFinset x).card * (G.neighborFinset x).card :=
    nat_le_sq _
  have hdeg : (G.neighborFinset x).card = G.degree x := rfl
  rw [hdeg] at hunion h2
  rw [hcard] at hunion h1
  omega

lemma exists_adj [Nontrivial α] (G : SimpleGraph α) (hG : G.Connected) :
    ∃ u v : α, G.Adj u v := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne α
  obtain ⟨p⟩ := hG.preconnected u v
  cases p with
  | nil => exact absurd rfl huv
  | cons h _ => exact ⟨_, _, h⟩

/-- Lemma B: some ordered adjacent pair has neighborhood-union of size at least
`2 A / n` (in multiplied-out integer form). -/
lemma lemB [Nontrivial α] (G : SimpleGraph α) (hG : G.Connected) :
    ∃ p : α × α, G.Adj p.1 p.2 ∧
      2 * (∑ x, indepNeighborsCard G x) ≤
        Fintype.card α * (G.neighborSet p.1 ∪ G.neighborSet p.2).ncard := by
  classical
  -- nonempty adjacent pairs
  obtain ⟨u₀, v₀, huv₀⟩ := exists_adj G hG
  have hPne : (adjPairs G).Nonempty := ⟨(u₀, v₀), mem_adjPairs.mpr huv₀⟩
  -- the maximizing pair
  obtain ⟨p₀, hp₀mem, hp₀max⟩ := Finset.exists_max_image (adjPairs G)
    (fun p => (G.neighborFinset p.1 ∪ G.neighborFinset p.2).card) hPne
  refine ⟨p₀, mem_adjPairs.mp hp₀mem, ?_⟩
  have hbridge : (G.neighborSet p₀.1 ∪ G.neighborSet p₀.2).ncard
      = (G.neighborFinset p₀.1 ∪ G.neighborFinset p₀.2).card := by
    rw [Set.ncard_eq_toFinset_card' (G.neighborSet p₀.1 ∪ G.neighborSet p₀.2)]
    congr 1
    ext z
    simp [mem_neighborFinset]
  rw [hbridge]
  -- notation (plain ℕ abbreviations)
  set n := Fintype.card α with hn
  set A := ∑ x, indepNeighborsCard G x with hA
  set D := ∑ x, G.degree x with hD
  set S2 := ∑ x, G.degree x * G.degree x with hS2
  set A2 := ∑ x, indepNeighborsCard G x * indepNeighborsCard G x with hA2
  set E := ∑ x, (localPairs G x).card with hE
  set M := (G.neighborFinset p₀.1 ∪ G.neighborFinset p₀.2).card with hM
  set SU := ∑ p ∈ adjPairs G, (G.neighborFinset p.1 ∪ G.neighborFinset p.2).card with hSU
  -- sum of unions is at most |P| * M
  have hsumU : SU ≤ D * M := by
    rw [hSU, hD, ← card_adjPairs, ← smul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun p hp => hp₀max p hp
  -- union + inter = degree sum, summed
  have hUI : SU + E = 2 * S2 := by
    rw [hSU, hE, ← sum_codeg, ← Finset.sum_add_distrib]
    have hstep : ∀ p ∈ adjPairs G,
        (G.neighborFinset p.1 ∪ G.neighborFinset p.2).card
          + (G.neighborFinset p.1 ∩ G.neighborFinset p.2).card
        = G.degree p.1 + G.degree p.2 := fun p _ =>
      Finset.card_union_add_card_inter _ _
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, sum_fst_degree, sum_snd_degree, hS2]
    omega
  -- local pair bound, summed
  have hEbound : E + A2 + D ≤ S2 + A := by
    have hs := Finset.sum_le_sum (s := (univ : Finset α))
      (f := fun x => (localPairs G x).card
        + indepNeighborsCard G x * indepNeighborsCard G x + G.degree x)
      (g := fun x => G.degree x * G.degree x + indepNeighborsCard G x)
      (fun x _ => localPairs_bound G x)
    simp only [Finset.sum_add_distrib] at hs
    rw [hE, hA2, hD, hS2, hA]
    omega
  -- Cauchy–Schwarz (in ℕ)
  have hCSd : D * D ≤ n * S2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset α)) (f := fun x => G.degree x)
    simp only [Finset.card_univ, Nat.cast_id] at h
    calc D * D = (∑ x, G.degree x) ^ 2 := by rw [hD]; ring
      _ ≤ Fintype.card α * ∑ x, G.degree x ^ 2 := h
      _ = n * S2 := by
          rw [hn, hS2]
          congr 1
          exact Finset.sum_congr rfl fun x _ => by ring
  have hCSa : A * A ≤ n * A2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset α))
      (f := fun x => indepNeighborsCard G x)
    simp only [Finset.card_univ, Nat.cast_id] at h
    calc A * A = (∑ x, indepNeighborsCard G x) ^ 2 := by rw [hA]; ring
      _ ≤ Fintype.card α * ∑ x, indepNeighborsCard G x ^ 2 := h
      _ = n * A2 := by
          rw [hn, hA2]
          congr 1
          exact Finset.sum_congr rfl fun x _ => by ring
  -- A ≤ D
  have hAD : A ≤ D := by
    rw [hA, hD]
    exact Finset.sum_le_sum fun x _ => indepNC_le_degree G x
  -- D ≥ 1
  have hD1 : 1 ≤ D := by
    have hne : (adjPairs G).card ≠ 0 := Finset.card_ne_zero_of_mem hp₀mem
    rw [card_adjPairs, ← hD] at hne
    omega
  -- assemble over ℝ
  have hgoal : (2 : ℝ) * A ≤ (n : ℝ) * M := by
    have hsumU' : (SU : ℝ) ≤ (D : ℝ) * M := by exact_mod_cast hsumU
    have hUI' : (SU : ℝ) + E = 2 * (S2 : ℝ) := by exact_mod_cast hUI
    have hEbound' : (E : ℝ) + A2 + D ≤ (S2 : ℝ) + A := by exact_mod_cast hEbound
    have hCSd' : (D : ℝ) * D ≤ (n : ℝ) * S2 := by exact_mod_cast hCSd
    have hCSa' : (A : ℝ) * A ≤ (n : ℝ) * A2 := by exact_mod_cast hCSa
    have hAD' : (A : ℝ) ≤ (D : ℝ) := by exact_mod_cast hAD
    have hD1' : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have key : 2 * (A : ℝ) * D + (n : ℝ) * ((D : ℝ) - A) ≤ (D : ℝ) * ((n : ℝ) * M) := by
      nlinarith [mul_le_mul_of_nonneg_left hEbound' hn0,
        mul_le_mul_of_nonneg_left hsumU' hn0,
        mul_le_mul_of_nonneg_left hAD' hn0]
    nlinarith [key, mul_le_mul_of_nonneg_left hAD' hn0]
  exact_mod_cast hgoal

/- ### Main theorem -/

lemma main {β : Type*} [Fintype β] [DecidableEq β] [Nontrivial β] (G : SimpleGraph β)
    (instD : DecidableRel G.Adj) (hG : G.Connected) :
    2 * (averageIndepNeighbors G - 1) ≤ @Ls β _ G instD := by
  classical
  obtain ⟨p, hadj, hkey⟩ := lemB G hG
  obtain ⟨T, hsp, htree, hleaf⟩ := lemA G hG hadj
  set c := ((Set.toFinset T.verts).filter fun x => T.degree x = 1).card with hc
  have hLs : (c : ℝ) ≤ @Ls β _ G instD := card_leaves_le_Ls G instD T hsp htree c le_rfl
  have hn0 : (0 : ℝ) < (Fintype.card β : ℝ) := by
    have : 0 < Fintype.card β := Fintype.card_pos
    exact_mod_cast this
  have havg : averageIndepNeighbors G
      = ((∑ x, indepNeighborsCard G x : ℕ) : ℝ) / (Fintype.card β : ℝ) := by
    simp only [averageIndepNeighbors, indepNeighbors]
    rw [Nat.cast_sum]
  have hexp : 2 * (((∑ x, indepNeighborsCard G x : ℕ) : ℝ) / (Fintype.card β : ℝ) - 1)
      = (2 * ((∑ x, indepNeighborsCard G x : ℕ) : ℝ) - 2 * (Fintype.card β : ℝ))
          / (Fintype.card β : ℝ) := by
    field_simp
  rw [havg, hexp, div_le_iff₀ hn0]
  have hkey' : (2 : ℝ) * ((∑ x, indepNeighborsCard G x : ℕ) : ℝ) ≤
      (Fintype.card β : ℝ) * (((G.neighborSet p.1 ∪ G.neighborSet p.2).ncard : ℕ) : ℝ) := by
    exact_mod_cast hkey
  have hleaf' : (((G.neighborSet p.1 ∪ G.neighborSet p.2).ncard : ℕ) : ℝ) ≤ (c : ℝ) + 2 := by
    exact_mod_cast hleaf
  nlinarith [hLs, hn0.le, mul_le_mul_of_nonneg_left hLs hn0.le,
    mul_le_mul_of_nonneg_left hleaf' hn0.le]

end

end Gc2Dev

namespace WrittenOnTheWallII.GraphConjecture2

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- WOWII Conjecture 2. -/
theorem conjecture2 (G : SimpleGraph α) (hG : G.Connected) :
    2 * (averageIndepNeighbors G - 1) ≤ Ls G := by
  exact Gc2Dev.main G _ hG

#print axioms conjecture2

end WrittenOnTheWallII.GraphConjecture2
