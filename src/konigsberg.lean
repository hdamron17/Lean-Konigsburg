import combinatorics.simple_graph.basic
import data.list.basic
import data.sum
import algebra.big_operators.basic
import data.list.rotate

-- Definition of multi_graph adapted from mathlib combinatorics.simple_graph

universe u

structure multi_graph (V : Type u) :=
  (adj : V → V → ℕ)
  (sym : ∀ ⦃u v : V⦄, adj u v = adj v u)

-- NOTE simple_graph is an extension with ∀ ⦃u v : V⦄, adj u v ≤ 1 and irreflexivity

namespace multi_graph
  variables {V : Type u} (G : multi_graph V)

  def adj_simple (u v : V) := G.adj u v > 0

  lemma sym_simple : symmetric G.adj_simple :=
  begin
    rw symmetric,
    intros u v,
    rw adj_simple,
    rw adj_simple,
    rw sym,
    simp,
  end

  def edge_set_simple : set (sym2 V) := sym2.from_rel G.sym_simple
  def neighbor_set_simple (v : V) := set_of (G.adj_simple v)

  lemma mem_neighbor_set (v w : V) : w ∈ G.neighbor_set_simple v ↔ G.adj_simple v w := iff.rfl

  def locally_finite := Π (v : V), fintype (G.neighbor_set_simple v)

  section decidable_eq
    variables [decidable_eq V]

    instance adj_simple_decidable_rel : decidable_rel (G.adj_simple) :=
    begin
      rw decidable_rel,
      intros u v,
      rw adj_simple,
      sorry
    end
  end decidable_eq

  section finite
    variables [fintype V] [decidable_eq V]

    instance neighbor_set_fintype (v : V) : fintype (G.neighbor_set_simple v) :=
    @subtype.fintype _ _ (by { simp_rw mem_neighbor_set, apply_instance }) _

    def neighbor_set_simple_finset (v : V) := (G.neighbor_set_simple v).to_finset
    def degree_simple (v : V) := (G.neighbor_set_simple_finset v).card
    def degree (v : V) := finset.sum (G.neighbor_set_simple_finset v) (G.adj v)
  end finite
end multi_graph

structure walk {V : Type u} (G : multi_graph V) :=
  (vertices : list V)
  (in_graph : list.chain' G.adj_simple vertices)
  -- (nonempty : vertices ≠ list.nil)

def closed_list {V : Type u} (l: list V) := l.head' = l.last'

namespace walk
  variables {V : Type u} {G : multi_graph V} [decidable_eq V] (W : walk G)

  def closed := closed_list W.vertices
  def edges : list (V × V) := list.zip W.vertices W.vertices.tail
  def edges_sym2 : list (sym2 V) := list.map (function.uncurry (λ (u v : V), ⟦(u, v)⟧)) W.edges
  def edges_count (u v : V) := W.edges_sym2.count ⟦(u,v)⟧
  def in_degree (v : V) := (W.edges.map prod.fst).count v
  def out_degree (v : V) := (W.edges.map prod.snd).count v
  def degree := W.in_degree + W.out_degree  -- Make sure we double count loops
  def edge_rel (u v: V) : Prop := ⟦(u,v)⟧ ∈ W.edges_sym2
  lemma edge_rel_sym : symmetric W.edge_rel :=
  begin
    rw symmetric,
    intros u v,
    rw edge_rel,
    rw sym2.eq_swap,
    rw ← edge_rel,
    simp,
  end
  def edge_set : set (sym2 V) := sym2.from_rel W.edge_rel_sym
  def eulerian := ∀ (u v: V), W.edges_count u v = G.adj u v
end walk


namespace multi_graph
  variables {V : Type u} (G : multi_graph V)

  def connected := ∀ ⦃u v : V⦄, ∃ (W : walk G),
    W.vertices.head' = u ∧ W.vertices.last' = v
end multi_graph

section eulerian

variables {V : Type u} (G : multi_graph V) [fintype V] [decidable_eq V] [decidable_rel G.adj_simple]

lemma count_eq_shift {v : V} {l₁ l₂: list V} (rot: l₂ = l₁.rotate 1) :
list.count v l₁ = list.count v l₂ :=
begin
  -- Base case empty list
  cases l₁,
  rw ← list.rotate_nil 1,
  rw rot,

  -- Inductive step
  rw rot,
  rw list.rotate_cons_succ,
  rw list.rotate_zero,
  rw list.count_append,
  rw add_comm,
  rw ← list.count_append,
  rw list.singleton_append,
end

lemma list_cons_unzip_sip_fst {V : Type u} (a b : V) (l : list V) :
((a :: b :: l).zip (b :: l)).unzip.fst = a :: ((b :: l).init) :=
begin
  simp,
  conv in ((b :: l).zip l){
    rw ← list.init_append_last (list.cons_ne_nil b l),
    congr,
    skip,
    rw ← list.append_nil l,
  },
  rw list.zip_append,
  rw list.zip_nil_right,
  rw list.append_nil,
  rw list.unzip_zip,
  simp,
  simp,
end

lemma circuit_indeg_eq_outdeg {W : walk G} (closed: W.closed) (v : V):
W.in_degree v = W.out_degree v :=
begin
  rw walk.in_degree,
  rw walk.out_degree,
  rw count_eq_shift,

  rw walk.edges,
  rw ← list.unzip_right,
  rw list.unzip_zip_right,
  swap,  -- Go ahead and show that tail is shorter
    rw (list.length_tail W.vertices),
    exact (nat.sub_le W.vertices.length 1),
  rw ← list.unzip_left,

  rw [walk.closed, closed_list] at closed,

  cases W.vertices,
    -- Base case empty list
    rw list.tail_nil,
    rw list.zip_nil_left,
    simp,

    cases tl,
      -- Singleton list
      simp,

      -- At least two elements
      rw list.tail_cons,
      rw list_cons_unzip_sip_fst hd tl_hd tl_tl,
      rw list.rotate_cons_succ,
      simp,
      rw list.init_append_last',
      simp,
      rw list.head' at closed,
      simp at closed,
      symmetry,
      exact closed,
end

lemma circuit_degree_even {W : walk G} (closed: W.closed) (v : V):
even (W.degree v) :=
begin
  rw walk.degree,
  simp,
  rw circuit_indeg_eq_outdeg G closed v,
  rw ← two_mul,
  rw even,
  existsi W.out_degree v,
  refl,
end

lemma eulerian_degree_eq {W : walk G} (euler: W.eulerian) (v : V):
W.degree v = G.degree v :=
begin
  -- TODO possibly use equiv.of_bijective and fintype.of_equiv_card
  -- TODO possibly prove handshake lemma for multigraphs and then make
  --      a contradiction if there exists one vertex with smaller degree
  --      in the walk than the graph (since it can't be larger)
  rw walk.degree,
  simp,
  rw [walk.in_degree,walk.out_degree],
  rw [multi_graph.degree, multi_graph.neighbor_set_simple_finset],
  rw walk.eulerian at euler,
  let edges_count_eq_adj := funext (euler v),
  simp at edges_count_eq_adj,
  rw ← edges_count_eq_adj,

  sorry
end

theorem eulerian_circuit_iff_even_degrees (conn: G.connected):
(∀ (v : V), even (G.degree v)) ↔ ∃ (W : walk G), W.eulerian ∧ W.closed :=
begin
  apply iff.intro,
  swap,
  -- Left direction
  intro exists_euler,
  cases exists_euler with W W_euler_circuit,
  cases W_euler_circuit with W_euler W_closed,

  intro v,
  rw ← eulerian_degree_eq G W_euler,
  apply circuit_degree_even G W_closed,

  -- Right direction
  -- TODO this direction will probably be a lot harder

  repeat { sorry },
end

end eulerian