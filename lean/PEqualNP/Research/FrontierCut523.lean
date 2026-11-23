import Mathlib
import PEqualNP.Defs.CircuitLowerBounds

namespace FrontierCut523
open PEqualNP.CircuitLowerBounds

def F (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 5) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 7)

def pos : Fin 8 → ℕ := ![3, 6, 12, 24, 33, 48, 65, 130]
def neg : Fin 7 → ℕ := ![82, 106, 137, 149, 212, 228, 232]
def point (m : ℕ) (i : Fin 8) := m.testBit i.val
def Below {α : Type} (x y : α → Bool) := ∀ i, x i = true → y i = true
instance {α : Type} [Fintype α] (x y : α → Bool) : Decidable (Below x y) :=
  inferInstanceAs (Decidable (∀ i, x i = true → y i = true))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem boundary : (∀ p, F (point (pos p)) = true) ∧
    (∀ q, F (point (neg q)) = false) ∧
    ∀ x, (F x = true → ∃ p, Below (point (pos p)) x) ∧
         (F x = false → ∃ q, Below x (point (neg q))) := by decide +kernel

theorem determines (G : (Fin 8 → Bool) → Bool)
    (mono : ∀ x y, Below x y → G x = true → G y = true) :
    G = F ↔ (∀ p, G (point (pos p)) = true) ∧ (∀ q, G (point (neg q)) = false) := by
  constructor
  · rintro rfl
    exact ⟨boundary.1, boundary.2.1⟩
  · rintro ⟨hp, hq⟩
    funext x
    cases e : F x with
    | true =>
      obtain ⟨p, h⟩ := (boundary.2.2 x).1 e
      exact mono _ _ h (hp p)
    | false =>
      obtain ⟨q, h⟩ := (boundary.2.2 x).2 e
      cases e' : G x with
      | false => rfl
      | true => simpa [hq q] using mono _ _ h e'

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def reads (gs : List Gate) (out i : ℕ) : Prop :=
  i = out ∨ ∃ g ∈ gs, i ∈ g.inputs

def basis (g : Gate) := g.op = GateOp.and ∨ g.op = GateOp.or

private theorem op_mono (g : Gate) (hb : basis g) (u v : ℕ → Bool)
    (h : ∀ i ∈ g.inputs, u i = true → v i = true) :
    g.op.eval (g.inputs.map u) = true → g.op.eval (g.inputs.map v) = true := by
  rcases hb with hOp | hOp
  · simpa [hOp, GateOp.eval] using
      (show (∀ i ∈ g.inputs, u i = true) → ∀ i ∈ g.inputs, v i = true from
        fun hu i hi => h i hi (hu i hi))
  · simpa [hOp, GateOp.eval] using
      (show (∃ i ∈ g.inputs, u i = true) → ∃ i ∈ g.inputs, v i = true from
        fun ⟨i, hi, hu⟩ => ⟨i, hi, h i hi hu⟩)

/-- Monotonicity of a suffix only needs values of wires that the suffix reads or returns. -/
theorem suffix_mono (gs : List Gate) (o : ℕ) (u v : List Bool)
    (hg : ∀ g ∈ gs, basis g) (hl : u.length = v.length)
    (h : ∀ i, i < u.length → reads gs o i → u.getD i false = true → v.getD i false = true) :
    (gs.foldl step u).getD o false = true → (gs.foldl step v).getD o false = true := by
  induction gs generalizing u v with
  | nil =>
    by_cases ho : o < u.length
    · exact h o ho (Or.inl rfl)
    · change u.getD o false = true → _
      rw [List.getD_eq_default u false (show u.length ≤ o by omega)]
      simp
  | cons g gs ih =>
    have get : ∀ i ∈ g.inputs, u.getD i false = true → v.getD i false = true := by
      intro i hi
      by_cases hey : i < u.length
      · exact h i hey (Or.inr ⟨g, by simp, hi⟩)
      · rw [List.getD_eq_default u false (show u.length ≤ i by omega)]
        simp
    have gate := op_mono g (hg g (by simp)) _ _ get
    apply ih (step u g) (step v g) (fun q hq => hg q (by simp [hq])) (by simp [step, hl])
    intro i hi hr
    by_cases hey : i < u.length
    · rw [step, step, List.getD_append _ _ _ _ hey, List.getD_append _ _ _ _ (hl ▸ hey)]
      apply h i hey
      rcases hr with he | ⟨q,hq,hi⟩
      · exact Or.inl he
      · exact Or.inr ⟨q, by simp [hq], hi⟩
    · have he : i = u.length := by simp [step] at hi; omega
      subst i
      simpa [step, hl] using gate

/-- Each separated output pair has a separating wire at the cut which still has a use. -/
theorem cut_separates (pre suf : List Gate) (out : ℕ) (x y : List Bool)
    (hg : ∀ g ∈ suf, basis g) (hsize : x.length = y.length)
    (hx : (Circuit.mk (pre ++ suf) out).eval x = true)
    (hy : (Circuit.mk (pre ++ suf) out).eval y = false) :
    ∃ i, i < (Circuit.mk pre out |>.wires x).length ∧ reads suf out i ∧
       (Circuit.mk pre out |>.wires x).getD i false = true ∧
       (Circuit.mk pre out |>.wires y).getD i false = false := by
  classical
  let u := pre.foldl step x
  let v := pre.foldl step y
  have hl (ls : List Gate) (w : List Bool) : (ls.foldl step w).length = w.length + ls.length := by
    induction ls generalizing w with
    | nil => simp
    | cons g gs ih => simp [ih, step]; omega
  have huv : u.length = v.length := by simp [u,v,hl,hsize]
  have hout₁ : (suf.foldl step u).getD out false = true := by
    change ((pre ++ suf).foldl step x).getD out false = true at hx
    exact List.foldl_append ▸ hx
  have hout₂ : (suf.foldl step v).getD out false = false := by
    change ((pre ++ suf).foldl step y).getD out false = false at hy
    exact List.foldl_append ▸ hy
  change ∃ i, i < u.length ∧ reads suf out i ∧ u.getD i false = true ∧ v.getD i false = false
  by_contra hs
  have hm : ∀ i, i < u.length → reads suf out i → u.getD i false = true → v.getD i false = true := by
    intro i hi hr ht
    cases hv : v.getD i false with
    | true => rfl
    | false => exact False.elim (hs ⟨i, hi, hr, ht, hv⟩)
  have bad := suffix_mono suf out u v hg huv hm hout₁
  exact Bool.noConfusion (hout₂.symm.trans bad)

theorem boundary_frontier (pre suf : List Gate) (out : ℕ) (hg : ∀ g ∈ suf, basis g)
    (correct : ∀ x, (Circuit.mk (pre ++ suf) out).eval (List.ofFn x) = F x)
    (p : Fin 8) (q : Fin 7) :
    let xp := List.ofFn (point (pos p))
    let xn := List.ofFn (point (neg q))
    ∃ i, i < (Circuit.mk pre out |>.wires xp).length ∧ reads suf out i ∧
       (Circuit.mk pre out |>.wires xp).getD i false = true ∧
       (Circuit.mk pre out |>.wires xn).getD i false = false := by
  apply cut_separates pre suf out _ _ hg (by simp)
  · rw [correct]; exact boundary.1 p
  · rw [correct]; exact boundary.2.1 q

end FrontierCut523

namespace FrontierCut523

open PEqualNP.CircuitLowerBounds

/-- Raw wire identifiers in the frontier immediately before a suffix. -/
noncomputable def frontier (m : ℕ) (gs : List Gate) (o : ℕ) : Finset ℕ := by
  classical exact (Finset.range m).filter (reads gs o)

@[simp] theorem mem_frontier {m i o : ℕ} {gs : List Gate} :
    i ∈ frontier m gs o ↔ i < m ∧ reads gs o i := by
  classical simp [frontier]

private theorem remove_unchanged {g : Gate} {a b m o : ℕ} {gs : List Gate}
    (hab : g.inputs = [a,b]) :
    (((frontier (m+1) gs o).erase m).erase a).erase b =
      ((frontier m (g::gs) o).erase a).erase b := by
  classical
  ext i
  simp only [Finset.mem_erase, mem_frontier, reads, List.mem_cons]
  constructor
  · rintro ⟨hb,ha,hm,hle,hr⟩
    refine ⟨hb,ha,by omega,?_⟩
    rcases hr with h | ⟨g',hg',hw⟩
    · exact Or.inl h
    · exact Or.inr ⟨g',Or.inr hg',hw⟩
  · rintro ⟨hb,ha,hle,hr⟩
    refine ⟨hb,ha,by omega,by omega,?_⟩
    rcases hr with h | ⟨g',hg',hw⟩
    · exact Or.inl h
    · rcases hg' with rfl | hg'
      · simp [hab,ha,hb] at hw
      · exact Or.inr ⟨g',hg',hw⟩

private theorem erase_cost (s : Finset ℕ) (i : ℕ) :
    (s.erase i).card + (if i ∈ s then 1 else 0) = s.card := by
  by_cases h : i ∈ s
  · simpa [h] using Finset.card_erase_add_one h
  · simp [h]

/-- A distinct-operand live gate spends one token per operand retained for later use. -/
theorem cardinal_transition {g : Gate} {a b m o : ℕ} {gs : List Gate}
    (hab : g.inputs = [a,b]) (ha : a < m) (hb : b < m) (hne : a ≠ b)
    (hlive : reads gs o m) :
    let before := frontier m (g::gs) o
    let after := frontier (m+1) gs o
    before.card + (if a ∈ after then 1 else 0) + (if b ∈ after then 1 else 0) = after.card + 1 := by
  classical
  let s := frontier m (g::gs) o
  let t := frontier (m+1) gs o
  change s.card + (if a ∈ t then 1 else 0) + (if b ∈ t then 1 else 0) = t.card + 1
  have hm : m ∈ t := mem_frontier.mpr ⟨by omega, hlive⟩
  have hA : a ∈ s := mem_frontier.mpr ⟨ha, Or.inr ⟨g, by simp, by simp [hab]⟩⟩
  have hB : b ∈ s := mem_frontier.mpr ⟨hb, Or.inr ⟨g, by simp, by simp [hab]⟩⟩
  have e := congrArg Finset.card (remove_unchanged (m:=m) (o:=o) (gs:=gs) hab)
  change (((t.erase m).erase a).erase b).card = ((s.erase a).erase b).card at e
  have e1 := erase_cost s a
  have e2 := erase_cost (s.erase a) b
  have e3 := erase_cost t m
  have e4 := erase_cost (t.erase m) a
  have e5 := erase_cost ((t.erase m).erase a) b
  have h1 : b ≠ a := Ne.symm hne
  have h2 : a ≠ m := ne_of_lt ha
  have h3 : b ≠ m := ne_of_lt hb
  rw [if_pos hA] at e1
  rw [if_pos (Finset.mem_erase.mpr ⟨h1,hB⟩)] at e2
  rw [if_pos hm] at e3
  have g4 : a ∈ t.erase m ↔ a ∈ t := by simp [h2]
  have g5 : b ∈ (t.erase m).erase a ↔ b ∈ t := by simp [h1,h3]
  simp only [g4] at e4
  simp only [g5] at e5
  omega

/-- Each gate reads two distinct earlier operands and its result has a future use (or is returned). -/
def LiveBinary (m : ℕ) (o : ℕ) : List Gate → Prop
  | [] => True
  | g :: gs => (∃ a b, g.inputs = [a,b] ∧ a < m ∧ b < m ∧ a ≠ b) ∧
      reads gs o m ∧ LiveBinary (m+1) o gs

noncomputable def tokens (m : ℕ) (o : ℕ) : List Gate → ℕ
  | [] => 0
  | g :: gs =>
      (g.inputs.filter fun i => decide (i ∈ frontier (m+1) gs o)).length + tokens (m+1) o gs

theorem token_account (m o : ℕ) (gs : List Gate) (good : LiveBinary m o gs) :
    (frontier m gs o).card + tokens m o gs =
      gs.length + (frontier (m + gs.length) [] o).card := by
  induction gs generalizing m with
  | nil => simp [tokens]
  | cons g gs ih =>
    obtain ⟨⟨a,b,hab,ha,hb,hn⟩,hl,ht⟩ := good
    have ec := cardinal_transition hab ha hb hn hl
    have et := ih (m+1) ht
    simp only [List.length_cons, tokens, hab]
    change (frontier m (g::gs) o).card + (([a,b].filter _).length + _) = _
    have ne : m + (gs.length + 1) = m+1+gs.length := by omega
    rw [ne]
    by_cases h₁ : a ∈ frontier (m+1) gs o <;> by_cases h₂ : b ∈ frontier (m+1) gs o <;>
      simp [h₁,h₂] at ec ⊢ <;> omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem exclusive : ∀ i : Fin 8, ∃ p q, ∀ j : Fin 8,
    point (pos p) j = true → point (neg q) j = false → j = i := by decide +kernel

theorem frontier_initial (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, basis g)
    (correct : ∀ x, (Circuit.mk gs o).eval (List.ofFn x) = F x) :
    frontier 8 gs o = Finset.range 8 := by
  ext k
  rw [mem_frontier, Finset.mem_range]
  constructor
  · exact And.left
  · intro hk
    refine ⟨hk,?_⟩
    obtain ⟨p,q,h⟩ := exclusive ⟨k,hk⟩
    obtain ⟨j,hj,hr,hp,hn⟩ := boundary_frontier [] gs o hg correct p q
    change j < (List.ofFn (point (pos p))).length at hj
    simp at hj
    change (List.ofFn (point (pos p))).getD j false = true at hp
    change (List.ofFn (point (neg q))).getD j false = false at hn
    have get (z : Fin 8 → Bool) : (List.ofFn z).getD j false = z ⟨j,hj⟩ := by
      have hh : j < (List.ofFn z).length := by simpa using hj
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hh, Option.getD_some, List.getElem_ofFn]
    rw [get] at hp hn
    have he : j = k := congrArg Fin.val (h ⟨j,hj⟩ hp hn)
    simpa only [← he] using hr

theorem eleven_gates_four_tokens (gs : List Gate) (sz : gs.length = 11)
    (hg : ∀ g ∈ gs, basis g) (good : LiveBinary 8 18 gs)
    (correct : ∀ x, (Circuit.mk gs 18).eval (List.ofFn x) = F x) : tokens 8 18 gs = 4 := by
  have h := token_account 8 18 gs good
  rw [frontier_initial gs 18 hg correct, sz] at h
  have he : frontier 19 [] 18 = {18} := by ext i; simp [reads]; omega
  norm_num [he] at h
  omega

end FrontierCut523
