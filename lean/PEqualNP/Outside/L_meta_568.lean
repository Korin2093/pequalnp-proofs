import Mathlib
import PEqualNP.Defs

namespace PEqualNP.MetaComplexity.FreeInput568

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

end PEqualNP.MetaComplexity.FreeInput568

namespace FreeInputOutput

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_nil, List.length_cons]
    omega

private theorem omit_new (w : List Bool) (b : Bool) (o : ℕ) (hne : o ≠ w.length) :
    (w ++ [b]).getD o false = w.getD o false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : o < w.length
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem last_gate_output (n : ℕ) (C : Circuit) (hm : IsMinimalCircuit n C)
    (hg : C.gates ≠ []) : C.output + 1 = n + C.gates.length := by
  obtain ⟨gs, g, h⟩ : ∃ gs g, C.gates = gs ++ [g] :=
    ⟨_, _, (List.dropLast_concat_getLast hg).symm⟩
  by_contra bad
  let D : Circuit := ⟨gs, C.output⟩
  have hfan : FanInTwo D := by
    intro a ha
    apply hm.1 a
    rw [h]
    exact List.mem_append_left _ ha
  have heq : circuitFun n D = circuitFun n C := by
    funext x
    let w := D.wires (List.ofFn x)
    have hl : w.length = n + gs.length := by
      simpa [w, D, Circuit.wires] using fold_length gs (List.ofFn x)
    have hne : C.output ≠ w.length := by
      simp [h] at bad
      omega
    change w.getD C.output false = _
    simp only [circuitFun, Circuit.eval, Circuit.wires, h, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    exact (omit_new w _ _ hne).symm
  have hsize := hm.2 D hfan heq
  simp [D, Circuit.size, h] at hsize

theorem free_or_has_gate (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (hnc : ∃ y y', H y ≠ H y')
    (hf : ∀ x : Fin (n + 1) → Bool, circuitFun (n + 1) C x =
      (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) : C.gates ≠ [] := by
  intro hempty
  have h_eval (y : Fin n → Bool) (b : Bool) :
      (List.ofFn (Fin.snoc y b)).getD C.output false = (b || H y) := by
    simpa [circuitFun, Circuit.eval, Circuit.wires, hempty] using hf (Fin.snoc y b)
  by_cases hout : C.output < n
  · let y : Fin n → Bool := fun _ => false
    have hx := h_eval y true
    have hi : (⟨C.output, by omega⟩ : Fin (n + 1)) = (⟨C.output, hout⟩ : Fin n).castSucc := rfl
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left (show C.output < n + 1 by omega), Option.getD_some, hi, Fin.snoc_castSucc, y, Bool.true_or] at hx
    contradiction
  · by_cases heq : C.output = n
    · obtain ⟨y, y', hy⟩ := hnc
      have allfalse (z : Fin n → Bool) : H z = false := by
        have hx := h_eval z false
        have hi : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := rfl
        simpa only [heq, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left (show n < n + 1 by omega), Option.getD_some, hi, Fin.snoc_last, Bool.false_or] using hx.symm
      exact hy ((allfalse y).trans (allfalse y').symm)
    · have hx := h_eval (fun _ => false) true
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_right (show ¬ C.output < n + 1 by omega), Option.getD_none, Bool.true_or] at hx
      contradiction

theorem free_or_output (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (hm : IsMinimalCircuit (n + 1) C) (hnc : ∃ y y', H y ≠ H y')
    (hf : ∀ x : Fin (n + 1) → Bool, circuitFun (n + 1) C x =
      (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) :
    ∃ j : Fin C.gates.length, j.val + 1 = C.gates.length ∧ C.output = n + 1 + j.val := by
  have h := free_or_has_gate n C H hnc hf
  have hpos := List.length_pos_iff.mpr h
  have ho := last_gate_output (n + 1) C hm h
  exact ⟨⟨C.gates.length - 1, by omega⟩, by simp; omega, by simp; omega⟩

end FreeInputOutput

namespace MinimalClean
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.FreeInput568

def gateValue (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem no_constant_or_alias (n : ℕ) (C : Circuit) (hm : IsMinimalCircuit n C)
    (hnc : ∃ x y, circuitFun n C x ≠ circuitFun n C y) (pre post : List Gate) (g : Gate)
    (hsplit : C.gates = pre ++ g :: post) (s : Stat) (hv : s.Valid (n + pre.length)) :
    ¬ ∀ x : Fin n → Bool, let w := wiresFrom pre (List.ofFn x); gateValue g w = s.val w := by
  intro heq
  let k := n + pre.length
  let old : List Stat := (List.range k).map Sum.inr
  let start : List Stat × List Gate := (old ++ [s], pre)
  let acc := elim n post start
  have hpre : ∀ a ∈ pre, Ok a := by
    intro a ha
    apply hm.1 a
    rw [hsplit]
    exact List.mem_append_left _ ha
  have hpost : ∀ a ∈ post, Ok a := by
    intro a ha
    apply hm.1 a
    rw [hsplit]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ ha)
  have hval (x : Fin n → Bool) :
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) =
      circuitFun n C x := by
    let w := wiresFrom pre (List.ofFn x)
    have lw : w.length = k := by simp [w, k, length_wiresFrom]
    have lo : old.length = k := by simp [old]
    have hstart : Inv n (List.ofFn x) (w ++ [gateValue g w]) start := by
      refine ⟨by simp [start, lw, lo], ?_⟩
      intro i
      change ((old ++ [s]).getD i (Sum.inl false)).Valid k ∧
        ((old ++ [s]).getD i (Sum.inl false)).val w = (w ++ [gateValue g w]).getD i false
      by_cases hik : i = k
      · subst i
        rw [getD_snoc_len _ _ _ _ lo, getD_snoc_len _ _ _ _ lw]
        exact ⟨hv, (heq x).symm⟩
      · rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
        by_cases hlt : i < k
        · have hwi : old.getD i (Sum.inl false) = Sum.inr i := by simp [old, hlt]
          rw [hwi]
          exact ⟨hlt, rfl⟩
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
          exact ⟨trivial, rfl⟩
    have h := (inv_elim n _ (by simp) post _ _ hpost hstart).2 C.output
    convert h.2 using 1
    change (wiresFrom C.gates (List.ofFn x)).getD C.output false = _
    rw [hsplit, wiresFrom_append]
    rfl
  have hs := elim_len n post start
  have hl : acc.2.length < C.gates.length := by
    change acc.2.length ≤ pre.length + post.length at hs
    simp [hsplit]
    omega
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨x, y, hne⟩ := hnc
    apply hne
    rw [← hval x, ← hval y, hst]
    rfl
  | inr i =>
    let D : Circuit := ⟨acc.2, i⟩
    have hfan : FanInTwo D := elim_ok n post start hpre
    have hfun : circuitFun n D = circuitFun n C := by
      funext x
      have hx := hval x
      rw [hst] at hx
      exact hx
    have := hm.2 D hfan hfun
    exact Nat.not_le_of_gt hl this

private def wireStatus (k i : ℕ) : Stat := if i < k then Sum.inr i else Sum.inl false

private theorem vs_valid (k i : ℕ) : (wireStatus k i).Valid k := by
  unfold wireStatus
  split <;> simp_all [Stat.Valid]

private theorem vs_val (w : List Bool) (k i : ℕ) (hl : w.length = k) :
    (wireStatus k i).val w = w.getD i false := by
  unfold wireStatus
  split
  · rfl
  · rw [List.getD_eq_default _ _ (by omega)]
    rfl

theorem gate_shape (n : ℕ) (C : Circuit) (hm : IsMinimalCircuit n C)
    (hnc : ∃ x y, circuitFun n C x ≠ circuitFun n C y) (pre post : List Gate) (g : Gate)
    (hs : C.gates = pre ++ g :: post) :
    (g.op = GateOp.not ∧ ∃ i < n + pre.length, g.inputs.head? = some i) ∨
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, g.inputs = [a,b] ∧ a < n + pre.length ∧ b < n + pre.length ∧ a ≠ b) := by
  let k := n + pre.length
  have hconst (b : Bool) (h : ∀ w : List Bool, w.length = k → gateValue g w = b) : False := by
    apply no_constant_or_alias n C hm hnc pre post g hs (.inl b) trivial
    intro x
    apply h
    simp [length_wiresFrom, k]
  have hwire (i : ℕ) (h : ∀ w : List Bool, w.length = k → gateValue g w = w.getD i false) : False := by
    apply no_constant_or_alias n C hm hnc pre post g hs (wireStatus k i) (vs_valid k i)
    intro x
    have hl : (wiresFrom pre (List.ofFn x)).length = k := by simp [length_wiresFrom, k]
    exact (h _ hl).trans (vs_val _ _ _ hl).symm
  have hok : Ok g := hm.1 g (by simp [hs])
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hok
  change op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not at hop
  change ins.length ≤ 2 at hlen
  rcases eq_or_ne op GateOp.not with rfl | hn
  · left
    refine ⟨rfl, ?_⟩
    cases ins with
    | nil => exact (hconst true (by simp [gateValue, GateOp.eval])).elim
    | cons i is =>
      by_cases hi : i < k
      · exact ⟨i, hi, rfl⟩
      · apply False.elim <| hconst true ?_
        intro w h
        simp [gateValue, GateOp.eval, List.getElem?_eq_none (show w.length ≤ i by omega)]
  · right
    have hops : op = GateOp.and ∨ op = GateOp.or := by tauto
    refine ⟨hops, ?_⟩
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d,l⟩⟩⟩
    · rcases hops with rfl | rfl
      · exact (hconst true (by simp [gateValue, GateOp.eval])).elim
      · exact (hconst false (by simp [gateValue, GateOp.eval])).elim
    · apply False.elim <| hwire a ?_
      rcases hops with rfl | rfl <;> simp [gateValue, GateOp.eval]
    · refine ⟨a, b, rfl, ?_, ?_, ?_⟩
      · by_contra hi
        change ¬ a < k at hi
        rcases hops with rfl | rfl
        · apply hconst false
          intro w h
          simp [gateValue, GateOp.eval, List.getElem?_eq_none (show w.length ≤ a by omega)]
        · apply hwire b
          intro w h
          simp [gateValue, GateOp.eval, List.getElem?_eq_none (show w.length ≤ a by omega)]
      · by_contra hi
        change ¬ b < k at hi
        rcases hops with rfl | rfl
        · apply hconst false
          intro w h
          simp [gateValue, GateOp.eval, List.getElem?_eq_none (show w.length ≤ b by omega)]
        · apply hwire a
          intro w h
          simp [gateValue, GateOp.eval, List.getElem?_eq_none (show w.length ≤ b by omega)]
      · intro heq
        subst b
        apply hwire a
        rcases hops with rfl | rfl <;> simp [gateValue, GateOp.eval]
    · simp at hlen

theorem exclude_terminal_and (n : ℕ) (C : Circuit) (hm : IsMinimalCircuit n C)
    (hnc : ∃ x y, circuitFun n C x ≠ circuitFun n C y) (pre : List Gate)
    (g : Gate) (z b : ℕ) (hs : C.gates = pre ++ [g]) (ho : C.output = n + pre.length)
    (hop : g.op = GateOp.and) (hins : g.inputs = [z,b] ∨ g.inputs = [b,z])
    (raise : (Fin n → Bool) → Fin n → Bool)
    (hone : ∀ x, circuitFun n C (raise x) = true)
    (hfix : ∀ x, (wiresFrom pre (List.ofFn (raise x))).getD b false =
      (wiresFrom pre (List.ofFn x)).getD b false) : False := by
  let k := n + pre.length
  have value (w : List Bool) : gateValue g w = (w.getD z false && w.getD b false) := by
    rcases hins with h | h <;> simp [gateValue, hop, h, GateOp.eval, Bool.and_comm]
  have out (x : Fin n → Bool) : circuitFun n C x = gateValue g (wiresFrom pre (List.ofFn x)) := by
    change (wiresFrom C.gates (List.ofFn x)).getD C.output false = _
    rw [hs, wiresFrom_append, ho]
    change (_ ++ [_]).getD _ false = _
    rw [getD_snoc_len _ _ _ _ (by simp [length_wiresFrom])]
    rfl
  apply no_constant_or_alias n C hm hnc pre [] g hs (wireStatus k z) (vs_valid _ _)
  intro x
  have hr := hone x
  rw [out, value, Bool.and_eq_true] at hr
  have hb := hr.2
  rw [hfix x] at hb
  dsimp only
  rw [value, hb, Bool.and_true, vs_val _ _ _ (by simp [length_wiresFrom, k])]

theorem terminal_reader_or (n : ℕ) (C : Circuit) (hm : IsMinimalCircuit n C)
    (hnc : ∃ x y, circuitFun n C x ≠ circuitFun n C y) (j : Fin C.gates.length) (z : ℕ)
    (hj : j.val + 1 = C.gates.length) (ho : C.output = n + j.val)
    (hlt : z < n + j.val)
    (read : (C.gates.get j).op = GateOp.not ∧ (C.gates.get j).inputs.head? = some z ∨
      (C.gates.get j).op ≠ GateOp.not ∧ z ∈ (C.gates.get j).inputs)
    (dom : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD z false = true →
      circuitFun n C x = true) : (C.gates.get j).op = GateOp.or := by
  let pre := C.gates.take j.val
  let g := C.gates.get j
  have hl : pre.length = j.val := by simp [pre]
  have hs : C.gates = pre ++ [g] := by
    change C.gates = C.gates.take j.val ++ [C.gates[j.val]]
    simp [List.take_append_getElem j.isLt, hj]
  let W := fun x : Fin n → Bool => wiresFrom pre (List.ofFn x)
  have hdom (x : Fin n → Bool) (hx : (W x).getD z false = true) : circuitFun n C x = true := by
    apply dom
    rw [wires_eq, hs, wiresFrom_append, getD_wiresFrom]
    · exact hx
    · simp [length_wiresFrom, hl, hlt]
  have out (x : Fin n → Bool) : circuitFun n C x = gateValue g (W x) := by
    change (wiresFrom C.gates (List.ofFn x)).getD C.output false = _
    rw [hs, wiresFrom_append, ho]
    change (_ ++ [_]).getD _ false = _
    rw [getD_snoc_len _ _ _ _ (by simp [length_wiresFrom, hl])]
    rfl
  rcases gate_shape n C hm hnc pre [] g hs with ⟨hop, _⟩ | ⟨hops,u,v,hin,_,_,_⟩
  · exfalso
    change g.op = GateOp.not ∧ _ ∨ g.op ≠ GateOp.not ∧ _ at read
    have hh := read.resolve_right (fun hr => hr.1 hop)
    obtain ⟨rest, hrest⟩ : ∃ rest, g.inputs = z :: rest := by
      cases h : g.inputs with
      | nil =>
        have he := hh.2
        change g.inputs.head? = some z at he
        simp [h] at he
      | cons a l =>
        have he := hh.2
        change g.inputs.head? = some z at he
        simp [h] at he
        exact ⟨l, he ▸ rfl⟩
    have always (x : Fin n → Bool) : circuitFun n C x = true := by
      cases h : (W x).getD z false with
      | false => rw [out]; simp only [gateValue, hop, hrest, List.map_cons, GateOp.eval, List.headD_cons, h, Bool.not_false]
      | true => exact hdom x h
    obtain ⟨x,y,ne⟩ := hnc
    exact ne ((always x).trans (always y).symm)
  · rcases hops with andOp | orOp
    · exfalso
      change g.op = GateOp.not ∧ _ ∨ g.op ≠ GateOp.not ∧ _ at read
      have hr := (read.resolve_left (fun h => by rw [andOp] at h; simp at h)).2
      change z ∈ g.inputs at hr
      rw [hin] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      apply no_constant_or_alias n C hm hnc pre [] g hs (.inr z) (by change z < n + pre.length; omega)
      intro x
      change gateValue g (W x) = (W x).getD z false
      cases hx : (W x).getD z false with
      | false =>
        rcases hr with rfl | rfl <;> simp [gateValue, andOp, hin, GateOp.eval, -List.getD_eq_getElem?_getD, hx]
      | true => exact (out x).symm.trans (hdom x hx)
    · exact orOp

theorem domination_from_factor (s a : ℕ) (C : Circuit) (hlo : s ≤ a) (hhi : a ≤ s + C.gates.length)
    (factor : ∀ x : Fin (s+1) → Bool,
      let v := wiresFrom (C.gates.take (a-s)) (List.ofFn x)
      circuitFun (s+1) C x =
        (v.getD a false || (wiresFrom (C.gates.drop (a-s)) (v.set a false)).getD C.output false)) :
    ∀ x : Fin (s+1) → Bool, (C.wires (List.ofFn x)).getD a false = true →
      circuitFun (s+1) C x = true := by
  intro x h
  let pre := C.gates.take (a-s)
  let post := C.gates.drop (a-s)
  have hsplit : C.gates = pre ++ post := (List.take_append_drop _ _).symm
  have hl : a < (wiresFrom pre (List.ofFn x)).length := by
    simp [length_wiresFrom, pre, List.length_take]
    omega
  rw [wires_eq, hsplit, wiresFrom_append, getD_wiresFrom post _ _ hl] at h
  rw [factor]
  change ((wiresFrom pre (List.ofFn x)).getD a false || _) = true
  rw [h, Bool.true_or]
end MinimalClean

namespace FreeInputLive

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.FreeInput568

private def shift (k i : ℕ) := if i < k then i else i - 1

private def shifted (k : ℕ) (g : Gate) : Gate :=
  ⟨(normGate g).op, (normGate g).inputs.map (shift k)⟩

private theorem suffix_agree (k : ℕ) (post : List Gate)
    (hno : ∀ g ∈ post, k ∉ (normGate g).inputs) (w v : List Bool)
    (hl : w.length = v.length + 1) (hk : k < w.length)
    (h : ∀ i, i ≠ k → w.getD i false = v.getD (shift k i) false) :
    ∀ i, i ≠ k → (wiresFrom post w).getD i false =
      (wiresFrom (post.map (shifted k)) v).getD (shift k i) false := by
  induction post generalizing w v with
  | nil => exact h
  | cons g post ih =>
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    have he : (shifted k g).op.eval ((shifted k g).inputs.map fun i => v.getD i false) = b := by
      unfold b
      rw [← normGate_eval g]
      congr 1
      simp only [shifted, List.map_map]
      apply List.map_congr_left
      intro i hi
      exact (h i (fun hei => hno g List.mem_cons_self (hei ▸ hi))).symm
    change ∀ i, i ≠ k → (wiresFrom post (w ++ [b])).getD i false =
      (wiresFrom (post.map (shifted k)) (v ++ [_])).getD (shift k i) false
    rw [he]
    apply ih (fun z hz => hno z (List.mem_cons_of_mem _ hz)) _ _ (by simp; omega) (by simp; omega)
    intro i hi
    by_cases hj : i = w.length
    · subst i
      have hshift : shift k w.length = v.length := by simp [shift, show ¬ w.length < k by omega]; omega
      rw [hshift, getD_snoc_eq, getD_snoc_eq]
    · have hj' : shift k i ≠ v.length := by unfold shift; split <;> omega
      rw [getD_snoc_ne _ _ _ _ hj, getD_snoc_ne _ _ _ _ hj', h i hi]

theorem live (n : ℕ) (C : Circuit) (hm : IsMinimalCircuit n C)
    (pre : List Gate) (g : Gate) (post : List Gate) (hs : C.gates = pre ++ g :: post)
    (ho : C.output ≠ n + pre.length) :
    ∃ z ∈ post, n + pre.length ∈ (normGate z).inputs := by
  by_contra! hno
  let k := n + pre.length
  let D : Circuit := ⟨pre ++ post.map (shifted k), shift k C.output⟩
  have hf : FanInTwo D := by
    intro z hz
    rcases List.mem_append.1 hz with hp | ht
    · exact hm.1 z (hs ▸ List.mem_append_left _ hp)
    · obtain ⟨t, ht0, heq⟩ := List.mem_map.1 ht
      subst z
      have hn := normGate_nok t (hm.1 t (hs ▸ List.mem_append_right _ (List.mem_cons_of_mem _ ht0)))
      exact ⟨hn.1.1, by simpa [shifted] using hn.1.2⟩
  have he : circuitFun n D = circuitFun n C := by
    funext x
    let w := wiresFrom pre (List.ofFn x)
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    have hl : w.length = k := by simp [w, k, length_wiresFrom]
    have h := suffix_agree k post hno (w ++ [b]) w (by simp) (by simp [hl]) (by
      intro i hi
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      by_cases hlt : i < k
      · simp [shift, hlt]
      · simp only [shift, ite_eq_right hlt]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)])
      C.output ho
    simp only [circuitFun, Circuit.eval, wires_eq, hs, D, wiresFrom_append]
    exact h.symm
  have := hm.2 D hf he
  simp [Circuit.size, D, hs] at this

end FreeInputLive

namespace PEqualNP.MetaComplexity.FreeInput568
open PEqualNP.CircuitLowerBounds

theorem mem_normGate_iff (g : Gate) (w : ℕ) :
    w ∈ (normGate g).inputs ↔
      (g.op = GateOp.not ∧ g.inputs.head? = some w ∨
       g.op ≠ GateOp.not ∧ w ∈ g.inputs) := by
  obtain ⟨op, ins⟩ := g
  cases op <;> cases ins <;> simp [normGate, eq_comm]

theorem pin_false_two (n w : ℕ) (acc : List Stat × List Gate)
    (pre : List Gate) (g : Gate) (post : List Gate)
    (hok : ∀ g' ∈ pre ++ g :: post, NOk g')
    (hw : w < acc.1.length)
    (hpin : acc.1.getD w (Sum.inl false) = Sum.inl false) (hread : w ∈ g.inputs)
    (hnext : (∃ h ∈ post, w ∈ h.inputs) ∨
      (g.op ≠ GateOp.or ∧ ∃ h ∈ post, acc.1.length + pre.length ∈ h.inputs)) :
    (elim n (pre ++ g :: post) acc).2.length + 2 ≤
      acc.2.length + (pre ++ g :: post).length := by
  let a := elim n pre acc
  let b := elimStep n a g
  have ha : a.1.length = acc.1.length + pre.length := elim_fst_len n pre acc
  have hga : NOk g := hok g (by simp)
  have hpok : ∀ h ∈ post, NOk h := fun h hh => hok h (by simp [hh])
  have hpinA : a.1.getD w (Sum.inl false) = Sum.inl false :=
    (elim_getD n w _ pre acc hw).trans hpin
  have hsizeA : a.2.length ≤ acc.2.length + pre.length := elim_len n pre acc
  have hsizeB : b.2.length = a.2.length := elimStep_none n a g hga w hread false hpinA
  have hb : b.1.length = a.1.length + 1 := by simp [b, elimStep]
  have hsave : (elim n post b).2.length + 1 ≤ b.2.length + post.length := by
    rcases hnext with hh | ⟨hnotor, hh⟩
    · apply elim_len_lt n w post b hpok (by omega) _ hh
      refine ⟨false, ?_⟩
      change (a.1 ++ [_]).getD w _ = _
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact hpinA
    · have hf : fixBit g = false := by
        obtain ⟨op, ins⟩ := g
        cases op <;> simp_all [fixBit]
      obtain ⟨c, hc⟩ := elimStep_const n a g hga w hread (hf ▸ hpinA)
      rw [ha] at hc
      exact elim_len_lt n (acc.1.length + pre.length) post b hpok (by omega) ⟨c, hc⟩ hh
  rw [elim_append, elim_cons]
  change (elim n post b).2.length + 2 ≤ _
  simp only [List.length_append, List.length_cons]
  omega

def finishOr (z : ℕ) : Stat → Gate
  | .inl true => ⟨.and, []⟩
  | .inl false => ⟨.or, [z]⟩
  | .inr j => ⟨.or, [z,j]⟩

theorem finishOr_ok (z : ℕ) (s : Stat) : Ok (finishOr z s) := by
  cases s with
  | inl c => cases c <;> simp [finishOr, Ok]
  | inr j => simp [finishOr, Ok]

theorem finishOr_value (v : List Bool) (z : ℕ) (s : Stat) :
    (wiresFrom [finishOr z s] v).getD v.length false = (v.getD z false || s.val v) := by
  cases s with
  | inl c => cases c <;> simp [finishOr, wiresFrom, GateOp.eval, Stat.val]
  | inr j => simp [finishOr, wiresFrom, GateOp.eval, Stat.val]

theorem rejoinCut (n z o : ℕ) (acc : List Stat × List Gate) (gs : List Gate)
    (hok : ∀ g ∈ gs, Ok g) (hacc : ∀ g ∈ acc.2, Ok g) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = (elim n gs acc).2.length + 1 ∧
      ∀ y old : List Bool, y.length = n → Inv n y old acc →
        D.eval y = ((wiresFrom (elim n gs acc).2 y).getD z false ||
          (wiresFrom gs old).getD o false) := by
  let a := elim n gs acc
  let s := a.1.getD o (.inl false)
  let D : Circuit := ⟨a.2 ++ [finishOr z s], n + a.2.length⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ a.2 ++ [finishOr z s] at hg
    rcases List.mem_append.1 hg with hg | hg
    · exact elim_ok n gs acc hacc g hg
    · simp only [List.mem_singleton] at hg
      exact hg ▸ finishOr_ok z s
  · simp [D, Circuit.size, a]
  · intro y old hy hi
    have hs : s.val (wiresFrom a.2 y) = (wiresFrom gs old).getD o false :=
      ((inv_elim n y hy gs old acc hok hi).2 o).2
    change (wiresFrom (a.2 ++ [finishOr z s]) y).getD (n + a.2.length) false = _
    rw [wiresFrom_append, ← hy, ← length_wiresFrom, finishOr_value, hs]
    rw [hy]

def pinnedPrefix (n z : ℕ) (pref : List Gate) : List Stat × List Gate :=
  (List.ofFn (fun j : Fin (n + pref.length) => if z = j.val then Sum.inl false else Sum.inr j.val), pref)

theorem pinnedPrefix_inv (n z : ℕ) (pref : List Gate) (y : List Bool) (hy : y.length = n) :
    Inv n y ((wiresFrom pref y).set z false) (pinnedPrefix n z pref) := by
  let v := wiresFrom pref y
  have hv : v.length = n + pref.length := by simp [v, length_wiresFrom, hy]
  constructor
  · simp [pinnedPrefix, length_wiresFrom, hy]
  · intro i
    by_cases hi : i < n + pref.length
    · have hv' : i < v.length := by omega
      by_cases h : z = i
      · subst z
        simp [pinnedPrefix, hi, List.getD_eq_getElem?_getD, ← show v = wiresFrom pref y from rfl,
          hv', Stat.Valid, Stat.val]
      · simp [pinnedPrefix, hi, List.getD_eq_getElem?_getD, ← show v = wiresFrom pref y from rfl,
          h, Stat.Valid, Stat.val]
    · change ((pinnedPrefix n z pref).1.getD i _).Valid _ ∧ _ = (v.set z false).getD i false
      rw [List.getD_eq_default _ _ (by simp [pinnedPrefix]; omega),
          List.getD_eq_default _ _ (by simp [hv]; omega)]
      exact ⟨trivial, rfl⟩

theorem elim_gates_extend (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    ∃ extra, (elim n gs acc).2 = acc.2 ++ extra := by
  induction gs generalizing acc with
  | nil => exact ⟨[], by simp [elim]⟩
  | cons g gs ih =>
    obtain ⟨extra, he⟩ := ih (elimStep n acc g)
    rw [elim_cons, he]
    exact ⟨_, List.append_assoc ..⟩

def readsWire (g : Gate) (z : ℕ) : Prop :=
  g.op = GateOp.not ∧ g.inputs.head? = some z ∨ g.op ≠ GateOp.not ∧ z ∈ g.inputs

theorem minimal_cut_reader (n z : ℕ) (C : Circuit) (pref pre : List Gate) (g : Gate) (post : List Gate)
    (hgs : C.gates = pref ++ (pre ++ g :: post))
    (hmin : IsMinimalCircuit n C) (hz : z < n + pref.length)
    (hfactor : ∀ x : Fin n → Bool,
      let v := wiresFrom pref (List.ofFn x)
      circuitFun n C x =
        (v.getD z false || (wiresFrom (pre ++ g :: post) (v.set z false)).getD C.output false))
    (hr : readsWire g z) :
    ¬ ((∃ h ∈ post, readsWire h z) ∨
      (g.op ≠ GateOp.or ∧ ∃ h ∈ post, readsWire h (n + pref.length + pre.length))) := by
  intro hbad
  let a := pinnedPrefix n z pref
  let ng := normGate g
  let pre' := pre.map normGate
  let post' := post.map normGate
  let gs := pre' ++ ng :: post'
  have hmap : gs = (pre ++ g :: post).map normGate := by simp [gs, pre', ng, post']
  have hn (t : Gate) (ht : t ∈ gs) : NOk t := by
    rw [hmap, List.mem_map] at ht
    obtain ⟨t', ht', rfl⟩ := ht
    exact normGate_nok _ (hmin.1 _ (hgs ▸ List.mem_append_right pref ht'))
  have ha : a.1.length = n + pref.length := by simp [a, pinnedPrefix]
  have hp : a.1.getD z (Sum.inl false) = Sum.inl false := by simp [a, pinnedPrefix, hz]
  have hg : ng.op = g.op := by cases g with | mk op ins => cases op <;> rfl
  have hpre : pre'.length = pre.length := by simp [pre']
  have postReader (k : ℕ) (hex : ∃ h ∈ post, readsWire h k) : ∃ h ∈ post', k ∈ h.inputs := by
    obtain ⟨h, hm, hrh⟩ := hex
    exact ⟨normGate h, List.mem_map.2 ⟨h,hm,rfl⟩, (mem_normGate_iff ..).2 hrh⟩
  have hs := pin_false_two n z a pre' ng post' hn (by omega) hp ((mem_normGate_iff ..).2 hr) (by
    rcases hbad with h | ⟨hne, h⟩
    · exact Or.inl (postReader z h)
    · exact Or.inr ⟨hg ▸ hne, by rw [ha, hpre]; exact postReader _ h⟩)
  obtain ⟨D, hD, ds, hv⟩ := rejoinCut n z C.output a gs (fun t ht => (hn t ht).1)
    (fun t ht => hmin.1 t (hgs ▸ List.mem_append_left _ ht))
  have heq : circuitFun n D = circuitFun n C := by
    funext x
    let v := wiresFrom pref (List.ofFn x)
    have hx := hv (List.ofFn x) (v.set z false) (by simp) (pinnedPrefix_inv n z pref _ (by simp))
    rw [hfactor x]
    change D.eval (List.ofFn x) = _
    rw [hx, hmap, wiresFrom_norm]
    obtain ⟨extra, hxg⟩ := elim_gates_extend n ((pre ++ g :: post).map normGate) a
    rw [hxg, wiresFrom_append, getD_wiresFrom _ _ z (by simp [a, pinnedPrefix, length_wiresFrom]; exact hz)]
    rfl
  have hd := hmin.2 D hD heq
  have hc : C.size = pref.length + gs.length := by simp [Circuit.size, hgs, hmap]
  change (elim n gs a).2.length + 2 ≤ pref.length + gs.length at hs
  omega

end PEqualNP.MetaComplexity.FreeInput568

namespace FreeInputChain

open PEqualNP.CircuitLowerBounds

def Uses (g : Gate) (i : ℕ) : Prop :=
  g.op = GateOp.not ∧ g.inputs.head? = some i ∨
    g.op ≠ GateOp.not ∧ i ∈ g.inputs

def advance (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def AgreeOn (keep : ℕ → Prop) (u v : List Bool) : Prop :=
  u.length = v.length ∧ ∀ i, keep i → u.getD i false = v.getD i false

private theorem eval_congr (g : Gate) (a b : ℕ → Bool)
    (h : ∀ w, Uses g w → a w = b w) :
    g.op.eval (g.inputs.map a) = g.op.eval (g.inputs.map b) := by
  by_cases hn : g.op = GateOp.not
  · cases he : g.inputs with
    | nil => simp
    | cons i is =>
      have hi := h i (Or.inl ⟨hn, by simp [he]⟩)
      simp [hn, GateOp.eval, hi]
  · congr 1
    exact List.map_congr_left (fun i hi => h i (Or.inr ⟨hn, hi⟩))

theorem suffix_agreement (keep : ℕ → Prop) (gs : List Gate) (u v : List Bool)
    (h : AgreeOn keep u v) (reads : ∀ g ∈ gs, ∀ i, Uses g i → keep i) :
    AgreeOn keep (gs.foldl advance u) (gs.foldl advance v) := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    · have e := eval_congr g (fun i => u.getD i false) (fun i => v.getD i false)
          (fun i hi => h.2 i (reads g (by simp) i hi))
      dsimp [AgreeOn, advance]
      constructor
      · simp [h.1]
      · intro i hi
        by_cases hl : i < u.length
        · rw [List.getD_append _ _ _ _ hl, List.getD_append _ _ _ _ (h.1 ▸ hl)]
          exact h.2 i hi
        · have hr : u.length ≤ i := by omega
          rw [List.getD_append_right _ _ _ _ hr, List.getD_append_right _ _ _ _ (h.1 ▸ hr),
            e, h.1]
    · exact fun q hq => reads q (by simp [hq])

end FreeInputChain

namespace FreeInputChain

open PEqualNP.CircuitLowerBounds

def ClosedPrefix (affected : ℕ → Prop) : ℕ → List Gate → Prop
  | _, [] => True
  | m, g :: gs => (¬ affected m → ∀ i, i < m → Uses g i → ¬ affected i) ∧
      ClosedPrefix affected (m+1) gs

theorem prefix_agreement (affected : ℕ → Prop) (gs : List Gate) (u v : List Bool)
    (h : AgreeOn (fun i => ¬ affected i) u v)
    (hc : ClosedPrefix affected u.length gs) :
    AgreeOn (fun i => ¬ affected i) (gs.foldl advance u) (gs.foldl advance v) := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨hn, htail⟩ := hc
    apply ih
    · dsimp [AgreeOn, advance]
      constructor
      · simp [h.1]
      · intro i hi
        by_cases hl : i < u.length
        · rw [List.getD_append _ _ _ _ hl, List.getD_append _ _ _ _ (h.1 ▸ hl)]
          exact h.2 i hi
        · have hr : u.length ≤ i := by omega
          rw [List.getD_append_right _ _ _ _ hr, List.getD_append_right _ _ _ _ (h.1 ▸ hr)]
          by_cases heq : i = u.length
          · have eval_eq := eval_congr g (fun j => u.getD j false) (fun j => v.getD j false)
                (fun j hj => by
                  by_cases hjl : j < u.length
                  · exact h.2 j (hn (heq ▸ hi) j hjl hj)
                  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by
                      have := h.1
                      omega)])
            rw [eval_eq, h.1]
          · have h1 : 1 ≤ i - u.length := by omega
            rw [← h.1, List.getD_eq_default _ _ (by simpa using h1),
              List.getD_eq_default _ _ (by simpa using h1)]
    · simpa [advance] using htail

def pinFalse (u : List Bool) (z : ℕ) : List Bool := u.set z false

private theorem pin_read (u : List Bool) (z i : ℕ) :
    (pinFalse u z).getD i false = (if i = z then false else u.getD i false) := by
  simp [pinFalse, List.getD_eq_getElem?_getD, List.getElem?_set]
  split <;> rename_i h
  · subst z
    split <;> simp
  · simp [Ne.symm h]

theorem frontier_factor (affected : ℕ → Prop) (z o : ℕ) (gs : List Gate)
    (u v : List Bool) (h : AgreeOn (fun i => ¬ affected i) u v)
    (hz : v.getD z false = true)
    (hreads : ∀ g ∈ gs, ∀ i, Uses g i → i = z ∨ ¬ affected i)
    (hout : o = z ∨ ¬ affected o)
    (hv : (gs.foldl advance v).getD o false = true) :
    (gs.foldl advance u).getD o false =
      (u.getD z false || (gs.foldl advance (pinFalse u z)).getD o false) := by
  let keep := fun i => i = z ∨ ¬ affected i
  cases hu : u.getD z false with
  | true =>
    have ha : AgreeOn keep u v := by
      refine ⟨h.1, ?_⟩
      intro i hi
      rcases hi with rfl | hna
      · exact hu.trans hz.symm
      · exact h.2 i hna
    exact ((suffix_agreement keep gs u v ha hreads).2 o hout).trans hv
  | false =>
    have ha : AgreeOn keep u (pinFalse u z) := by
      refine ⟨by simp [pinFalse], ?_⟩
      intro i _
      rw [pin_read]
      split <;> simp_all
    exact (suffix_agreement keep gs u _ ha hreads).2 o hout

end FreeInputChain

namespace FreeInputChain
open PEqualNP.CircuitLowerBounds

theorem closedPrefix_of_readers (A : ℕ → Prop) (gs : List Gate) (m : ℕ)
    (h : ∀ p g, gs[p]? = some g → ∀ i, i < m+p → Uses g i → A i → A (m+p)) :
    ClosedPrefix A m gs := by
  induction gs generalizing m with
  | nil => trivial
  | cons g gs ih =>
    constructor
    · intro hn i hi hr ha
      exact hn (h 0 g (by simp) i (by simpa using hi) hr ha)
    · apply ih
      intro p q hq i hi hr ha
      have eq : m + 1 + p = m + (p+1) := by omega
      rw [eq] at hi ⊢
      exact h (p+1) q (by simpa using hq) i hi hr ha

theorem forced_prefix (A : ℕ → Prop) (gs : List Gate) (w : List Bool)
    (base : ∀ i, i < w.length → A i → w.getD i false = true)
    (chain : ∀ p g, gs[p]? = some g → A (w.length+p) →
      g.op = GateOp.or ∧ ∃ i ∈ g.inputs, i < w.length+p ∧ A i) :
    ∀ i, i < (gs.foldl advance w).length → A i →
      (gs.foldl advance w).getD i false = true := by
  induction gs generalizing w with
  | nil => exact base
  | cons g gs ih =>
    apply ih
    · intro i hi ha
      by_cases hold : i < w.length
      · exact (List.getD_append _ _ _ _ hold).trans (base i hold ha)
      · have he : i = w.length := by
          simp [advance] at hi
          omega
        subst i
        obtain ⟨hop, j, hj, hjl, hja⟩ := chain 0 g (by simp) ha
        have hval := base j hjl hja
        change (w ++ [_]).getD w.length false = true
        rw [List.getD_append_right _ _ _ _ (le_refl _)]
        simpa [hop, GateOp.eval, List.any_eq_true] using
          (show ∃ j ∈ g.inputs, w.getD j false = true from ⟨j, hj, hval⟩)
    · intro p q hq ha
      have he : (advance w g).length+p = w.length+(p+1) := by simp [advance]; omega
      rw [he] at ha ⊢
      exact chain (p+1) q (by simpa using hq) ha

end FreeInputChain

namespace FreeInputChain
open PEqualNP.CircuitLowerBounds

def Edge (s : ℕ) (C : Circuit) (t b : ℕ) : Prop :=
  ∃ j : Fin C.gates.length, b = s + 1 + j.val ∧ Uses (C.gates.get j) t

theorem natural_input_lower {s t : ℕ} {C : Circuit}
    (r : Relation.ReflTransGen (Edge s C) s t) : s ≤ t := by
  cases r with
  | refl => omega
  | tail _ h => obtain ⟨j, rfl, _⟩ := h; omega

private theorem advance_len (xs : List Bool) (gs : List Gate) :
    (gs.foldl advance xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih => simp [ih, advance]; omega

theorem graph_frontier_factor (s a : ℕ) (C : Circuit) (pre post : List Gate)
    (hC : C.gates = pre ++ post) (ha : a = s + pre.length)
    (reach : Relation.ReflTransGen (Edge s C) s a)
    (noSkip : ∀ t d, Relation.ReflTransGen (Edge s C) s t → t < a → a < d →
      ¬ Edge s C t d)
    (orChain : ∀ j : Fin C.gates.length,
      Relation.ReflTransGen (Edge s C) s (s + 1 + j.val) →
      s + 1 + j.val ≤ a →
      (C.gates.get j).op = GateOp.or ∧ ∃ i ∈ (C.gates.get j).inputs,
        i < s + 1 + j.val ∧ Relation.ReflTransGen (Edge s C) s i)
    (outAbove : a ≤ C.output) (xs : List Bool) (len : xs.length = s + 1)
    (hiOutput : C.eval (xs.set s true) = true) :
    C.eval xs = ((pre.foldl advance xs).getD a false ||
      (post.foldl advance (pinFalse (pre.foldl advance xs) a)).getD C.output false) := by
  let R := Edge s C
  let A := fun i => Relation.ReflTransGen R s i ∧ i ≤ a
  let ys := xs.set s true
  have ylen : ys.length = s+1 := by simp [ys, len]
  have base : AgreeOn (fun i => ¬ A i) xs ys := by
    constructor
    · omega
    · intro i hn
      have his : s ≠ i := by
        rintro rfl
        exact hn ⟨.refl, by omega⟩
      simp [ys, List.getD_eq_getElem?_getD, his]
  have forcedBase : ∀ i, i < ys.length → A i → ys.getD i false = true := by
    intro i hil hi
    have hsi := natural_input_lower hi.1
    have he : s = i := by omega
    subst i
    simp [ys, List.getD_eq_getElem?_getD, show s < xs.length by omega]
  have preLookup : ∀ p g, pre[p]? = some g → ∃ j : Fin C.gates.length,
      j.val = p ∧ C.gates.get j = g ∧ p < pre.length := by
    intro p g hg
    obtain ⟨hp, eq⟩ := List.getElem?_eq_some_iff.mp hg
    have hpc : p < C.gates.length := by rw [hC, List.length_append]; omega
    refine ⟨⟨p, hpc⟩, rfl, ?_, hp⟩
    simpa [List.get_eq_getElem, hC, List.getElem_append_left hp] using eq
  have cp : ClosedPrefix A xs.length pre := by
    apply closedPrefix_of_readers
    intro p g hp i _ hr hi
    obtain ⟨j, hj, he, hl⟩ := preLookup p g hp
    exact ⟨hi.1.tail ⟨j, by omega, he ▸ hr⟩, by omega⟩
  have fc : ∀ p g, pre[p]? = some g → A (ys.length + p) →
      g.op = GateOp.or ∧ ∃ i ∈ g.inputs, i < ys.length+p ∧ A i := by
    intro p g hp hi
    obtain ⟨j, hj, he, hl⟩ := preLookup p g hp
    have key : s + 1 + j.val = ys.length + p := by omega
    obtain ⟨hop, i, hin, hie, hir⟩ := orChain j (key ▸ hi.1) (by omega)
    rw [he] at hop hin
    exact ⟨hop, i, hin, by omega, hir, by omega⟩
  have hv := forced_prefix A pre ys forcedBase fc a (by rw [advance_len]; omega) ⟨reach, le_rfl⟩
  have rpost : ∀ g ∈ post, ∀ i, Uses g i → i = a ∨ ¬ A i := by
    intro g hg i uses
    by_cases eq : i = a
    · exact Or.inl eq
    right
    intro hi
    obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨hpl, he⟩ := List.getElem?_eq_some_iff.mp hp
    let j : Fin C.gates.length := ⟨pre.length+p, by rw [hC, List.length_append]; omega⟩
    have jval : j.val = pre.length+p := rfl
    have gj : C.gates.get j = g := by
      simpa [j, List.get_eq_getElem, hC, List.getElem_append_right (show pre.length ≤ pre.length+p by omega)] using he
    exact noSkip i (s+1+j.val) hi.1 (by have := hi.2; omega) (by omega) ⟨j, rfl, gj ▸ uses⟩
  have hout : C.output = a ∨ ¬ A C.output := by
    by_cases h : C.output = a
    · exact Or.inl h
    exact Or.inr (fun hh => h (Nat.le_antisymm hh.2 outAbove))
  have decomp (u : List Bool) : C.eval u = (post.foldl advance (pre.foldl advance u)).getD C.output false := by
    change (C.gates.foldl advance u).getD C.output false = _
    rw [hC, List.foldl_append]
  rw [decomp]
  exact frontier_factor A a C.output post _ _ (prefix_agreement A pre xs ys base cp)
    hv rpost hout ((decomp ys).symm.trans hiOutput)

end FreeInputChain

namespace FreeInputChain
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem eval_set_last (n : ℕ) (H : (Fin n → Bool) → Bool) (C : Circuit)
    (hf : ∀ x : Fin (n+1) → Bool, circuitFun (n+1) C x =
      (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) (x : Fin (n+1) → Bool) :
    C.eval ((List.ofFn x).set n true) = true := by
  let y := Function.update x (Fin.last n) true
  have hxy : (List.ofFn x).set n true = List.ofFn y := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_set, List.getElem_ofFn]
      by_cases he : i = n <;> simp [y, Function.update, Fin.ext_iff, he, eq_comm]
  rw [hxy]
  change circuitFun (n+1) C y = true
  simp [hf, y]

end FreeInputChain

namespace FreeInputChain
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem free_bit_sensitive (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (hnc : ∃ y y', H y ≠ H y')
    (hf : ∀ x : Fin (n + 1) → Bool, circuitFun (n + 1) C x =
      (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) :
    ∃ y : Fin n → Bool,
      circuitFun (n+1) C (Fin.snoc y false) = false ∧
      circuitFun (n+1) C (Fin.snoc y true) = true := by
  obtain ⟨y, y', hd⟩ := hnc
  obtain ⟨z,hz⟩ : ∃ z, H z = false := by
    cases h : H y with
    | false => exact ⟨y,h⟩
    | true =>
      refine ⟨y',?_⟩
      cases e : H y' <;> simp_all
  refine ⟨z, ?_, ?_⟩ <;> simpa [hz] using hf (Fin.snoc z _)

theorem snoc_agreement (n : ℕ) (y : Fin n → Bool) (a b : Bool) :
    AgreeOn (fun i => i ≠ n) (List.ofFn (Fin.snoc y a)) (List.ofFn (Fin.snoc y b)) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases he : i < n
  · have e : (⟨i, by omega⟩ : Fin (n+1)) = (⟨i,he⟩ : Fin n).castSucc := rfl
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left (show i < n+1 by omega), Option.getD_some, e, Fin.snoc_castSucc]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_right (show ¬ i < n+1 by omega)]

theorem has_free_reader (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (hnc : ∃ y y', H y ≠ H y') (hout : C.output ≠ n)
    (hf : ∀ x : Fin (n + 1) → Bool, circuitFun (n + 1) C x =
      (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) :
    ∃ j : Fin C.gates.length, Uses (C.gates.get j) n := by
  by_contra hn
  obtain ⟨y, h0, h1⟩ := free_bit_sensitive n C H hnc hf
  have nod : ∀ g ∈ C.gates, ∀ i, Uses g i → i ≠ n := by
    intro g hg i hu he
    subst i
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hg
    exact hn ⟨j, hj ▸ hu⟩
  have eq := (suffix_agreement (fun i => i ≠ n) C.gates _ _ (snoc_agreement n y false true)
    nod).2 C.output hout
  change circuitFun (n+1) C (Fin.snoc y false) = circuitFun (n+1) C (Fin.snoc y true) at eq
  rw [h0,h1] at eq
  contradiction

end FreeInputChain

namespace FreeInputChain

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.FreeInput568

theorem gate_split (C : Circuit) (j : Fin C.gates.length) :
    C.gates = C.gates.take j.val ++ C.gates.get j :: C.gates.drop (j.val+1) := by
  change _ = _ ++ C.gates[j.val] :: _
  rw [List.getElem_cons_drop j.isLt, List.take_append_drop]

theorem indexed_gate_shape {n : ℕ} (C : Circuit) (hm : IsMinimalCircuit n C)
    (hnc : ∃ x y, circuitFun n C x ≠ circuitFun n C y) (j : Fin C.gates.length) :
    let g := C.gates.get j
    (g.op = GateOp.not ∧ ∃ i < n + j.val, g.inputs.head? = some i) ∨
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, g.inputs = [a,b] ∧ a < n + j.val ∧ b < n + j.val ∧ a ≠ b) := by
  simpa [List.length_take, Nat.min_eq_left j.isLt.le] using
    MinimalClean.gate_shape n C hm hnc _ _ _ (gate_split C j)

theorem indexed_reader_lt {n : ℕ} (C : Circuit) (hm : IsMinimalCircuit n C)
    (hnc : ∃ x y, circuitFun n C x ≠ circuitFun n C y) (j : Fin C.gates.length) (a : ℕ)
    (h : Uses (C.gates.get j) a) : a < n + j.val := by
  rcases indexed_gate_shape C hm hnc j with ⟨hop,i,hi,hhead⟩ | ⟨hop,b,c,hins,hb,hc,_⟩
  · rcases h with ⟨_, hh⟩ | ⟨hx,_⟩
    · rw [hh] at hhead
      exact Option.some.inj hhead ▸ hi
    · exact (hx hop).elim
  · rcases h with ⟨hx,_⟩ | ⟨_, hm⟩
    · rcases hop with h|h <;> rw [h] at hx <;> cases hx
    · simp only [hins, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> assumption

theorem indexed_edge_lt {s : ℕ} (C : Circuit) (hm : IsMinimalCircuit (s+1) C)
    (hnc : ∃ x y, circuitFun (s+1) C x ≠ circuitFun (s+1) C y) {a b : ℕ}
    (h : Edge s C a b) : a < b := by
  obtain ⟨j,rfl,hj⟩ := h
  exact indexed_reader_lt C hm hnc j a hj

theorem indexed_live {s : ℕ} (C : Circuit) (hm : IsMinimalCircuit (s+1) C)
    (j : Fin C.gates.length) (h : C.output ≠ s+1+j.val) :
    ∃ d, Edge s C (s+1+j.val) d := by
  let post := C.gates.drop (j.val+1)
  have hl : (C.gates.take j.val).length = j.val := by simp
  obtain ⟨g, hg, hr⟩ := FreeInputLive.live (s+1) C hm _ (C.gates.get j) post (gate_split C j) (by rwa [hl])
  rw [hl] at hr
  have hmem : g ∈ C.gates := by exact List.mem_of_mem_drop hg
  obtain ⟨i,hi⟩ := List.mem_iff_get.1 hmem
  exact ⟨s+1+i.val,i,rfl,hi.symm ▸ (mem_normGate_iff g _).1 hr⟩

end FreeInputChain

namespace PEqualNP.MetaComplexity.FreeInput568

open PEqualNP.CircuitLowerBounds

theorem minimal_cut_by_index (n z p : ℕ) (C : Circuit)
    (hmin : IsMinimalCircuit n C) (hz : z < n + p)
    (factor : ∀ x : Fin n → Bool,
      let v := wiresFrom (C.gates.take p) (List.ofFn x)
      circuitFun n C x =
        (v.getD z false || (wiresFrom (C.gates.drop p) (v.set z false)).getD C.output false))
    (j : Fin C.gates.length) (hp : p ≤ j.val) (hr : readsWire (C.gates.get j) z) :
    ∀ t : Fin C.gates.length, j < t →
      ¬ readsWire (C.gates.get t) z ∧
      ((C.gates.get j).op ≠ GateOp.or → ¬ readsWire (C.gates.get t) (n + j.val)) := by
  let pref := C.gates.take p
  let pre := (C.gates.drop p).take (j.val - p)
  let post := C.gates.drop (j.val + 1)
  have ppl : p ≤ C.gates.length := by omega
  have plen : pref.length = p := by simp [pref, ppl]
  have qlen : pre.length = j.val - p := by simp [pre]; omega
  have split : C.gates.drop p = pre ++ C.gates.get j :: post := by
    have hh := List.take_append_drop (j.val-p) (C.gates.drop p)
    rw [List.drop_drop, Nat.add_sub_of_le hp, List.drop_eq_getElem_cons j.isLt] at hh
    exact hh.symm
  have whole : C.gates = pref ++ (pre ++ C.gates.get j :: post) := by
    rw [← split]
    exact (List.take_append_drop ..).symm
  have exclude := minimal_cut_reader n z C pref pre (C.gates.get j) post whole hmin
    (by omega) (by rw [← split]; exact factor) hr
  intro t hlt
  have hmem : C.gates.get t ∈ post := by
    apply List.mem_drop_iff_getElem.mpr
    have ht : j.val < t.val := hlt
    refine ⟨t.val - (j.val + 1), by omega, ?_⟩
    simp [show j.val + 1 + (t.val - (j.val + 1)) = t.val by omega]
  refine ⟨fun h => exclude (Or.inl ⟨_, hmem, h⟩), fun hnor h => ?_⟩
  apply exclude
  right
  refine ⟨hnor, _, hmem, ?_⟩
  simpa only [show n + pref.length + pre.length = n + j.val by omega] using h

theorem minimal_cut_unique (n z p : ℕ) (C : Circuit)
    (hmin : IsMinimalCircuit n C) (hz : z < n + p)
    (factor : ∀ x : Fin n → Bool,
      let v := wiresFrom (C.gates.take p) (List.ofFn x)
      circuitFun n C x =
        (v.getD z false || (wiresFrom (C.gates.drop p) (v.set z false)).getD C.output false))
    (j t : Fin C.gates.length) (hj : p ≤ j.val) (ht : p ≤ t.val)
    (rj : readsWire (C.gates.get j) z) (rt : readsWire (C.gates.get t) z) : j = t := by
  rcases lt_trichotomy j t with h | h | h
  · exact ((minimal_cut_by_index n z p C hmin hz factor j hj rj t h).1 rt).elim
  · exact h
  · exact ((minimal_cut_by_index n z p C hmin hz factor t ht rt j h).1 rj).elim

end PEqualNP.MetaComplexity.FreeInput568

namespace FreeInputChain
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.FreeInput568

theorem indexed_factor (s a : ℕ) (C : Circuit) (H : (Fin s → Bool) → Bool)
    (hf : ∀ x : Fin (s+1) → Bool, circuitFun (s+1) C x =
      (x (Fin.last s) || H (fun i : Fin s => x i.castSucc)))
    (reach : Relation.ReflTransGen (Edge s C) s a)
    (noSkip : ∀ t d, Relation.ReflTransGen (Edge s C) s t → t < a → a < d →
      ¬ Edge s C t d)
    (orChain : ∀ j : Fin C.gates.length,
      Relation.ReflTransGen (Edge s C) s (s + 1 + j.val) →
      s + 1 + j.val ≤ a →
      (C.gates.get j).op = GateOp.or ∧ ∃ i ∈ (C.gates.get j).inputs,
        i < s + 1 + j.val ∧ Relation.ReflTransGen (Edge s C) s i)
    (outAbove : a ≤ C.output) :
    ∀ x : Fin (s+1) → Bool,
      let v := wiresFrom (C.gates.take (a-s)) (List.ofFn x)
      circuitFun (s+1) C x =
        (v.getD a false || (wiresFrom (C.gates.drop (a-s)) (v.set a false)).getD C.output false) := by
  have lo := natural_input_lower reach
  have hi : a ≤ s + C.gates.length := by
    cases reach with
    | refl => omega
    | tail _ edge => obtain ⟨j, rfl, _⟩ := edge; omega
  have ha : a = s + (C.gates.take (a-s)).length := by simp [List.length_take]; omega
  intro x
  exact graph_frontier_factor s a C _ _ (List.take_append_drop (a-s) C.gates).symm ha
    reach noSkip orChain outAbove (List.ofFn x) (by simp) (eval_set_last s H C hf x)

end FreeInputChain

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.FreeInput568
open FreeInputChain

theorem advance_frontier (s z : ℕ) (C : Circuit)
    (hm : IsMinimalCircuit (s+1) C)
    (hlo : s ≤ z) (_hhi : z < s+C.gates.length)
    (ltEdge : ∀ a b, Edge s C a b → a < b)
    (live : ∀ j : Fin C.gates.length, s+1+j.val ≠ s+C.gates.length →
      ∃ t : Fin C.gates.length, Uses (C.gates.get t) (s+1+j.val))
    (haveReader : ∃ j : Fin C.gates.length, Uses (C.gates.get j) z)
    (factor : ∀ x : Fin (s+1) → Bool,
      let v := wiresFrom (C.gates.take (z-s)) (List.ofFn x)
      circuitFun (s+1) C x = (v.getD z false ||
        (wiresFrom (C.gates.drop (z-s)) (v.set z false)).getD C.output false))
    (terminalOr : ∀ j : Fin C.gates.length, s+1+j.val = s+C.gates.length →
      Uses (C.gates.get j) z → (C.gates.get j).op = GateOp.or) :
    ∃ j : Fin C.gates.length,
      Uses (C.gates.get j) z ∧ (C.gates.get j).op = GateOp.or ∧
      z < s+1+j.val ∧ ∀ d, Edge s C z d → d = s+1+j.val := by
  obtain ⟨j, hj⟩ := haveReader
  have hjlt := ltEdge _ _ ⟨j,rfl,hj⟩
  have first := minimal_cut_by_index (s+1) z (z-s) C hm (by omega) factor j (by omega) hj
  have hor : (C.gates.get j).op = GateOp.or := by
    by_cases hlast : s+1+j.val = s+C.gates.length
    · exact terminalOr j hlast hj
    · obtain ⟨t,ht⟩ := live j hlast
      have htlt := ltEdge _ _ ⟨t,rfl,ht⟩
      by_contra hnot
      exact (first t (show j.val < t.val by omega)).2 hnot ht
  refine ⟨j,hj,hor,hjlt,?_⟩
  rintro d ⟨t,rfl,ht⟩
  have htlt := ltEdge _ _ ⟨t,rfl,ht⟩
  have he := minimal_cut_unique (s+1) z (z-s) C hm (by omega) factor j t
    (by omega) (by omega) hj ht
  rw [he]

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.FreeInput568
open FreeInputChain

theorem local_advance (s : ℕ) (C : Circuit) (H : (Fin s → Bool) → Bool)
    (hm : IsMinimalCircuit (s+1) C) (hnc : ∃ y y', H y ≠ H y')
    (hf : ∀ x : Fin (s+1) → Bool, circuitFun (s+1) C x =
      (x (Fin.last s) || H (fun i : Fin s => x i.castSucc)))
    (hfunc : ∃ x y, circuitFun (s+1) C x ≠ circuitFun (s+1) C y)
    (hout : C.output = s+C.gates.length) (z : ℕ)
    (hr : Relation.ReflTransGen (Edge s C) s z) (hhi : z < s+C.gates.length)
    (hskip : ∀ t d, Relation.ReflTransGen (Edge s C) s t → t < z → z < d →
      ¬ Edge s C t d)
    (hor : ∀ j : Fin C.gates.length,
      Relation.ReflTransGen (Edge s C) s (s+1+j.val) → s+1+j.val ≤ z →
      (C.gates.get j).op = GateOp.or ∧ ∃ i ∈ (C.gates.get j).inputs,
        i < s+1+j.val ∧ Relation.ReflTransGen (Edge s C) s i) :
    ∃ j : Fin C.gates.length, Edge s C z (s+1+j.val) ∧
      (C.gates.get j).op = GateOp.or ∧ ∀ d, Edge s C z d → d = s+1+j.val := by
  have hlo := natural_input_lower hr
  have factor := indexed_factor s z C H hf hr hskip hor (by omega)
  have live (j : Fin C.gates.length) (h : s+1+j.val ≠ s+C.gates.length) :
      ∃ t : Fin C.gates.length, Uses (C.gates.get t) (s+1+j.val) := by
    obtain ⟨_,t,_,ht⟩ := indexed_live C hm j (by omega)
    exact ⟨t,ht⟩
  have reader : ∃ j : Fin C.gates.length, Uses (C.gates.get j) z := by
    by_cases hz : z = s
    · subst z
      exact has_free_reader s C H hnc (by omega) hf
    · let j : Fin C.gates.length := ⟨z-(s+1),by omega⟩
      have eq : s+1+j.val = z := by dsimp [j]; omega
      exact eq ▸ live j (by omega)
  have dom (x : Fin (s+1) → Bool) (h : (C.wires (List.ofFn x)).getD z false = true) :
      circuitFun (s+1) C x = true := by
    have hi : z < (wiresFrom (C.gates.take (z-s)) (List.ofFn x)).length := by
      simp [length_wiresFrom, List.length_take]; omega
    rw [wires_eq, ← List.take_append_drop (z-s) C.gates, wiresFrom_append, getD_wiresFrom _ _ _ hi] at h
    simpa only [h, Bool.true_or] using factor x
  obtain ⟨j,hj,ho,_,hu⟩ := advance_frontier s z C hm hlo hhi
    (fun _ _ he => indexed_edge_lt C hm hfunc he) live reader factor (by
      intro j hend hj
      exact MinimalClean.terminal_reader_or (s+1) C hm hfunc j z (by omega) (by omega)
        (indexed_reader_lt C hm hfunc j z hj) hj dom)
  exact ⟨j,⟨j,rfl,hj⟩,ho,hu⟩

private theorem extractOrPath {s N : ℕ} (R : ℕ → ℕ → Prop) (hN : 0 < N)
    (next : ∀ a, Relation.ReflTransGen R s a → a ≠ s + N →
      ∃ b, R a b ∧ a < b ∧ b ≤ s + N ∧ ∀ d, R a d → d = b)
    (stop : ∀ d, ¬ R (s + N) d) :
    ∃ (k : ℕ) (c : Fin (k + 1) → Fin N), StrictMono c ∧
      (c (Fin.last k)).val + 1 = N ∧
      (∀ w, R s w ↔ w = s + 1 + (c 0).val) ∧
      (∀ i : Fin k, ∀ w, R (s + 1 + (c i.castSucc).val) w ↔
        w = s + 1 + (c i.succ).val) ∧
      (∀ j : Fin N, Relation.TransGen R s (s + 1 + j.val) ↔
        ∃ i : Fin (k + 1), c i = j) := by
  classical
  let f (a : ℕ) := if h : Relation.ReflTransGen R s a ∧ a ≠ s + N
    then (next a h.1 h.2).choose else a
  let v (i : ℕ) := f^[i] s
  have h0 : v 0 = s := rfl
  have hs (i : ℕ) : v (i+1) = f (v i) := Function.iterate_succ_apply' f i s
  have stay (i : ℕ) (h : v i = s + N) : v (i + 1) = s + N := by
    rw [hs, h]
    simp [f]
  have prop (a : ℕ) (hr : Relation.ReflTransGen R s a) (hne : a ≠ s + N) :
      R a (f a) ∧ a < f a ∧ f a ≤ s + N ∧ ∀ d, R a d → d = f a := by
    simpa [f, hr, hne] using (next a hr hne).choose_spec
  have inv (i : ℕ) : Relation.ReflTransGen R s (v i) ∧ v i ≤ s + N ∧
      (s + i ≤ v i ∨ v i = s + N) := by
    induction i with
    | zero => exact ⟨.refl, by omega, Or.inl (by omega)⟩
    | succ i ih =>
      by_cases e : v i = s + N
      · rw [stay i e]
        exact ⟨e ▸ ih.1, le_rfl, Or.inr rfl⟩
      obtain ⟨he, hl, hu, _⟩ := prop _ ih.1 e
      rw [hs]
      exact ⟨ih.1.tail he, hu, Or.inl (by rcases ih.2.2 with h | h <;> omega)⟩
  have hit : ∃ i, v i = s + N := by
    have h := inv N
    exact ⟨N, by rcases h.2.2 with h' | h' <;> omega⟩
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hit = k + 1 := by
    have e := Nat.find_spec hit
    cases h : Nat.find hit with
    | zero => rw [h, h0] at e; omega
    | succ k => exact ⟨k, rfl⟩
  have endval : v (k + 1) = s + N := hk ▸ Nat.find_spec hit
  have active (i : ℕ) (hi : i < k + 1) : v i ≠ s + N :=
    Nat.find_min hit (hk.symm ▸ hi)
  have step (i : ℕ) (hi : i < k + 1) :
      R (v i) (v (i+1)) ∧ v i < v (i+1) ∧ ∀ w, R (v i) w ↔ w = v (i+1) := by
    obtain ⟨he, hl, _, hu⟩ := prop _ (inv i).1 (active i hi)
    rw [hs]
    exact ⟨he, hl, fun w => ⟨hu w, fun h => h ▸ he⟩⟩
  have gt (i : ℕ) (hi : i < k + 1) : s < v (i+1) := by
    have hle := (inv i).2.2.resolve_right (active i hi)
    have := (step i hi).2.1
    omega
  let c (i : Fin (k + 1)) : Fin N := ⟨v (i.val+1) - (s+1), by
    have := gt i.val i.isLt
    have := (inv (i.val+1)).2.1
    omega⟩
  have val (i : Fin (k + 1)) : s + 1 + (c i).val = v (i.val+1) := by
    change s + 1 + (v (i.val+1) - (s+1)) = _
    have := gt i.val i.isLt
    omega
  refine ⟨k, c, Fin.strictMono_iff_lt_succ.mpr ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have h := (step (i.val+1) (by omega)).2.1
    have ha := val i.castSucc
    have hb := val i.succ
    change (c i.castSucc).val < (c i.succ).val
    simp only [Fin.val_castSucc, Fin.val_succ] at ha hb
    omega
  · have h := val (Fin.last k)
    simp only [Fin.val_last, endval] at h
    omega
  · intro w
    rw [val]
    exact (step 0 (by omega)).2.2 w
  · intro i w
    rw [val, val]
    exact (step (i.val+1) (by omega)).2.2 w
  · have forward (w : ℕ) (h : Relation.TransGen R s w) :
        ∃ i : Fin (k+1), w = v (i.val+1) := by
      induction h with
      | single he => exact ⟨0, ((step 0 (by omega)).2.2 _).mp he⟩
      | tail _ he ih =>
        obtain ⟨i, rfl⟩ := ih
        by_cases e : i.val + 1 = k + 1
        · rw [e, endval] at he
          exact (stop _ he).elim
        · have hi := i.isLt
          exact ⟨⟨i.val+1, by omega⟩, ((step (i.val+1) (by omega)).2.2 _).mp he⟩
    intro j
    constructor
    · intro hj
      obtain ⟨i, hi⟩ := forward _ hj
      exact ⟨i, Fin.ext (by have := val i; omega)⟩
    · rintro ⟨i, rfl⟩
      rw [val]
      exact Relation.TransGen.tail' (inv i.val).1 (step i.val i.isLt).1

private theorem sideOffPath {s N k : ℕ} (R : ℕ → ℕ → Prop)
    (c : Fin (k + 1) → Fin N) (hc : StrictMono c)
    (hshape : ∀ a b, R a b → s < b ∧ b ≤ s + N)
    (hr : ∀ j : Fin N, Relation.TransGen R s (s+1+j.val) ↔ ∃ i, c i = j)
    (hout : ∀ d, ¬ R (s+1+(c (Fin.last k)).val) d)
    (hnext : ∀ i : Fin k, ∀ d, R (s+1+(c i.castSucc).val) d →
      d = s+1+(c i.succ).val)
    {u : ℕ} {j : Fin (k+1)} (he : R u (s+1+(c j).val))
    (hdiff : ∀ i : Fin k, j = i.succ → u ≠ s+1+(c i.castSucc).val) :
    ¬ Relation.TransGen R s u := by
  intro hreach
  obtain ⟨a, _, ha⟩ := (Relation.TransGen.tail'_iff.mp hreach)
  obtain ⟨hlo,hhi⟩ := hshape _ _ ha
  let q : Fin N := ⟨u-(s+1), by omega⟩
  have eq : s+1+q.val = u := by change s+1+(u-(s+1)) = u; omega
  obtain ⟨i,hi⟩ := (hr q).mp (eq.symm ▸ hreach)
  have hu : s+1+(c i).val = u := hi ▸ eq
  rw [← hu] at he
  by_cases last : i = Fin.last k
  · rw [last] at he
    exact hout _ he
  · obtain ⟨i',rfl⟩ := Fin.eq_castSucc_of_ne_last last
    have hj := hnext i' _ he
    have hji : j = i'.succ := hc.injective (Fin.ext (by omega))
    exact hdiff i' hji hu.symm

private theorem earlierReadersBound {R : ℕ → ℕ → Prop} {s a : ℕ}
    (ltWire : ∀ u v, R u v → u < v)
    (ha : Relation.ReflTransGen R s a)
    (unique : ∀ t, Relation.ReflTransGen R s t → t < a → ∀ d e, R t d → R t e → d = e)
    {t d : ℕ} (ht : Relation.ReflTransGen R s t) (hlt : t < a) (hd : R t d) : d ≤ a := by
  have suffix {u : ℕ} (hu : Relation.ReflTransGen R s u) (hul : u < a) :
      Relation.ReflTransGen R u a := by
    induction hu with
    | refl => exact ha
    | tail hb he ih =>
      have hba := (ltWire _ _ he).trans hul
      rcases (ih hba).cases_head with bad | ⟨q, hq, hqa⟩
      · omega
      · simpa [unique _ hb hba _ _ he hq] using hqa
  rcases (suffix ht hlt).cases_head with bad | ⟨q, hq, hqa⟩
  · omega
  rw [unique _ ht hlt _ _ hd hq]
  have mono {v u : ℕ} (h : Relation.ReflTransGen R v u) : v ≤ u := by
    induction h with
    | refl => exact le_rfl
    | tail _ he ih => exact ih.trans (ltWire _ _ he).le
  exact mono hqa

open PEqualNP.CircuitLowerBounds

private def chainReads (g : Gate) (a : ℕ) : Prop :=
  (g.op = GateOp.not ∧ g.inputs.head? = some a) ∨
  (g.op ≠ GateOp.not ∧ a ∈ g.inputs)

private def chainEdge (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  ∃ j : Fin C.gates.length, b = n+1+j.val ∧ chainReads (C.gates.get j) a

private theorem chainAssembly {n : ℕ} {C : Circuit}
    (hne : 0 < C.gates.length) (ho : C.output = n+C.gates.length)
    (stop : ∀ d, ¬ chainEdge n C (n+C.gates.length) d)
    (unique : ∀ a, Relation.ReflTransGen (chainEdge n C) n a → a ≠ n+C.gates.length →
        ∃ b, chainEdge n C a b ∧ a < b ∧
        ∀ d, chainEdge n C a d → d = b)
    (binary : ∀ j : Fin C.gates.length, Relation.TransGen (chainEdge n C) n (n+1+j.val) →
        (C.gates.get j).op = GateOp.or ∧
        ∃ v w, v ≠ w ∧ v < n+1+j.val ∧ w < n+1+j.val ∧
          (C.gates.get j).inputs = [v,w]) :
    ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) := by
  classical
  let R := chainEdge n C
  let N := C.gates.length
  have shape (a b) (h : R a b) : n < b ∧ b ≤ n+N := by
    obtain ⟨j,rfl,_⟩ := h
    have hlt : j.val < N := j.isLt
    omega
  obtain ⟨k,c,hc,hl,first,deeper,reach⟩ := extractOrPath R hne
    (fun a hr hne' => by
      obtain ⟨b,hb,hlt,hu⟩ := unique a hr hne'
      exact ⟨b,hb,hlt,(shape _ _ hb).2,hu⟩) stop
  let wire (i : Fin (k+1)) := n+1+(c i).val
  have hr (i : Fin (k+1)) : Relation.TransGen R n (wire i) :=
    (reach (c i)).mpr ⟨i,rfl⟩
  have re (w) (j : Fin N) : R w (n+1+j.val) ↔ chainReads (C.gates.get j) w := by
    refine ⟨?_,fun h => ⟨j,rfl,h⟩⟩
    rintro ⟨q,hq,h⟩
    have e : j = q := Fin.ext (by omega)
    exact e ▸ h
  have mem (w) (i : Fin (k+1)) : R w (wire i) ↔ w ∈ (C.gates.get (c i)).inputs := by
    rw [re]
    unfold chainReads
    rw [(binary (c i) (hr i)).1]
    simp
  have hout (d) : ¬ R (wire (Fin.last k)) d := by
    have he : wire (Fin.last k) = n+N := by dsimp [wire,N] at *; omega
    exact he.symm ▸ stop d
  have oth (a) (i : Fin (k+1)) (h : R a (wire i)) :
      ∃ b, b ∈ (C.gates.get (c i)).inputs ∧ b ≠ a ∧ b < wire i := by
    obtain ⟨_,v,w,hvw,hv,hw,he⟩ := binary (c i) (hr i)
    have hmem := (mem a i).mp h
    rw [he] at hmem ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem ⊢
    rcases hmem with rfl|rfl
    · exact ⟨w,Or.inr rfl,hvw.symm,hw⟩
    · exact ⟨v,Or.inl rfl,hvw,hv⟩
  have fst : R n (wire 0) := (first _).mpr rfl
  have nxt (i : Fin k) : R (wire i.castSucc) (wire i.succ) := (deeper i _).mpr rfl
  refine ⟨k,c,hc,hl,?_,?_,(mem _ 0).mp fst,fun i => (mem _ _).mp (nxt i),?_,?_,reach,?_,?_⟩
  · omega
  · intro i
    obtain ⟨ho',v,w,_,_,_,he⟩ := binary (c i) (hr i)
    exact ⟨ho',by rw [he]; rfl⟩
  · intro j h
    have e := (first _).mp ((re n j).mpr h)
    exact Fin.ext (by omega)
  · intro i j h
    have e := (deeper i _).mp ((re _ j).mpr h)
    exact Fin.ext (by omega)
  · obtain ⟨b,hb,hne',hlt⟩ := oth n 0 fst
    refine ⟨b,hb,hne',hlt,?_⟩
    apply sideOffPath R c hc shape reach hout (fun i d h => (deeper i d).mp h) ((mem _ _).mpr hb)
    intro i h
    have e := congrArg Fin.val h
    simp at e
  · intro i
    obtain ⟨b,hb,hne',hlt⟩ := oth _ _ (nxt i)
    have he := (mem _ _).mpr hb
    have hbn : b ≠ n := by
      rintro rfl
      have e := (first _).mp he
      have hzero : i.succ = (0 : Fin (k+1)) :=
        hc.injective (Fin.ext (by dsimp [wire] at e; omega))
      have := congrArg Fin.val hzero
      simp at this
    refine ⟨b,hb,hne',hbn,hlt,?_⟩
    apply sideOffPath R c hc shape reach hout (fun j d h => (deeper j d).mp h) he
    intro j h
    have eq := Fin.succ_injective _ h
    exact eq ▸ hne'

private theorem frontierAssembly {n : ℕ} {C : Circuit}
    (hne : 0 < C.gates.length) (ho : C.output = n+C.gates.length)
    (inc : ∀ a b, chainEdge n C a b → a < b)
    (arity : ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.or →
        ∃ v w, v ≠ w ∧ v < n+1+j.val ∧ w < n+1+j.val ∧
          (C.gates.get j).inputs = [v,w])
    (advanceFrontier : ∀ a, Relation.ReflTransGen (chainEdge n C) n a →
        a < n+C.gates.length →
        (∀ t d, Relation.ReflTransGen (chainEdge n C) n t → t < a → a < d →
          ¬ chainEdge n C t d) →
        (∀ j : Fin C.gates.length, Relation.ReflTransGen (chainEdge n C) n (n+1+j.val) →
          n+1+j.val ≤ a → (C.gates.get j).op = GateOp.or ∧
          ∃ i ∈ (C.gates.get j).inputs, i < n+1+j.val ∧
             Relation.ReflTransGen (chainEdge n C) n i) →
        ∃ j : Fin C.gates.length, chainEdge n C a (n+1+j.val) ∧
          (C.gates.get j).op = GateOp.or ∧
          ∀ d, chainEdge n C a d → d = n+1+j.val) :
    ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) := by
  let R := chainEdge n C
  let T := n + C.gates.length
  let w (j : Fin C.gates.length) := n+1+j.val
  let succProp a := ∃ j : Fin C.gates.length, R a (w j) ∧ (C.gates.get j).op = GateOp.or ∧
    ∀ d, R a d → d = w j
  have upper {a b : ℕ} (h : R a b) : b ≤ T := by
    obtain ⟨j,rfl,h⟩ := h
    have := j.isLt
    dsimp [T]
    omega
  have reachUpper {a : ℕ} (h : Relation.ReflTransGen R n a) : a ≤ T := by
    rcases h.cases_tail with rfl|⟨b,_,hb⟩
    · dsimp [T]; omega
    · exact upper hb
  have or_of_prior (j : Fin C.gates.length) (h : Relation.ReflTransGen R n (w j))
      (prior : ∀ b, b < w j → Relation.ReflTransGen R n b → succProp b) :
      (C.gates.get j).op = GateOp.or ∧
      ∃ i ∈ (C.gates.get j).inputs, i < w j ∧ Relation.ReflTransGen R n i := by
    rcases h.cases_tail with hbad|⟨b,hrb,hb⟩
    · dsimp [w] at hbad; omega
    obtain ⟨j',_,hop,uni⟩ := prior b (inc _ _ hb) hrb
    have hw := uni _ hb
    have hjj : j' = j := Fin.ext (by dsimp [w] at hw; omega)
    subst j'
    obtain ⟨j',hw',hr'⟩ := hb
    have hjj : j' = j := Fin.ext (by dsimp [w] at hw'; omega)
    subst j'
    rcases hr' with ⟨hn,_⟩|⟨hn,hmem⟩
    · rw [hop] at hn; contradiction
    · exact ⟨hop,b,hmem,inc _ _ ⟨j,rfl,Or.inr ⟨hn,hmem⟩⟩,hrb⟩
  have allSucc (a : ℕ) (hr : Relation.ReflTransGen R n a) (hlt : a < T) : succProp a := by
    induction a using Nat.strong_induction_on with
    | ind a ih =>
      apply advanceFrontier a hr hlt
      · intro t d hrt hta had he
        have hu : ∀ b, Relation.ReflTransGen R n b → b < a →
            ∀ v w', R b v → R b w' → v = w' := by
          intro b hrb hba v w' hv hw
          obtain ⟨_,_,_,uniq⟩ := ih b hba hrb (hba.trans hlt)
          exact (uniq v hv).trans (uniq w' hw).symm
        exact (Nat.not_lt_of_ge (earlierReadersBound inc hr hu hrt hta he)) had
      · intro j hrj hja
        apply or_of_prior j hrj
        intro b hbj hrb
        have hba := lt_of_lt_of_le hbj hja
        exact ih b hba hrb (hba.trans hlt)
  refine chainAssembly hne ho (fun d he => ?_) ?_ ?_
  · exact (Nat.not_lt_of_ge (upper he)) (inc _ _ he)
  · intro a hr hne'
    obtain ⟨j,he,_,hu⟩ := allSucc a hr (lt_of_le_of_ne (reachUpper hr) hne')
    exact ⟨w j,he,inc _ _ he,hu⟩
  · intro j hrj
    have hir := or_of_prior j hrj.to_reflTransGen (fun b hbj hrb =>
      allSucc b hrb (hbj.trans_le (reachUpper hrj.to_reflTransGen)))
    exact ⟨hir.1,arity j hir.1⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity FreeInputChain

theorem PEqualNP.Outside.L_meta_568 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) := by
  intro n C H hm hnc hf
  obtain ⟨y,h0,h1⟩ := free_bit_sensitive n C H hnc hf
  have hfunc : ∃ x y, circuitFun (n+1) C x ≠ circuitFun (n+1) C y :=
    ⟨Fin.snoc y false, Fin.snoc y true, by rw [h0,h1]; decide⟩
  obtain ⟨j,hj,hout⟩ := FreeInputOutput.free_or_output n C H hm hnc hf
  have ho : C.output = n + C.gates.length := by omega
  apply frontierAssembly (by omega) ho
  · intro a b h
    exact indexed_edge_lt C hm hfunc h
  · intro j hop
    rcases indexed_gate_shape C hm hfunc j with ⟨hn,_⟩ | ⟨_,v,w,hi,hv,hw,hd⟩
    · rw [hop] at hn
      contradiction
    · exact ⟨v,w,hd,hv,hw,hi⟩
  · exact local_advance n C H hm hnc hf hfunc ho
