import Mathlib
import PEqualNP.Outside.L_meta_543
import PEqualNP.MetaComplexity.L106

namespace LeafDecor519
open PEqualNP.MetaComplexity

def addLeaves {n d : ℕ} (g : (Fin n → Bool) → Bool) (root : Fin d → Fin n)
    (x : Fin (n+d) → Bool) : Bool :=
  g (fun i => x (Fin.castAdd d i)) ||
    decide (∃ i : Fin d, x (Fin.castAdd d (root i)) = true ∧ x (Fin.natAdd n i) = true)

private lemma addLeaves_succ {n d : ℕ} (g : (Fin n → Bool) → Bool) (r : Fin (d+1) → Fin n)
    (x : Fin (n+(d+1)) → Bool) :
    addLeaves g r x = (addLeaves g (fun i => r i.castSucc) (fun j => x j.castSucc) ||
      (x (Fin.castAdd (d+1) (r (Fin.last d))) && x (Fin.last (n+d)))) := by
  unfold addLeaves
  simp only [Fin.exists_fin_succ',Bool.decide_or,Bool.decide_and,Bool.decide_eq_true]
  rw [Bool.or_assoc]
  rfl

private lemma embed_base {n d : ℕ} (g : (Fin n → Bool) → Bool) (r : Fin d → Fin n)
    (y : Fin n → Bool) : addLeaves g r (Fin.addCases y (fun _ => false)) = g y := by
  simp [addLeaves]

theorem delete_fresh_leaves (n d : ℕ) (g : (Fin n → Bool) → Bool) (r : Fin d → Fin n)
    (hnc : ∃ x y, g x ≠ g y)
    (seeds : ∀ i : Fin d, ∃ y, y (r i) = true ∧ g y = false) (s : ℕ)
    (hc : HasCircuitSize (n+d) (addLeaves g r) s) :
    ∃ t, t+d ≤ s ∧ HasCircuitSize n g t := by
  induction d generalizing s with
  | zero =>
    refine ⟨s,by omega,?_⟩
    have eq : addLeaves g r = g := by funext x; simp [addLeaves]
    exact eq ▸ hc
  | succ d ih =>
    let r' := fun i : Fin d => r i.castSucc
    let f := addLeaves g r'
    let v := Fin.castAdd d (r (Fin.last d))
    obtain ⟨a,b,hne⟩ := hnc
    have f_nc : ∃ x y, f x ≠ f y :=
      ⟨Fin.addCases a (fun _ => false), Fin.addCases b (fun _ => false), by
        simpa only [f,embed_base] using hne⟩
    obtain ⟨y,hy,hy'⟩ := seeds (Fin.last d)
    have vtrue : ∃ x : Fin (n+d) → Bool, x v = true ∧ f x = false :=
      ⟨Fin.addCases y (fun _ => false),by simpa [v] using hy,by simpa only [f,embed_base] using hy'⟩
    have hstep := PEqualNP.Outside.L_meta_543 (n+d) s f v f_nc vtrue
    have hs' : HasCircuitSize ((n+d)+1) (fun x : Fin ((n+d)+1) → Bool =>
        f (fun j => x j.castSucc) || (x v.castSucc && x (Fin.last (n+d)))) s := by
      convert hc using 1
      funext x
      exact (addLeaves_succ g r x).symm
    obtain ⟨t,ht,hf⟩ := hstep hs'
    obtain ⟨q,hq,hg⟩ := ih r' (fun i => seeds i.castSucc) t hf
    exact ⟨q, by omega, hg⟩

def cycleEdge (n : ℕ) (x : Fin n → Bool) :=
  decide (∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)

private theorem cycle_seed (n : ℕ) (hn : 5 ≤ n) (v : Fin n) :
    ∃ x, x v = true ∧ cycleEdge n x = false := by
  refine ⟨fun i => decide (i = v), by simp, ?_⟩
  simp only [cycleEdge, decide_eq_true_eq, decide_eq_false_iff_not]
  rintro ⟨i,j,step,hi,hj⟩
  rw [hi,hj] at step
  by_cases lt : v.val + 1 < n
  · rw [Nat.mod_eq_of_lt lt] at step
    omega
  · have eq : v.val + 1 = n := by omega
    rw [eq,Nat.mod_self] at step
    omega

theorem leaf_cycle_lower (n d : ℕ) (hn : 5 ≤ n) (r : Fin d → Fin n) (s : ℕ)
    (hc : HasCircuitSize (n+d) (addLeaves (cycleEdge n) r) s) :
    n+(n+1)/2+d ≤ s+1 := by
  have one : cycleEdge n (fun _ => true) = true := by
    apply decide_eq_true
    refine ⟨⟨0,by omega⟩, ⟨1,by omega⟩, ?_, rfl,rfl⟩
    exact (Nat.mod_eq_of_lt (show 1 < n by omega))
  have zero : cycleEdge n (fun _ => false) = false := by simp [cycleEdge]
  obtain ⟨t,hpay,hc'⟩ := delete_fresh_leaves n d _ r
    ⟨fun _ => true,fun _ => false,by rw [one,zero]; decide⟩ (fun i => cycle_seed n hn (r i)) s hc
  have := (PEqualNP.MetaComplexity.L106 n t hn).mp hc'
  omega

theorem alternating_leaves (h s : ℕ) (hh : 4 ≤ h)
    (hc : HasCircuitSize (2*h+h)
      (addLeaves (cycleEdge (2*h)) (fun i : Fin h => (⟨2*i.val,by omega⟩ : Fin (2*h)))) s) :
    4*h ≤ s+1 := by
  have := leaf_cycle_lower (2*h) h (by omega) _ s hc
  omega

end LeafDecor519
