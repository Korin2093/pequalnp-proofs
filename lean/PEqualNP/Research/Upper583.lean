import Mathlib
import PEqualNP.Defs

namespace Subdivision583

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gate (op : GateOp) (i j : ℕ) : Gate := ⟨op,[i,j]⟩

def circuit : Circuit := ⟨[
    gate .or 4 5, gate .or 10 6, gate .and 0 11,
    gate .or 4 7, gate .or 13 8, gate .and 1 14,
    gate .or 5 7, gate .or 16 9, gate .and 2 17,
    gate .or 6 8, gate .or 19 9, gate .and 3 20,
    gate .or 12 15, gate .or 18 21, gate .or 22 23],24⟩

theorem size15 : circuit.size = 15 := rfl

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp [circuit] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp [gate]

set_option maxRecDepth 10000 in
theorem correct (x : Fin 10 → Bool) :
    circuit.eval (List.ofFn x) = true ↔ ∃ u v : Fin 10,
       (u.val,v.val) ∈ ([(0,4),(4,1),(0,5),(5,2),(0,6),(6,3),
           (1,7),(7,2),(1,8),(8,3),(2,9),(9,3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true := by
  have equiv : circuit.eval (List.ofFn x) = ((x 0 && (x 4 || x 5 || x 6)) ||
    (x 1 && (x 4 || x 7 || x 8)) || ((x 2 && (x 5 || x 7 || x 9)) ||
     (x 3 && (x 6 || x 8 || x 9)))) := by
    rw [show List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9] by rfl]
    simp [circuit, gate, Circuit.eval, Circuit.wires, GateOp.eval]
  rw [equiv]
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
      Bool.or_eq_true, Bool.and_eq_true, or_assoc]
  constructor
  · rintro (⟨h, h'|h'|h'⟩ | ⟨h,h'|h'|h'⟩ | ⟨h,h'|h'|h'⟩ | ⟨h,h'|h'|h'⟩)
    all_goals first
      | exact ⟨0,4,by decide,h,h'⟩
      | exact ⟨0,5,by decide,h,h'⟩
      | exact ⟨0,6,by decide,h,h'⟩
      | exact ⟨4,1,by decide,h',h⟩
      | exact ⟨1,7,by decide,h,h'⟩
      | exact ⟨1,8,by decide,h,h'⟩
      | exact ⟨5,2,by decide,h',h⟩
      | exact ⟨7,2,by decide,h',h⟩
      | exact ⟨2,9,by decide,h,h'⟩
      | exact ⟨6,3,by decide,h',h⟩
      | exact ⟨8,3,by decide,h',h⟩
      | exact ⟨9,3,by decide,h',h⟩
  · rintro ⟨u,v,edges,hu,hv⟩
    rcases edges with e|e|e|e|e|e|e|e|e|e|e|e
    all_goals
      obtain ⟨e1,e2⟩ := e
      obtain ⟨u,hu'⟩ := u
      obtain ⟨v,hv'⟩ := v
      simp only at e1 e2
      subst u
      subst v
      simp_all

end Subdivision583

theorem Upper583.sharp : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 15 ∧ (∀ x : Fin 10 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 10, (u.val, v.val) ∈ ([(0, 4), (4, 1), (0, 5), (5, 2), (0, 6), (6, 3), (1, 7), (7, 2), (1, 8), (8, 3), (2, 9), (9, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) :=
  ⟨Subdivision583.circuit, Subdivision583.monotone, Subdivision583.size15, Subdivision583.correct⟩
