import Mathlib
import PEqualNP.Defs.Gct

namespace RowSymmetricLevel

variable {I : Type} [Fintype I] [DecidableEq I]

abbrev Mat (I : Type) := I × I → ℂ

def turn (a b : I) (t : Mat I) : Mat I := fun z => t (Equiv.swap a b z.1,z.2)

def level (L : Submodule ℂ (Mat I)) := ∀ t ∈ L,
    (∑ f : I ↪ I, ∏ i, (1+t (i,f i))) = (Nat.factorial (Fintype.card I) : ℂ)

def invariant (L : Submodule ℂ (Mat I)) := ∀ t ∈ L, ∀ a b : I, turn a b t ∈ L

private theorem no_two (L : Submodule ℂ (Mat I)) (hl : level L) {a j k : I} (hjk : j ≠ k)
    (T : Mat I) (ht : T ∈ L) (hj : ∀ r ≠ a, 1 + T (r,j) = 0)
    (hk : ∀ r ≠ a, 1 + T (r,k) = 0) : False := by
  have zero (f : I ↪ I) : ∏ i, (1+T (i,f i)) = 0 := by
    have sur := Finite.surjective_of_injective f.injective
    obtain ⟨u,hu⟩ := sur j
    obtain ⟨v,hv⟩ := sur k
    by_cases hua : u = a
    · have hva : v ≠ a := by rintro rfl; subst u; exact hjk (hu.symm.trans hv)
      exact Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hv]; exact hk v hva)
    · exact Finset.prod_eq_zero (Finset.mem_univ u) (by rw [hu]; exact hj u hua)
  have he := hl T ht
  simp only [zero,Finset.sum_const_zero] at he
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) he.symm

theorem no_flat (L : Submodule ℂ (Mat I)) (hl : level L) (T : Mat I) (hT : T ∈ L)
    (a : I) (flat : ∀ i j, T (i,j) = T (a,j)) : T = 0 := by
  funext z
  by_contra hn
  have nz : T (a,z.2) ≠ 0 := by
    change T z ≠ 0 at hn
    simpa only [flat z.1 z.2] using hn
  let x := -(T (a,z.2))⁻¹
  have h := hl (x • T) (L.smul_mem x hT)
  have allzero (f : I ↪ I) : ∏ i, (1+(x • T) (i,f i)) = 0 := by
    obtain ⟨r,hr⟩ := Finite.surjective_of_injective f.injective z.2
    apply Finset.prod_eq_zero (Finset.mem_univ r)
    change 1 + x * T (r, f r) = 0
    rw [hr,flat]
    simp [x,nz]
  simp only [allzero,Finset.sum_const_zero] at h
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) h.symm

private def diff (L : Submodule ℂ (Mat I)) (a b : I) : L →ₗ[ℂ] (I→ℂ) where
  toFun t j := t.val (a,j) - t.val (b,j)
  map_add' t s := by funext j; simp only [Submodule.coe_add, Pi.add_apply]; ring
  map_smul' c t := by funext j; simp only [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private theorem unequal (L : Submodule ℂ (Mat I)) (hl : level L) (hs : invariant L)
    (a b : I) (hab : a ≠ b) (t : L) (j k : I) (hjk : j ≠ k)
    (he : diff L a b t j = diff L a b t k) : diff L a b t j = 0 := by
  let w := diff L a b t
  let d : Mat I := t.val - turn a b t.val
  have hd : d ∈ L := L.sub_mem t.property (hs t.val t.property a b)
  have db (i : I) : d (b,i) = -w i := by
    change t.val (b,i) - t.val (Equiv.swap a b b,i) = - (t.val (a,i)-t.val (b,i))
    rw [Equiv.swap_apply_right]; ring
  have dn (r i : I) (ra : r ≠ a) (rb : r ≠ b) : d (r,i) = 0 := by
    change t.val (r,i) - t.val (Equiv.swap a b r,i) = 0
    rw [Equiv.swap_apply_of_ne_of_ne ra rb]; simp
  let D : Mat I := ∑ q ∈ Finset.univ.erase a, turn b q d
  have hD : D ∈ L := L.sum_mem (fun q _ => hs d hd b q)
  have spec (r i : I) (ra : r ≠ a) : D (r,i) = -w i := by
    change (∑ q ∈ Finset.univ.erase a, turn b q d) (r,i) = _
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single r]
    · exact (congrArg (fun x => d (x,i)) (Equiv.swap_apply_right b r)).trans (db i)
    · intro q hq hqr
      have qne : q ≠ a := (Finset.mem_erase.mp hq).1
      have g : Equiv.swap b q a = a := Equiv.swap_apply_of_ne_of_ne hab qne.symm
      have n1 : Equiv.swap b q r ≠ a := by
        intro e; exact ra ((Equiv.swap b q).injective (e.trans g.symm))
      have n2 : Equiv.swap b q r ≠ b := by
        intro e; exact hqr.symm ((Equiv.swap b q).injective (e.trans (Equiv.swap_apply_right b q).symm))
      exact dn _ i n1 n2
    · simp [ra]
  by_contra hn
  change w j ≠ 0 at hn
  change w j = w k at he
  apply no_two L hl (a := a) hjk ((w j)⁻¹ • D) (L.smul_mem _ hD)
  · intro r hr
    change 1 + (w j)⁻¹ * D (r,j) = 0
    rw [spec _ _ hr]
    simp [hn]
  · intro r hr
    change 1 + (w j)⁻¹ * D (r,k) = 0
    rw [spec _ _ hr,←he]
    simp [hn]

end RowSymmetricLevel

namespace RowSymmetricLevel

private theorem coordinate {I V : Type} [Nonempty I] [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] (I → ℂ)) (noCoincidence : ∀ v j k, j ≠ k → f v j = f v k → f v j = 0) :
    ∃ j : I, ∀ v, f v j = 0 → f v = 0 := by
  classical
  by_cases allzero : ∀ v, f v = 0
  · exact ⟨Classical.arbitrary I,fun v _ => allzero v⟩
  push Not at allzero
  obtain ⟨u,hu⟩ := allzero
  obtain ⟨j,hj⟩ : ∃ j, f u j ≠ 0 := by
    by_contra! h; exact hu (funext h)
  refine ⟨j,fun v h => ?_⟩
  funext k
  by_contra hk
  change f v k ≠ 0 at hk
  have hjk : j ≠ k := by rintro rfl; contradiction
  let c := (f u j - f u k) / f v k
  let s := u + c • v
  have fj : f s j = f u j := by simp [s,h]
  have fk : f s k = f u j := by
    change f (u + c • v) k = _
    simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,c]
    field_simp
    ring
  exact hj ((fj.symm.trans (noCoincidence s j k hjk (fj.trans fk.symm))))

variable {I : Type} [Fintype I] [DecidableEq I]

theorem dimension_bound (L : Submodule ℂ (Mat I)) (h : level L) (hs : invariant L)
    (a b : I) (hab : a ≠ b) : Module.finrank ℂ L ≤ Fintype.card I - 1 := by
  classical
  letI : Nonempty I := ⟨a⟩
  obtain ⟨j,hj⟩ := coordinate (diff L a b) (unequal L h hs a b hab)
  let f : L →ₗ[ℂ] ({i : I // i ≠ a} → ℂ) :=
    { toFun := fun t i => t.val (a,j)-t.val (i.val,j)
      map_add' := fun t s => by funext i; simp only [Submodule.coe_add, Pi.add_apply]; ring
      map_smul' := fun c t => by funext i; simp only [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have ker (t : L) (ht : f t = 0) : t = 0 := by
    apply Subtype.ext
    apply no_flat L h t.val t.property a
    intro i k
    by_cases ia : i = a
    · rw [ia]
    let t' : L := ⟨turn b i t.val, hs t.val t.property b i⟩
    have ea : Equiv.swap b i a = a := Equiv.swap_apply_of_ne_of_ne hab (Ne.symm ia)
    have dd (l : I) : diff L a b t' l = t.val (a,l) - t.val (i,l) := by
      change t.val (Equiv.swap b i a,l) - t.val (Equiv.swap b i b,l) = _
      rw [ea, Equiv.swap_apply_left]
    have u := congrFun ht ⟨i,ia⟩
    have hz : diff L a b t' j = 0 := (dd j).trans u
    have all := congrFun (hj t' hz) k
    exact (sub_eq_zero.mp ((dd k).symm.trans all)).symm
  have hf : Function.Injective f := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply ker
    rw [map_sub,hxy,sub_self]
  have e := LinearMap.finrank_le_finrank_of_injective (f := f) hf
  simpa [Module.finrank_fin_fun] using e

end RowSymmetricLevel

namespace RowSymmetricLevel

theorem of_permpoly {n : ℕ} (L : Submodule ℂ (Mat (Fin n)))
    (h : ∀ t ∈ L, MvPolynomial.eval (fun p => 1+t p) (PEqualNP.Gct.permPoly ℂ n) =
      (Nat.factorial n : ℂ)) : level L := by
  classical
  intro t ht
  let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => 1+t (i,j)
  calc
    _ = M.transpose.permanent := by
      unfold Matrix.permanent
      apply Fintype.sum_equiv (Equiv.embeddingEquivOfFinite _)
      intro f; rfl
    _ = M.permanent := Matrix.permanent_transpose M
    _ = MvPolynomial.eval (fun p => 1+t p) (PEqualNP.Gct.permPoly ℂ n) := by
      simp [M,PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]
    _ = _ := by simpa using h t ht

theorem permPoly_bound {n : ℕ} (hn : 2 ≤ n) (L : Submodule ℂ (Mat (Fin n)))
    (h : ∀ t ∈ L, MvPolynomial.eval (fun p => 1+t p) (PEqualNP.Gct.permPoly ℂ n) =
      (Nat.factorial n : ℂ)) (hs : invariant L) : Module.finrank ℂ L ≤ n-1 := by
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  have ab : a ≠ b := by simp [a,b]
  simpa using dimension_bound L (of_permpoly L h) hs a b ab

end RowSymmetricLevel
namespace RowSymmetricLevel

theorem all_sizes {n : ℕ} (L : Submodule ℂ (Mat (Fin n)))
    (h : ∀ t ∈ L, MvPolynomial.eval (fun p => 1+t p) (PEqualNP.Gct.permPoly ℂ n) =
      (Nat.factorial n : ℂ)) (hs : invariant L) : Module.finrank ℂ L ≤ n-1 := by
  by_cases hn : 2 ≤ n
  · exact permPoly_bound hn L h hs
  have trivialL : L = ⊥ := by
    apply le_antisymm _ bot_le
    intro t ht
    change t = 0
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · funext p; exact Fin.elim0 p.1
    · exact no_flat L (of_permpoly L h) t ht (0 : Fin 1)
        (fun i j => congrArg (fun k => t (k,j)) (Subsingleton.elim _ _))
  rw [trivialL, finrank_bot]
  omega

end RowSymmetricLevel


namespace RowSymmetricLevel

open Polynomial
open scoped Polynomial

variable {I : Type} [Fintype I] [DecidableEq I]

def rowFactor (r j : I) : ℂ := if j = r then 1 - (Fintype.card I : ℂ) else 1

theorem sparse_from_model (w : I → ℂ)
    (hyp : ∀ z : ℂ, (∑ r : I, ∏ j : I, (1 + z * (w j * rowFactor r j))) =
      (Fintype.card I : ℂ))
    (j k : I) (hjk : j ≠ k) : w j = 0 ∨ w k = 0 := by
  classical
  by_contra! h
  let S := Finset.univ.filter fun j : I => w j ≠ 0
  have mems (i : I) : i ∈ S ↔ w i ≠ 0 := by simp [S]
  have hj : j ∈ S := (mems j).2 h.1
  have hk : k ∈ S := (mems k).2 h.2
  have hd : 1 < S.card := Finset.one_lt_card.mpr ⟨j,hj,k,hk,hjk⟩
  have hn : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨j⟩
  let f (r i : I) : ℂ[X] := 1 + C (w i * rowFactor r i) * X
  have reduced (z : ℂ) (r : I) :
      (∏ i ∈ S, (1+z*(w i*rowFactor r i))) = ∏ i : I, (1+z*(w i*rowFactor r i)) := by
    apply Finset.prod_subset (Finset.subset_univ S)
    intro i _ hi
    have hz : w i = 0 := by simpa [S] using hi
    simp [hz]
  have poly : (∑ r : I, ∏ i ∈ S, f r i) = C (Fintype.card I : ℂ) := by
    apply Polynomial.funext
    intro z
    simp only [Polynomial.eval_finsetSum,Polynomial.eval_prod,f,eval_add,eval_mul,eval_one,eval_C,eval_X,mul_comm _ z,reduced]
    exact hyp z
  have top (r : I) : (∏ i ∈ S, f r i).coeff S.card = ∏ i ∈ S, (w i * rowFactor r i) := by
    have hdeg (i : I) : (f r i).natDegree ≤ 1 := by
      apply natDegree_add_le_of_degree_le
      · simp
      · exact (natDegree_mul_le ..).trans (by simp only [natDegree_C,natDegree_X,zero_add,le_refl])
    simpa only [f,Nat.mul_one,coeff_add,coeff_one,coeff_C_mul_X,if_pos rfl,ite_true,if_neg (by decide : (1:ℕ) ≠ 0),zero_add] using coeff_prod_of_natDegree_le S (f r) 1 (fun i _ => hdeg i)
  have zero : (∑ r : I, ∏ i ∈ S, (w i * rowFactor r i)) = 0 := by
    have := congrArg (fun p : ℂ[X] => p.coeff S.card) poly
    simpa [Polynomial.finsetSum_coeff,top,coeff_C,show S.card ≠ 0 by omega] using this
  let T := ∏ i ∈ S, w i
  have hT : T ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => (mems i).1 hi)
  have val (r : I) : (∏ i ∈ S, rowFactor r i) =
      1 - (if r ∈ S then (Fintype.card I : ℂ) else 0) := by
    by_cases hr : r ∈ S <;> simp [rowFactor,hr]
  simp_rw [Finset.prod_mul_distrib, val] at zero
  change (∑ r, T * _) = 0 at zero
  rw [←Finset.mul_sum] at zero
  have second := (mul_eq_zero.mp zero).resolve_left hT
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const_zero] at second
  have hh : (Fintype.card I : ℂ) - (S.card : ℂ) * Fintype.card I = 0 := by simpa using second
  have one : (1 - (S.card : ℂ)) * (Fintype.card I : ℂ) = 0 := by linear_combination hh
  have natnz : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have eq := sub_eq_zero.mp ((mul_eq_zero.mp one).resolve_right natnz)
  exact (show (1 : ℕ) ≠ S.card by omega) (by exact_mod_cast eq)

end RowSymmetricLevel
namespace RowSymmetricLevel

variable {I : Type} [Fintype I] [DecidableEq I]

theorem sparse_difference (L : Submodule ℂ (Mat I)) (hl : level L) (hs : invariant L)
    (a b : I) (hab : a ≠ b) (t : Mat I) (ht : t ∈ L) (j k : I) (hjk : j ≠ k) :
    t (a,j)-t (b,j) = 0 ∨ t (a,k)-t (b,k) = 0 := by
  classical
  let w (i : I) := t (a,i)-t (b,i)
  let d : Mat I := t-turn a b t
  have hd : d ∈ L := L.sub_mem ht (hs _ ht a b)
  have da (i : I) : d (a,i) = w i := by
    change t (a,i) - t (Equiv.swap a b a,i) = _
    rw [Equiv.swap_apply_left]
  have db (i : I) : d (b,i) = -w i := by
    change t (b,i) - t (Equiv.swap a b b,i) = -(t (a,i)-t (b,i))
    rw [Equiv.swap_apply_right]; ring
  have dn (r i : I) (ra : r ≠ a) (rb : r ≠ b) : d (r,i) = 0 := by
    change t (r,i)-t (Equiv.swap a b r,i) = 0
    simp [Equiv.swap_apply_of_ne_of_ne ra rb]
  let D : Mat I := ∑ q ∈ Finset.univ.erase a, turn b q d
  have hD : D ∈ L := L.sum_mem (fun q _ => hs d hd b q)
  have special (i : I) : D (a,i) = ((Fintype.card I : ℂ)-1)*w i := by
    change (∑ q ∈ Finset.univ.erase a, turn b q d) (a,i) = _
    rw [Finset.sum_apply]
    have fix (q : I) (hq : q ∈ Finset.univ.erase a) : turn b q d (a,i) = w i := by
      have ne : a ≠ q := Ne.symm (Finset.mem_erase.mp hq).1
      change d (Equiv.swap b q a,i) = w i
      rw [Equiv.swap_apply_of_ne_of_ne hab ne,da]
    rw [Finset.sum_congr rfl fix]
    have pos : 1 ≤ Fintype.card I := Fintype.card_pos_iff.mpr ⟨a⟩
    simp [Finset.card_erase_of_mem, Nat.cast_sub pos]
  have regular (r i : I) (ra : r ≠ a) : D (r,i) = -w i := by
    change (∑ q ∈ Finset.univ.erase a, turn b q d) (r,i) = _
    rw [Finset.sum_apply,Finset.sum_eq_single r]
    · exact (congrArg (fun x => d (x,i)) (Equiv.swap_apply_right b r)).trans (db i)
    · intro q hq hqr
      have qne : q ≠ a := (Finset.mem_erase.mp hq).1
      have g : Equiv.swap b q a = a := Equiv.swap_apply_of_ne_of_ne hab qne.symm
      have n1 : Equiv.swap b q r ≠ a := by
        intro e; exact ra ((Equiv.swap b q).injective (e.trans g.symm))
      have n2 : Equiv.swap b q r ≠ b := by
        intro e; exact hqr.symm ((Equiv.swap b q).injective (e.trans (Equiv.swap_apply_right b q).symm))
      exact dn _ i n1 n2
    · simp [ra]
  let U (r : I) : Mat I := fun p => w p.2 * rowFactor r p.1
  have allU (r : I) : U r ∈ L := by
    have eq : U r = -(turn a r D) := by
      funext p
      obtain ⟨i,l⟩ := p
      change w l * rowFactor r i = -D (Equiv.swap a r i,l)
      by_cases hir : i = r
      · subst i; rw [Equiv.swap_apply_right,special]; simp [rowFactor]; ring
      · have sn : Equiv.swap a r i ≠ a := by
          intro e; exact hir ((Equiv.swap a r).injective (e.trans (Equiv.swap_apply_right a r).symm))
        simp [rowFactor,hir,regular _ _ sn]
    rw [eq]
    exact L.neg_mem (hs _ hD a r)
  apply sparse_from_model w _ j k hjk
  intro z
  let M (r : I) := ∏ i : I, (1+z*(w i*rowFactor r i))
  let term (f : I ↪ I) (r : I) := ∏ i : I, (1+z*(w (f i)*rowFactor r i))
  have lev (r : I) : (∑ f : I ↪ I, term f r) = (Nat.factorial (Fintype.card I) : ℂ) :=
    hl (z • U r) (L.smul_mem _ (allU r))
  have eq (f : I ↪ I) (r : I) : term f r = M (f r) := by
    apply Fintype.prod_equiv f.equivOfFiniteSelfEmbedding
    intro i
    change 1 + z*(w (f i)*rowFactor r i) = 1+z*(w (f i)*rowFactor (f r) (f i))
    simp [rowFactor]
  have sumRows (f : I ↪ I) : (∑ r, term f r) = ∑ j, M j :=
    calc
      _ = ∑ r, M (f r) := Finset.sum_congr rfl (fun r _ => eq f r)
      _ = _ := f.equivOfFiniteSelfEmbedding.sum_comp M
  have comb : (∑ r : I, ∑ f : I ↪ I, term f r) =
      (Fintype.card I : ℂ) * (Fintype.card I).factorial := by simp [lev]
  rw [Finset.sum_comm] at comb
  simp_rw [sumRows] at comb
  have co : Fintype.card (I ↪ I) = (Fintype.card I).factorial := by
    rw [Fintype.card_congr (Equiv.embeddingEquivOfFinite I),Fintype.card_perm]
  simp only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul,co] at comb
  rw [mul_comm (Fintype.card I : ℂ)] at comb
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) comb

end RowSymmetricLevel


namespace RowSymmetricLevel

variable {I : Type} [Fintype I] [DecidableEq I]

def columnSpace (j : I) : Submodule ℂ (Mat I) where
  carrier := {t | (∀ i k, k ≠ j → t (i,k) = 0) ∧ ∑ i, t (i,j) = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hf, sf⟩ ⟨hg, sg⟩
    exact ⟨fun i k h => by simp [hf i k h, hg i k h],
      by simp only [Pi.add_apply, Finset.sum_add_distrib, sf, sg, add_zero]⟩
  smul_mem' := by
    rintro c f ⟨hf,sf⟩
    exact ⟨fun i k h => by simp [hf i k h],
      by simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, sf, mul_zero]⟩

theorem columnSpace_invariant (j : I) : invariant (columnSpace j) := by
  rintro t ⟨off,total⟩ a b
  exact ⟨fun i k h => off _ _ h, (Equiv.sum_comp (Equiv.swap a b) (fun i => t (i,j))).trans total⟩

theorem columnSpace_level (j : I) : level (columnSpace j) := by
  classical
  let : Nonempty I := ⟨j⟩
  rintro t ⟨off,total⟩
  have prod (e : Equiv.Perm I) :
      (∏ i, (1 + t (i,e i))) = 1 + t (e.symm j,j) := by
    rw [Finset.prod_eq_single (e.symm j)]
    · simp
    · intro i hi hn
      have h : e i ≠ j := fun eq => hn (e.injective (by simpa using eq))
      simp [off i _ h]
    · simp
  let S (i : I) := ∑ e : Equiv.Perm I, t (e.symm i,j)
  have same (i : I) : S j = S i := by
    apply Fintype.sum_equiv (Equiv.mulLeft (Equiv.swap j i))
    intro e
    change t (e.symm j,j) = t (e.symm ((Equiv.swap j i).symm i),j)
    simp
  have all : ∑ i, S i = 0 := by
    unfold S
    rw [Finset.sum_comm]
    have h (e : Equiv.Perm I) : ∑ i, t (e.symm i,j) = 0 :=
      (e.symm.sum_comp (fun i => t (i,j))).trans total
    simp [h]
  have Sj : S j = 0 := by
    simp only [← same, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at all
    exact (mul_eq_zero.mp all).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  calc
    _ = ∑ e : Equiv.Perm I, ∏ i, (1 + t (i,e i)) := by
      apply Fintype.sum_equiv (Equiv.embeddingEquivOfFinite _)
      intro f; rfl
    _ = _ := by simp only [prod, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, ← show S j = ∑ e : Equiv.Perm I, t (e.symm j,j) from rfl,
        Sj, add_zero, Fintype.card_perm]

theorem columnSpace_finrank (j : I) :
    Module.finrank ℂ (columnSpace j) = Fintype.card I - 1 := by
  classical
  let K := {i : I // i ≠ j}
  let f : columnSpace j →ₗ[ℂ] (K → ℂ) := {
    toFun := fun t i => t.val (i.val,j)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have inj : Function.Injective f := by
    intro t u htu
    have eq (i : K) : t.val (i.val,j) = u.val (i.val,j) := congrFun htu i
    have tj := t.property.2
    have uj := u.property.2
    rw [Fintype.sum_eq_add_sum_subtype_ne _ j] at tj uj
    have eqj : t.val (j,j) = u.val (j,j) := by
      simp only [eq] at tj
      exact add_right_cancel (tj.trans uj.symm)
    apply Subtype.ext
    funext ⟨i,k⟩
    by_cases hk : k = j
    · subst k
      by_cases hi : i = j
      · simpa [hi] using eqj
      · exact eq ⟨i,hi⟩
    · exact (t.property.1 i k hk).trans (u.property.1 i k hk).symm
  have sur : Function.Surjective f := by
    intro v
    let c (i : I) := if h : i ≠ j then v ⟨i,h⟩ else -(∑ k : K, v k)
    let t : Mat I := fun p => if p.2 = j then c p.1 else 0
    have ht : t ∈ columnSpace j := by
      refine ⟨fun i k h => by simp [t,h],?_⟩
      simp only [t, ite_eq_left rfl]
      rw [Fintype.sum_eq_add_sum_subtype_ne _ j]
      have hc (i : K) : c i.val = v i := by simp [c,i.property]
      have hj : c j = -(∑ k : K, v k) := by simp [c]
      simp only [hc,hj]
      exact neg_add_cancel (∑ k : K, v k)
    exact ⟨⟨t,ht⟩,funext fun i => by change t (i.val,j) = _; simp [t,c,i.property]⟩
  have eq := (LinearEquiv.ofBijective f ⟨inj,sur⟩).finrank_eq
  simpa [K, Module.finrank_fin_fun] using eq

end RowSymmetricLevel


namespace RowSymmetricLevel

variable {I : Type} [Fintype I] [DecidableEq I]

private def unitAt (i j : I) : Mat I := fun z => if z.1 = i then if z.2 = j then 1 else 0 else 0

private theorem elementary_mem (L : Submodule ℂ (Mat I)) (hs : invariant L)
    (t : Mat I) (ht : t ∈ L) (a b j : I) (hab : a ≠ b)
    (hn : t (a,j) - t (b,j) ≠ 0)
    (other : ∀ k, k ≠ j → t (a,k) - t (b,k) = 0) :
    ∀ i, unitAt a j - unitAt i j ∈ L := by
  let w := t (a,j) - t (b,j)
  have gen : t - turn a b t = w • (unitAt a j - unitAt b j) := by
    funext z
    obtain ⟨r,k⟩ := z
    by_cases h : k = j
    · subst k
      by_cases ha : r = a
      · subst r; simp [turn, unitAt, hab, w]
      · by_cases hb : r = b
        · subst r; simp [turn, unitAt, ha, w]
        · simp [turn, unitAt, ha, hb, Equiv.swap_apply_of_ne_of_ne ha hb]
    · have eq := sub_eq_zero.mp (other k h)
      by_cases ha : r = a
      · subst r; simp [turn, unitAt, h, eq]
      · by_cases hb : r = b
        · subst r; simp [turn, unitAt, h, eq]
        · simp [turn, unitAt, h, Equiv.swap_apply_of_ne_of_ne ha hb]
  have base : unitAt a j - unitAt b j ∈ L := by
    have mem := L.sub_mem ht (hs t ht a b)
    rw [gen] at mem
    have mem' := L.smul_mem w⁻¹ mem
    simpa [smul_smul, show w ≠ 0 from hn] using mem'
  intro i
  by_cases ha : i = a
  · subst i; simp
  have eq : turn b i (unitAt a j - unitAt b j) = unitAt a j - unitAt i j := by
    have fix_a : Equiv.swap b i a = a := Equiv.swap_apply_of_ne_of_ne hab (Ne.symm ha)
    funext z
    obtain ⟨r,k⟩ := z
    have iff_a : Equiv.swap b i r = a ↔ r = a := by
      conv_lhs => rhs; rw [←fix_a]
      exact (Equiv.swap b i).injective.eq_iff
    have iff_i : Equiv.swap b i r = b ↔ r = i := by
      conv_lhs => rhs; rw [← Equiv.swap_apply_right b i]
      exact (Equiv.swap b i).injective.eq_iff
    simp [turn,unitAt,iff_a,iff_i]
  rw [←eq]
  exact hs _ base b i

private theorem contains_column (L : Submodule ℂ (Mat I)) (a j : I)
    (basis_mem : ∀ i, unitAt a j - unitAt i j ∈ L) : columnSpace j ≤ L := by
  intro x hx
  obtain ⟨supp, hz⟩ := hx
  have decomp : (∑ i, (-x (i,j)) • (unitAt a j - unitAt i j)) = x := by
    funext z
    obtain ⟨r,k⟩ := z
    rw [Finset.sum_apply]
    by_cases hk : k = j
    · subst k
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, Finset.sum_neg_distrib, hz]
      simp [unitAt]
    · simp [unitAt,hk,supp r k hk]
  rw [←decomp]
  exact L.sum_mem fun i _ => L.smul_mem _ (basis_mem i)

theorem classify_of_sparse (L : Submodule ℂ (Mat I)) (hl : level L) (hs : invariant L)
    (sparse : ∀ (a b : I), a ≠ b → ∀ t ∈ L, ∀ (j k : I), j ≠ k →
       t (a,j) - t (b,j) = 0 ∨ t (a,k) - t (b,k) = 0) :
    L = ⊥ ∨ ∃ j, L = columnSpace j := by
  classical
  by_cases hb : L = ⊥
  · exact Or.inl hb
  right
  obtain ⟨t,ht,hne⟩ : ∃ t ∈ L, t ≠ 0 := by
    by_contra! h
    exact hb (le_antisymm (fun x hx => h x hx) bot_le)
  obtain ⟨z,hz⟩ : ∃ z, t z ≠ 0 := by
    by_contra! hz
    exact hne (funext hz)
  let a := z.1
  obtain ⟨b,j,hj⟩ : ∃ b j, t (a,j) ≠ t (b,j) := by
    by_contra! eq
    exact hne (no_flat L hl t ht a (fun b j => (eq b j).symm))
  have hab : a ≠ b := by rintro rfl; contradiction
  have hn := sub_ne_zero.mpr hj
  have other (k : I) (hk : k ≠ j) := (sparse a b hab t ht j k hk.symm).resolve_left hn
  have incl := contains_column L a j (elementary_mem L hs t ht a b j hab hn other)
  refine ⟨j,(Submodule.eq_of_le_of_finrank_le incl ?_).symm⟩
  rw [columnSpace_finrank]
  exact dimension_bound L hl hs a b hab

end RowSymmetricLevel

namespace RowSymmetricLevel

theorem classify {I : Type} [Fintype I] [DecidableEq I] (L : Submodule ℂ (Mat I))
    (hl : level L) (hs : invariant L) : L = ⊥ ∨ ∃ j, L = columnSpace j :=
  classify_of_sparse L hl hs (sparse_difference L hl hs)

theorem classify_permanent {n : ℕ} (L : Submodule ℂ (Mat (Fin n)))
    (hl : ∀ t ∈ L, MvPolynomial.eval (fun p => 1+t p) (PEqualNP.Gct.permPoly ℂ n) =
      (Nat.factorial n : ℂ)) (hs : invariant L) : L = ⊥ ∨ ∃ j, L = columnSpace j :=
  classify L (of_permpoly L hl) hs

end RowSymmetricLevel

namespace RowSymmetricLevel

variable {I : Type} [Fintype I] [DecidableEq I]

def rowPerm (g : Equiv.Perm I) (T : Mat I) : Mat I :=
  fun z => T (g z.1, z.2)

def invariantUnder (G : Subgroup (Equiv.Perm I)) (L : Submodule ℂ (Mat I)) : Prop :=
  ∀ g ∈ G, ∀ T ∈ L, rowPerm g T ∈ L

def twoTransitive (G : Subgroup (Equiv.Perm I)) : Prop :=
  ∀ a b u v : I, a ≠ b → u ≠ v → ∃ g ∈ G, g a = u ∧ g b = v

theorem invariant_of_twoTransitive (G : Subgroup (Equiv.Perm I)) (L : Submodule ℂ (Mat I))
    (hG : twoTransitive G) (hi : invariantUnder G L) : invariant L := by
  classical
  intro T hT a b
  by_cases ab : a = b
  · subst b
    have eq : turn a a T = T := by
      funext z
      simp [turn]
    rw [eq]; exact hT
  obtain ⟨g,hg,ga,gb⟩ := hG a b b a ab (Ne.symm ab)
  let S := T - rowPerm g T
  have hS : S ∈ L := L.sub_mem hT (hi g hg T hT)
  have sumS (j : I) : ∑ x : I, S (x,j) = 0 := by
    change ∑ x : I,(T (x,j) - T (g x,j)) = 0
    rw [Finset.sum_sub_distrib, Equiv.sum_comp g (fun x => T (x,j)), sub_self]
  let H := G ⊓ MulAction.stabilizer (Equiv.Perm I) a
  let D : Mat I := ∑ k : H, rowPerm k.val S
  have hD : D ∈ L := L.sum_mem (fun k _ => hi k.val k.property.1 S hS)
  have Dval (x j : I) : D (x,j) = ∑ k : H, S (k.val x,j) := by
    simp [D,Finset.sum_apply,rowPerm]
  have Dfix (j : I) : D (a,j) = (Fintype.card H : ℂ) * (T (a,j)-T (b,j)) := by
    rw [Dval]
    have fix (k : H) : k.val a = a := k.property.2
    simp [fix,S,rowPerm,ga,mul_sub]
  have Dother (x j : I) (hx : x ≠ a) : D (x,j) = D (b,j) := by
    obtain ⟨m,hm,ma,mb⟩ := hG a b a x ab (Ne.symm hx)
    let k : H := ⟨m,hm,ma⟩
    have be : k.val b = x := mb
    rw [Dval,Dval,←be]
    exact Equiv.sum_comp (Equiv.mulRight k) (fun k' : H => S (k'.val b,j))
  have sumD (j : I) : ∑ x : I, D (x,j) = 0 := by
    simp only [Dval]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k hk
    exact (Equiv.sum_comp k.val (fun x => S (x,j))).trans (sumS j)
  let n : ℂ := Fintype.card I
  let m : ℂ := Fintype.card H
  have npos : n ≠ 0 := by
    let : Nonempty I := ⟨a⟩
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have mpos : m ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have balance (j : I) : (n-1)*D (b,j) + D (a,j) = 0 := by
    have hsum := Finset.sum_erase_add (Finset.univ : Finset I) (fun x => D (x,j)) (Finset.mem_univ a)
    have hconst : ∑ x ∈ Finset.univ.erase a, D (x,j) =
        ∑ _x ∈ (Finset.univ : Finset I).erase a, D (b,j) := by
      exact Finset.sum_congr rfl (fun x hx => Dother x j (Finset.ne_of_mem_erase hx))
    rw [hconst,Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ,nsmul_eq_mul,Nat.cast_sub (by let : Nonempty I := ⟨a⟩; exact Fintype.card_pos)] at hsum
    simpa only [n,Nat.cast_one,sumD] using hsum
  have scale (j : I) : (n-1)/(n*m) * (D (a,j)-D (b,j)) = T (a,j)-T (b,j) := by
    have h1 := balance j
    have h2 : D (a,j) = m * (T (a,j)-T (b,j)) := Dfix j
    field_simp [npos,mpos]
    linear_combination n*h2 - h1
  have hb : rowPerm g D ∈ L := hi g hg D hD
  have hmem := L.sub_mem hT (L.smul_mem ((n-1)/(n*m)) (L.sub_mem hD hb))
  convert hmem using 1
  ext ⟨r,j⟩
  change T (Equiv.swap a b r,j) = T (r,j) - (n-1)/(n*m) * (D (r,j) - D (g r,j))
  by_cases ra : r = a
  · subst r
    rw [Equiv.swap_apply_left,ga,scale]
    ring
  by_cases rb : r = b
  · subst r
    rw [Equiv.swap_apply_right,gb,←neg_sub (D (a,j)) (D (b,j)),mul_neg,scale]
    ring
  have gr : g r ≠ a := fun e => rb (g.injective (e.trans gb.symm))
  rw [Equiv.swap_apply_of_ne_of_ne ra rb,Dother r j ra,Dother (g r) j gr]
  ring

theorem twoTransitive_bound {n : ℕ} (L : Submodule ℂ (Mat (Fin n)))
    (h : ∀ t ∈ L, MvPolynomial.eval (fun p => 1+t p) (PEqualNP.Gct.permPoly ℂ n) =
      (Nat.factorial n : ℂ)) (G : Subgroup (Equiv.Perm (Fin n))) (hG : twoTransitive G)
    (hi : invariantUnder G L) : Module.finrank ℂ L ≤ n-1 :=
  all_sizes L h (invariant_of_twoTransitive G L hG hi)

end RowSymmetricLevel


namespace RowSymmetricLevel

theorem sharp_on_permanent {n : ℕ} (j : Fin n) :
    invariant (columnSpace j) ∧ Module.finrank ℂ (columnSpace j) = n-1 ∧
    ∀ t ∈ columnSpace j, MvPolynomial.eval (fun p => 1+t p) (PEqualNP.Gct.permPoly ℂ n) =
      (Nat.factorial n : ℂ) := by
  refine ⟨columnSpace_invariant j, by simpa using columnSpace_finrank j, ?_⟩
  intro t ht
  let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => 1+t (i,k)
  calc
    _ = M.permanent := by
      simp [M,PEqualNP.Gct.permPoly,Matrix.permanent,Matrix.mvPolynomialX_apply]
    _ = M.transpose.permanent := (Matrix.permanent_transpose M).symm
    _ = ∑ f : Fin n ↪ Fin n, ∏ i, (1+t (i,f i)) := by
      symm
      unfold Matrix.permanent
      apply Fintype.sum_equiv (Equiv.embeddingEquivOfFinite _)
      intro f; rfl
    _ = _ := by simpa using columnSpace_level j t ht

end RowSymmetricLevel

namespace RowSymmetricLevel

theorem classify_twoTransitive {I : Type} [Fintype I] [DecidableEq I]
    (L : Submodule ℂ (Mat I)) (hl : level L)
    (G : Subgroup (Equiv.Perm I)) (hG : twoTransitive G) (hi : invariantUnder G L) :
    L = ⊥ ∨ ∃ j, L = columnSpace j :=
  classify L hl (invariant_of_twoTransitive G L hG hi)

theorem classify_twoTransitive_permanent {n : ℕ} (L : Submodule ℂ (Mat (Fin n)))
    (hl : ∀ t ∈ L, MvPolynomial.eval (fun p => 1+t p) (PEqualNP.Gct.permPoly ℂ n) =
      (Nat.factorial n : ℂ)) (G : Subgroup (Equiv.Perm (Fin n))) (hG : twoTransitive G)
    (hi : invariantUnder G L) : L = ⊥ ∨ ∃ j, L = columnSpace j :=
  classify_twoTransitive L (of_permpoly L hl) G hG hi

end RowSymmetricLevel

namespace RowSymmetricLevel

theorem columnSpace_invariantUnder {I : Type} [Fintype I] [DecidableEq I]
    (G : Subgroup (Equiv.Perm I)) (j : I) : invariantUnder G (columnSpace j) := by
  rintro g _ T ⟨hoff,hsum⟩
  exact ⟨fun i k h => hoff (g i) k h, (Equiv.sum_comp g (fun i => T (i,j))).trans hsum⟩

theorem twoTransitive_level_iff {I : Type} [Fintype I] [DecidableEq I]
    (L : Submodule ℂ (Mat I)) (G : Subgroup (Equiv.Perm I)) (hG : twoTransitive G) :
    level L ∧ invariantUnder G L ↔ L = ⊥ ∨ ∃ j, L = columnSpace j := by
  constructor
  · rintro ⟨hl,hi⟩
    exact classify_twoTransitive L hl G hG hi
  · rintro (rfl | ⟨j,rfl⟩)
    · constructor
      · intro t ht
        have e : t = 0 := by simpa using ht
        subst t
        have hc := Fintype.card_congr (Equiv.embeddingEquivOfFinite I)
        simp only [Fintype.card_perm] at hc
        simpa using congrArg (fun n : ℕ => (n : ℂ)) hc
      · intro g hg t ht
        have e : t = 0 := by simpa using ht
        subst t
        exact Submodule.zero_mem _
    · exact ⟨columnSpace_level j,columnSpace_invariantUnder G j⟩

end RowSymmetricLevel
