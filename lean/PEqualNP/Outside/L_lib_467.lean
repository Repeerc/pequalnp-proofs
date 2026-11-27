import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_467

theorem double_count (n m : ℕ) (A : Fin m → Finset (Fin (3 * n))) (S : Finset (Fin m)) :
    (∑ x : Fin (3 * n), (S.filter (fun i => x ∈ A i)).card) = ∑ i ∈ S, (A i).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← Finset.card_filter]
  congr 1
  ext x
  simp

theorem card_eq_three (n m : ℕ) (A : Fin m → Finset (Fin (3 * n)))
    (h3 : ∀ i, (A i).card = 3) (S : Finset (Fin m)) :
    (∑ i ∈ S, (A i).card) = 3 * S.card := by
  rw [Finset.sum_congr rfl (fun i _ => h3 i), Finset.sum_const, nsmul_eq_mul]
  simp [mul_comm]

theorem main (n m : ℕ) (A : Fin m → Finset (Fin (3 * n))) (h3 : ∀ i, (A i).card = 3) :
    ((∃ S : Finset (Fin m), S.card ≤ n ∧ ∀ x, ∃ i ∈ S, x ∈ A i) ↔
     ∃ S : Finset (Fin m), ∀ x : Fin (3 * n), ∃! i : Fin m, i ∈ S ∧ x ∈ A i) := by
  classical
  constructor
  · rintro ⟨S, hle, hcov⟩
    have hdc := double_count n m A S
    have hct := card_eq_three n m A h3 S
    have hge : ∀ x : Fin (3 * n), 1 ≤ (S.filter (fun i => x ∈ A i)).card := by
      intro x
      obtain ⟨i, hiS, hix⟩ := hcov x
      exact Finset.card_pos.mpr ⟨i, by simp [hiS, hix]⟩
    have hsum1 : (3 * n) ≤ ∑ x : Fin (3 * n), (S.filter (fun i => x ∈ A i)).card := by
      have h1 : (∑ _x : Fin (3 * n), (1:ℕ)) ≤
          ∑ x : Fin (3 * n), (S.filter (fun i => x ∈ A i)).card :=
        Finset.sum_le_sum (fun x _ => hge x)
      simpa using h1
    rw [hdc, hct] at hsum1
    have hcard : S.card = n := by omega
    refine ⟨S, ?_⟩
    intro x
    obtain ⟨i, hiS, hix⟩ := hcov x
    refine ⟨i, ⟨hiS, hix⟩, ?_⟩
    intro j hj
    by_contra hji
    have hcx : 2 ≤ (S.filter (fun k => x ∈ A k)).card := by
      refine Finset.one_lt_card.mpr ⟨i, ?_, j, ?_, fun h => hji h.symm⟩
      · simp [hiS, hix]
      · simp [hj.1, hj.2]
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin (3 * n)))
      (fun y => (S.filter (fun k => y ∈ A k)).card) (Finset.mem_univ x)
    have hrest : (3 * n - 1) ≤ ∑ y ∈ (Finset.univ : Finset (Fin (3 * n))).erase x,
        (S.filter (fun k => y ∈ A k)).card := by
      have h1 : (∑ _y ∈ (Finset.univ : Finset (Fin (3 * n))).erase x, (1:ℕ)) ≤
          ∑ y ∈ (Finset.univ : Finset (Fin (3 * n))).erase x,
            (S.filter (fun k => y ∈ A k)).card :=
        Finset.sum_le_sum (fun y _ => hge y)
      simpa [Finset.card_erase_of_mem (Finset.mem_univ x)] using h1
    have : 3 * n + 1 ≤ ∑ y : Fin (3 * n), (S.filter (fun k => y ∈ A k)).card := by
      rw [← hsplit]
      omega
    omega
  · rintro ⟨S, huniq⟩
    have hcov : ∀ x, ∃ i ∈ S, x ∈ A i := by
      intro x
      obtain ⟨i, hi, _⟩ := huniq x
      exact ⟨i, hi.1, hi.2⟩
    have hge : ∀ x : Fin (3 * n), 1 ≤ (S.filter (fun i => x ∈ A i)).card := by
      intro x
      obtain ⟨i, hiS, hix⟩ := hcov x
      exact Finset.card_pos.mpr ⟨i, by simp [hiS, hix]⟩
    have hle1 : ∀ x : Fin (3 * n), (S.filter (fun i => x ∈ A i)).card ≤ 1 := by
      intro x
      obtain ⟨i, hi, huniq'⟩ := huniq x
      have hsub : S.filter (fun k => x ∈ A k) ⊆ {i} := by
        intro k hk
        simp only [Finset.mem_filter] at hk
        simp [huniq' k hk]
      have := Finset.card_le_card hsub
      simpa using this
    have hsum_eq : (∑ x : Fin (3 * n), (S.filter (fun i => x ∈ A i)).card) = 3 * n := by
      have h1 : ∀ x : Fin (3 * n), (S.filter (fun i => x ∈ A i)).card = 1 := by
        intro x
        have a := hge x
        have b := hle1 x
        omega
      rw [Finset.sum_congr rfl (fun x _ => h1 x)]
      simp
    have hdc := double_count n m A S
    have hct := card_eq_three n m A h3 S
    rw [hdc, hct] at hsum_eq
    refine ⟨S, ?_, hcov⟩
    omega


end PEqualNP.Outside.L_lib_467

theorem PEqualNP.Outside.L_lib_467 : (∀ (n m : ℕ) (A : Fin m → Finset (Fin (3 * n))), (∀ i, (A i).card = 3) →
  ((∃ S : Finset (Fin m), S.card ≤ n ∧ ∀ x, ∃ i ∈ S, x ∈ A i) ↔
   ∃ S : Finset (Fin m), ∀ x : Fin (3 * n), ∃! i : Fin m, i ∈ S ∧ x ∈ A i)) :=
  PEqualNP.Outside.L_lib_467.main
