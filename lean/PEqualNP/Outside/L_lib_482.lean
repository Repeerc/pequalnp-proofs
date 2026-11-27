import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_482

theorem main (n m : ℕ) (L : Fin m → Fin 3 → Fin n × Bool) :
  let ev := fun (x : Fin n → Bool) (i : Fin m) (k : Fin 3) => x (L i k).1 == (L i k).2
  let nae := fun (a b c : Bool) => ¬ (a = b ∧ b = c)
  (∃ x : Fin n → Bool, ∀ i, ∃ k, ev x i k = true) ↔
    ∃ (x : Fin n → Bool) (s : Fin m → Bool) (z : Bool), ∀ i,
      nae (ev x i 0) (ev x i 1) (s i) ∧ nae (!(s i)) (ev x i 2) z := by
  dsimp only
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, fun i => if (x (L i 0).1 == (L i 0).2) = (x (L i 1).1 == (L i 1).2)
        then !(x (L i 0).1 == (L i 0).2) else false, false, ?_⟩
    intro i
    have h := hx i
    obtain ⟨k, hk⟩ := h
    have hk' : (x (L i 0).1 == (L i 0).2) = true ∨ (x (L i 1).1 == (L i 1).2) = true ∨
        (x (L i 2).1 == (L i 2).2) = true := by
      fin_cases k <;> simp_all
    generalize ha : (x (L i 0).1 == (L i 0).2) = a at hk' ⊢
    generalize hb : (x (L i 1).1 == (L i 1).2) = b at hk' ⊢
    generalize hc : (x (L i 2).1 == (L i 2).2) = c at hk' ⊢
    cases a <;> cases b <;> cases c <;> simp_all
  · rintro ⟨x, s, z, h⟩
    by_cases hz : z = false
    · refine ⟨x, ?_⟩
      intro i
      have h1 := (h i).1
      have h2 := (h i).2
      generalize ha : (x (L i 0).1 == (L i 0).2) = a at h1 h2 ⊢
      generalize hb : (x (L i 1).1 == (L i 1).2) = b at h1 h2 ⊢
      generalize hc : (x (L i 2).1 == (L i 2).2) = c at h1 h2 ⊢
      subst hz
      have hkey : a = true ∨ b = true ∨ c = true := by
        cases a <;> cases b <;> cases c <;> simp_all
      rcases hkey with h0 | h0 | h0
      · exact ⟨0, by rw [ha, h0]⟩
      · exact ⟨1, by rw [hb, h0]⟩
      · exact ⟨2, by rw [hc, h0]⟩
    · have hzt : z = true := by cases z <;> simp_all
      refine ⟨fun j => !(x j), ?_⟩
      intro i
      have h1 := (h i).1
      have h2 := (h i).2
      generalize ha : (x (L i 0).1 == (L i 0).2) = a at h1 h2 ⊢
      generalize hb : (x (L i 1).1 == (L i 1).2) = b at h1 h2 ⊢
      generalize hc : (x (L i 2).1 == (L i 2).2) = c at h1 h2 ⊢
      subst hzt
      have hkey : a = false ∨ b = false ∨ c = false := by
        cases a <;> cases b <;> cases c <;> simp_all
      rcases hkey with h0 | h0 | h0
      · refine ⟨0, ?_⟩
        cases hx0 : x (L i 0).1 <;> cases hb0 : (L i 0).2 <;> simp_all
      · refine ⟨1, ?_⟩
        cases hx1 : x (L i 1).1 <;> cases hb1 : (L i 1).2 <;> simp_all
      · refine ⟨2, ?_⟩
        cases hx2 : x (L i 2).1 <;> cases hb2 : (L i 2).2 <;> simp_all

end PEqualNP.Outside.L_lib_482

theorem PEqualNP.Outside.L_lib_482 : (∀ (n m : ℕ) (L : Fin m → Fin 3 → Fin n × Bool),
  let ev := fun (x : Fin n → Bool) (i : Fin m) (k : Fin 3) => x (L i k).1 == (L i k).2
  let nae := fun (a b c : Bool) => ¬ (a = b ∧ b = c)
  (∃ x : Fin n → Bool, ∀ i, ∃ k, ev x i k = true) ↔
    ∃ (x : Fin n → Bool) (s : Fin m → Bool) (z : Bool), ∀ i,
      nae (ev x i 0) (ev x i 1) (s i) ∧ nae (!(s i)) (ev x i 2) z) :=
  PEqualNP.Outside.L_lib_482.main
