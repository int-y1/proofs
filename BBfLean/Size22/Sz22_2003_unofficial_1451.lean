import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1451: [7/15, 27/77, 22/3, 5/11, 363/2]

Vector representation:
```
 0 -1 -1  1  0
 0  3  0 -1 -1
 1 -1  0  0  1
 0  0  1  0 -1
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1451

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; finish
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih a (c + 1) e); ring_nf; finish

theorem r3_chain : ∀ k, ∀ a e, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (a + 1) (e + 1)); ring_nf; finish

theorem r3r2_drain : ∀ k, ∀ a b, ⟨a, b + 1, 0, k, 0⟩ [fm]⊢* ⟨a + k, b + 1 + 2 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · ring_nf; finish
  · step fm; step fm; rw [show b + 2 + 1 = (b + 2) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (b + 2)); ring_nf; finish

theorem block_step : ∀ C, ∀ A D, ⟨A + 1, 1, C + 7, D, 2⟩ [fm]⊢* ⟨A, 1, C, D + 5, 2⟩ := by
  intro C A D
  rw [show C + 7 = (C + 6) + 1 from by ring]; step fm
  rw [show (2 : ℕ) = 1 + 1 from rfl]; step fm
  rw [show C + 6 = (C + 5) + 1 from by ring]; step fm
  rw [show C + 5 = (C + 4) + 1 from by ring]; step fm
  rw [show C + 4 = (C + 3) + 1 from by ring]; step fm
  rw [show (1 : ℕ) = 0 + 1 from rfl]; step fm
  rw [show C + 3 = (C + 2) + 1 from by ring]; step fm
  rw [show C + 2 = (C + 1) + 1 from by ring]; step fm
  rw [show C + 1 = C + 1 from rfl]; step fm
  step fm; ring_nf; finish

theorem to_canonical (A B D : ℕ) :
    (⟨A, B + 1, 0, D, 0⟩ : Q) [fm]⊢* ⟨A + 3 * D + B + 1, 0, B + 1 + 2 * D, 0, 0⟩ := by
  apply stepStar_trans (r3r2_drain D A B)
  apply stepStar_trans (r3_chain (B + 1 + 2 * D) (A + D) 0)
  have h := r4_chain (B + 1 + 2 * D) (A + D + (B + 1 + 2 * D)) 0 0
  simp only [Nat.zero_add] at h ⊢
  rw [show A + D + (B + 1 + 2 * D) = A + 3 * D + B + 1 from by ring] at h ⊢
  exact h

theorem drain_phase : ∀ C, ∀ A D, C ≤ 7 * A + 6 →
    ∃ a' c', a' ≥ 1 ∧ c' ≥ 1 ∧ c' + 1 ≤ 7 * a' ∧ (⟨A, 1, C, D, 2⟩ : Q) [fm]⊢* ⟨a', 0, c', 0, 0⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ih
  intro A D hCA
  by_cases hC7 : C < 7
  · -- C < 7: base cases. Use rcases to decompose C.
    rcases C with _ | _ | _ | _ | _ | _ | _ | C' <;>
      (try simp only [Nat.reduceAdd, Nat.zero_add] at *)
    · -- C = 0
      rcases D with _ | _ | D
      · exact ⟨A + 1, 3, by omega, by omega, by omega, by
          step fm; exact r4_chain 3 (A + 1) 0 0⟩
      · exact ⟨A + 4, 5, by omega, by omega, by omega, by
          step fm; apply stepStar_trans (r3_chain 4 A 1); exact r4_chain 5 (A + 4) 0 0⟩
      · refine ⟨A + 3 * D + 7, 7 + 2 * D, by omega, by omega, by omega, ?_⟩
        rw [show D + 2 = (D + 1) + 1 from by ring, show (2 : ℕ) = 1 + 1 from rfl]; step fm
        rw [show D + 1 = D + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]; step fm
        have h := to_canonical A 6 D; exact h
    · -- C = 1
      rcases D with _ | D
      · exact ⟨A + 3, 4, by omega, by omega, by omega, by
          step fm; step fm
          apply stepStar_trans (r3_chain 3 A 1); exact r4_chain 4 (A + 3) 0 0⟩
      · refine ⟨A + 3 * D + 6, 6 + 2 * D, by omega, by omega, by omega, ?_⟩
        step fm
        rw [show D + 1 + 1 = (D + 1) + 1 from by ring, show (2 : ℕ) = 1 + 1 from rfl]; step fm
        rw [show D + 1 = D + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]; step fm
        have h := to_canonical A 5 D; exact h
    · -- C = 2
      refine ⟨A + 3 * D + 5, 5 + 2 * D, by omega, by omega, by omega, ?_⟩
      rw [show (2 : ℕ) = 1 + 1 from rfl]; step fm
      rw [show D + 1 = D + 1 from rfl, show (2 : ℕ) = 1 + 1 from rfl]; step fm
      rw [show (1 : ℕ) = 0 + 1 from rfl]; step fm
      rw [show D + 1 = D + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]; step fm
      have h := to_canonical A 4 D; exact h
    · -- C = 3
      refine ⟨A + 3 * D + 7, 4 + 2 * D + 2, by omega, by omega, by omega, ?_⟩
      rw [show (3 : ℕ) = 2 + 1 from rfl]; step fm
      rw [show D + 1 = D + 1 from rfl, show (2 : ℕ) = 1 + 1 from rfl]; step fm
      rw [show (2 : ℕ) = 1 + 1 from rfl]; step fm
      rw [show (1 : ℕ) = 0 + 1 from rfl]; step fm
      rw [show D + 2 = (D + 1) + 1 from by ring, show (1 : ℕ) = 0 + 1 from rfl]; step fm
      have h := to_canonical A 3 (D + 1); exact h
    · -- C = 4
      refine ⟨A + 3 * D + 9, 3 + 2 * D + 4, by omega, by omega, by omega, ?_⟩
      rw [show (4 : ℕ) = 3 + 1 from rfl]; step fm
      rw [show D + 1 = D + 1 from rfl, show (2 : ℕ) = 1 + 1 from rfl]; step fm
      rw [show (3 : ℕ) = 2 + 1 from rfl]; step fm
      rw [show (2 : ℕ) = 1 + 1 from rfl]; step fm
      rw [show (1 : ℕ) = 0 + 1 from rfl]; step fm
      rw [show D + 3 = (D + 2) + 1 from by ring, show (1 : ℕ) = 0 + 1 from rfl]; step fm
      have h := to_canonical A 2 (D + 2); exact h
    · -- C = 5
      refine ⟨A + 3 * D + 11, 2 + 2 * D + 6, by omega, by omega, by omega, ?_⟩
      rw [show (5 : ℕ) = 4 + 1 from rfl]; step fm
      rw [show D + 1 = D + 1 from rfl, show (2 : ℕ) = 1 + 1 from rfl]; step fm
      rw [show (4 : ℕ) = 3 + 1 from rfl]; step fm
      rw [show (3 : ℕ) = 2 + 1 from rfl]; step fm
      rw [show (2 : ℕ) = 1 + 1 from rfl]; step fm
      rw [show D + 3 = (D + 2) + 1 from by ring, show (1 : ℕ) = 0 + 1 from rfl]; step fm
      rw [show (1 : ℕ) = 0 + 1 from rfl]; step fm
      have h := to_canonical A 1 (D + 3); exact h
    · -- C = 6
      refine ⟨A + 3 * D + 13, 3 + 2 * D + 6, by omega, by omega, by omega, ?_⟩
      rw [show (6 : ℕ) = 5 + 1 from rfl]; step fm
      rw [show D + 1 = D + 1 from rfl, show (2 : ℕ) = 1 + 1 from rfl]; step fm
      rw [show (5 : ℕ) = 4 + 1 from rfl]; step fm
      rw [show (4 : ℕ) = 3 + 1 from rfl]; step fm
      rw [show (3 : ℕ) = 2 + 1 from rfl]; step fm
      rw [show D + 3 = (D + 2) + 1 from by ring, show (1 : ℕ) = 0 + 1 from rfl]; step fm
      rw [show (2 : ℕ) = 1 + 1 from rfl]; step fm
      rw [show (1 : ℕ) = 0 + 1 from rfl]; step fm
      step fm
      rw [show D + 4 = (D + 3) + 1 from by ring, show (1 : ℕ) = 0 + 1 from rfl]; step fm
      have h := to_canonical (A + 1) 2 (D + 3)
      rw [show A + 1 + 3 * (D + 3) + 2 + 1 = A + 3 * D + 13 from by ring,
          show 2 + 1 + 2 * (D + 3) = 3 + 2 * D + 6 from by ring] at h; exact h
    · -- C' + 7 < 7: impossible.
      exact absurd hC7 (by omega)
  · -- C ≥ 7: block step then IH. C ≤ 7A+6 and C ≥ 7 → A ≥ 1.
    push_neg at hC7
    have hA1 : A ≥ 1 := by omega
    obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
    have hC : C = (C - 7) + 7 := by omega
    rw [hC]
    have hblock := block_step (C - 7) A' D
    obtain ⟨a', c', ha', hc', hca', hrest⟩ := ih (C - 7) (by omega) A' (D + 5) (by omega)
    exact ⟨a', c', ha', hc', hca', stepStar_trans hblock hrest⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 3, 0, 0⟩) (by execute fm 5)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c, q = ⟨a, 0, c, 0, 0⟩ ∧ a ≥ 1 ∧ c ≥ 1 ∧ c + 1 ≤ 7 * a)
  · intro q ⟨a, c, hq, ha, hc, hca⟩
    subst hq
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have hR5 : (⟨a' + 1, 0, c, 0, 0⟩ : Q) [fm]⊢ ⟨a', 1, c, 0, 2⟩ := rfl
    obtain ⟨a'', c', ha'', hc', hca'', hdrain⟩ := drain_phase c a' 0 (by omega)
    exact ⟨⟨a'', 0, c', 0, 0⟩,
           ⟨a'', c', rfl, ha'', hc', by omega⟩,
           step_stepStar_stepPlus hR5 hdrain⟩
  · exact ⟨1, 3, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_1451
