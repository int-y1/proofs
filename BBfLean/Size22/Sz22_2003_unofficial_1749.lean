import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1749: [81/35, 5/33, 14/3, 11/7, 21/2]

Vector representation:
```
 0  4 -1 -1  0
 0 -1  1  0 -1
 1 -1  0  1  0
 0  0  0 -1  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1749

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+4, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ d e, ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish

theorem r3_chain : ∀ k, ∀ a d, ⟨a, b + k, 0, d, 0⟩ [fm]⊢* ⟨a + k, b, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 1) (d + 1)); ring_nf; finish

theorem spiral : ∀ k, ∀ a b, ⟨a, b + 1, k + 1, 0, 0⟩ [fm]⊢* ⟨a + k + 1, b + 3 * k + 4, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · step fm; step fm; finish
  · step fm; step fm; apply stepStar_trans (ih (a + 1) (b + 3)); ring_nf; finish

theorem unfold_c0 : ⟨a + 1, 0, 0, 0, e + 5⟩ [fm]⊢* ⟨a, 0, 4, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem unfold_c1 : ⟨a + 1, 0, c + 1, 0, e + 5⟩ [fm]⊢* ⟨a, 0, c + 5, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem unfold_loop : ∀ k, ∀ a c, ⟨a + k, 0, c + 1, 0, 5 * k + e⟩ [fm]⊢* ⟨a, 0, c + 4 * k + 1, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 5 * (k + 1) + e = 5 * k + (e + 5) from by ring]
    apply stepStar_trans (unfold_c1 (a := a + k) (c := c) (e := 5 * k + e))
    rw [show c + 5 = (c + 4) + 1 from by ring]
    apply stepStar_trans (ih a (c + 4)); ring_nf; finish

theorem final_r0 (hC : C ≥ 2) : ⟨a + 1, 0, C, 0, 0⟩ [fm]⊢⁺ ⟨a + 4 * C + 1, 0, 0, 3 * C + 2, 0⟩ := by
  obtain ⟨c, rfl⟩ : ∃ c, C = c + 2 := ⟨C - 2, by omega⟩
  step fm; step fm
  apply stepStar_trans (spiral c a 4)
  rw [show 4 + 3 * c + 4 = 0 + (3 * c + 8) from by ring]
  apply stepStar_trans (r3_chain (3 * c + 8) (a + c + 1) 0)
  ring_nf; finish

theorem final_r1 (hC : C ≥ 1) : ⟨a + 1, 0, C, 0, 1⟩ [fm]⊢⁺ ⟨a + 4 * C + 4, 0, 0, 3 * C + 4, 0⟩ := by
  obtain ⟨c, rfl⟩ : ∃ c, C = c + 1 := ⟨C - 1, by omega⟩
  step fm; step fm; step fm
  apply stepStar_trans (spiral c a 3)
  rw [show 3 + 3 * c + 4 = 0 + (3 * c + 7) from by ring]
  apply stepStar_trans (r3_chain (3 * c + 7) (a + c + 1) 0)
  ring_nf; finish

theorem final_r2 (hC : C ≥ 1) : ⟨a + 1, 0, C, 0, 2⟩ [fm]⊢⁺ ⟨a + 4 * C + 7, 0, 0, 3 * C + 6, 0⟩ := by
  obtain ⟨c, rfl⟩ : ∃ c, C = c + 1 := ⟨C - 1, by omega⟩
  step fm; step fm; step fm; step fm
  rw [show c + 1 + 1 = (c + 1) + 1 from by ring]
  apply stepStar_trans (spiral (c + 1) a 2)
  rw [show 2 + 3 * (c + 1) + 4 = 0 + (3 * c + 9) from by ring]
  apply stepStar_trans (r3_chain (3 * c + 9) (a + c + 2) 0)
  ring_nf; finish

theorem final_r3 (hC : C ≥ 1) : ⟨a + 1, 0, C, 0, 3⟩ [fm]⊢⁺ ⟨a + 4 * C + 10, 0, 0, 3 * C + 8, 0⟩ := by
  obtain ⟨c, rfl⟩ : ∃ c, C = c + 1 := ⟨C - 1, by omega⟩
  step fm; step fm; step fm; step fm; step fm
  rw [show c + 1 + 2 = (c + 2) + 1 from by ring]
  apply stepStar_trans (spiral (c + 2) a 1)
  rw [show 1 + 3 * (c + 2) + 4 = 0 + (3 * c + 11) from by ring]
  apply stepStar_trans (r3_chain (3 * c + 11) (a + c + 3) 0)
  ring_nf; finish

theorem final_r4 (hC : C ≥ 1) : ⟨a + 1, 0, C, 0, 4⟩ [fm]⊢⁺ ⟨a + 4 * C + 13, 0, 0, 3 * C + 10, 0⟩ := by
  obtain ⟨c, rfl⟩ : ∃ c, C = c + 1 := ⟨C - 1, by omega⟩
  step fm; step fm; step fm; step fm; step fm; step fm
  rw [show c + 1 + 3 = (c + 3) + 1 from by ring]
  apply stepStar_trans (spiral (c + 3) a 0)
  rw [show 0 + 3 * (c + 3) + 4 = 0 + (3 * c + 13) from by ring]
  apply stepStar_trans (r3_chain (3 * c + 13) (a + c + 4) 0)
  ring_nf; finish

theorem d2_trans : ⟨a + 1, 0, 0, 2, 0⟩ [fm]⊢⁺ ⟨a + 7, 0, 0, 6, 0⟩ := by
  execute fm 14

theorem d3_trans : ⟨a + 1, 0, 0, 3, 0⟩ [fm]⊢⁺ ⟨a + 10, 0, 0, 8, 0⟩ := by
  execute fm 20

theorem d4_trans : ⟨a + 1, 0, 0, 4, 0⟩ [fm]⊢⁺ ⟨a + 13, 0, 0, 10, 0⟩ := by
  execute fm 26

theorem large_d_trans (hr : r ≤ 4) :
    ⟨a + n + 2, 0, 0, 5 * n + 5 + r, 0⟩ [fm]⊢⁺ ⟨a + 16 * n + 3 * r + 17, 0, 0, 12 * n + 2 * r + 14, 0⟩ := by
  rw [show 5 * n + 5 + r = 0 + (5 * n + 5 + r) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (5 * n + 5 + r) 0 0 (a := a + n + 2))
  rw [show (0 + (5 * n + 5 + r) : ℕ) = (5 * n + r) + 5 from by ring,
      show a + n + 2 = (a + n + 1) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (unfold_c0 (a := a + n + 1) (e := 5 * n + r))
  rw [show (4 : ℕ) = 3 + 1 from by ring,
      show a + n + 1 = (a + 1) + n from by ring]
  apply stepStar_stepPlus_stepPlus (unfold_loop n (a + 1) 3 (e := r))
  rw [show 3 + 4 * n + 1 = 4 * n + 4 from by ring]
  interval_cases r <;> (
    first
    | (apply stepPlus_stepStar_stepPlus (final_r0 (C := 4 * n + 4) (by omega)); ring_nf; finish)
    | (apply stepPlus_stepStar_stepPlus (final_r1 (C := 4 * n + 4) (by omega)); ring_nf; finish)
    | (apply stepPlus_stepStar_stepPlus (final_r2 (C := 4 * n + 4) (by omega)); ring_nf; finish)
    | (apply stepPlus_stepStar_stepPlus (final_r3 (C := 4 * n + 4) (by omega)); ring_nf; finish)
    | (apply stepPlus_stepStar_stepPlus (final_r4 (C := 4 * n + 4) (by omega)); ring_nf; finish))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 6, 0⟩) (by execute fm 16)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 2 ∧ 5 * a ≥ d + 5)
  · intro c ⟨A, D, hq, hd, ha⟩; subst hq
    rcases (show D = 2 ∨ D = 3 ∨ D = 4 ∨ D ≥ 5 from by omega) with rfl | rfl | rfl | hd5
    · obtain ⟨a', rfl⟩ : ∃ a', A = a' + 1 := ⟨A - 1, by omega⟩
      exact ⟨⟨a' + 7, 0, 0, 6, 0⟩, ⟨a' + 7, 6, rfl, by omega, by omega⟩, d2_trans⟩
    · obtain ⟨a', rfl⟩ : ∃ a', A = a' + 1 := ⟨A - 1, by omega⟩
      exact ⟨⟨a' + 10, 0, 0, 8, 0⟩, ⟨a' + 10, 8, rfl, by omega, by omega⟩, d3_trans⟩
    · obtain ⟨a', rfl⟩ : ∃ a', A = a' + 1 := ⟨A - 1, by omega⟩
      exact ⟨⟨a' + 13, 0, 0, 10, 0⟩, ⟨a' + 13, 10, rfl, by omega, by omega⟩, d4_trans⟩
    · obtain ⟨r, hr, n, hdn⟩ : ∃ r, r ≤ 4 ∧ ∃ n, D = 5 * n + 5 + r := by
        refine ⟨(D - 5) % 5, ?_, (D - 5) / 5, ?_⟩
        · have := Nat.mod_lt (D - 5) (by omega : (5 : ℕ) > 0); omega
        · have := Nat.div_add_mod (D - 5) 5; omega
      subst hdn
      have hAn : A ≥ n + 2 := by omega
      obtain ⟨a', rfl⟩ : ∃ a', A = a' + n + 2 := ⟨A - n - 2, by omega⟩
      refine ⟨⟨a' + 16 * n + 3 * r + 17, 0, 0, 12 * n + 2 * r + 14, 0⟩,
        ⟨a' + 16 * n + 3 * r + 17, 12 * n + 2 * r + 14, rfl, by omega, by omega⟩, ?_⟩
      exact large_d_trans hr
  · exact ⟨7, 6, rfl, by omega, by omega⟩
