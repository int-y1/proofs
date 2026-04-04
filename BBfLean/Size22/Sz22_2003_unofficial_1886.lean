import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1886: [9/35, 5/33, 98/3, 11/49, 21/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  1  0 -1
 1 -1  0  2  0
 0  0  0 -2  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1886

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r4_drain' : ∀ k, ⟨a, 0, 0, 2 * k + r, e⟩ [fm]⊢* ⟨a, 0, 0, r, e + k⟩ := by
  intro k; induction' k with k ih generalizing a r e
  · simp; exists 0
  · rw [show 2 * (k + 1) + r = (2 * k + r) + 2 from by ring]
    step fm; apply stepStar_trans (ih (a := a) (r := r) (e := e + 1)); ring_nf; finish

theorem r3_chain : ∀ b, ⟨a, b, 0, d, 0⟩ [fm]⊢* ⟨a + b, 0, 0, d + 2 * b, 0⟩ := by
  intro b; induction' b with b ih generalizing a d
  · simp; exists 0
  · step fm; apply stepStar_trans (ih (a := a + 1) (d := d + 2)); ring_nf; finish

theorem drain_round : ⟨a + 1, 2, c, 0, e + 3⟩ [fm]⊢* ⟨a, 2, c + 2, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem drain_chain : ∀ m, ⟨a + m, 2, c, 0, 3 * m + e⟩ [fm]⊢* ⟨a, 2, c + 2 * m, 0, e⟩ := by
  intro m; induction' m with m ih generalizing a c e
  · simp; exists 0
  · rw [show a + (m + 1) = (a + m) + 1 from by ring,
        show 3 * (m + 1) + e = 3 * m + (e + 3) from by ring]
    apply stepStar_trans drain_round
    apply stepStar_trans (ih (a := a) (c := c + 2) (e := e)); ring_nf; finish

theorem c_unwind_step : ⟨a, b + 1, c + 2, 0, 0⟩ [fm]⊢* ⟨a + 1, b + 4, c, 0, 0⟩ := by
  step fm; step fm; step fm; finish

theorem c_unwind_even : ∀ j, ⟨a, b + 1, 2 * j, 0, 0⟩ [fm]⊢* ⟨a + j, b + 3 * j + 1, 0, 0, 0⟩ := by
  intro j; induction' j with j ih generalizing a b
  · simp; exists 0
  · rw [show 2 * (j + 1) = (2 * j) + 2 from by ring]
    apply stepStar_trans (c_unwind_step (a := a) (b := b) (c := 2 * j))
    apply stepStar_trans (ih (a := a + 1) (b := b + 3)); ring_nf; finish

theorem c_unwind_odd : ∀ j, ⟨a, b + 1, 2 * j + 1, 0, 0⟩ [fm]⊢* ⟨a + j + 1, b + 3 * j + 2, 0, 1, 0⟩ := by
  intro j; induction' j with j ih generalizing a b
  · step fm; step fm; finish
  · rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 from by ring]
    apply stepStar_trans (c_unwind_step (a := a) (b := b) (c := 2 * j + 1))
    apply stepStar_trans (ih (a := a + 1) (b := b + 3)); ring_nf; finish

theorem odd_k1 : ⟨A + 1, 0, 0, 3, 0⟩ [fm]⊢⁺ ⟨A + 2, 0, 0, 5, 0⟩ := by execute fm 6
theorem odd_k2 : ⟨A + 1, 0, 0, 5, 0⟩ [fm]⊢⁺ ⟨A + 3, 0, 0, 6, 0⟩ := by execute fm 10

theorem even_trans_0 : ∀ m, ⟨A + 3 * m + 2, 0, 0, 6 * m + 2, 0⟩ [fm]⊢⁺
    ⟨A + 6 * m + 3, 0, 0, 6 * m + 4, 0⟩ := by
  intro m
  rw [show 6 * m + 2 = 2 * (3 * m + 1) + 0 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain' (3 * m + 1) (a := A + 3 * m + 2) (r := 0) (e := 0))
  simp only [Nat.zero_add]
  rw [show A + 3 * m + 2 = (A + 3 * m + 1) + 1 from by ring]
  step fm
  rw [show (3 * m + 1 : ℕ) = (3 * m) + 1 from by ring]; step fm; step fm
  rw [show A + 3 * m + 1 = (A + 2 * m + 1) + m from by ring,
      show (3 * m : ℕ) = 3 * m + 0 from by ring]
  apply stepStar_trans (drain_chain m (a := A + 2 * m + 1) (c := 0) (e := 0)); simp only [Nat.zero_add]
  apply stepStar_trans (c_unwind_even m (a := A + 2 * m + 1) (b := 1))
  rw [show A + 2 * m + 1 + m = A + 3 * m + 1 from by ring, show 1 + 3 * m + 1 = 3 * m + 2 from by ring]
  apply stepStar_trans (r3_chain (3 * m + 2) (a := A + 3 * m + 1) (d := 0)); ring_nf; finish

theorem even_trans_1 : ∀ m, ⟨A + 3 * m + 3, 0, 0, 6 * m + 4, 0⟩ [fm]⊢⁺
    ⟨A + 6 * m + 5, 0, 0, 6 * m + 5, 0⟩ := by
  intro m
  rw [show 6 * m + 4 = 2 * (3 * m + 2) + 0 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain' (3 * m + 2) (a := A + 3 * m + 3) (r := 0) (e := 0))
  simp only [Nat.zero_add]
  rw [show A + 3 * m + 3 = (A + 3 * m + 2) + 1 from by ring]
  step fm; rw [show (3 * m + 2 : ℕ) = (3 * m + 1) + 1 from by ring]; step fm; step fm
  rw [show A + 3 * m + 2 = (A + 2 * m + 2) + m from by ring]
  apply stepStar_trans (drain_chain m (a := A + 2 * m + 2) (c := 0) (e := 1)); simp only [Nat.zero_add]
  apply stepStar_trans (step_stepStar (by simp [fm]; rfl : (A + 2 * m + 2, 2, 2 * m, 0, 1) [fm]⊢ (A + 2 * m + 2, 1, 2 * m + 1, 0, 0)))
  apply stepStar_trans (c_unwind_odd m (a := A + 2 * m + 2) (b := 0))
  rw [show A + 2 * m + 2 + m + 1 = A + 3 * m + 3 from by ring, show 0 + 3 * m + 2 = 3 * m + 2 from by ring]
  apply stepStar_trans (r3_chain (3 * m + 2) (a := A + 3 * m + 3) (d := 1)); ring_nf; finish

theorem even_trans_2 : ∀ m, ⟨A + 3 * m + 4, 0, 0, 6 * m + 6, 0⟩ [fm]⊢⁺
    ⟨A + 6 * m + 7, 0, 0, 6 * m + 9, 0⟩ := by
  intro m
  rw [show 6 * m + 6 = 2 * (3 * m + 3) + 0 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain' (3 * m + 3) (a := A + 3 * m + 4) (r := 0) (e := 0))
  simp only [Nat.zero_add]
  rw [show A + 3 * m + 4 = (A + 3 * m + 3) + 1 from by ring]
  step fm; rw [show (3 * m + 3 : ℕ) = (3 * m + 2) + 1 from by ring]; step fm; step fm
  rw [show A + 3 * m + 3 = (A + 2 * m + 3) + m from by ring]
  apply stepStar_trans (drain_chain m (a := A + 2 * m + 3) (c := 0) (e := 2)); simp only [Nat.zero_add]
  apply stepStar_trans (step_stepStar (by simp [fm]; rfl : (A + 2 * m + 3, 2, 2 * m, 0, 2) [fm]⊢ (A + 2 * m + 3, 1, 2 * m + 1, 0, 1)))
  step fm
  rw [show A + 2 * m + 3 = (A + 2 * m + 2) + 1 from by ring]; step fm
  step fm
  apply stepStar_trans (c_unwind_odd m (a := A + 2 * m + 2) (b := 2))
  rw [show A + 2 * m + 2 + m + 1 = A + 3 * m + 3 from by ring, show 2 + 3 * m + 2 = 3 * m + 4 from by ring]
  apply stepStar_trans (r3_chain (3 * m + 4) (a := A + 3 * m + 3) (d := 1)); ring_nf; finish

theorem odd_trans_0 : ∀ m, ⟨A + 3 * m + 4, 0, 0, 6 * m + 7, 0⟩ [fm]⊢⁺
    ⟨A + 6 * m + 7, 0, 0, 6 * m + 7, 0⟩ := by
  intro m
  rw [show 6 * m + 7 = 2 * (3 * m + 3) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain' (3 * m + 3) (a := A + 3 * m + 4) (r := 1) (e := 0))
  simp only [Nat.zero_add]
  rw [show A + 3 * m + 4 = (A + 3 * m + 3) + 1 from by ring]
  step fm; rw [show (3 * m + 3 : ℕ) = (3 * m + 2) + 1 from by ring]
  step fm; step fm; rw [show (3 * m + 2 : ℕ) = (3 * m + 1) + 1 from by ring]
  step fm; step fm; rw [show (3 * m + 1 : ℕ) = (3 * m) + 1 from by ring]
  step fm
  rw [show A + 3 * m + 3 = (A + 2 * m + 3) + m from by ring,
      show (3 * m : ℕ) = 3 * m + 0 from by ring]
  apply stepStar_trans (drain_chain m (a := A + 2 * m + 3) (c := 1) (e := 0))
  rw [show 1 + 2 * m = 2 * m + 1 from by ring]
  apply stepStar_trans (c_unwind_odd m (a := A + 2 * m + 3) (b := 1))
  rw [show A + 2 * m + 3 + m + 1 = A + 3 * m + 4 from by ring, show 1 + 3 * m + 2 = 3 * m + 3 from by ring]
  apply stepStar_trans (r3_chain (3 * m + 3) (a := A + 3 * m + 4) (d := 1)); ring_nf; finish

theorem odd_trans_1 : ∀ m, ⟨A + 3 * m + 5, 0, 0, 6 * m + 9, 0⟩ [fm]⊢⁺
    ⟨A + 6 * m + 9, 0, 0, 6 * m + 8, 0⟩ := by
  intro m
  rw [show 6 * m + 9 = 2 * (3 * m + 4) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain' (3 * m + 4) (a := A + 3 * m + 5) (r := 1) (e := 0))
  simp only [Nat.zero_add]
  rw [show A + 3 * m + 5 = (A + 3 * m + 4) + 1 from by ring]
  step fm; rw [show (3 * m + 4 : ℕ) = (3 * m + 3) + 1 from by ring]
  step fm; step fm; rw [show (3 * m + 3 : ℕ) = (3 * m + 2) + 1 from by ring]
  step fm; step fm; rw [show (3 * m + 2 : ℕ) = (3 * m + 1) + 1 from by ring]
  step fm
  rw [show A + 3 * m + 4 = (A + 2 * m + 4) + m from by ring]
  apply stepStar_trans (drain_chain m (a := A + 2 * m + 4) (c := 1) (e := 1))
  rw [show 1 + 2 * m = 2 * m + 1 from by ring]
  step fm
  rw [show 2 * m + 1 + 1 = 2 * (m + 1) from by ring]
  apply stepStar_trans (c_unwind_even (m + 1) (a := A + 2 * m + 4) (b := 0))
  rw [show A + 2 * m + 4 + (m + 1) = A + 3 * m + 5 from by ring, show 0 + 3 * (m + 1) + 1 = 3 * m + 4 from by ring]
  apply stepStar_trans (r3_chain (3 * m + 4) (a := A + 3 * m + 5) (d := 0)); ring_nf; finish

theorem odd_trans_2 : ∀ m, ⟨A + 3 * m + 6, 0, 0, 6 * m + 11, 0⟩ [fm]⊢⁺
    ⟨A + 6 * m + 11, 0, 0, 6 * m + 12, 0⟩ := by
  intro m
  rw [show 6 * m + 11 = 2 * (3 * m + 5) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain' (3 * m + 5) (a := A + 3 * m + 6) (r := 1) (e := 0))
  simp only [Nat.zero_add]
  rw [show A + 3 * m + 6 = (A + 3 * m + 5) + 1 from by ring]
  step fm; rw [show (3 * m + 5 : ℕ) = (3 * m + 4) + 1 from by ring]
  step fm; step fm; rw [show (3 * m + 4 : ℕ) = (3 * m + 3) + 1 from by ring]
  step fm; step fm; rw [show (3 * m + 3 : ℕ) = (3 * m + 2) + 1 from by ring]
  step fm
  rw [show A + 3 * m + 5 = (A + 2 * m + 5) + m from by ring]
  apply stepStar_trans (drain_chain m (a := A + 2 * m + 5) (c := 1) (e := 2))
  rw [show 1 + 2 * m = 2 * m + 1 from by ring]
  step fm; step fm
  rw [show A + 2 * m + 5 = (A + 2 * m + 4) + 1 from by ring]; step fm
  step fm
  rw [show 2 * m + 1 + 1 = 2 * (m + 1) from by ring]
  apply stepStar_trans (c_unwind_even (m + 1) (a := A + 2 * m + 4) (b := 2))
  rw [show A + 2 * m + 4 + (m + 1) = A + 3 * m + 5 from by ring, show 2 + 3 * (m + 1) + 1 = 3 * m + 6 from by ring]
  apply stepStar_trans (r3_chain (3 * m + 6) (a := A + 3 * m + 5) (d := 0)); ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 6, 0⟩) (by execute fm 18)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 2 ∧ 2 * a ≥ d + 2)
  · intro c ⟨a, d, hq, hd, ha⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      obtain ⟨n, rfl | rfl | rfl⟩ : ∃ n, k = 3 * n ∨ k = 3 * n + 1 ∨ k = 3 * n + 2 := ⟨k / 3, by omega⟩
      · obtain ⟨B, rfl⟩ : ∃ B, a = B + 3 * n + 2 := ⟨a - (3 * n + 2), by omega⟩
        exact ⟨_, ⟨B + 6 * n + 3, 6 * n + 4, rfl, by omega, by omega⟩,
          show ⟨B + 3 * n + 2, 0, 0, 2 * (3 * n + 1), 0⟩ [fm]⊢⁺ _ by
            rw [show 2 * (3 * n + 1) = 6 * n + 2 from by ring]; exact even_trans_0 n⟩
      · obtain ⟨B, rfl⟩ : ∃ B, a = B + 3 * n + 3 := ⟨a - (3 * n + 3), by omega⟩
        exact ⟨_, ⟨B + 6 * n + 5, 6 * n + 5, rfl, by omega, by omega⟩,
          show ⟨B + 3 * n + 3, 0, 0, 2 * (3 * n + 1 + 1), 0⟩ [fm]⊢⁺ _ by
            rw [show 2 * (3 * n + 1 + 1) = 6 * n + 4 from by ring]; exact even_trans_1 n⟩
      · obtain ⟨B, rfl⟩ : ∃ B, a = B + 3 * n + 4 := ⟨a - (3 * n + 4), by omega⟩
        exact ⟨_, ⟨B + 6 * n + 7, 6 * n + 9, rfl, by omega, by omega⟩,
          show ⟨B + 3 * n + 4, 0, 0, 2 * (3 * n + 2 + 1), 0⟩ [fm]⊢⁺ _ by
            rw [show 2 * (3 * n + 2 + 1) = 6 * n + 6 from by ring]; exact even_trans_2 n⟩
    · subst hK
      rcases (show K = 0 ∨ K = 1 ∨ K ≥ 2 from by omega) with rfl | rfl | hK2
      · omega
      · obtain ⟨B, rfl⟩ : ∃ B, a = B + 1 := ⟨a - 1, by omega⟩
        exact ⟨_, ⟨B + 2, 5, rfl, by omega, by omega⟩, odd_k1⟩
      · obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
        rcases k with _ | k'
        · obtain ⟨B, rfl⟩ : ∃ B, a = B + 1 := ⟨a - 1, by omega⟩
          exact ⟨_, ⟨B + 3, 6, rfl, by omega, by omega⟩,
            show ⟨B + 1, 0, 0, 2 * (0 + 2) + 1, 0⟩ [fm]⊢⁺ _ by simp; exact odd_k2⟩
        · obtain ⟨n, rfl | rfl | rfl⟩ : ∃ n, k' = 3 * n ∨ k' = 3 * n + 1 ∨ k' = 3 * n + 2 := ⟨k' / 3, by omega⟩
          · obtain ⟨B, rfl⟩ : ∃ B, a = B + 3 * n + 4 := ⟨a - (3 * n + 4), by omega⟩
            exact ⟨_, ⟨B + 6 * n + 7, 6 * n + 7, rfl, by omega, by omega⟩,
              show ⟨B + 3 * n + 4, 0, 0, 2 * (3 * n + 1 + 2) + 1, 0⟩ [fm]⊢⁺ _ by
                rw [show 2 * (3 * n + 1 + 2) + 1 = 6 * n + 7 from by ring]; exact odd_trans_0 n⟩
          · obtain ⟨B, rfl⟩ : ∃ B, a = B + 3 * n + 5 := ⟨a - (3 * n + 5), by omega⟩
            exact ⟨_, ⟨B + 6 * n + 9, 6 * n + 8, rfl, by omega, by omega⟩,
              show ⟨B + 3 * n + 5, 0, 0, 2 * (3 * n + 1 + 1 + 2) + 1, 0⟩ [fm]⊢⁺ _ by
                rw [show 2 * (3 * n + 1 + 1 + 2) + 1 = 6 * n + 9 from by ring]; exact odd_trans_1 n⟩
          · obtain ⟨B, rfl⟩ : ∃ B, a = B + 3 * n + 6 := ⟨a - (3 * n + 6), by omega⟩
            exact ⟨_, ⟨B + 6 * n + 11, 6 * n + 12, rfl, by omega, by omega⟩,
              show ⟨B + 3 * n + 6, 0, 0, 2 * (3 * n + 2 + 1 + 2) + 1, 0⟩ [fm]⊢⁺ _ by
                rw [show 2 * (3 * n + 2 + 1 + 2) + 1 = 6 * n + 11 from by ring]; exact odd_trans_2 n⟩
  · exact ⟨4, 6, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1886
