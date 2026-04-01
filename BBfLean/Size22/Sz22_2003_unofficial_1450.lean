import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1450: [7/15, 27/77, 22/3, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  0
 0  3  0 -1 -1
 1 -1  0  0  1
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1450

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem r3_chain : ∀ k, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

theorem e_to_c : ∀ k, ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing c
  · exists 0
  · rw [Nat.add_succ]; step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

theorem drain_round : ⟨a + 1, 0, c + 4, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 3, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; ring_nf; finish

theorem drain_rounds : ∀ k d, ⟨a + k, 0, c + 4 * k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih
  · intro d; exists 0
  · intro d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 4 * (k + 1) = (c + 4 * k) + 4 from by ring]
    apply stepStar_trans drain_round
    apply stepStar_trans (ih (d + 3))
    rw [show d + 3 + 3 * k = d + 3 * (k + 1) from by ring]; finish

-- R3+R2 combined round. Cases on b avoids match compiler issues.
theorem r3r2_round : ⟨a, b + 1, 0, d + 1, 0⟩ [fm]⊢* ⟨a + 1, b + 3, 0, d, 0⟩ := by
  cases b <;> (step fm; step fm; ring_nf; finish)

-- R3/R2 chain: fully drains d, accumulating into a and b.
theorem r3r2_chain : ∀ k, ⟨a, b + 1, 0, k, 0⟩ [fm]⊢* ⟨a + k, b + 2 * k + 1, 0, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · apply stepStar_trans (r3r2_round (a := a) (b := b) (d := k))
    apply stepStar_trans (ih (a := a + 1) (b := b + 2))
    ring_nf; finish

-- Tail r=0: ⟨a+1, 0, 0, d+1, 0⟩ → R5, R2 → ⟨a, 4, 0, d, 0⟩ → r3r2 chain.
theorem tail_r0 : ⟨a + 1, 0, 0, d + 1, 0⟩ [fm]⊢* ⟨a + d, 2 * d + 4, 0, 0, 0⟩ := by
  step fm; step fm
  apply stepStar_trans (r3r2_chain d (a := a) (b := 3))
  ring_nf; finish

-- Tail r=1: ⟨a+1, 0, 1, d, 0⟩ → R5, R1, R2 → ⟨a, 3, 0, d, 0⟩ → r3r2 chain.
theorem tail_r1 : ⟨a + 1, 0, 1, d, 0⟩ [fm]⊢* ⟨a + d, 2 * d + 3, 0, 0, 0⟩ := by
  step fm; step fm; step fm
  apply stepStar_trans (r3r2_chain d (a := a) (b := 2))
  ring_nf; finish

-- Tail r=2: ⟨a+1, 0, 2, d, 0⟩ → R5, R1, R2, R1 → ⟨a, 2, 0, d+1, 0⟩ → r3r2 chain.
theorem tail_r2 : ⟨a + 1, 0, 2, d, 0⟩ [fm]⊢* ⟨a + d + 1, 2 * d + 4, 0, 0, 0⟩ := by
  step fm; step fm; step fm; step fm
  apply stepStar_trans (r3r2_chain (d + 1) (a := a) (b := 1))
  ring_nf; finish

-- Tail r=3: ⟨a+1, 0, 3, d, 0⟩ → R5, R1, R2, R1, R1 → ⟨a, 1, 0, d+2, 0⟩ → r3r2 chain.
theorem tail_r3 : ⟨a + 1, 0, 3, d, 0⟩ [fm]⊢* ⟨a + d + 2, 2 * d + 5, 0, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (r3r2_chain (d + 2) (a := a) (b := 0))
  ring_nf; finish

-- Full transition for b ≡ 0 (mod 4): b = 4*(m+1).
theorem trans_mod0 (m : ℕ) :
    ⟨a, 4 * (m + 1), 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 6 * m + 4, 6 * m + 8, 0, 0, 0⟩ := by
  rw [show 4 * (m + 1) = (4 * m + 3) + 1 from by ring]
  step fm
  apply stepStar_trans (r3_chain (4 * m + 3) (a := a + 1) (e := 1))
  rw [show a + 1 + (4 * m + 3) = a + 4 * m + 4 from by ring,
      show 1 + (4 * m + 3) = 4 * m + 4 from by ring]
  apply stepStar_trans (e_to_c (4 * m + 4) (a := a + 4 * m + 4) (c := 0))
  rw [show (0 : ℕ) + (4 * m + 4) = 0 + 4 * (m + 1) from by ring,
      show a + 4 * m + 4 = (a + 3 * m + 3) + (m + 1) from by ring]
  apply stepStar_trans (drain_rounds (m + 1) 0 (a := a + 3 * m + 3) (c := 0))
  rw [show (0 : ℕ) + 3 * (m + 1) = (3 * m + 2) + 1 from by ring,
      show a + 3 * m + 3 = (a + 3 * m + 2) + 1 from by ring]
  apply stepStar_trans (tail_r0 (a := a + 3 * m + 2) (d := 3 * m + 2))
  ring_nf; finish

-- Full transition for b ≡ 1 (mod 4): b = 4*m + 1.
theorem trans_mod1 (m : ℕ) :
    ⟨a, 4 * m + 1, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 6 * m, 6 * m + 3, 0, 0, 0⟩ := by
  rw [show 4 * m + 1 = (4 * m) + 1 from by ring]
  step fm
  apply stepStar_trans (r3_chain (4 * m) (a := a + 1) (e := 1))
  rw [show a + 1 + 4 * m = a + 4 * m + 1 from by ring,
      show 1 + 4 * m = 4 * m + 1 from by ring]
  apply stepStar_trans (e_to_c (4 * m + 1) (a := a + 4 * m + 1) (c := 0))
  rw [show (0 : ℕ) + (4 * m + 1) = 1 + 4 * m from by ring,
      show a + 4 * m + 1 = (a + 3 * m + 1) + m from by ring]
  apply stepStar_trans (drain_rounds m 0 (a := a + 3 * m + 1) (c := 1))
  rw [show (0 : ℕ) + 3 * m = 3 * m from by ring,
      show a + 3 * m + 1 = (a + 3 * m) + 1 from by ring]
  apply stepStar_trans (tail_r1 (a := a + 3 * m) (d := 3 * m))
  ring_nf; finish

-- Full transition for b ≡ 2 (mod 4): b = 4*m + 2.
theorem trans_mod2 (m : ℕ) :
    ⟨a, 4 * m + 2, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 6 * m + 2, 6 * m + 4, 0, 0, 0⟩ := by
  rw [show 4 * m + 2 = (4 * m + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (r3_chain (4 * m + 1) (a := a + 1) (e := 1))
  rw [show a + 1 + (4 * m + 1) = a + 4 * m + 2 from by ring,
      show 1 + (4 * m + 1) = 4 * m + 2 from by ring]
  apply stepStar_trans (e_to_c (4 * m + 2) (a := a + 4 * m + 2) (c := 0))
  rw [show (0 : ℕ) + (4 * m + 2) = 2 + 4 * m from by ring,
      show a + 4 * m + 2 = (a + 3 * m + 2) + m from by ring]
  apply stepStar_trans (drain_rounds m 0 (a := a + 3 * m + 2) (c := 2))
  rw [show (0 : ℕ) + 3 * m = 3 * m from by ring,
      show a + 3 * m + 2 = (a + 3 * m + 1) + 1 from by ring]
  apply stepStar_trans (tail_r2 (a := a + 3 * m + 1) (d := 3 * m))
  ring_nf; finish

-- Full transition for b ≡ 3 (mod 4): b = 4*m + 3.
theorem trans_mod3 (m : ℕ) :
    ⟨a, 4 * m + 3, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 6 * m + 4, 6 * m + 5, 0, 0, 0⟩ := by
  rw [show 4 * m + 3 = (4 * m + 2) + 1 from by ring]
  step fm
  apply stepStar_trans (r3_chain (4 * m + 2) (a := a + 1) (e := 1))
  rw [show a + 1 + (4 * m + 2) = a + 4 * m + 3 from by ring,
      show 1 + (4 * m + 2) = 4 * m + 3 from by ring]
  apply stepStar_trans (e_to_c (4 * m + 3) (a := a + 4 * m + 3) (c := 0))
  rw [show (0 : ℕ) + (4 * m + 3) = 3 + 4 * m from by ring,
      show a + 4 * m + 3 = (a + 3 * m + 3) + m from by ring]
  apply stepStar_trans (drain_rounds m 0 (a := a + 3 * m + 3) (c := 3))
  rw [show (0 : ℕ) + 3 * m = 3 * m from by ring,
      show a + 3 * m + 3 = (a + 3 * m + 2) + 1 from by ring]
  apply stepStar_trans (tail_r3 (a := a + 3 * m + 2) (d := 3 * m))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 4, 0, 0, 0⟩)
  · execute fm 10
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a b, q = ⟨a, b, 0, 0, 0⟩ ∧ a ≥ 1 ∧ b ≥ 1)
  · intro c ⟨a, b, hq, ha, hb⟩; subst hq
    rcases (show b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 from by omega)
      with h0 | h1 | h2 | h3
    · obtain ⟨m, hm⟩ : ∃ m, b = 4 * m := ⟨b / 4, by omega⟩
      have : m ≥ 1 := by omega
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [hm]
      exact ⟨⟨a + 6 * m' + 4, 6 * m' + 8, 0, 0, 0⟩,
        ⟨a + 6 * m' + 4, 6 * m' + 8, rfl, by omega, by omega⟩,
        trans_mod0 m'⟩
    · obtain ⟨m, hm⟩ : ∃ m, b = 4 * m + 1 := ⟨b / 4, by omega⟩
      rw [hm]
      exact ⟨⟨a + 6 * m, 6 * m + 3, 0, 0, 0⟩,
        ⟨a + 6 * m, 6 * m + 3, rfl, by omega, by omega⟩,
        trans_mod1 m⟩
    · obtain ⟨m, hm⟩ : ∃ m, b = 4 * m + 2 := ⟨b / 4, by omega⟩
      rw [hm]
      exact ⟨⟨a + 6 * m + 2, 6 * m + 4, 0, 0, 0⟩,
        ⟨a + 6 * m + 2, 6 * m + 4, rfl, by omega, by omega⟩,
        trans_mod2 m⟩
    · obtain ⟨m, hm⟩ : ∃ m, b = 4 * m + 3 := ⟨b / 4, by omega⟩
      rw [hm]
      exact ⟨⟨a + 6 * m + 4, 6 * m + 5, 0, 0, 0⟩,
        ⟨a + 6 * m + 4, 6 * m + 5, rfl, by omega, by omega⟩,
        trans_mod3 m⟩
  · exact ⟨1, 4, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1450
