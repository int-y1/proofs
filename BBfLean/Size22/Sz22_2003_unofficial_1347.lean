import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1347: [63/10, 35/33, 28/3, 11/7, 3/2]

Vector representation:
```
-1  2 -1  1  0
 0 -1  1  1 -1
 2 -1  0  1  0
 0  0  0 -1  1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1347

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ a d e,
    ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a d (e + 1)); ring_nf; finish

theorem r3_chain : ∀ k, ∀ a b d,
    ⟨a, b + k, 0, d, 0⟩ [fm]⊢* ⟨a + 2 * k, b, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    step fm; apply stepStar_trans (ih (a + 2) b (d + 1)); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a b d e,
    ⟨a + k, b + 1, 0, d, e + k⟩ [fm]⊢* ⟨a, b + 1 + k, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring,
        show b + 1 + (k + 1) = (b + 1 + 1) + k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring,
        show (e + k) + 1 = e + k + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (b + 1) (d + 2) e)
    ring_nf; finish

theorem r2_only_chain : ∀ k, ∀ b c d,
    ⟨0, b + k, c, d, k⟩ [fm]⊢* ⟨0, b, c + k, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show c + (k + 1) = (c + 1) + k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    step fm; apply stepStar_trans (ih b (c + 1) (d + 1)); ring_nf; finish

theorem zero_bc : ∀ C, ∀ B D,
    ⟨0, B + 1, C, D, 0⟩ [fm]⊢* ⟨2 * B + 3 * C + 2, 0, 0, D + B + 3 * C + 1, 0⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ihC; intro B D
  match C with
  | 0 =>
    rw [show 2 * B + 3 * 0 + 2 = 0 + 2 * (B + 1) from by ring,
        show D + B + 3 * 0 + 1 = D + (B + 1) from by ring]
    have := r3_chain (B + 1) 0 0 D
    rw [show (0 : ℕ) + (B + 1) = B + 1 from by ring] at this; exact this
  | 1 =>
    rw [show 2 * B + 3 * 1 + 2 = 1 + 2 * (B + 2) from by ring,
        show D + B + 3 * 1 + 1 = D + 2 + (B + 2) from by ring]
    step fm; step fm
    have := r3_chain (B + 2) 1 0 (D + 2)
    rw [show (0 : ℕ) + (B + 2) = B + 2 from by ring] at this; exact this
  | C + 2 =>
    rw [show 2 * B + 3 * (C + 2) + 2 = 2 * (B + 3) + 3 * C + 2 from by ring,
        show D + B + 3 * (C + 2) + 1 = (D + 3) + (B + 3) + 3 * C + 1 from by ring]
    step fm; step fm; step fm
    exact ihC C (by omega) (B + 3) (D + 3)

-- Case 1: E ≤ A
theorem phase_ge (k E : ℕ) :
    ⟨k + E, (0 : ℕ) + 1, 0, 0, (0 : ℕ) + E⟩ [fm]⊢*
    ⟨k + 2 * E + 2, 0, 0, 3 * E + 1, 0⟩ := by
  -- R2+R1 chain: E rounds
  have h1 : ⟨k + E, (0 : ℕ) + 1, 0, 0, (0 : ℕ) + E⟩ [fm]⊢*
      ⟨k, 0 + 1 + E, 0, 0 + 2 * E, 0⟩ :=
    r2r1_chain E k 0 0 0
  -- R3 chain: (1+E) rounds
  have h2 : ⟨k, (0 : ℕ) + (1 + E), 0, 2 * E, 0⟩ [fm]⊢*
      ⟨k + 2 * (1 + E), 0, 0, 2 * E + (1 + E), 0⟩ :=
    r3_chain (1 + E) k 0 (2 * E)
  rw [show (0 : ℕ) + 1 + E = 0 + (1 + E) from by ring,
      show (0 : ℕ) + 2 * E = 2 * E from by ring] at h1
  apply stepStar_trans h1
  rw [show k + 2 * E + 2 = k + 2 * (1 + E) from by ring,
      show 3 * E + 1 = 2 * E + (1 + E) from by ring]
  exact h2

-- Case 2: A < E, E ≤ 2A
theorem phase_lt (A G : ℕ) (hGA : G + 1 ≤ A) :
    ⟨A, (0 : ℕ) + 1, 0, 0, A + 1 + G⟩ [fm]⊢*
    ⟨2 * A + G + 3, 0, 0, 3 * A + 3 * G + 4, 0⟩ := by
  -- Phase 1: R2+R1 chain, A rounds
  have h1 : ⟨0 + A, (0 : ℕ) + 1, 0, 0, (G + 1) + A⟩ [fm]⊢*
      ⟨0, 0 + 1 + A, 0, 0 + 2 * A, G + 1⟩ :=
    r2r1_chain A 0 0 0 (G + 1)
  rw [show (0 : ℕ) + A = A from by ring,
      show (G + 1) + A = A + 1 + G from by ring,
      show (0 : ℕ) + 1 + A = 1 + A from by ring,
      show (0 : ℕ) + 2 * A = 2 * A from by ring] at h1
  -- Phase 2: R2-only chain, (G+1) rounds
  -- 1+A = (A-G) + (G+1). A-G >= 1.
  have h2 : ⟨0, (A - G) + (G + 1), 0, 2 * A, G + 1⟩ [fm]⊢*
      ⟨0, A - G, 0 + (G + 1), 2 * A + (G + 1), 0⟩ :=
    r2_only_chain (G + 1) (A - G) 0 (2 * A)
  rw [show (A - G) + (G + 1) = 1 + A from by omega,
      show (0 : ℕ) + (G + 1) = G + 1 from by ring] at h2
  -- Phase 3: zero_bc
  have hAG : A - G ≥ 1 := by omega
  have h3 : ⟨0, (A - G - 1) + 1, G + 1, 2 * A + (G + 1), 0⟩ [fm]⊢*
      ⟨2 * (A - G - 1) + 3 * (G + 1) + 2, 0, 0,
       2 * A + (G + 1) + (A - G - 1) + 3 * (G + 1) + 1, 0⟩ :=
    zero_bc (G + 1) (A - G - 1) (2 * A + (G + 1))
  rw [show (A - G - 1) + 1 = A - G from by omega] at h3
  apply stepStar_trans h1
  apply stepStar_trans h2
  rw [show 2 * A + G + 3 = 2 * (A - G - 1) + 3 * (G + 1) + 2 from by omega,
      show 3 * A + 3 * G + 4 = 2 * A + (G + 1) + (A - G - 1) + 3 * (G + 1) + 1 from by omega]
  exact h3

theorem main_trans (a e : ℕ) (hinv : e + 1 ≤ 2 * (a + 1)) :
    ⟨a + 2, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨a + e + 4, 0, 0, 0, 3 * e + 4⟩ := by
  -- R5 step
  have hR5 : ⟨a + 2, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨a + 1, 1, 0, 0, e + 1⟩ := by
    rw [show a + 2 = (a + 1) + 1 from by ring]; step fm; finish
  -- Main phase: (a+1, 1, 0, 0, e+1) →* (a+e+4, 0, 0, 3e+4, 0)
  have hPhase : ⟨a + 1, 1, 0, 0, e + 1⟩ [fm]⊢*
      ⟨a + e + 4, 0, 0, 3 * e + 4, 0⟩ := by
    rcases le_or_gt (e + 1) (a + 1) with hle | hgt
    · -- Case E ≤ A: use phase_ge with k = a+1-e-1 = a-e
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      -- a + 1 = e + 1 + k, so k = a - e
      have := phase_ge k (e + 1)
      rw [show k + (e + 1) = a + 1 from by omega,
          show (0 : ℕ) + 1 = 1 from by ring,
          show (0 : ℕ) + (e + 1) = e + 1 from by ring,
          show k + 2 * (e + 1) + 2 = a + e + 4 from by omega,
          show 3 * (e + 1) + 1 = 3 * e + 4 from by ring] at this
      exact this
    · -- Case A < E: use phase_lt
      -- e+1 > a+1, so e ≥ a+1, so e = a+1+G for some G
      -- Also hinv: e+1 ≤ 2(a+1), so G+1 ≤ a+1, i.e. G ≤ a
      obtain ⟨G, hG⟩ := Nat.exists_eq_add_of_le (show (a + 1) + 1 ≤ e + 1 from hgt)
      -- e + 1 = a + 1 + 1 + G, so e = a + 1 + G
      have := phase_lt (a + 1) G (by omega)
      rw [show (0 : ℕ) + 1 = 1 from by ring,
          show a + 1 + 1 + G = e + 1 from by omega,
          show 2 * (a + 1) + G + 3 = a + e + 4 from by omega,
          show 3 * (a + 1) + 3 * G + 4 = 3 * e + 4 from by omega] at this
      exact this
  -- R4 drain
  have hR4 : ⟨a + e + 4, 0, 0, 3 * e + 4, 0⟩ [fm]⊢*
      ⟨a + e + 4, 0, 0, 0, 3 * e + 4⟩ := by
    rw [show 3 * e + 4 = 0 + (3 * e + 4) from by ring,
        show (0 : ℕ) = 0 + 0 from by ring]
    rw [show (0 : ℕ) + 0 + (3 * e + 4) = 0 + (3 * e + 4) from by ring]
    exact r4_chain (3 * e + 4) (a + e + 4) 0 0
  exact stepPlus_stepStar_stepPlus hR5 (stepStar_trans hPhase hR4)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 2, 0, 0, 0, e + 1⟩ ∧ e + 1 ≤ 2 * (a + 1))
  · intro c ⟨a, e, hc, hinv⟩
    subst hc
    exact ⟨⟨a + e + 4, 0, 0, 0, 3 * e + 4⟩,
      ⟨a + e + 2, 3 * e + 3, rfl, by omega⟩, main_trans a e hinv⟩
  · exact ⟨0, 0, rfl, by omega⟩
