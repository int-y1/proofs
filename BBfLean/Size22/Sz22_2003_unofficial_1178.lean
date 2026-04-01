import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1178: [5/6, 49/2, 44/35, 3/11, 5/7, 1/5]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  1
 0  1  0  0 -1
 0  0  1 -1  0
 0  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1178

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | _ => none

-- R4 chain: move e to b when a=0, c=0.
theorem e_to_b_aux : ∀ k b, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · intro b; exists 0
  · intro b
    rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

theorem e_to_b (k : ℕ) (hE : E = e + k) (hB : B = b + k) :
    ⟨0, b, 0, d, E⟩ [fm]⊢* ⟨0, B, 0, d, e⟩ := by
  subst hE; subst hB; exact e_to_b_aux k b

-- R3+R2+R2 chain: when a=0, b=0.
theorem r3r2r2_chain_aux : ∀ k c d e, ⟨0, 0, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 3 * k + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih c (d + 3) (e + 1))
    ring_nf; finish

theorem r3r2r2_chain (k : ℕ) (hc : C = c + k) (hd : D = d + 1) :
    ⟨0, 0, C, D, e⟩ [fm]⊢* ⟨0, 0, c, d + 3 * k + 1, e + k⟩ := by
  subst hc; subst hd; exact r3r2r2_chain_aux k c d e

-- Drain pairs: R3+R1+R1 repeated k times, reducing b by 2 each time.
theorem drain_pairs : ∀ k n c d e, ⟨0, n + 2 * k, c + 1, d + k, e⟩ [fm]⊢* ⟨0, n, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro n c d e
  · exists 0
  · rw [show n + 2 * (k + 1) = (n + 2 * k + 1) + 1 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih n (c + 1) d (e + 1))
    ring_nf; finish

-- Odd tail: when b=1, do R3+R1+R2 to get b=0.
theorem odd_tail : ⟨0, 1, c + 1, d + 1, e⟩ [fm]⊢* ⟨0, 0, c + 1, d + 2, e + 1⟩ := by
  step fm; step fm; step fm; finish

-- Even: compose all phases. (0, 2k, 0, d'+k+2, 0) →⁺ (0, 2k+1, 0, d'+3k+4, 0)
theorem even_trans (k d' : ℕ) :
    ⟨0, 2 * k, 0, d' + k + 2, 0⟩ [fm]⊢⁺ ⟨0, 2 * k + 1, 0, d' + 3 * k + 4, 0⟩ := by
  rw [show d' + k + 2 = (d' + k + 1) + 1 from by ring,
      show 2 * k = 0 + 2 * k from by ring,
      show (0 : ℕ) = 0 + 0 from by ring]
  step fm
  rw [show d' + k + 1 = (d' + 1) + k from by ring]
  apply stepStar_trans (drain_pairs k 0 0 (d' + 1) 0)
  apply stepStar_trans (r3r2r2_chain (c := 0) (d := d') (k + 1) (by ring) (by ring) (e := 0 + k))
  rw [show d' + 3 * (k + 1) + 1 = d' + 3 * k + 4 from by ring]
  exact e_to_b (b := 0) (e := 0) (2 * k + 1) (by ring) (by ring) (d := d' + 3 * k + 4)

-- Odd: compose all phases. (0, 2k+1, 0, d'+k+2, 0) →⁺ (0, 2k+2, 0, d'+3k+5, 0)
theorem odd_trans (k d' : ℕ) :
    ⟨0, 2 * k + 1, 0, d' + k + 2, 0⟩ [fm]⊢⁺ ⟨0, 2 * k + 2, 0, d' + 3 * k + 5, 0⟩ := by
  rw [show d' + k + 2 = (d' + k + 1) + 1 from by ring,
      show 2 * k + 1 = 1 + 2 * k from by ring,
      show (0 : ℕ) = 0 + 0 from by ring]
  step fm
  rw [show d' + k + 1 = (d' + 1) + k from by ring]
  apply stepStar_trans (drain_pairs k 1 0 (d' + 1) 0)
  rw [show 0 + k + 1 = k + 1 from by ring,
      show 0 + k = k from by ring]
  apply stepStar_trans (odd_tail (c := k) (d := d') (e := k))
  apply stepStar_trans (r3r2r2_chain (c := 0) (d := d' + 1) (k + 1) (by ring) (by ring) (e := k + 1))
  rw [show (d' + 1) + 3 * (k + 1) + 1 = d' + 3 * k + 5 from by ring]
  exact e_to_b (b := 0) (e := 0) (2 * k + 2) (by ring) (by ring) (d := d' + 3 * k + 5)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n d, q = ⟨0, n, 0, d, 0⟩ ∧ d ≥ n + 2)
  · intro c ⟨n, d, hq, hd⟩; subst hq
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [show k + k = 2 * k from by ring] at hk; subst hk
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + k + 2 := ⟨d - k - 2, by omega⟩
      exact ⟨⟨0, 2 * k + 1, 0, d' + 3 * k + 4, 0⟩,
        ⟨2 * k + 1, d' + 3 * k + 4, rfl, by omega⟩,
        even_trans k d'⟩
    · subst hk
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + k + 2 := ⟨d - k - 2, by omega⟩
      exact ⟨⟨0, 2 * k + 2, 0, d' + 3 * k + 5, 0⟩,
        ⟨2 * k + 2, d' + 3 * k + 5, rfl, by omega⟩,
        odd_trans k d'⟩
  · exact ⟨0, 2, rfl, by omega⟩
