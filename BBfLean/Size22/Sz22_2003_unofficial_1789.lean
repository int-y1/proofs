import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1789: [9/10, 44/21, 539/2, 5/11, 3/7]

Vector representation:
```
-1  2 -1  0  0
 2 -1  0 -1  1
-1  0  0  2  1
 0  0  1  0 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1789

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r3_chain : ∀ k d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (d + 2) (e + 1)); ring_nf; finish

theorem r4_chain : ∀ k e c d, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro e c d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih e (c + 1) d); ring_nf; finish

theorem spiral_chain : ∀ k b d e, ⟨0, b + 1, c + 2 * k, d + k, e⟩ [fm]⊢* ⟨0, b + 3 * k + 1, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show c + 2 * (k + 1) = c + 2 * k + 2 from by ring,
        show d + (k + 1) = d + k + 1 from by ring,
        show b + 1 = (b + 1 - 1) + 1 from by omega]
    step fm; step fm; step fm
    show ⟨0, b + 1 - 1 + 4, c + 2 * k, d + k, e + 1⟩ [fm]⊢* _
    rw [show b + 1 - 1 + 4 = (b + 3) + 1 from by omega]
    apply stepStar_trans (ih (b + 3) d (e + 1))
    rw [show b + 3 + 3 * k + 1 = b + 3 * (k + 1) + 1 from by ring,
        show e + 1 + k = e + (k + 1) from by ring]; finish

theorem r2_chain : ∀ k a b d e, ⟨a, b + k, 0, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 2) b d (e + 1)); ring_nf; finish

theorem r3_r2x2_chain : ∀ k a e, ⟨a + 1, 2 * k + 2, 0, 0, e⟩ [fm]⊢* ⟨a + 3 * k + 4, 0, 0, 0, e + 3 * k + 3⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · step fm; step fm; step fm; finish
  · rw [show 2 * (k + 1) + 2 = 2 * k + 2 + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) (e + 3)); ring_nf; finish

theorem main_trans (a e : ℕ) (hle : e ≤ 3 * a + 3) :
    ⟨a + 2, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨3 * a + 2 * e + 7, 0, 0, 0, 2 * a + 3 * e + 6⟩ := by
  -- Obtain K from parity
  rcases Nat.even_or_odd (a + e) with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- Even: a + e = K + K
    have hKb : K ≤ 2 * a + 2 := by omega
    -- R3 first step for stepPlus
    rw [show a + 2 = (a + 1) + 1 from by ring]
    step fm
    show ⟨a + 1, 0, 0, 2, e + 1⟩ [fm]⊢* _
    rw [show (a + 1 : ℕ) = 0 + (a + 1) from by ring]
    apply stepStar_trans (r3_chain (a + 1) (a := 0) 2 (e + 1))
    rw [show 2 + 2 * (a + 1) = 2 * a + 4 from by ring,
        show e + 1 + (a + 1) = 0 + (a + e + 2) from by ring]
    apply stepStar_trans (r4_chain (a + e + 2) 0 0 (2 * a + 4))
    rw [show 0 + (a + e + 2) = a + e + 2 from by ring,
        show (2 * a + 4 : ℕ) = (2 * a + 3) + 1 from by ring]
    step fm
    show ⟨0, 1, a + e + 2, 2 * a + 3, 0⟩ [fm]⊢* _
    -- Spiral chain (K+1 rounds)
    rw [show a + e + 2 = 0 + 2 * (K + 1) from by omega,
        show (2 * a + 3 : ℕ) = (2 * a + 2 - K) + (K + 1) from by omega]
    apply stepStar_trans (spiral_chain (K + 1) (c := 0) 0 (2 * a + 2 - K) 0)
    -- After spiral: (0, 3K+4, 0, 2a+2-K, K+1)
    -- Rewrite for R2 chain: b = rem + (2a+2-K), d = 0 + (2a+2-K)
    show ⟨0, 0 + 3 * (K + 1) + 1, 0, 2 * a + 2 - K, 0 + (K + 1)⟩ [fm]⊢* _
    simp only [Nat.zero_add]
    rw [show 3 * (K + 1) + 1 = 3 * K + 4 from by ring]
    -- Convert to r2_chain form: need d = 0 + (2a+2-K) form
    -- Set D = 2a+2-K as abbreviation
    -- R2 chain
    -- R2 chain with rem = 2e+2, D = 2a+2-K
    have r2_applied : ⟨0, (2 * e + 2) + (2 * a + 2 - K), 0, 0 + (2 * a + 2 - K), K + 1⟩ [fm]⊢*
        ⟨0 + 2 * (2 * a + 2 - K), 2 * e + 2, 0, 0, K + 1 + (2 * a + 2 - K)⟩ :=
      r2_chain (2 * a + 2 - K) 0 (2 * e + 2) 0 (K + 1)
    simp only [Nat.zero_add] at r2_applied
    rw [show (3 * K + 4 : ℕ) = (2 * e + 2) + (2 * a + 2 - K) from by omega]
    apply stepStar_trans r2_applied
    -- r3_r2x2 chain
    rw [show 2 * (2 * a + 2 - K) = (2 * (2 * a + 2 - K) - 1) + 1 from by omega,
        show (2 * e + 2 : ℕ) = 2 * e + 2 from rfl]
    apply stepStar_trans (r3_r2x2_chain e (2 * (2 * a + 2 - K) - 1) (K + 1 + (2 * a + 2 - K)))
    rw [show 2 * (2 * a + 2 - K) - 1 + 3 * e + 4 = 3 * a + 2 * e + 7 from by omega,
        show K + 1 + (2 * a + 2 - K) + 3 * e + 3 = 2 * a + 3 * e + 6 from by omega]
    finish
  · -- Odd: a + e = 2 * K + 1
    have hKb : K ≤ 2 * a + 1 := by omega
    rw [show a + 2 = (a + 1) + 1 from by ring]
    step fm
    show ⟨a + 1, 0, 0, 2, e + 1⟩ [fm]⊢* _
    rw [show (a + 1 : ℕ) = 0 + (a + 1) from by ring]
    apply stepStar_trans (r3_chain (a + 1) (a := 0) 2 (e + 1))
    rw [show 2 + 2 * (a + 1) = 2 * a + 4 from by ring,
        show e + 1 + (a + 1) = 0 + (a + e + 2) from by ring]
    apply stepStar_trans (r4_chain (a + e + 2) 0 0 (2 * a + 4))
    rw [show 0 + (a + e + 2) = a + e + 2 from by ring,
        show (2 * a + 4 : ℕ) = (2 * a + 3) + 1 from by ring]
    step fm
    show ⟨0, 1, a + e + 2, 2 * a + 3, 0⟩ [fm]⊢* _
    -- Spiral chain (K+1 rounds), leaving c = 1
    rw [show a + e + 2 = 1 + 2 * (K + 1) from by omega,
        show (2 * a + 3 : ℕ) = (2 * a + 2 - K) + (K + 1) from by omega]
    apply stepStar_trans (spiral_chain (K + 1) (c := 1) 0 (2 * a + 2 - K) 0)
    show ⟨0, 0 + 3 * (K + 1) + 1, 1, 2 * a + 2 - K, 0 + (K + 1)⟩ [fm]⊢* _
    simp only [Nat.zero_add]
    rw [show 3 * (K + 1) + 1 = 3 * K + 4 from by ring]
    -- Spiral tail: R2+R1 (c=1)
    rw [show (2 * a + 2 - K : ℕ) = (2 * a + 1 - K) + 1 from by omega,
        show (3 * K + 4 : ℕ) = (3 * K + 3) + 1 from by ring]
    step fm; step fm
    show ⟨1, 3 * K + 3 + 2, 0, 2 * a + 1 - K, K + 1 + 1⟩ [fm]⊢* _
    rw [show 3 * K + 3 + 2 = 3 * K + 5 from by ring,
        show K + 1 + 1 = K + 2 from by ring]
    -- R2 chain to drain d
    -- R2 chain with rem = 2e+2, D = 2a+1-K
    have r2_applied : ⟨1, (2 * e + 2) + (2 * a + 1 - K), 0, 0 + (2 * a + 1 - K), K + 2⟩ [fm]⊢*
        ⟨1 + 2 * (2 * a + 1 - K), 2 * e + 2, 0, 0, K + 2 + (2 * a + 1 - K)⟩ :=
      r2_chain (2 * a + 1 - K) 1 (2 * e + 2) 0 (K + 2)
    simp only [Nat.zero_add] at r2_applied
    rw [show (3 * K + 5 : ℕ) = (2 * e + 2) + (2 * a + 1 - K) from by omega]
    apply stepStar_trans r2_applied
    -- r3_r2x2 chain
    rw [show 1 + 2 * (2 * a + 1 - K) = (2 * (2 * a + 1 - K)) + 1 from by omega,
        show (2 * e + 2 : ℕ) = 2 * e + 2 from rfl]
    apply stepStar_trans (r3_r2x2_chain e (2 * (2 * a + 1 - K)) (K + 2 + (2 * a + 1 - K)))
    rw [show 2 * (2 * a + 1 - K) + 3 * e + 4 = 3 * a + 2 * e + 7 from by omega,
        show K + 2 + (2 * a + 1 - K) + 3 * e + 3 = 2 * a + 3 * e + 6 from by omega]
    finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 4⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 2, 0, 0, 0, e⟩ ∧ e ≤ 3 * a + 3)
  · intro c ⟨a, e, hq, hle⟩
    subst hq
    exact ⟨⟨3 * a + 2 * e + 7, 0, 0, 0, 2 * a + 3 * e + 6⟩,
      ⟨3 * a + 2 * e + 5, 2 * a + 3 * e + 6, rfl, by omega⟩, main_trans a e hle⟩
  · exact ⟨2, 4, rfl, by omega⟩
