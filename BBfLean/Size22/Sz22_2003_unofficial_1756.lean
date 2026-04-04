import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1756: [9/10, 2/21, 539/2, 5/7, 28/11]

Vector representation:
```
-1  2 -1  0  0
 1 -1  0 -1  0
-1  0  0  2  1
 0  0  1 -1  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1756

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

theorem d_to_c (d e : ℕ) : ∀ k, ∀ c, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · rw [show d + (k + 1) = d + k + 1 from by ring]; step fm
    rw [show c + (k + 1) = (c + 1) + k from by ring]; exact ih (c + 1)

theorem loop5 : ∀ k, ∀ b c e, ⟨0, b, c + 3 * k, 0, e + k⟩ [fm]⊢* ⟨0, b + 5 * k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show c + 3 * (k + 1) = c + 3 * k + 3 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    step fm; step fm; step fm; step fm; step fm
    rw [show b + 5 * (k + 1) = (b + 5) + 5 * k from by ring]; exact ih (b + 5) c e

theorem tail_c2 : ⟨0, b, 2, 0, e + 1⟩ [fm]⊢* ⟨1, b + 3, 0, 0, e⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem tail_c1 : ⟨0, b, 1, 0, e + 1⟩ [fm]⊢* ⟨2, b + 1, 0, 0, e⟩ := by
  step fm; step fm; step fm; finish

theorem r3r2r2 : ∀ k, ∀ a b e, ⟨a + 1, b + 2 * k, 0, 0, e⟩ [fm]⊢* ⟨a + 1 + k, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + 2 * (k + 1) = b + 2 * k + 2 from by ring]
    step fm; step fm; step fm
    rw [show a + 1 + (k + 1) = (a + 1) + 1 + k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    exact ih (a + 1) b (e + 1)

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]; step fm
    rw [show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    exact ih a (d + 2) (e + 1)

theorem b1_tail : ⟨a + 1, 1, 0, 0, e⟩ [fm]⊢* ⟨a + 1, 0, 0, 1, e + 1⟩ := by
  step fm; step fm; finish

theorem even_drain : ⟨a + 1, 2 * k, 0, 0, e⟩ [fm]⊢*
    ⟨0, 0, 0, 2 * (a + 1 + k), e + (a + 1) + 2 * k⟩ := by
  rw [show 2 * k = 0 + 2 * k from by ring]
  apply stepStar_trans (r3r2r2 k a 0 e)
  rw [show a + 1 + k = 0 + (a + 1 + k) from by ring]
  apply stepStar_trans (r3_chain (a + 1 + k) 0 0 (e + k))
  ring_nf; finish

theorem odd_drain : ⟨a + 1, 2 * k + 1, 0, 0, e⟩ [fm]⊢*
    ⟨0, 0, 0, 2 * (a + 1 + k) + 1, e + (a + 1) + (2 * k + 1)⟩ := by
  rw [show 2 * k + 1 = 1 + 2 * k from by ring]
  apply stepStar_trans (r3r2r2 k a 1 e)
  rw [show a + 1 + k = a + k + 1 from by ring]
  apply stepStar_trans (b1_tail (a := a + k) (e := e + k))
  rw [show a + k + 1 = 0 + (a + k + 1) from by ring]
  apply stepStar_trans (r3_chain (a + k + 1) 0 1 (e + k + 1))
  ring_nf; finish

theorem full_drain : ∀ B, ⟨A + 1, B, 0, 0, E⟩ [fm]⊢*
    ⟨0, 0, 0, 2 * (A + 1) + B, E + (A + 1) + B⟩ := by
  intro B
  rcases Nat.even_or_odd B with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    have := even_drain (a := A) (k := k) (e := E)
    convert this using 1; ring_nf
  · subst hk
    have := odd_drain (a := A) (k := k) (e := E)
    convert this using 1; ring_nf

theorem a0_entry : ⟨0, b + 1, 0, 0, e + 1⟩ [fm]⊢* ⟨3, b, 0, 0, e⟩ := by
  step fm; step fm; finish

theorem a0_drain : ∀ B, ⟨0, B + 1, 0, 0, E + 1⟩ [fm]⊢* ⟨0, 0, 0, B + 6, E + B + 3⟩ := by
  intro B
  apply stepStar_trans (a0_entry (b := B) (e := E))
  have := full_drain B (A := 2) (E := E)
  convert this using 1; ring_nf

theorem phase2_r0 : ⟨0, 0, 3 * n, 0, E + n⟩ [fm]⊢* ⟨0, 5 * n, 0, 0, E⟩ := by
  rw [show 3 * n = 0 + 3 * n from by ring, show 5 * n = 0 + 5 * n from by ring]
  exact loop5 n 0 0 E

theorem phase2_r1 : ⟨0, 0, 3 * n + 1, 0, E + n + 1⟩ [fm]⊢* ⟨2, 5 * n + 1, 0, 0, E⟩ := by
  rw [show 3 * n + 1 = 1 + 3 * n from by ring, show E + n + 1 = (E + 1) + n from by ring]
  apply stepStar_trans (loop5 n 0 1 (E + 1))
  rw [show (0 : ℕ) + 5 * n = 5 * n from by ring]; exact tail_c1

theorem phase2_r2 : ⟨0, 0, 3 * n + 2, 0, E + n + 1⟩ [fm]⊢* ⟨1, 5 * n + 3, 0, 0, E⟩ := by
  rw [show 3 * n + 2 = 2 + 3 * n from by ring, show E + n + 1 = (E + 1) + n from by ring]
  apply stepStar_trans (loop5 n 0 2 (E + 1))
  rw [show (0 : ℕ) + 5 * n = 5 * n from by ring]; exact tail_c2

theorem trans_mod0 :
    ⟨0, 0, 0, 3 * (m + 2), G + m + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 5 * m + 15, G + 5 * m + 12⟩ := by
  rw [show 3 * (m + 2) = (3 * m + 5) + 1 from by ring]; step fm
  rw [show 3 * m + 5 = 0 + (3 * m + 5) from by ring]
  apply stepStar_trans (d_to_c 0 (G + m + 3) (3 * m + 5) 1)
  rw [show 1 + (3 * m + 5) = 3 * (m + 2) from by ring,
      show G + m + 3 = (G + 1) + (m + 2) from by ring]
  apply stepStar_trans (phase2_r0 (n := m + 2) (E := G + 1))
  rw [show 5 * (m + 2) = (5 * m + 9) + 1 from by ring]
  apply stepStar_trans (a0_drain (5 * m + 9) (E := G))
  ring_nf; finish

theorem trans_mod1 :
    ⟨0, 0, 0, 3 * (p + 2) + 1, G + p + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 5 * p + 15, G + 5 * p + 13⟩ := by
  rw [show 3 * (p + 2) + 1 = (3 * p + 6) + 1 from by ring]; step fm
  rw [show 3 * p + 6 = 0 + (3 * p + 6) from by ring]
  apply stepStar_trans (d_to_c 0 (G + p + 3) (3 * p + 6) 1)
  rw [show 1 + (3 * p + 6) = 3 * (p + 2) + 1 from by ring,
      show G + p + 3 = G + (p + 2) + 1 from by ring]
  apply stepStar_trans (phase2_r1 (n := p + 2) (E := G))
  have := full_drain (5 * (p + 2) + 1) (A := 1) (E := G)
  convert this using 1; ring_nf

theorem trans_mod2 :
    ⟨0, 0, 0, 3 * (n + 1) + 2, G + n + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 5 * n + 10, G + 5 * n + 9⟩ := by
  rw [show 3 * (n + 1) + 2 = (3 * n + 4) + 1 from by ring]; step fm
  rw [show 3 * n + 4 = 0 + (3 * n + 4) from by ring]
  apply stepStar_trans (d_to_c 0 (G + n + 2) (3 * n + 4) 1)
  rw [show 1 + (3 * n + 4) = 3 * (n + 1) + 2 from by ring,
      show G + n + 2 = G + (n + 1) + 1 from by ring]
  apply stepStar_trans (phase2_r2 (n := n + 1) (E := G))
  have := full_drain (5 * (n + 1) + 3) (A := 0) (E := G)
  convert this using 1; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 5, 4⟩) (by execute fm 14)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ D ≥ 5 ∧ E ≥ D - 1)
  · intro c ⟨D, E, hq, hD, hE⟩; subst hq
    obtain ⟨r, q, rfl | rfl | rfl⟩ : ∃ r q, D = 3 * q ∨ D = 3 * q + 1 ∨ D = 3 * q + 2 :=
      ⟨D % 3, D / 3, by omega⟩
    · obtain ⟨m, rfl⟩ : ∃ m, q = m + 2 := ⟨q - 2, by omega⟩
      obtain ⟨G, rfl⟩ : ∃ G, E = G + m + 3 := ⟨E - m - 3, by omega⟩
      exact ⟨⟨0, 0, 0, 5 * m + 15, G + 5 * m + 12⟩,
        ⟨5 * m + 15, G + 5 * m + 12, rfl, by omega, by omega⟩, trans_mod0⟩
    · obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
      obtain ⟨G, rfl⟩ : ∃ G, E = G + p + 3 := ⟨E - p - 3, by omega⟩
      exact ⟨⟨0, 0, 0, 5 * p + 15, G + 5 * p + 13⟩,
        ⟨5 * p + 15, G + 5 * p + 13, rfl, by omega, by omega⟩, trans_mod1⟩
    · obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
      obtain ⟨G, rfl⟩ : ∃ G, E = G + n + 2 := ⟨E - n - 2, by omega⟩
      exact ⟨⟨0, 0, 0, 5 * n + 10, G + 5 * n + 9⟩,
        ⟨5 * n + 10, G + 5 * n + 9, rfl, by omega, by omega⟩, trans_mod2⟩
  · exact ⟨5, 4, rfl, by omega, by omega⟩
