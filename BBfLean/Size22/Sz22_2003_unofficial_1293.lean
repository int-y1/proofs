import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1293: [63/10, 12/77, 121/2, 5/3, 7/11]

Vector representation:
```
-1  2 -1  1  0
 2  1  0 -1 -1
-1  0  0  0  2
 0 -1  1  0  0
 0  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1293

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R3 drain: a → e (c=0, d=0)
theorem r3_drain : ∀ k b e, ⟨k, b, 0, 0, e⟩ [fm]⊢* ⟨0, b, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    step fm; exact ih b (e + 2)

-- R4 drain: b → c (a=0, d=0)
theorem r4_drain : ∀ k c e, ⟨0, k, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm; apply stepStar_trans (ih (c + 1) e); ring_nf; finish

-- R2 chain: d,e → a,b (c=0)
theorem r2_chain : ∀ k a b d e, ⟨a, b, 0, d + k, e + k⟩ [fm]⊢* ⟨a + 2 * k, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 2) (b + 1) d e); ring_nf; finish

-- Interleaved R2,R1,R1 round chain
theorem interleaved : ∀ k b c d e,
    ⟨0, b, c + 2 * k, d + 1, e + k⟩ [fm]⊢* ⟨0, b + 5 * k, c, d + k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 5) c (d + 1) e); ring_nf; finish

-- Tail: (a+1, B, 0, D, 0) →* (0, 0, B+D, 0, 2a+3D+2)
theorem tail_e_zero : ∀ D, ∀ a B,
    ⟨a + 1, B, 0, D, 0⟩ [fm]⊢* ⟨0, 0, B + D, 0, 2 * a + 3 * D + 2⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ihD; intro a B
  rcases D with _ | _ | D
  · -- D=0
    apply stepStar_trans (r3_drain (a + 1) B 0)
    apply stepStar_trans (r4_drain B 0 (0 + 2 * (a + 1)))
    ring_nf; finish
  · -- D=1
    step fm; step fm
    apply stepStar_trans (r3_drain (a + 2) (B + 1) 1)
    apply stepStar_trans (r4_drain (B + 1) 0 (1 + 2 * (a + 2)))
    ring_nf; finish
  · -- D+2: R3, R2, R2, then IH with D
    step fm; step fm; step fm
    rw [show a + 1 + 1 + 2 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ihD D (by omega) (a + 3) (B + 1 + 1))
    ring_nf; finish

-- Full tail: (a, B, 0, D+1, E+1) →* (0, 0, B+D+1, 0, 2a+E+3D+4)
theorem full_tail : ∀ D E a B,
    ⟨a, B, 0, D + 1, E + 1⟩ [fm]⊢* ⟨0, 0, B + D + 1, 0, 2 * a + E + 3 * D + 4⟩ := by
  intro D; induction' D with D ihD
  · -- D=0: R2, r3_drain, r4_drain
    intro E a B; step fm
    apply stepStar_trans (r3_drain (a + 2) (B + 1) E)
    apply stepStar_trans (r4_drain (B + 1) 0 (E + 2 * (a + 2)))
    ring_nf; finish
  · intro E; rcases E with _ | E
    · -- E=0: R2, then tail_e_zero
      intro a B; step fm
      rw [show a + 2 = (a + 1) + 1 from by ring]
      apply stepStar_trans (tail_e_zero (D + 1) (a + 1) (B + 1))
      ring_nf; finish
    · -- E≥1: R2, then ihD
      intro a B; step fm
      rw [show D + 1 = D + 1 from rfl,
          show E + 1 = E + 1 from rfl]
      apply stepStar_trans (ihD E (a + 2) (B + 1))
      ring_nf; finish

-- c=0, e≥3
theorem trans_c0 (e : ℕ) :
    ⟨0, 0, 0, 0, e + 3⟩ [fm]⊢⁺ ⟨0, 0, 1, 0, e + 5⟩ := by
  rw [show e + 3 = (e + 1) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (r3_drain 2 1 (e + 1))
  apply stepStar_trans (r4_drain 1 0 ((e + 1) + 2 * 2))
  ring_nf; finish

-- c=1, e≥3
theorem trans_c1 (e : ℕ) :
    ⟨0, 0, 1, 0, e + 3⟩ [fm]⊢⁺ ⟨0, 0, 4, 0, e + 6⟩ := by
  rw [show e + 3 = (e + 1) + 2 from by ring]
  step fm; step fm; step fm
  rw [show e + 1 = e + 1 from rfl]
  step fm
  apply stepStar_trans (r3_drain 3 4 e)
  apply stepStar_trans (r4_drain 4 0 (e + 2 * 3))
  ring_nf; finish

-- c = 2m+2 (even ≥ 2), e ≥ m+3
theorem trans_even (m : ℕ) (e : ℕ) :
    ⟨0, 0, 2 * m + 2, 0, e + m + 3⟩ [fm]⊢⁺ ⟨0, 0, 6 * m + 7, 0, e + 3 * m + 7⟩ := by
  rw [show e + m + 3 = (e + m + 1) + 2 from by ring]
  step fm; step fm
  rw [show 2 * m + 2 = (2 * m) + 2 from by ring]
  step fm; step fm
  rw [show 2 * m = 0 + 2 * m from by ring,
      show e + m + 1 = (e + 1) + m from by ring]
  apply stepStar_trans (interleaved m 5 0 1 (e + 1))
  rw [show 5 + 5 * m = 5 * m + 5 from by ring,
      show 1 + m + 1 = (m + 1) + 1 from by ring,
      show e + 1 = (e) + 1 from rfl]
  apply stepStar_trans (full_tail (m + 1) e 0 (5 * m + 5))
  ring_nf; finish

-- c = 2m+3 (odd ≥ 3), e ≥ m+3
theorem trans_odd (m : ℕ) (e : ℕ) :
    ⟨0, 0, 2 * m + 3, 0, e + m + 3⟩ [fm]⊢⁺ ⟨0, 0, 6 * m + 10, 0, e + 3 * m + 8⟩ := by
  rw [show e + m + 3 = (e + m + 1) + 2 from by ring]
  step fm; step fm
  rw [show 2 * m + 3 = (2 * m + 1) + 2 from by ring]
  step fm; step fm
  rw [show 2 * m + 1 = 1 + 2 * m from by ring,
      show e + m + 1 = (e + 1) + m from by ring]
  apply stepStar_trans (interleaved m 5 1 1 (e + 1))
  rw [show 5 + 5 * m = 5 * m + 5 from by ring,
      show 1 + m + 1 = (m + 1) + 1 from by ring]
  step fm
  rw [show 5 * m + 5 + 1 = 5 * m + 6 from by ring]
  step fm
  rw [show 5 * m + 6 + 2 = 5 * m + 8 from by ring,
      show (m + 1) + 1 = m + 2 from by ring]
  rcases e with _ | e
  · -- e=0: tail_e_zero
    apply stepStar_trans (tail_e_zero (m + 2) 0 (5 * m + 8))
    ring_nf; finish
  · -- e≥1: full_tail
    rw [show m + 2 = (m + 1) + 1 from by ring,
        show e + 1 = e + 1 from rfl]
    apply stepStar_trans (full_tail (m + 1) e 1 (5 * m + 8))
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 4⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c, 0, e⟩ ∧ 2 * e ≥ c + 5)
  · intro q ⟨c, e, hq, he⟩; subst hq
    refine ⟨⟨0, 0, 3 * c + 1, 0, c + e + 2⟩, ⟨3 * c + 1, c + e + 2, rfl, by omega⟩, ?_⟩
    rcases c with _ | _ | c
    · -- c=0: e ≥ 3
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 3 := ⟨e - 3, by omega⟩
      convert trans_c0 e' using 2; ring_nf
    · -- c=1: e ≥ 3
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 3 := ⟨e - 3, by omega⟩
      convert trans_c1 e' using 2; ring_nf
    · -- c+2: split even/odd
      rcases Nat.even_or_odd c with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- c even = 2m: c+2 = 2m+2
        subst hm
        rw [show m + m + 2 = 2 * m + 2 from by ring]
        obtain ⟨e', rfl⟩ : ∃ e', e = e' + m + 3 := ⟨e - m - 3, by omega⟩
        convert trans_even m e' using 2; ring_nf
      · -- c odd = 2m+1: c+2 = 2m+3
        subst hm
        rw [show 2 * m + 1 + 2 = 2 * m + 3 from by ring]
        obtain ⟨e', rfl⟩ : ∃ e', e = e' + m + 3 := ⟨e - m - 3, by omega⟩
        convert trans_odd m e' using 2; ring_nf
  · exact ⟨1, 4, rfl, by omega⟩

end Sz22_2003_unofficial_1293
