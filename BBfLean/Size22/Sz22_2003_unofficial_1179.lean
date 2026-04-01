import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1179: [5/6, 49/2, 44/35, 3/11, 605/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  1
 0  1  0  0 -1
 0  0  1 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1179

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | _ => none

-- R4 repeated: move e to b.
theorem e_to_b : ∀ k b d, ⟨(0 : ℕ), b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- R1R1R3 chain: each round does R1, R1, R3.
theorem r1r1r3_chain : ∀ k, ∀ b c d e,
    ⟨(2 : ℕ), 2 * k + b, c, d + k, e⟩ [fm]⊢* ⟨2, b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · simp; exists 0
  · rw [show 2 * (k + 1) + b = (2 * k + b + 1) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show 2 * k + b + 1 = (2 * k + b) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih b (c + 1) d (e + 1))
    ring_nf; finish

-- R3R2R2 chain: each round does R3, R2, R2.
theorem r3r2r2_chain : ∀ k, ∀ d e,
    ⟨(0 : ℕ), 0, k, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * k + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · simp; exists 0
  · step fm
    step fm
    step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih (d + 3) (e + 1))
    ring_nf; finish

-- Even e transition: (0,0,0,d'+m+2,2m) →⁺ (0,0,0,d'+3m+4,2m+3)
theorem main_even (m d' : ℕ) :
    ⟨(0 : ℕ), 0, 0, d' + m + 2, 2 * m⟩ [fm]⊢⁺ ⟨0, 0, 0, d' + 3 * m + 4, 2 * m + 3⟩ := by
  -- Phase 1: e_to_b
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * m) 0 (d' + m + 2))
  rw [show (0 : ℕ) + 2 * m = 2 * m from by ring]
  -- Phase 2: R5+R3
  rw [show d' + m + 2 = (d' + m) + 2 from by ring]
  step fm; step fm
  -- Phase 3: r1r1r3 chain with k=m
  rw [show (2 * m : ℕ) = 2 * m + 0 from by ring,
      show d' + m = d' + m from rfl]
  apply stepStar_trans (r1r1r3_chain m 0 0 d' 3)
  rw [show (0 : ℕ) + m = m from by ring, show (3 : ℕ) + m = m + 3 from by ring]
  -- Phase 4: R2, R2
  step fm; step fm
  -- Phase 5: r3r2r2 chain with k=m
  rw [show d' + 4 = (d' + 3) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain m (d' + 3) (m + 3))
  ring_nf; finish

-- Odd e transition: (0,0,0,d'+m+3,2m+1) →⁺ (0,0,0,d'+3m+6,2m+4)
theorem main_odd (m d' : ℕ) :
    ⟨(0 : ℕ), 0, 0, d' + m + 3, 2 * m + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d' + 3 * m + 6, 2 * m + 4⟩ := by
  -- Phase 1: e_to_b
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * m + 1) 0 (d' + m + 3))
  rw [show (0 : ℕ) + (2 * m + 1) = 2 * m + 1 from by ring]
  -- Phase 2: R5+R3
  rw [show d' + m + 3 = (d' + m + 1) + 2 from by ring]
  step fm; step fm
  -- Phase 3: r1r1r3 chain with k=m, leaving b=1
  rw [show (2 * m + 1 : ℕ) = 2 * m + 1 from rfl,
      show d' + m + 1 = (d' + 1) + m from by ring]
  apply stepStar_trans (r1r1r3_chain m 1 0 (d' + 1) 3)
  rw [show (0 : ℕ) + m = m from by ring, show (3 : ℕ) + m = m + 3 from by ring]
  -- Phase 4: R1+R2
  step fm; step fm
  -- Phase 5: r3r2r2 chain with k=m+1
  rw [show d' + 1 + 2 = (d' + 2) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (m + 1) (d' + 2) (m + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 9, 6⟩) (by execute fm 21)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ e + 1 ∧ d ≥ 2 ∧ 3 ∣ e)
  · intro c ⟨d, e, hq, hde, hd2, hdiv⟩; subst hq
    rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- e even: e = 2m, and 3 ∣ 2m, so m = 3k for some k (since gcd(2,3)=1)
      rw [show m + m = 2 * m from by ring] at hm; subst hm
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + m + 2 := ⟨d - m - 2, by omega⟩
      refine ⟨⟨0, 0, 0, d' + 3 * m + 4, 2 * m + 3⟩,
        ⟨d' + 3 * m + 4, 2 * m + 3, rfl, by omega, by omega, ?_⟩,
        main_even m d'⟩
      obtain ⟨k, hk⟩ := hdiv
      exact ⟨k + 1, by omega⟩
    · -- e odd: e = 2m + 1, and 3 ∣ (2m+1)
      subst hm
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + m + 3 := ⟨d - m - 3, by omega⟩
      refine ⟨⟨0, 0, 0, d' + 3 * m + 6, 2 * m + 4⟩,
        ⟨d' + 3 * m + 6, 2 * m + 4, rfl, by omega, by omega, ?_⟩,
        main_odd m d'⟩
      obtain ⟨k, hk⟩ := hdiv
      exact ⟨k + 1, by omega⟩
  · exact ⟨9, 6, rfl, by omega, by omega, ⟨2, by omega⟩⟩

end Sz22_2003_unofficial_1179
