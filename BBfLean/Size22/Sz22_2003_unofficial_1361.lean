import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1361: [63/10, 4/33, 143/2, 5/7, 14/13]

Vector representation:
```
-1  2 -1  1  0  0
 2 -1  0  0 -1  0
-1  0  0  0  1  1
 0  0  1 -1  0  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1361

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

-- R3 chain: drain a into e and f
theorem a_to_ef : ∀ k d e f,
    ⟨k, (0:ℕ), (0:ℕ), d, e, f⟩ [fm]⊢* ⟨(0:ℕ), (0:ℕ), (0:ℕ), d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]; step fm
    apply stepStar_trans (ih d (e + 1) (f + 1)); ring_nf; finish

-- R4 transfer: d to c
theorem d_to_c : ∀ k c d e f,
    ⟨(0:ℕ), (0:ℕ), c, d + k, e, f⟩ [fm]⊢* ⟨(0:ℕ), (0:ℕ), c + k, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (c + 1) d e f); ring_nf; finish

-- R2 chain: drain b (when c=0, so R1 doesn't fire; R2 has priority over R3)
theorem r2_drain : ∀ k a b d e f,
    ⟨a, b + k, (0:ℕ), d, e + k, f⟩ [fm]⊢* ⟨a + 2 * k, b, (0:ℕ), d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a b d e f
  · simp; exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) b d e f); ring_nf; finish

-- R2,R1,R1 chain: each round consumes 2 from c, adds 3 to b, 2 to d, 1 from e
theorem r211_chain : ∀ k b c d e f,
    ⟨(0:ℕ), b + 1, c + 2 * k, d, e + k + 1, f⟩ [fm]⊢*
    ⟨(0:ℕ), b + 3 * k + 1, c, d + 2 * k, e + 1, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · simp; exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm; step fm; step fm
    rw [show b + 2 + 2 = (b + 3) + 1 from by ring]
    apply stepStar_trans (ih (b + 3) c (d + 2) e f); ring_nf; finish

-- Drain a and b when c=0: R2 drains b (with R3 intervening when e=0), then R3 drains a.
-- Result: e gains a+b+1, f gains a+2*b+1.
theorem drain_ab : ∀ b a d e f,
    ⟨a + 1, b, (0:ℕ), d, e, f⟩ [fm]⊢*
    ⟨(0:ℕ), (0:ℕ), (0:ℕ), d, e + a + b + 1, f + a + 2 * b + 1⟩ := by
  intro b; induction' b with b ih <;> intro a d e f
  · apply stepStar_trans (a_to_ef (a + 1) d e f); ring_nf; finish
  · rcases e with _ | e
    · -- e=0: R3 fires (a+1≥1, c=0 so no R1; b+1≥1 but e=0 so no R2), then R2 fires
      step fm; step fm
      apply stepStar_trans (ih (a + 1) d 0 (f + 1)); ring_nf; finish
    · -- e≥1: R2 fires (b+1≥1, e+1≥1, and R1 needs c≥1 which is 0)
      step fm
      apply stepStar_trans (ih (a + 2) d e f); ring_nf; finish

-- Even c transition: d = 2k+1, c = d-1 = 2k (even)
-- (0,0,0,2k+1,E,F) ⊢⁺ (0,0,0,2k+2,E+2k+2,F+6k+3) when E ≥ 4k+2, F ≥ 1
theorem main_even (k E' F' : ℕ) :
    ⟨(0:ℕ), (0:ℕ), (0:ℕ), 2*k+1, E'+4*k+2, F'+1⟩ [fm]⊢⁺
    ⟨(0:ℕ), (0:ℕ), (0:ℕ), 2*k+2, E'+6*k+4, F'+6*k+4⟩ := by
  -- d_to_c: (0,0,2k+1,0,E'+4k+2,F'+1)
  rw [show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (2*k+1) 0 0 (E'+4*k+2) (F'+1))
  rw [show 0 + (2 * k + 1) = 2 * k + 1 from by ring]
  -- R5: (1,0,2k+1,1,E'+4k+2,F')
  rw [show F' + 1 = F' + 1 from rfl]
  step fm
  -- R1: (0,2,2k,2,E'+4k+2,F')
  rw [show 2 * k + 1 = 2 * k + 1 from rfl]
  step fm
  -- State: (0, 2, 2k, 2, E'+4k+2, F')
  -- r211_chain: (0, 1+1, 0+2k, 2, (E'+3k+1)+k+1, F')
  rw [show (2:ℕ) = 1 + 1 from rfl,
      show 2 * k = 0 + 2 * k from by ring,
      show E' + 4 * k + 2 = (E' + 3 * k + 1) + k + 1 from by ring]
  apply stepStar_trans (r211_chain k 1 0 2 (E'+3*k+1) F')
  -- State: (0, 3k+2, 0, 2k+2, E'+3k+2, F')
  rw [show 1 + 3 * k + 1 = 0 + (3 * k + 2) from by ring,
      show 2 + 2 * k = 2 * k + 2 from by ring,
      show (E' + 3 * k + 1) + 1 = E' + (3 * k + 2) from by ring]
  -- r2_drain: (6k+4, 0, 0, 2k+2, E', F')
  apply stepStar_trans (r2_drain (3*k+2) 0 0 (2*k+2) E' F')
  rw [show 0 + 2 * (3 * k + 2) = 6 * k + 4 from by ring]
  -- a_to_ef: (0, 0, 0, 2k+2, E'+6k+4, F'+6k+4)
  apply stepStar_trans (a_to_ef (6*k+4) (2*k+2) E' F')
  ring_nf; finish

-- Odd c transition: d = 2k+2, c = d-1 = 2k+1 (odd)
-- (0,0,0,2k+2,E,F) ⊢⁺ (0,0,0,2k+3,E+2k+3,F+6k+6) when E ≥ 4k+4, F ≥ 1
theorem main_odd (k E' F' : ℕ) :
    ⟨(0:ℕ), (0:ℕ), (0:ℕ), 2*k+2, E'+4*k+4, F'+1⟩ [fm]⊢⁺
    ⟨(0:ℕ), (0:ℕ), (0:ℕ), 2*k+3, E'+6*k+7, F'+6*k+7⟩ := by
  -- d_to_c: (0,0,2k+2,0,E'+4k+4,F'+1)
  rw [show 2 * k + 2 = 0 + (2 * k + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (2*k+2) 0 0 (E'+4*k+4) (F'+1))
  rw [show 0 + (2 * k + 2) = 2 * k + 2 from by ring]
  -- R5: (1,0,2k+2,1,E'+4k+4,F')
  step fm
  -- R1: (0,2,2k+1,2,E'+4k+4,F')
  step fm
  -- r211_chain with k rounds: (0, 1+1, 1+2k, 2, (E'+3k+3)+k+1, F')
  rw [show (2:ℕ) = 1 + 1 from rfl,
      show 2 * k + 1 = 1 + 2 * k from by ring,
      show E' + 4 * k + 4 = (E' + 3 * k + 3) + k + 1 from by ring]
  apply stepStar_trans (r211_chain k 1 1 2 (E'+3*k+3) F')
  -- State: (0, 3k+2, 1, 2k+2, E'+3k+4, F')
  rw [show 1 + 3 * k + 1 = 3 * k + 2 from by ring,
      show 2 + 2 * k = 2 * k + 2 from by ring,
      show (E' + 3 * k + 3) + 1 = (E' + 3 * k + 3) + 1 from rfl]
  -- R2: needs b = 3k+2 ≥ 1 and e = E'+3k+4 ≥ 1
  rw [show 3 * k + 2 = (3 * k + 1) + 1 from by ring,
      show (E' + 3 * k + 3) + 1 = (E' + 3 * k + 3) + 1 from rfl]
  step fm
  -- State: (2, 3k+1, 1, 2k+2, E'+3k+3, F')
  -- R1: a=2≥1, c=1≥1
  step fm
  -- State: (1, 3k+3, 0, 2k+3, E'+3k+3, F')
  -- drain_ab with a=0, b=3k+3
  rw [show (1:ℕ) = 0 + 1 from by ring,
      show 3 * k + 1 + 2 = 3 * k + 3 from by ring]
  apply stepStar_trans (drain_ab (3*k+3) 0 (2*k+3) (E'+3*k+3) F')
  ring_nf; finish

-- Combined main transition
theorem main_trans (d E F : ℕ) (hd : d ≥ 2) (hE : E ≥ 2 * d) (hF : F ≥ 1) :
    ⟨(0:ℕ), (0:ℕ), (0:ℕ), d, E, F⟩ [fm]⊢⁺ ⟨(0:ℕ), (0:ℕ), (0:ℕ), d + 1, E + d + 1, F + 3 * d⟩ := by
  rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- d even: d = 2m, d-1 = 2m-1 (odd c)
    rw [show m + m = 2 * m from by ring] at hm; subst hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    obtain ⟨E', rfl⟩ : ∃ E', E = E' + 4 * k + 4 := ⟨E - (4 * k + 4), by omega⟩
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by ring,
        show E' + 4 * k + 4 + 2 * (k + 1) + 1 = E' + 6 * k + 7 from by ring,
        show (F' + 1) + 3 * (2 * (k + 1)) = F' + 6 * k + 7 from by ring]
    exact main_odd k E' F'
  · -- d odd: d = 2m+1, d-1 = 2m (even c)
    subst hm
    obtain ⟨E', rfl⟩ : ∃ E', E = E' + 4 * m + 2 := ⟨E - (4 * m + 2), by omega⟩
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
        show E' + 4 * m + 2 + (2 * m + 1) + 1 = E' + 6 * m + 4 from by ring,
        show (F' + 1) + 3 * (2 * m + 1) = F' + 6 * m + 4 from by ring]
    exact main_even m E' F'

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 4, 4⟩) (by execute fm 12)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e f, q = ⟨0, 0, 0, d, e, f⟩ ∧ d ≥ 2 ∧ e ≥ 2 * d ∧ f ≥ 1)
  · intro q ⟨d, e, f, hq, hd, hE, hF⟩
    subst hq
    exact ⟨⟨0, 0, 0, d + 1, e + d + 1, f + 3 * d⟩,
      ⟨d + 1, e + d + 1, f + 3 * d, rfl, by omega, by omega, by omega⟩,
      main_trans d e f hd hE hF⟩
  · exact ⟨2, 4, 4, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_1361
