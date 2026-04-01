import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1408: [7/15, 11/3, 18/77, 5/121, 147/2]

Vector representation:
```
 0 -1 -1  1  0
 0 -1  0  0  1
 1  2  0 -1 -1
 0  0  1  0 -2
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1408

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

-- R3R2R2 chain: each round a+=1, d-=1, e+=1
theorem r3r2r2_chain : ∀ k, ∀ a d e,
    ⟨a, 0, 0, d + k, e + 1⟩ [fm]⊢* ⟨a + k, 0, 0, d, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) d (e + 1))
    ring_nf; finish

-- R4 chain: removes pairs from e, adds to c
theorem r4_chain : ∀ k, ∀ a c e,
    ⟨a, 0, c, 0, e + 2 * k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e)
    ring_nf; finish

-- c-drain via R5+R1 pairs
theorem c_drain : ∀ k, ∀ a d,
    ⟨a + k, 0, k, d, 0⟩ [fm]⊢* ⟨a, 0, 0, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (d + 3))
    ring_nf; finish

-- Odd-e cascade: (A+(y+3), 0, y+3, 0, 1) ⊢* (A+3, 0, 0, 3*y+4, 0)
-- After R5,R1,R3,R1,R1 we reach (A+y+3, 0, y, 4, 0), then c_drain y.
theorem odd_cascade : ∀ y, ∀ A,
    ⟨A + (y + 3), 0, y + 3, 0, 1⟩ [fm]⊢* ⟨A + 3, 0, 0, 3 * y + 4, 0⟩ := by
  intro y A
  rw [show A + (y + 3) = (A + (y + 2)) + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm
  rw [show A + (y + 2) + 1 = (A + 3) + y from by ring]
  apply stepStar_trans (c_drain y (A + 3) 4)
  ring_nf; finish

-- d odd: (a+1, 0, 0, 2*m+5, 0) ⊢⁺ (a+m+3, 0, 0, 3*m+12, 0)
theorem trans_odd (a m : ℕ) :
    ⟨a + 1, 0, 0, 2 * m + 5, 0⟩ [fm]⊢⁺ ⟨a + m + 3, 0, 0, 3 * m + 12, 0⟩ := by
  -- R5+R2
  step fm; step fm
  -- R3R2R2 chain (2m+7) rounds
  rw [show 2 * m + 5 + 2 = 0 + (2 * m + 7) from by ring,
      show (0 : ℕ) = 0 + 0 from by ring]
  apply stepStar_trans (r3r2r2_chain (2 * m + 7) a 0 0)
  -- (a+2m+7, 0, 0, 0, 2m+8). R4 (m+4) rounds: e = 0 + 2*(m+4)
  rw [show 0 + (2 * m + 7) + 1 = 0 + 2 * (m + 4) from by ring]
  apply stepStar_trans (r4_chain (m + 4) (a + (2 * m + 7)) 0 0)
  -- (a+2m+7, 0, m+4, 0, 0). c_drain (m+4)
  rw [show a + (2 * m + 7) = (a + m + 3) + (m + 4) from by ring,
      show 0 + (m + 4) = m + 4 from by ring]
  apply stepStar_trans (c_drain (m + 4) (a + m + 3) 0)
  ring_nf; finish

-- d even: (a+1, 0, 0, 2*m+4, 0) ⊢⁺ (a+m+6, 0, 0, 3*m+4, 0)
theorem trans_even (a m : ℕ) :
    ⟨a + 1, 0, 0, 2 * m + 4, 0⟩ [fm]⊢⁺ ⟨a + m + 6, 0, 0, 3 * m + 4, 0⟩ := by
  -- R5+R2
  step fm; step fm
  -- R3R2R2 chain (2m+6) rounds
  rw [show 2 * m + 4 + 2 = 0 + (2 * m + 6) from by ring,
      show (0 : ℕ) = 0 + 0 from by ring]
  apply stepStar_trans (r3r2r2_chain (2 * m + 6) a 0 0)
  -- (a+2m+6, 0, 0, 0, 2m+7). R4 (m+3) rounds: e = 1 + 2*(m+3)
  rw [show 0 + (2 * m + 6) + 1 = 1 + 2 * (m + 3) from by ring]
  apply stepStar_trans (r4_chain (m + 3) (a + (2 * m + 6)) 0 1)
  -- (a+2m+6, 0, m+3, 0, 1). odd_cascade y=m, A=a+m+3.
  -- A+(y+3) = a+m+3+m+3 = a+2m+6. ✓
  rw [show 0 + (m + 3) = m + 3 from by ring,
      show m + 3 = m + 3 from rfl,
      show a + (2 * m + 6) = (a + m + 3) + (m + 3) from by ring]
  apply stepStar_trans (odd_cascade m (a + m + 3))
  ring_nf; finish

-- Main transition using parity of d (offset by 4).
-- Canonical: (a+1, 0, 0, d+4, 0).
-- Even d: d=2m, FM d = 2m+4. Next: (a+m+6, 0, 0, 3m+4, 0) = ((a+m+5)+1, 0, 0, (3m)+4, 0).
-- Odd d: d=2m+1, FM d = 2m+5. Next: (a+m+3, 0, 0, 3m+12, 0) = ((a+m+2)+1, 0, 0, (3m+8)+4, 0).
theorem main_trans (a d : ℕ) :
    ∃ a' d', (⟨a + 1, 0, 0, d + 4, 0⟩ : Q) [fm]⊢⁺ ⟨a' + 1, 0, 0, d' + 4, 0⟩ := by
  rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- d even: d = m + m
    subst hm
    rw [show m + m + 4 = 2 * m + 4 from by ring]
    exact ⟨a + m + 5, 3 * m, by
      rw [show (a + m + 5) + 1 = a + m + 6 from by ring,
          show 3 * m + 4 = 3 * m + 4 from rfl]
      exact trans_even a m⟩
  · -- d odd: d = 2 * m + 1
    subst hm
    rw [show 2 * m + 1 + 4 = 2 * m + 5 from by ring]
    exact ⟨a + m + 2, 3 * m + 8, by
      rw [show (a + m + 2) + 1 = a + m + 3 from by ring,
          show 3 * m + 8 + 4 = 3 * m + 12 from by ring]
      exact trans_odd a m⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 6, 0⟩)
  · execute fm 26
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = (⟨a + 1, 0, 0, d + 4, 0⟩ : Q))
  · intro c ⟨a, d, hc⟩
    subst hc
    obtain ⟨a', d', h⟩ := main_trans a d
    exact ⟨⟨a' + 1, 0, 0, d' + 4, 0⟩, ⟨a', d', rfl⟩, h⟩
  · exact ⟨1, 2, rfl⟩

end Sz22_2003_unofficial_1408
