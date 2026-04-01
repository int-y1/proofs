import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1557: [7/45, 11/5, 50/77, 3/11, 245/2]

Vector representation:
```
 0 -2 -1  1  0
 0  0 -1  0  1
 1  0  2 -1 -1
 0  1  0  0 -1
-1  0  1  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1557

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+2, e⟩
  | _ => none

-- R5+R1 chain: each round a-=1, b-=2, d+=3.
theorem r5r1_chain : ∀ k a b d, ⟨a + k, b + 2 * k, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih
  · intro a b d; exists 0
  · intro a b d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a b (d + 3)); ring_nf; finish

-- R3+R2+R2 loop with b=0: each round a+=1, d-=1, e+=1.
theorem r3r2_b0 : ∀ k a d e, ⟨a, 0, 0, d + k, e + 1⟩ [fm]⊢* ⟨a + k, 0, 0, d, e + k + 1⟩ := by
  intro k; induction' k with k ih
  · intro a d e; exists 0
  · intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) d (e + 1)); ring_nf; finish

-- R3+R2+R2 loop with b=1: each round a+=1, d-=1, e+=1.
theorem r3r2_b1 : ∀ k a d e, ⟨a, 1, 0, d + k, e + 1⟩ [fm]⊢* ⟨a + k, 1, 0, d, e + k + 1⟩ := by
  intro k; induction' k with k ih
  · intro a d e; exists 0
  · intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) d (e + 1)); ring_nf; finish

-- R4 drain: transfer e to b.
theorem r4_drain : ∀ k a b e, ⟨a, b, 0, 0, e + k⟩ [fm]⊢* ⟨a, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a b e; exists 0
  · intro a b e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) e); ring_nf; finish

-- Even case: (F+K+2, 2K+2, 0, 0, 0) ⊢⁺ (F+3K+5, 3K+6, 0, 0, 0)
theorem main_even (F K : ℕ) :
    ⟨F + K + 2, 2 * K + 2, 0, 0, 0⟩ [fm]⊢⁺ ⟨F + 3 * K + 5, 3 * K + 6, 0, 0, 0⟩ := by
  -- R5+R1 chain: K+1 rounds, b goes from 2K+2 to 0, a decreases by K+1.
  rw [show F + K + 2 = (F + 1) + (K + 1) from by ring,
      show 2 * K + 2 = 0 + 2 * (K + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1_chain (K + 1) (F + 1) 0 0)
  rw [show 0 + 3 * (K + 1) = 3 * K + 3 from by ring]
  -- At (F+1, 0, 0, 3K+3, 0). R5 then R2.
  rw [show F + 1 = F + 1 from rfl]
  step fm; step fm
  -- At (F, 0, 0, 3K+5, 1). R3+R2+R2 loop: 3K+5 rounds.
  rw [show 3 * K + 5 = 0 + (3 * K + 5) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2_b0 (3 * K + 5) F 0 0)
  rw [show F + (3 * K + 5) = F + 3 * K + 5 from by ring,
      show 0 + (3 * K + 5) + 1 = 0 + (3 * K + 6) from by ring]
  -- R4 drain: 3K+6 rounds.
  apply stepStar_trans (r4_drain (3 * K + 6) (F + 3 * K + 5) 0 0)
  ring_nf; finish

-- Odd case: (F+K+2, 2K+3, 0, 0, 0) ⊢⁺ (F+3K+5, 3K+7, 0, 0, 0)
theorem main_odd (F K : ℕ) :
    ⟨F + K + 2, 2 * K + 3, 0, 0, 0⟩ [fm]⊢⁺ ⟨F + 3 * K + 5, 3 * K + 7, 0, 0, 0⟩ := by
  -- R5+R1 chain: K+1 rounds, b goes from 2K+3 to 1, a decreases by K+1.
  rw [show F + K + 2 = (F + 1) + (K + 1) from by ring,
      show 2 * K + 3 = 1 + 2 * (K + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1_chain (K + 1) (F + 1) 1 0)
  rw [show 0 + 3 * (K + 1) = 3 * K + 3 from by ring]
  -- At (F+1, 1, 0, 3K+3, 0). R5 then R2 (b=1<2 so R2 not R1).
  step fm; step fm
  -- At (F, 1, 0, 3K+5, 1). R3+R2+R2 loop: 3K+5 rounds.
  rw [show 3 * K + 5 = 0 + (3 * K + 5) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2_b1 (3 * K + 5) F 0 0)
  rw [show F + (3 * K + 5) = F + 3 * K + 5 from by ring,
      show 0 + (3 * K + 5) + 1 = 0 + (3 * K + 6) from by ring]
  -- R4 drain: 3K+6 rounds, but b starts at 1 so result is 1+3K+6 = 3K+7.
  apply stepStar_trans (r4_drain (3 * K + 6) (F + 3 * K + 5) 1 0)
  ring_nf; finish

-- Main transition combining even and odd cases.
theorem main_trans (A B : ℕ) (hB : B ≥ 3) (hAB : 2 * A ≥ B + 1) :
    ∃ A' B', (⟨A, B, 0, 0, 0⟩ [fm]⊢⁺ ⟨A', B', 0, 0, 0⟩) ∧ B' ≥ 3 ∧ 2 * A' ≥ B' + 1 := by
  rcases Nat.even_or_odd B with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- Even B = 2K, K ≥ 2.
    rw [show K + K = 2 * K from by ring] at hK; subst hK
    have hK1 : K ≥ 2 := by omega
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have hAK : A ≥ K' + 2 := by omega
    obtain ⟨F, rfl⟩ : ∃ F, A = F + K' + 2 := ⟨A - K' - 2, by omega⟩
    exact ⟨F + 3 * K' + 5, 3 * K' + 6, main_even F K', by omega, by omega⟩
  · -- Odd B = 2K+1, K ≥ 1.
    subst hK
    have hK1 : K ≥ 1 := by omega
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have hAK : A ≥ K' + 2 := by omega
    obtain ⟨F, rfl⟩ : ∃ F, A = F + K' + 2 := ⟨A - K' - 2, by omega⟩
    exact ⟨F + 3 * K' + 5, 3 * K' + 7, main_odd F K', by omega, by omega⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 3, 0, 0, 0⟩) (by execute fm 11)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A B, q = ⟨A, B, 0, 0, 0⟩ ∧ B ≥ 3 ∧ 2 * A ≥ B + 1)
  · intro q ⟨A, B, hq, hB, hAB⟩
    subst hq
    obtain ⟨A', B', hstep, hB', hAB'⟩ := main_trans A B hB hAB
    exact ⟨⟨A', B', 0, 0, 0⟩, ⟨A', B', rfl, hB', hAB'⟩, hstep⟩
  · exact ⟨2, 3, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1557
