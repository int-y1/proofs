import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #135: [1/45, 196/15, 3/7, 25/2, 3/5]

Vector representation:
```
 0 -2 -1  0
 2 -1 -1  2
 0  1  0 -1
-1  0  2  0
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_135

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+2, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R3 repeated: convert d to b (c=0 ensures R1,R2 don't fire)
theorem d_to_b : ∀ k a b, ⟨a, b, 0, k⟩ [fm]⊢* ⟨a, b+k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  step fm
  apply stepStar_trans (ih a (b + 1))
  ring_nf; finish

-- R4 repeated: convert a to c (b=0, d=0)
theorem a_to_c : ∀ k c, ⟨k, 0, c, 0⟩ [fm]⊢* ⟨0, 0, c+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  step fm
  apply stepStar_trans (ih (c + 2))
  ring_nf; finish

-- R3,R2 chain: each pair converts 1 c into 2 a and 1 d
theorem r3r2_chain : ∀ k a d, ⟨a, 0, k, d+1⟩ [fm]⊢* ⟨a+2*k, 0, 0, d+1+k⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  step fm; step fm
  apply stepStar_trans (ih (a + 2) (d + 1))
  ring_nf; finish

-- R1,R1,R4 chain: j blocks, each removes 4 from b and 1 from a
theorem r1r1_r4_chain : ∀ j a b, ⟨a+j, b+4*j, 2, 0⟩ [fm]⊢* ⟨a, b, 2, 0⟩ := by
  intro j; induction' j with j ih <;> intro a b
  · exists 0
  rw [show a + (j + 1) = a + j + 1 from by ring,
      show b + 4 * (j + 1) = b + 4 * j + 4 from by ring]
  have hstep1 : fm ⟨a + j + 1, b + 4 * j + 4, 2, 0⟩ =
      some ⟨a + j + 1, b + 4 * j + 2, 1, 0⟩ := by
    rw [show b + 4 * j + 4 = (b + 4 * j + 2) + 2 from by ring,
        show (2 : ℕ) = 1 + 1 from rfl]; rfl
  apply stepStar_trans (step_stepStar hstep1)
  have hstep2 : fm ⟨a + j + 1, b + 4 * j + 2, 1, 0⟩ =
      some ⟨a + j + 1, b + 4 * j, 0, 0⟩ := by
    rw [show b + 4 * j + 2 = (b + 4 * j) + 2 from by ring,
        show (1 : ℕ) = 0 + 1 from rfl]; rfl
  apply stepStar_trans (step_stepStar hstep2)
  have hstep3 : fm ⟨a + j + 1, b + 4 * j, 0, 0⟩ =
      some ⟨a + j, b + 4 * j, 2, 0⟩ := by
    rcases b with _ | _ | b <;> simp [fm]
  apply stepStar_trans (step_stepStar hstep3)
  exact ih a b

-- d=2 transition: (m+2, 0, 0, 2) →⁺ (4m+4, 0, 0, 2m+3)
theorem d2_trans : ⟨m+2, 0, 0, 2⟩ [fm]⊢⁺ ⟨4*m+4, 0, 0, 2*m+3⟩ := by
  apply stepStar_stepPlus_stepPlus (d_to_b 2 (m+2) 0)
  simp only [Nat.zero_add]
  -- R4, R1
  step fm; step fm
  -- (m+1, 0, 1, 0). a_to_c then R5, R2, r3r2_chain.
  apply stepStar_trans (a_to_c (m+1) 1)
  -- (0, 0, 2m+3, 0)
  rw [show 1 + 2 * (m + 1) = (2 * m + 2) + 1 from by ring]
  -- R5: (0, 1, 2m+2, 0)
  have hstep1 : fm ⟨0, 0, (2*m+2)+1, 0⟩ = some ⟨0, 1, 2*m+2, 0⟩ := rfl
  apply stepStar_trans (step_stepStar hstep1)
  -- R2: (2, 0, 2m+1, 2)
  have hstep2 : fm ⟨0, 1, 2*m+2, 0⟩ = some ⟨2, 0, 2*m+1, 2⟩ := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]; rfl
  apply stepStar_trans (step_stepStar hstep2)
  -- r3r2_chain
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (2*m+1) 2 1)
  ring_nf; finish

-- d=3 transition: (a+1, 0, 0, 3) →⁺ (a+2, 0, 0, 2)
theorem d3_trans : ⟨a+1, 0, 0, 3⟩ [fm]⊢⁺ ⟨a+2, 0, 0, 2⟩ := by
  execute fm 6

-- d=4(j+1)+3: (m+j+2, 0, 0, 4(j+1)+3) →⁺ (m+2, 0, 0, 2)
theorem odd3_trans (m j : ℕ) : ⟨m+j+2, 0, 0, 4*(j+1)+3⟩ [fm]⊢⁺ ⟨m+2, 0, 0, 2⟩ := by
  rw [show 4 * (j + 1) + 3 = 4 * j + 7 from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (4*j+7) (m+j+2) 0)
  simp only [Nat.zero_add]
  -- R4
  have hstep : fm ⟨m + j + 2, 4 * j + 7, 0, 0⟩ =
      some ⟨m + j + 1, 4 * j + 7, 2, 0⟩ := by
    rw [show m + j + 2 = (m + j + 1) + 1 from by ring]; rfl
  apply stepStar_stepPlus_stepPlus (step_stepStar hstep)
  -- r1r1_r4_chain
  rw [show 4 * j + 7 = 3 + 4 * (j + 1) from by ring,
      show m + j + 1 = m + (j + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r1r1_r4_chain (j+1) m 3)
  -- (m, 3, 2, 0). R1, R2.
  execute fm 2

-- d=4(j+1)+1: (m+j+2, 0, 0, 4*(j+1)+1) →⁺ (m+4, 0, 0, 3)
theorem odd1_trans (m j : ℕ) : ⟨m+j+2, 0, 0, 4*(j+1)+1⟩ [fm]⊢⁺ ⟨m+4, 0, 0, 3⟩ := by
  rw [show 4 * (j + 1) + 1 = 4 * j + 5 from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (4*j+5) (m+j+2) 0)
  simp only [Nat.zero_add]
  -- R4
  have hstep : fm ⟨m + j + 2, 4 * j + 5, 0, 0⟩ =
      some ⟨m + j + 1, 4 * j + 5, 2, 0⟩ := by
    rw [show m + j + 2 = (m + j + 1) + 1 from by ring]; rfl
  apply stepStar_stepPlus_stepPlus (step_stepStar hstep)
  -- r1r1_r4_chain
  rw [show 4 * j + 5 = 1 + 4 * (j + 1) from by ring,
      show m + j + 1 = m + (j + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r1r1_r4_chain (j+1) m 1)
  -- (m, 1, 2, 0). R2, R3, R2.
  execute fm 3

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2⟩)
  · execute fm 3
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d⟩ ∧ d ≥ 2 ∧ 2 * a ≥ d + 2 ∧ (d = 2 ∨ Odd d))
  · intro c ⟨a, d, hq, hd, ha, hparity⟩; subst hq
    rcases hparity with rfl | hodd
    · -- d = 2
      obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 := ⟨a - 2, by omega⟩
      exact ⟨⟨4*m+4, 0, 0, 2*m+3⟩,
        ⟨4*m+4, 2*m+3, rfl, by omega, by omega, Or.inr ⟨m+1, by ring⟩⟩,
        d2_trans⟩
    · -- d odd
      obtain ⟨k, rfl⟩ := hodd
      rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · -- k = 2j, d = 4j+1
        rcases j with _ | j
        · omega
        · -- j>=1, d = 4(j+1)+1
          rw [show 2 * (j + 1 + (j + 1)) + 1 = 4 * (j + 1) + 1 from by ring]
          obtain ⟨m, rfl⟩ : ∃ m, a = m + j + 2 := ⟨a - j - 2, by omega⟩
          exact ⟨⟨m+4, 0, 0, 3⟩,
            ⟨m+4, 3, rfl, by omega, by omega, Or.inr ⟨1, by ring⟩⟩,
            odd1_trans m j⟩
      · -- k = 2j+1, d = 4j+3
        rcases j with _ | j
        · -- j=0, d=3
          obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
          exact ⟨⟨m+2, 0, 0, 2⟩,
            ⟨m+2, 2, rfl, by omega, by omega, Or.inl rfl⟩,
            d3_trans⟩
        · -- j>=1, d = 4(j+1)+3
          rw [show 2 * (2 * (j + 1) + 1) + 1 = 4 * (j + 1) + 3 from by ring]
          obtain ⟨m, rfl⟩ : ∃ m, a = m + j + 2 := ⟨a - j - 2, by omega⟩
          exact ⟨⟨m+2, 0, 0, 2⟩,
            ⟨m+2, 2, rfl, by omega, by omega, Or.inl rfl⟩,
            odd3_trans m j⟩
  · exact ⟨2, 2, rfl, by omega, by omega, Or.inl rfl⟩

end Sz22_2003_unofficial_135
