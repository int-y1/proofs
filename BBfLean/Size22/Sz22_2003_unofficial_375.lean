import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #375: [2/15, 9/14, 3025/2, 7/5, 10/11]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  0
-1  0  2  0  2
 0  0 -1  1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_375

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: convert c to d
theorem c_to_d : ∀ k c d, ⟨0, 0, c + k, d, e⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; apply stepStar_trans (ih _ _); ring_nf; finish

-- R3 repeated: convert a to c and e
theorem r3_chain : ∀ k c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  step fm; apply stepStar_trans (ih _ _); ring_nf; finish

-- 4-step middle chunk
theorem mid_step_b0 : ⟨0, 0, 0, d + 2, e + 1⟩ [fm]⊢⁺ ⟨0, 3, 0, d, e⟩ := by
  execute fm 4

theorem mid_step_bS : ⟨0, b + 1, 0, d + 2, e + 1⟩ [fm]⊢⁺ ⟨0, b + 4, 0, d, e⟩ := by
  execute fm 4

-- Generalized middle phase for even d
-- We prove: (0, b, 0, d + 2*k, e) →* (0, b + 3*k, 0, d, e - k) conceptually,
-- but to avoid subtraction, we parameterize with e' and set e = e' + k.
theorem mid_phase_even : ∀ k b d e, ⟨0, b, 0, d + 2 * k, e + k⟩ [fm]⊢* ⟨0, b + 3 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · simp; exists 0
  -- Goal: (0, b, 0, d + 2*(k+1), e + (k+1)) →* (0, b + 3*(k+1), 0, d, e)
  -- Rewrite as: (0, b, 0, (d + 2*k) + 2, (e+k) + 1) → mid_step → (0, b+3, 0, d+2*k, e+k) → ih
  rcases b with _ | b
  · -- b = 0
    have hgoal : (0, 0, 0, d + 2 * (k + 1), e + (k + 1)) = (0, 0, 0, (d + 2 * k) + 2, (e + k) + 1) := by ring_nf
    rw [hgoal]
    apply stepStar_trans (stepPlus_stepStar mid_step_b0)
    apply stepStar_trans (ih 3 d e)
    ring_nf; finish
  · -- b ≥ 1
    have hgoal : (0, b + 1, 0, d + 2 * (k + 1), e + (k + 1)) = (0, b + 1, 0, (d + 2 * k) + 2, (e + k) + 1) := by ring_nf
    rw [hgoal]
    apply stepStar_trans (stepPlus_stepStar mid_step_bS)
    apply stepStar_trans (ih (b + 4) d e)
    ring_nf; finish

-- R3+R1+R1: consume 2 from b
theorem consume_b_pair : ⟨a + 1, b + 2, 0, 0, e⟩ [fm]⊢⁺ ⟨a + 2, b, 0, 0, e + 2⟩ := by
  execute fm 3

-- Consume even b pairs
theorem consume_b_pairs : ∀ k a e, ⟨a + 1, 2 * k, 0, 0, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · simp; exists 0
  have hgoal : (a + 1, 2 * (k + 1), 0, 0, e) = (a + 1, (2 * k) + 2, 0, 0, e) := by ring_nf
  rw [hgoal]
  apply stepStar_trans (stepPlus_stepStar consume_b_pair)
  have h := ih (a + 1) (e + 2)
  apply stepStar_trans h; ring_nf; finish

-- Consume odd b pairs: leaves 1 remaining
theorem consume_b_pairs_odd : ∀ k a e, ⟨a + 1, 2 * k + 1, 0, 0, e⟩ [fm]⊢* ⟨a + k + 1, 1, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · simp; exists 0
  have hgoal : (a + 1, 2 * (k + 1) + 1, 0, 0, e) = (a + 1, (2 * k + 1) + 2, 0, 0, e) := by ring_nf
  rw [hgoal]
  apply stepStar_trans (stepPlus_stepStar consume_b_pair)
  have h := ih (a + 1) (e + 2)
  apply stepStar_trans h; ring_nf; finish

-- Handle b=1
theorem consume_b_one : ⟨a + 1, 1, 0, 0, e⟩ [fm]⊢⁺ ⟨a + 1, 0, 1, 0, e + 2⟩ := by
  execute fm 2

-- R5+R1 start
theorem r5_r1_start : ⟨0, b + 1, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨2, b, 0, 0, e⟩ := by
  execute fm 2

-- Variant of consume_b_pairs starting from a=2 instead of a+1
theorem consume_b_pairs_from2 : ∀ k e, ⟨2, 2 * k, 0, 0, e⟩ [fm]⊢* ⟨k + 2, 0, 0, 0, e + 2 * k⟩ := by
  intro k e
  have h := consume_b_pairs k 1 e
  rw [show 1 + k + 1 = k + 2 from by ring, show (1 : ℕ) + 1 = 2 from rfl] at h
  exact h

theorem consume_b_pairs_odd_from2 : ∀ k e, ⟨2, 2 * k + 1, 0, 0, e⟩ [fm]⊢* ⟨k + 2, 1, 0, 0, e + 2 * k⟩ := by
  intro k e
  have h := consume_b_pairs_odd k 1 e
  rw [show 1 + k + 1 = k + 2 from by ring, show (1 : ℕ) + 1 = 2 from rfl] at h
  exact h

-- Final D=0 phase: (0, b+1, 0, 0, e+1) →⁺ (0, 0, b+4, 0, e+2b+4)
theorem final_d0 : ∀ b e, ⟨0, b + 1, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, b + 4, 0, e + 2 * b + 4⟩ := by
  intro b e
  apply stepPlus_stepStar_stepPlus r5_r1_start
  rcases Nat.even_or_odd b with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- b even = 2k
    rw [show k + k = 2 * k from by ring] at hk; subst hk
    apply stepStar_trans (consume_b_pairs_from2 k e)
    apply stepStar_trans (r3_chain (k + 2) 0 (e + 2 * k))
    ring_nf; finish
  · -- b odd = 2k + 1
    subst hk
    apply stepStar_trans (consume_b_pairs_odd_from2 k e)
    apply stepStar_trans (stepPlus_stepStar consume_b_one)
    apply stepStar_trans (r3_chain (k + 2) 1 (e + 2 * k + 2))
    ring_nf; finish

-- D=1 with b=0
theorem d1_b0 : ⟨0, 0, 0, 1, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 3, 0, e + 4⟩ := by
  step fm; step fm; step fm
  apply stepStar_trans (stepPlus_stepStar consume_b_one)
  apply stepStar_trans (r3_chain 1 1 (e + 2))
  ring_nf; finish

-- D=1 start with b≥1
theorem d1_start : ⟨0, b + 1, 0, 1, e + 1⟩ [fm]⊢⁺ ⟨1, b + 2, 0, 0, e⟩ := by
  execute fm 3

-- Final D=1 phase: (0, b, 0, 1, e+1) →⁺ (0, 0, b+3, 0, e+2b+4)
theorem final_d1 : ∀ b e, ⟨0, b, 0, 1, e + 1⟩ [fm]⊢⁺ ⟨0, 0, b + 3, 0, e + 2 * b + 4⟩ := by
  intro b e
  rcases b with _ | b
  · exact d1_b0
  · apply stepPlus_stepStar_stepPlus d1_start
    -- At (1, b+2, 0, 0, e)
    rcases Nat.even_or_odd (b + 2) with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- b+2 even = 2j
      rw [show j + j = 2 * j from by ring] at hj
      rw [show (1 : ℕ) = 0 + 1 from rfl, hj]
      apply stepStar_trans (consume_b_pairs j 0 e)
      simp only [Nat.zero_add]
      apply stepStar_trans (r3_chain (j + 1) 0 (e + 2 * j))
      -- b = 2j - 2, so b + 3 = 2j + 1, etc.
      -- Need: (0, 0, 0 + 2*(j+1), 0, e+2j + 2*(j+1)) = (0, 0, b+1+3, 0, e+2*(b+1)+4)
      -- = (0, 0, 2j+2, 0, e+4j+2) vs (0, 0, b+4, 0, e+2b+6)
      -- b = 2j-2: b+4 = 2j+2 ✓; e+2b+6 = e+4j-4+6 = e+4j+2 ✓
      have hb : b + 2 = 2 * j := hj
      have : 0 + 2 * (j + 1) = b + 4 := by omega
      rw [this]
      have : e + 2 * j + 2 * (j + 1) = e + 2 * (b + 1) + 4 := by omega
      rw [this]; finish
    · -- b+2 odd = 2j+1
      rw [show (1 : ℕ) = 0 + 1 from rfl, hj]
      apply stepStar_trans (consume_b_pairs_odd j 0 e)
      simp only [Nat.zero_add]
      apply stepStar_trans (stepPlus_stepStar consume_b_one)
      apply stepStar_trans (r3_chain (j + 1) 1 (e + 2 * j + 2))
      have hb : b + 2 = 2 * j + 1 := hj
      have : 1 + 2 * (j + 1) = b + 4 := by omega
      rw [this]
      have : e + 2 * j + 2 + 2 * (j + 1) = e + 2 * (b + 1) + 4 := by omega
      rw [this]; finish

-- Full even transition: (0, 0, 2(k+1), 0, m) →⁺ (0, 0, 3k+6, 0, m+5k+6)
theorem full_even (hm : m ≥ k + 2) :
    ⟨0, 0, 2 * (k + 1), 0, m⟩ [fm]⊢⁺ ⟨0, 0, 3 * k + 6, 0, m + 5 * k + 6⟩ := by
  obtain ⟨e, rfl⟩ : ∃ e, m = e + k + 2 := ⟨m - k - 2, by omega⟩
  -- Phase 1: c_to_d
  have hc2d : (0, 0, 2 * (k + 1), 0, e + k + 2) = (0, 0, 0 + 2 * (k + 1), 0, e + k + 2) := by ring_nf
  rw [hc2d]
  apply stepStar_stepPlus_stepPlus (c_to_d (2 * (k + 1)) 0 0)
  -- Phase 2: mid_phase_even
  have hmid : (0, 0, 0, 0 + 2 * (k + 1), e + k + 2) = (0, 0, 0, 0 + 2 * (k + 1), (e + 1) + (k + 1)) := by ring_nf
  rw [hmid]
  apply stepStar_stepPlus_stepPlus (mid_phase_even (k + 1) 0 0 (e + 1))
  simp only [Nat.zero_add]
  -- Phase 3: final_d0
  have hfd : (0, 3 * (k + 1), 0, 0, e + 1) = (0, (3 * k + 2) + 1, 0, 0, e + 1) := by ring_nf
  rw [hfd]
  apply stepPlus_stepStar_stepPlus (final_d0 (3 * k + 2) e)
  ring_nf; finish

-- Full odd transition: (0, 0, 2k+1, 0, m) →⁺ (0, 0, 3k+3, 0, m+5k+3)
theorem full_odd (hm : m ≥ k + 1) :
    ⟨0, 0, 2 * k + 1, 0, m⟩ [fm]⊢⁺ ⟨0, 0, 3 * k + 3, 0, m + 5 * k + 3⟩ := by
  obtain ⟨e, rfl⟩ : ∃ e, m = e + k + 1 := ⟨m - k - 1, by omega⟩
  -- Phase 1: c_to_d
  have hc2d : (0, 0, 2 * k + 1, 0, e + k + 1) = (0, 0, 0 + (2 * k + 1), 0, e + k + 1) := by ring_nf
  rw [hc2d]
  apply stepStar_stepPlus_stepPlus (c_to_d (2 * k + 1) 0 0)
  -- Phase 2: mid_phase_even for the even part, but d is odd
  -- d = 2k+1: write as d' + 2*k where d'=1
  have hmid : (0, 0, 0, 0 + (2 * k + 1), e + k + 1) = (0, 0, 0, 1 + 2 * k, (e + 1) + k) := by ring_nf
  rw [hmid]
  apply stepStar_stepPlus_stepPlus (mid_phase_even k 0 1 (e + 1))
  simp only [Nat.zero_add]
  -- Phase 3: final_d1
  apply stepPlus_stepStar_stepPlus (final_d1 (3 * k) e)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 2⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n m, q = ⟨0, 0, n, 0, m⟩ ∧ n ≥ 1 ∧ 2 * m ≥ n + 1)
  · intro c ⟨n, m, hq, hn, hm⟩; subst hq
    rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- n even = 2j
      rw [show j + j = 2 * j from by ring] at hj
      rcases j with _ | k
      · omega
      · subst hj
        exact ⟨⟨0, 0, 3 * k + 6, 0, m + 5 * k + 6⟩,
               ⟨3 * k + 6, m + 5 * k + 6, rfl, by omega, by omega⟩,
               full_even (by omega)⟩
    · -- n odd = 2j + 1
      subst hj
      exact ⟨⟨0, 0, 3 * j + 3, 0, m + 5 * j + 3⟩,
             ⟨3 * j + 3, m + 5 * j + 3, rfl, by omega, by omega⟩,
             full_odd (by omega)⟩
  · exact ⟨2, 2, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_375
