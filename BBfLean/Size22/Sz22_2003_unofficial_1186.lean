import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1186: [5/6, 49/2, 44/35, 9/11, 55/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  1
 0  2  0  0 -1
 0  0  1 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1186

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 drain: move e to b
theorem e_to_b : ∀ k b, ⟨(0:ℕ), b, 0, d, k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b
  · simp; exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (b + 2))
    ring_nf; finish

-- Interleave R3+R1+R1 chain
theorem interleave : ∀ k c d e, c ≥ 1 →
    ⟨(0:ℕ), 2 * k, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e hc
  · simp; exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    step fm; step fm; step fm
    apply stepStar_trans (ih (c' + 2) d (e + 1) (by omega))
    ring_nf; finish

-- Drain R3+R2+R2 chain
theorem drain : ∀ k c d e,
    ⟨(0:ℕ), 0, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 3 * k + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 1))
    ring_nf; finish

-- e=0 case: (0,0,0,d+2,0) ⊢⁺ (0,0,0,d+4,2)
theorem main_e0 : ⟨(0:ℕ), 0, 0, d + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 4, 2⟩ := by
  execute fm 4

-- Full transition: (0,0,0,D,E) ⊢⁺ (0,0,0,D',E') when D ≥ E+2 and E ≥ 1.
-- Written as (0,0,0,d+e+3,e+1) ⊢⁺ (0,0,0,d+3e+7,2e+4) where d ≥ 0 and e ≥ 0.
-- Here D = d+e+3, E = e+1, so D ≥ E+2 iff d+e+3 ≥ e+3 iff d ≥ 0. Always true.
-- D' = d+3e+7 = (d+e+3) + (2e+4). E' = 2e+4.
-- D' ≥ E'+2 iff d+3e+7 ≥ 2e+6 iff d+e+1 ≥ 0. Always true.
theorem main_e_pos (d : ℕ) (e : ℕ) :
    ⟨(0:ℕ), 0, 0, d + e + 3, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 3 * e + 7, 2 * e + 4⟩ := by
  -- Phase 1: R4 drain (e+1 steps): (0,0,0,d+e+3,e+1) →* (0,2e+2,0,d+e+3,0)
  apply stepStar_stepPlus_stepPlus
  · have h := e_to_b (e + 1) 0 (d := d + e + 3)
    rw [show 0 + 2 * (e + 1) = 2 * e + 2 from by ring] at h
    exact h
  -- Phase 2: R5 + R3 + R1 + R1 (4 steps)
  -- (0,2e+2,0,d+e+3,0) → R5 → (0,2e+2,1,d+e+2,1)
  -- → R3 → (2,2e+2,0,d+e+1,2)
  -- → R1 → (1,2e+1,1,d+e+1,2)
  -- → R1 → (0,2e,2,d+e+1,2)
  step fm; step fm; step fm; step fm
  -- Phase 3: Interleave (e rounds)
  rw [show d + e + 1 = (d + 1) + e from by ring]
  apply stepStar_trans (interleave e 2 (d + 1) 2 (by omega))
  -- Phase 4: Drain (e+2 rounds)
  -- State: (0, 0, 2+e, d+1, 2+e). Need to match drain pattern.
  have h4 := drain (e + 2) 0 d (2 + e)
  -- h4: (0, 0, 0+(e+2), d+1, 2+e) →* (0, 0, 0, d+3*(e+2)+1, (2+e)+(e+2))
  rw [show 0 + (e + 2) = 2 + e from by ring] at h4
  apply stepStar_trans h4
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ e + 2)
  · intro c ⟨d, e, hq, hd⟩; subst hq
    rcases e with _ | e
    · -- e = 0
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
      exact ⟨⟨0, 0, 0, d' + 4, 2⟩, ⟨d' + 4, 2, rfl, by omega⟩, main_e0⟩
    · -- e = e + 1
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + e + 3 := ⟨d - e - 3, by omega⟩
      exact ⟨⟨0, 0, 0, d' + 3 * e + 7, 2 * e + 4⟩,
        ⟨d' + 3 * e + 7, 2 * e + 4, rfl, by omega⟩,
        main_e_pos d' e⟩
  · exact ⟨2, 0, rfl, by omega⟩

end Sz22_2003_unofficial_1186
