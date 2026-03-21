import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #124: [8/15, 33/14, 55/2, 7/11, 3/7]

Vector representation:
```
 3 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  1
 0  0  0  1 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_124

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R1R2 chain: each round does R1 (b=1,c≥1) then R2 (a≥1,d≥1)
theorem r1r2_chain : ∀ k, ∀ a c d e, ⟨a, 1, c+k, d+k, e⟩ [fm]⊢* ⟨a+2*k, 1, c, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- R2 chain: R2 fires when a≥1 and d≥1, and c=0 prevents R1
theorem r2_chain : ∀ k, ∀ a b d e, ⟨a+k, b, 0, d+k, e⟩ [fm]⊢* ⟨a, b+k, 0, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- R3R1 chain: R3 then R1 alternating
-- (a+1, b+k, 0, 0, e) ->* (a+1+2k, b, 0, 0, e+k)
theorem r3r1_chain : ∀ k, ∀ a b e, ⟨a+1, b+k, 0, 0, e⟩ [fm]⊢* ⟨a+1+2*k, b, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm  -- R3: (a+1, _, 0, 0, e) -> (a, _, 1, 0, e+1)
  step fm  -- R1: (a, (b+k)+1, 0+1, 0, e+1) -> (a+3, b+k, 0, 0, e+1)
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3 chain: a → c,e when b=0, d=0
theorem r3_chain : ∀ k, ∀ a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+k, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4 chain: e → d when a=0, b=0
theorem r4_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Main transition: from (0, 0, C+1, C+D+1, 0) to (0, 0, 2*C+D+3, 3*C+3*D+3, 0)
-- where D ≤ 2*C+2
theorem main_trans (C D : ℕ) (hD : D ≤ 2*C+2) :
    ⟨0, 0, C+1, C+D+1, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*C+D+3, 3*C+3*D+3, 0⟩ := by
  -- Phase 0: R5 step: (0, 0, C+1, (C+D)+1, 0) -> (0, 1, C+1, C+D, 0)
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, C+1, C+D, 0⟩)
  · show fm ⟨0, 0, C + 1, (C + D) + 1, 0⟩ = some ⟨0, 1, C + 1, C + D, 0⟩; simp [fm]
  -- Phase 1: R1R2 chain: C rounds
  apply stepStar_trans (c₂ := ⟨2*C, 1, 1, D, C⟩)
  · have h := r1r2_chain C 0 1 D 0
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- Phase 2: Last R1 step: (2C, 0+1, 0+1, D, C) -> (2C+3, 0, 0, D, C)
  apply stepStar_trans (c₂ := ⟨2*C+3, 0, 0, D, C⟩)
  · step fm; finish
  -- Phase 3: R2 chain: D steps
  obtain ⟨a, ha⟩ : ∃ a, 2*C+3 = a + D := ⟨2*C+3-D, by omega⟩
  apply stepStar_trans (c₂ := ⟨a, D, 0, 0, C+D⟩)
  · rw [ha]
    have h := r2_chain D a 0 0 C
    simp only [Nat.zero_add] at h; exact h
  -- Phase 4: R3R1 chain: D rounds
  -- Need a ≥ 1. a = 2C+3-D ≥ 1 since D ≤ 2C+2.
  have ha1 : a ≥ 1 := by omega
  obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a-1, by omega⟩
  apply stepStar_trans (c₂ := ⟨a'+1+2*D, 0, 0, 0, C+2*D⟩)
  · rw [ha']
    have h := r3r1_chain D a' 0 (C+D)
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- Phase 5: R3 chain
  apply stepStar_trans (c₂ := ⟨0, 0, a'+1+2*D, 0, C+2*D+(a'+1+2*D)⟩)
  · have h := r3_chain (a'+1+2*D) 0 0 (C+2*D)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 6: R4 chain
  have hk : C+2*D+(a'+1+2*D) = C+2*D+a'+1+2*D := by ring
  rw [hk]
  apply stepStar_trans (c₂ := ⟨0, 0, a'+1+2*D, C+2*D+a'+1+2*D, 0⟩)
  · have h := r4_chain (C+2*D+a'+1+2*D) (a'+1+2*D) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Now close the goal
  have h1 : a' + 1 + 2 * D = 2 * C + D + 3 := by omega
  have h2 : C + 2 * D + a' + 1 + 2 * D = 3 * C + 3 * D + 3 := by omega
  rw [h1, h2]; finish

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0) reaches (0,0,1,1,0)
  -- (1,0,0,0,0) ->R3-> (0,0,1,0,1) ->R4-> (0,0,1,1,0): 2 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 1, 0⟩) (by execute fm 2)
  -- Use progress_nonhalt with predicate
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ C D, q = ⟨0, 0, C+1, C+D+1, 0⟩ ∧ D ≤ 2*C+2)
  · intro c ⟨C, D, hq, hD⟩; subst hq
    refine ⟨⟨0, 0, 2*C+D+3, 3*C+3*D+3, 0⟩,
            ⟨2*C+D+2, C+2*D, ?_, ?_⟩,
            main_trans C D hD⟩
    · have h1 : 2 * C + D + 3 = 2 * C + D + 2 + 1 := by omega
      have h2 : 3 * C + 3 * D + 3 = 2 * C + D + 2 + (C + 2 * D) + 1 := by omega
      rw [h1, h2]
    · omega
  · exact ⟨0, 0, rfl, by omega⟩

end Sz21_140_unofficial_124
