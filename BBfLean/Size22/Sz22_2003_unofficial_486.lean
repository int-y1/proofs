import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #486: [28/15, 3/22, 175/2, 11/7, 9/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  1  0
 0  0  0 -1  1
 0  2 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_486

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- R4 chain: (0,0,c,d+k,e) -> (0,0,c,d,e+k)
theorem r4_chain : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = d + k + 1 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    step fm; apply stepStar_trans (ih c d (e + 1)); ring_nf; finish

-- (R2, R1) chain
theorem r2_r1_chain : ∀ k a c d e, ⟨a + 1, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + k + 1, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = c + k + 1 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (d + 1) e); ring_nf; finish

-- R2 drain: (a+k,b,0,d,k) -> (a,b+k,0,d,0)
theorem r2_drain : ∀ k a b d, ⟨a + k, b, 0, d, k⟩ [fm]⊢* ⟨a, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring,
        show b + (k + 1) = b + k + 1 from by ring]
    step fm; apply stepStar_trans (ih a (b + 1) d); ring_nf; finish

-- Pure R3 chain: (k,0,c,d,0) -> (0,0,c+2k,d+k,0)
theorem r3_chain : ∀ k c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · step fm; apply stepStar_trans (ih (c + 2) (d + 1)); ring_nf; finish

-- (R3,R1,R1) rounds: each round b-=2, a+=3, d+=3
theorem r3r1r1_chain : ∀ k a b d, ⟨a + 1, b + 2 * k, 0, d, 0⟩ [fm]⊢* ⟨a + 3 * k + 1, b, 0, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · simp; exists 0
  · rw [show b + 2 * (k + 1) = b + 2 * k + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) b (d + 3)); ring_nf; finish

-- b=1 terminal: (a+1,1,0,d,0) -> (0,0,2a+5,d+a+4,0)
theorem b1_terminal : ∀ a d, ⟨a + 1, 1, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 2 * a + 5, d + a + 4, 0⟩ := by
  intro a d; step fm; step fm; step fm
  apply stepStar_trans (r3_chain (a + 1) 3 (d + 3)); ring_nf; finish

-- Phase 6 even: B = 2k
theorem phase6_even : ∀ k a d, ⟨a + 1, 2 * k, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 2 * a + 6 * k + 2, d + a + 6 * k + 1, 0⟩ := by
  intro k a d
  have h1 := r3r1r1_chain k a 0 d
  rw [show 0 + 2 * k = 2 * k from by ring] at h1
  apply stepStar_trans h1
  apply stepStar_trans (r3_chain (a + 3 * k + 1) 0 (d + 3 * k)); ring_nf; finish

-- Phase 6 odd: B = 2k+1
theorem phase6_odd : ∀ k a d, ⟨a + 1, 2 * k + 1, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 2 * a + 6 * k + 5, d + a + 6 * k + 4, 0⟩ := by
  intro k a d
  have h1 := r3r1r1_chain k a 1 d
  rw [show 1 + 2 * k = 2 * k + 1 from by ring] at h1
  apply stepStar_trans h1
  apply stepStar_trans (b1_terminal (a + 3 * k) (d + 3 * k)); ring_nf; finish

theorem main_transition (c d : ℕ) (hc : c ≥ 4) (hd : d ≥ c) (hd2 : d ≤ 2 * c - 4) :
    ⟨0, 0, c, d, 0⟩ [fm]⊢⁺ ⟨0, 0, c + d + 5, 2 * d + 6, 0⟩ := by
  -- First R4 step gives ⊢
  apply step_stepStar_stepPlus (c₂ := ⟨0, 0, c, d - 1, 1⟩)
  · show fm ⟨0, 0, c, d, 0⟩ = some ⟨0, 0, c, d - 1, 1⟩
    conv_lhs => rw [show d = (d - 1) + 1 from by omega]
    simp [fm]
  -- Remaining R4s + rest: (0,0,c,d-1,1) ->* (0,0,c,0,d)
  apply stepStar_trans (c₂ := ⟨0, 0, c, 0, d⟩)
  · have h := r4_chain (d - 1) c 0 1
    rw [show 0 + (d - 1) = d - 1 from by ring,
        show 1 + (d - 1) = d from by omega] at h; exact h
  -- R5: (0,0,c,0,d) -> (0,2,c-1,0,d)
  apply stepStar_trans (c₂ := ⟨0, 2, c - 1, 0, d⟩)
  · rw [show c = (c - 1) + 1 from by omega]; step fm; finish
  -- R1, R1: (0,2,c-1,0,d) -> (4,0,c-3,2,d)
  apply stepStar_trans (c₂ := ⟨4, 0, c - 3, 2, d⟩)
  · rw [show c - 1 = (c - 3) + 1 + 1 from by omega]; step fm; step fm; finish
  -- R2_R1 chain x (c-3): (4,0,c-3,2,d) -> (c+1,0,0,c-1,d-c+3)
  apply stepStar_trans (c₂ := ⟨c + 1, 0, 0, c - 1, d - c + 3⟩)
  · have h := r2_r1_chain (c - 3) 3 0 2 (d - c + 3)
    rw [show 0 + (c - 3) = c - 3 from by ring,
        show (d - c + 3) + (c - 3) = d from by omega,
        show 3 + 1 = 4 from by ring,
        show 3 + (c - 3) + 1 = c + 1 from by omega,
        show 2 + (c - 3) = c - 1 from by omega] at h; exact h
  -- R2 drain: (c+1,0,0,c-1,d-c+3) -> (2c-d-2,d-c+3,0,c-1,0)
  apply stepStar_trans (c₂ := ⟨2 * c - d - 2, d - c + 3, 0, c - 1, 0⟩)
  · have h := r2_drain (d - c + 3) (2 * c - d - 2) 0 (c - 1)
    rw [show (2 * c - d - 2) + (d - c + 3) = c + 1 from by omega,
        show 0 + (d - c + 3) = d - c + 3 from by ring] at h; exact h
  -- Phase 6: parity split on B = d - c + 3
  rcases Nat.even_or_odd (d - c + 3) with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- even case: d - c + 3 = K + K
    have hK2 : d - c + 3 = 2 * K := by omega
    rw [hK2]
    have h := phase6_even K (2 * c - d - 3) (c - 1)
    rw [show (2 * c - d - 3) + 1 = 2 * c - d - 2 from by omega,
        show 2 * (2 * c - d - 3) + 6 * K + 2 = c + d + 5 from by omega,
        show c - 1 + (2 * c - d - 3) + 6 * K + 1 = 2 * d + 6 from by omega] at h
    exact h
  · -- odd case: d - c + 3 = K + K + 1
    have hK2 : d - c + 3 = 2 * K + 1 := by omega
    rw [hK2]
    have h := phase6_odd K (2 * c - d - 3) (c - 1)
    rw [show (2 * c - d - 3) + 1 = 2 * c - d - 2 from by omega,
        show 2 * (2 * c - d - 3) + 6 * K + 5 = c + d + 5 from by omega,
        show c - 1 + (2 * c - d - 3) + 6 * K + 4 = 2 * d + 6 from by omega] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 8, 8, 0⟩) (by execute fm 12)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c d, q = ⟨0, 0, c, d, 0⟩ ∧ c ≥ 4 ∧ d ≥ c ∧ d ≤ 2 * c - 4)
  · intro q ⟨c, d, hq, hc, hd, hd2⟩; subst hq
    exact ⟨_, ⟨c + d + 5, 2 * d + 6, rfl, by omega, by omega, by omega⟩,
           main_transition c d hc hd hd2⟩
  · exact ⟨8, 8, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_486
