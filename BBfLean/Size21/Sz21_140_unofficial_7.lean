import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #7: [1/45, 196/15, 3/7, 25/2, 3/5]

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

namespace Sz21_140_unofficial_7

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+2, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R3 repeated: d → b
theorem d_to_b : ⟨a, b, 0, d+k⟩ [fm]⊢* ⟨a, b+k, 0, d⟩ := by
  have many_step : ∀ k b d, ⟨a, b, 0, d+k⟩ [fm]⊢* ⟨a, b+k, 0, d⟩ := by
    intro k; induction' k with k h <;> intro b d
    · exists 0
    rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (h _ _); ring_nf; finish
  exact many_step k b d

-- R4 repeated: a → c
theorem a_to_c : ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, 0⟩ := by
  have many_step : ∀ k a c, ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, 0⟩ := by
    intro k; induction' k with k h <;> intro a c
    · exists 0
    rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (h _ _); ring_nf; finish
  exact many_step k a c

-- R3+R2 chain
theorem r3r2_chain : ∀ k, ∀ a c d, ⟨a, 0, c+k, d+1⟩ [fm]⊢* ⟨a+2*k, 0, c, d+k+1⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm
  rw [show d + 2 = (d + 1) + 1 from by ring]
  apply stepStar_trans (h (a + 2) c (d + 1))
  ring_nf; finish

-- Phase 1
theorem phase1 : ⟨0, 0, c+2, 0⟩ [fm]⊢* ⟨2*c+2, 0, 0, c+2⟩ := by
  step fm; step fm
  have h := r3r2_chain c 2 0 1
  simp only [Nat.zero_add] at h
  rw [show (1 : ℕ) + 1 = 2 from by ring,
      show 1 + c + 1 = c + 2 from by ring,
      show 2 + 2 * c = 2 * c + 2 from by ring] at h
  exact h

-- Drain round
theorem drain_round : ⟨a+1, b+4, 0, 0⟩ [fm]⊢* ⟨a, b, 0, 0⟩ := by
  step fm; step fm; step fm; finish

-- Drain chain
theorem drain_chain : ∀ k, ∀ a b, ⟨a+k, b+4*k, 0, 0⟩ [fm]⊢* ⟨a, b, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show b + 4 * (k + 1) = (b + 4 * k) + 4 from by ring]
  apply stepStar_trans drain_round
  exact h a b

-- B=3 terminal
theorem b3_to_b2 : ⟨a+1, 3, 0, 0⟩ [fm]⊢* ⟨a+2, 2, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- B=2 terminal
theorem b2_to_01 : ⟨a+1, 2, 0, 0⟩ [fm]⊢* ⟨a, 0, 1, 0⟩ := by
  step fm; step fm; finish

-- B=1 terminal
theorem b1_to_b3 : ⟨a+1, 1, 0, 0⟩ [fm]⊢* ⟨a+4, 3, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Phase 5: R4 chain
theorem phase5 : ⟨a, 0, 1, 0⟩ [fm]⊢* ⟨0, 0, 2*a+1, 0⟩ := by
  have h := @a_to_c (a := 0) (k := a) (c := 1)
  simp only [Nat.zero_add] at h
  rw [show 1 + 2 * a = 2 * a + 1 from by ring] at h; exact h

-- End phase for b=3
theorem end_b3 : ⟨a+1, 3, 0, 0⟩ [fm]⊢* ⟨0, 0, 2*a+3, 0⟩ := by
  apply stepStar_trans b3_to_b2
  rw [show a + 2 = (a + 1) + 1 from by ring]
  apply stepStar_trans b2_to_01
  have h := phase5 (a := a + 1)
  rw [show 2 * (a + 1) + 1 = 2 * a + 3 from by ring] at h
  exact h

-- End phase for b=1
theorem end_b1 : ⟨a+1, 1, 0, 0⟩ [fm]⊢* ⟨0, 0, 2*a+9, 0⟩ := by
  apply stepStar_trans b1_to_b3
  rw [show a + 4 = (a + 3) + 1 from by ring]
  have h := end_b3 (a := a + 3)
  rw [show 2 * (a + 3) + 3 = 2 * a + 9 from by ring] at h
  exact h

-- Main transition for c = 3 mod 4
theorem trans_mod3 (K : ℕ) : ⟨0, 0, 4*K+3, 0⟩ [fm]⊢⁺ ⟨0, 0, 14*K+9, 0⟩ := by
  rw [show 4*K+3 = (4*K+1)+2 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, ((4*K+1)+1)+1, 0⟩ = some ⟨0, 1, (4*K+1)+1, 0⟩; simp [fm]
  apply stepStar_trans
  · show ⟨0, 1, (4*K+1)+1, 0⟩ [fm]⊢* ⟨2, 0, 4*K+1, 2⟩
    step fm; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨8*K+4, 0, 0, 4*K+3⟩)
  · have h := r3r2_chain (4*K+1) 2 0 1
    simp only [Nat.zero_add] at h
    rw [show (1 : ℕ) + 1 = 2 from by ring,
        show 2 + 2 * (4 * K + 1) = 8 * K + 4 from by ring,
        show 1 + (4 * K + 1) + 1 = 4 * K + 3 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨8*K+4, 4*K+3, 0, 0⟩)
  · have h := @d_to_b (a := 8*K+4) (b := 0) (d := 0) (k := 4*K+3)
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans (c₂ := ⟨7*K+4, 3, 0, 0⟩)
  · have h := drain_chain K (7*K+4) 3
    rw [show (7*K+4)+K = 8*K+4 from by ring,
        show 3+4*K = 4*K+3 from by ring] at h; exact h
  rw [show 7*K+4 = (7*K+3)+1 from by ring]
  have h := end_b3 (a := 7*K+3)
  rw [show 2*(7*K+3)+3 = 14*K+9 from by ring] at h; exact h

-- Main transition for c = 1 mod 4
theorem trans_mod1 (K : ℕ) : ⟨0, 0, 4*K+5, 0⟩ [fm]⊢⁺ ⟨0, 0, 14*K+21, 0⟩ := by
  rw [show 4*K+5 = (4*K+3)+2 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, ((4*K+3)+1)+1, 0⟩ = some ⟨0, 1, (4*K+3)+1, 0⟩; simp [fm]
  apply stepStar_trans
  · show ⟨0, 1, (4*K+3)+1, 0⟩ [fm]⊢* ⟨2, 0, 4*K+3, 2⟩
    step fm; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨8*K+8, 0, 0, 4*K+5⟩)
  · have h := r3r2_chain (4*K+3) 2 0 1
    simp only [Nat.zero_add] at h
    rw [show (1 : ℕ) + 1 = 2 from by ring,
        show 2 + 2 * (4 * K + 3) = 8 * K + 8 from by ring,
        show 1 + (4 * K + 3) + 1 = 4 * K + 5 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨8*K+8, 4*K+5, 0, 0⟩)
  · have h := @d_to_b (a := 8*K+8) (b := 0) (d := 0) (k := 4*K+5)
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans (c₂ := ⟨7*K+7, 1, 0, 0⟩)
  · have h := drain_chain (K+1) (7*K+7) 1
    rw [show (7*K+7)+(K+1) = 8*K+8 from by ring,
        show 1+4*(K+1) = 4*K+5 from by ring] at h; exact h
  rw [show 7*K+7 = (7*K+6)+1 from by ring]
  have h := end_b1 (a := 7*K+6)
  rw [show 2*(7*K+6)+9 = 14*K+21 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨0, 0, 4*n+3, 0⟩ ∨ q = ⟨0, 0, 4*n+5, 0⟩)
  · intro c ⟨n, hn⟩
    rcases hn with h | h
    · rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact ⟨⟨0, 0, 14*n+9, 0⟩, ⟨7*m+1, Or.inr (by subst h hm; ring_nf)⟩,
               h ▸ trans_mod3 n⟩
      · exact ⟨⟨0, 0, 14*n+9, 0⟩, ⟨7*m+5, Or.inl (by subst h hm; ring_nf)⟩,
               h ▸ trans_mod3 n⟩
    · rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact ⟨⟨0, 0, 14*n+21, 0⟩, ⟨7*m+4, Or.inr (by subst h hm; ring_nf)⟩,
               h ▸ trans_mod1 n⟩
      · exact ⟨⟨0, 0, 14*n+21, 0⟩, ⟨7*m+8, Or.inl (by subst h hm; ring_nf)⟩,
               h ▸ trans_mod1 n⟩
  · exact ⟨0, Or.inl rfl⟩
