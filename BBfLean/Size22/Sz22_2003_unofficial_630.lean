import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #630: [35/6, 143/2, 4/55, 3/7, 165/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 0  1  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_630

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e+1, f⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b (d e f : ℕ) : ∀ k b,
    ⟨(0:ℕ), b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _); ring_nf; finish

-- R3,R2,R2 chain: each round converts 1 c to 1 e and 2 f
theorem r3r2r2_chain (d : ℕ) : ∀ k c e f,
    ⟨(0:ℕ), 0, c+k, d, e+1, f⟩ [fm]⊢* ⟨0, 0, c, d, e+k+1, f+2*k⟩ := by
  intro k; induction' k with k h <;> intro c e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- Big phase: (2, b, C, D, E, F) →* (0, 0, 0, D+b, E+C+2, F+2*C+b+2)
-- Requires 2*E ≥ b to ensure R3 fires in each round.
theorem big_phase : ∀ b, ∀ C D E F, 2*E ≥ b →
    ⟨(2:ℕ), b, C, D, E, F⟩ [fm]⊢* ⟨0, 0, 0, D+b, E+C+2, F+2*C+b+2⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro C D E F hE
  rcases b with _ | _ | b'
  · step fm; step fm
    rw [show C = 0 + C from by ring, show E + 1 + 1 = (E + 1) + 1 from by ring]
    apply stepStar_trans (r3r2r2_chain D C 0 (E+1) (F+1+1))
    ring_nf; finish
  · step fm; step fm
    rw [show C + 1 = 0 + (C + 1) from by ring]
    apply stepStar_trans (r3r2r2_chain (D+1) (C+1) 0 E (F+1))
    ring_nf; finish
  · obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
    rw [show (b' + 2 : ℕ) = (b' + 1) + 1 from by ring]
    step fm; step fm
    rw [show C + 1 + 1 = (C + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b' (by omega) (C+1) (D+2) E' F (by omega))
    ring_nf; finish

-- Transition for n ≥ 1: (0,0,0,n+1,2n+3,f+1) →⁺ (0,0,0,n+2,2n+5,f+n+4)
theorem trans_succ (n f : ℕ) :
    ⟨(0:ℕ), 0, 0, n+1, 2*(n+1)+1, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, n+2, 2*(n+2)+1, f+n+4⟩ := by
  -- Phase 1: R4 chain (n+1 steps): d→b
  have h1 := d_to_b 0 (2*(n+1)+1) (f+1) (n+1) 0
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  -- Phase 2: R5
  apply step_stepStar_stepPlus (show fm ⟨0, n+1, 0, 0, 2*(n+1)+1, f+1⟩ =
    some ⟨0, n+2, 1, 0, 2*(n+1)+2, f⟩ from by unfold fm; ring_nf)
  -- Phase 3: R3
  rw [show 2*(n+1)+2 = (2*(n+1)+1)+1 from by ring]
  apply stepStar_trans (step_stepStar
    (show fm ⟨0, n+2, 1, 0, (2*(n+1)+1)+1, f⟩ =
      some ⟨2, n+2, 0, 0, 2*(n+1)+1, f⟩ from by unfold fm; rfl))
  -- Phase 4: big_phase
  apply stepStar_trans (big_phase (n+2) 0 0 (2*(n+1)+1) f (by omega))
  simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero]; ring_nf; finish

-- Transition for n = 0: (0,0,0,0,1,f+1) →⁺ (0,0,0,1,3,f+3)
theorem trans_zero (f : ℕ) :
    ⟨(0:ℕ), 0, 0, 0, 1, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, 3, f+3⟩ := by
  -- R5: (0,1,1,0,2,f), R3: (2,1,0,0,1,f), big_phase(1,0,0,1,f)
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  -- Now at (0, 0+1, 0+1, 0, 1+1, f) i.e. (0, 1, 1, 0, 2, f)
  apply stepStar_trans (step_stepStar
    (show fm ⟨0, 0+1, 0+1, 0, 1+1, f⟩ = some ⟨2, 0+1, 0, 0, 1, f⟩ from by unfold fm; rfl))
  -- Now at (2, 1, 0, 0, 1, f)
  apply stepStar_trans (big_phase 1 0 0 1 f (by omega))
  simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero]; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n f, q = ⟨0, 0, 0, n, 2*n+1, f+1⟩)
  · intro c ⟨n, f, hq⟩; subst hq
    rcases n with _ | n
    · exact ⟨⟨0, 0, 0, 1, 3, f+3⟩, ⟨1, f+2, by ring_nf⟩, trans_zero f⟩
    · exact ⟨⟨0, 0, 0, n+2, 2*(n+2)+1, f+n+4⟩,
        ⟨n+2, f+n+3, by ring_nf⟩, trans_succ n f⟩
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_630
