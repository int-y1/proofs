import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #391: [2/15, 99/14, 325/2, 7/11, 21/13]

Vector representation:
```
 1 -1 -1  0  0  0
-1  2  0 -1  1  0
-1  0  2  0  0  1
 0  0  0  1 -1  0
 0  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_391

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+2, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+2, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

-- R4 chain: drains e into d.
theorem r4_chain : ∀ k c d e f,
    (⟨0, 0, c, d, e+k, f⟩ : Q) [fm]⊢* ⟨0, 0, c, d+k, e, f⟩ := by
  intro k; induction k with
  | zero => intro c d e f; simp; exists 0
  | succ k ih =>
    intro c d e f
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) e f)
    ring_nf; finish

-- R1 chain: k steps of R1.
theorem r1_chain : ∀ k a b c d e f,
    (⟨a, b+k, c+k, d, e, f⟩ : Q) [fm]⊢* ⟨a+k, b, c, d, e, f⟩ := by
  intro k; induction k with
  | zero => intro a b c d e f; simp; exists 0
  | succ k ih =>
    intro a b c d e f
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b c d e f)
    ring_nf; finish

-- R2 chain when c = 0: drains d while building b and e.
theorem r2_chain_c0 : ∀ k a b d e f,
    (⟨a+k, b, 0, d+k, e, f⟩ : Q) [fm]⊢* ⟨a, b+2*k, 0, d, e+k, f⟩ := by
  intro k; induction k with
  | zero => intro a b d e f; simp; exists 0
  | succ k ih =>
    intro a b d e f
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 2) d (e + 1) f)
    ring_nf; finish

-- (R1, R1, R2) loop: j+1 iterations.
-- Each iteration: a+1, b=2 → R1 → a+2, b=1 → R1 → a+3, b=0 → R2 → a+2, b=2
-- Net per iteration: a→a+1, c→c-2, d→d-1, e→e+1.
theorem loop_iter : ∀ j a c d e f,
    (⟨a+1, 2, c+2*(j+1), d+(j+1), e, f⟩ : Q) [fm]⊢*
    ⟨a+j+2, 2, c, d, e+j+1, f⟩ := by
  intro j; induction j with
  | zero =>
    intro a c d e f; step fm; step fm; step fm; ring_nf; finish
  | succ j ih =>
    intro a c d e f
    rw [show c + 2 * (j + 1 + 1) = (c + 2 * (j + 1)) + 2 from by ring,
        show d + (j + 1 + 1) = (d + (j + 1)) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1) f)
    ring_nf; finish

-- Phase C even: m = 2(p+1). (1, 0, 2(p+1), 2(p+1), e, f) ->* (1, 2(p+1), 0, 0, e+2(p+1), f)
theorem phaseC_even (p e f : ℕ) :
    (⟨1, 0, 2*(p+1), 2*(p+1), e, f⟩ : Q) [fm]⊢* ⟨1, 2*(p+1), 0, 0, e+2*(p+1), f⟩ := by
  -- R2, R1, R1, R2: 4 initial steps -> (1, 2, 2p, 2p, e+2, f) or (1, 2, 0, 0, e+2, f) if p=0
  step fm; step fm; step fm; step fm
  rcases p with _ | p
  · ring_nf; finish
  -- Now at (1, 2, 2*(p+1), 2*(p+1), e+2, f)
  apply stepStar_trans
  · show (⟨1, 2, 2*(p+1), 2*(p+1), e+2, f⟩ : Q) [fm]⊢* ⟨p+2, 2, 0, p+1, e+p+3, f⟩
    have h := loop_iter p 0 0 (p+1) (e+2) f
    rw [show 0 + 2 * (p + 1) = 2 * (p + 1) from by ring,
        show p + 1 + (p + 1) = 2 * (p + 1) from by ring,
        show 0 + 1 = 1 from by ring,
        show 0 + p + 2 = p + 2 from by ring,
        show e + 2 + p + 1 = e + p + 3 from by ring] at h; exact h
  apply stepStar_trans
  · show (⟨p+2, 2, 0, p+1, e+p+3, f⟩ : Q) [fm]⊢* ⟨1, 2*(p+2), 0, 0, e+2*(p+2), f⟩
    have h := r2_chain_c0 (p+1) 1 2 0 (e+p+3) f
    rw [show 0 + (p + 1) = p + 1 from by ring,
        show 1 + (p + 1) = p + 2 from by ring] at h
    apply stepStar_trans h; ring_nf; finish
  ring_nf; finish

-- Phase C odd: m = 2(p+1)+1. (1, 0, 2(p+1)+1, 2(p+1)+1, e, f) ->* (1, 2(p+1)+1, 0, 0, e+2(p+1)+1, f)
theorem phaseC_odd (p e f : ℕ) :
    (⟨1, 0, 2*(p+1)+1, 2*(p+1)+1, e, f⟩ : Q) [fm]⊢*
    ⟨1, 2*(p+1)+1, 0, 0, e+2*(p+1)+1, f⟩ := by
  -- R2, R1, R1, R2: 4 initial steps -> (1, 2, 2p+1, 2p+1, e+2, f) or (1, 2, 1, 1, e+2, f) if p=0
  step fm; step fm; step fm; step fm
  rcases p with _ | p
  · -- p=0: (1, 2, 1, 1, e+2, f) -> R1, R2 chain
    step fm; step fm; ring_nf; finish
  -- Now at (1, 2, 2*(p+1)+1, 2*(p+1)+1, e+2, f)
  apply stepStar_trans
  · show (⟨1, 2, 2*(p+1)+1, 2*(p+1)+1, e+2, f⟩ : Q) [fm]⊢* ⟨p+2, 2, 1, p+2, e+p+3, f⟩
    have h := loop_iter p 0 1 (p+2) (e+2) f
    rw [show 1 + 2 * (p + 1) = 2 * (p + 1) + 1 from by ring,
        show p + 2 + (p + 1) = 2 * (p + 1) + 1 from by ring,
        show 0 + 1 = 1 from by ring,
        show 0 + p + 2 = p + 2 from by ring,
        show e + 2 + p + 1 = e + p + 3 from by ring] at h; exact h
  -- Now at (p+2, 2, 1, p+2, e+p+3, f)
  -- R1: (p+3, 1, 0, p+2, e+p+3, f) -> R2 chain
  step fm
  apply stepStar_trans
  · have h := r2_chain_c0 (p+2) 1 1 0 (e+p+3) f
    rw [show 0 + (p + 2) = p + 2 from by ring,
        show 1 + (p + 2) = p + 3 from by ring] at h
    apply stepStar_trans h; ring_nf; finish
  ring_nf; finish

-- Phase C: reduce_loop
-- (1, 0, m, m, e, f) ->* (1, m, 0, 0, e+m, f)
theorem phaseC : ∀ m e f, (⟨1, 0, m, m, e, f⟩ : Q) [fm]⊢* ⟨1, m, 0, 0, e+m, f⟩ := by
  intro m e f
  rcases m with _ | _ | m
  · exists 0
  · step fm; step fm; ring_nf; finish
  · rcases Nat.even_or_odd (m + 2) with ⟨p, hp⟩ | ⟨p, hp⟩
    · obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      rw [show m + 2 = 2 * (p' + 1) from by omega]
      exact phaseC_even p' e f
    · obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      rw [show m + 2 = 2 * (p' + 1) + 1 from by omega]
      exact phaseC_odd p' e f

-- R1/R3 drain: strong induction on a+2*b.
theorem r1r3_drain : ∀ n a b c e f, a + 2 * b ≤ n →
    (⟨a+1, b, c, 0, e, f⟩ : Q) [fm]⊢* ⟨0, 0, 2*a+b+c+2, 0, e, f+a+b+1⟩ := by
  intro n; induction' n using Nat.strongRecOn with n ih; intro a b c e f hle
  rcases b with _ | b
  · -- b = 0: pure R3 steps
    rcases a with _ | a
    · step fm; ring_nf; finish
    · step fm
      apply stepStar_trans (ih (a + 2 * 0) (by omega) a 0 (c + 2) e (f + 1) (by omega))
      ring_nf; finish
  · rcases c with _ | c
    · -- b ≥ 1, c = 0: R3 fires
      rcases a with _ | a
      · -- a = 0: R3 then R1
        step fm; step fm
        apply stepStar_trans (ih (0 + 2 * b) (by omega) 0 b 1 e (f + 1) (by omega))
        ring_nf; finish
      · -- a ≥ 1: R3
        step fm
        apply stepStar_trans (ih (a + 2 * (b + 1)) (by omega) a (b + 1) 2 e (f + 1) (by omega))
        ring_nf; finish
    · -- b ≥ 1, c ≥ 1: R1 fires
      step fm
      have h := ih (a + 1 + 2 * b) (by omega) (a + 1) b c e f (by omega)
      rw [show 2 * (a + 1) + b + c + 2 = 2 * a + (b + 1) + (c + 1) + 2 from by ring,
          show f + (a + 1) + b + 1 = f + a + (b + 1) + 1 from by ring] at h
      exact h

-- Main transition: one full cycle.
theorem main_trans (k g : ℕ) :
    (⟨1, 0, k+1, k+1, 0, g⟩ : Q) [fm]⊢⁺ ⟨1, 0, k+2, k+2, 0, g+k+1⟩ := by
  -- Phase 1: phaseC
  apply stepStar_stepPlus_stepPlus
  · exact phaseC (k+1) 0 g
  -- Normalize 0+(k+1) from phaseC output
  simp only [Nat.zero_add]
  -- Phase 2: R3 step
  step fm
  -- Phase 3: R1 + r1r3_drain
  apply stepStar_trans
  · show (⟨0, k + 1, 2, 0, k + 1, g + 1⟩ : Q) [fm]⊢* ⟨0, 0, k + 3, 0, k + 1, g + k + 2⟩
    step fm  -- R1: (1, k, 1, 0, k+1, g+1)
    apply stepStar_trans
    · have h := r1r3_drain (0 + 2 * k) 0 k 1 (k + 1) (g + 1) (by omega)
      rw [show 2 * 0 + k + 1 + 2 = k + 3 from by ring,
          show g + 1 + 0 + k + 1 = g + k + 2 from by ring] at h; exact h
    finish
  -- Phase 4: R4 chain
  apply stepStar_trans
  · have h := r4_chain (k + 1) (k + 3) 0 0 (g + k + 2)
    rw [show 0 + (k + 1) = k + 1 from by ring] at h; exact h
  -- Phase 5: R5 + R1
  step fm; step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 1, 1, 0, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, g⟩ ↦ ⟨1, 0, k+1, k+1, 0, g⟩) ⟨0, 0⟩
  intro ⟨k, g⟩
  exact ⟨⟨k+1, g+k+1⟩, main_trans k g⟩

end Sz22_2003_unofficial_391
