import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1470: [7/15, 3/847, 500/7, 11/5, 7/2]

Vector representation:
```
 0 -1 -1  1  0
 0  1  0 -1 -2
 2  0  3 -1  0
 0  0 -1  0  1
-1  0  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1470

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+2⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a c, (⟨a, 0, c, k, 0⟩ : Q) [fm]⊢* ⟨a + 2 * k, 0, c + 3 * k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; simp; exists 0
  | succ k ih =>
    intro a c; step fm
    apply stepStar_trans (ih (a + 2) (c + 3)); ring_nf; finish

theorem r4_chain : ∀ k, ∀ a e, (⟨a, 0, k, 0, e⟩ : Q) [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; simp; exists 0
  | succ k ih =>
    intro a e; step fm
    apply stepStar_trans (ih a (e + 1)); ring_nf; finish

theorem r5r2_chain : ∀ k, ∀ a b, (⟨a + k, b, 0, 0, 2 * k⟩ : Q) [fm]⊢* ⟨a, b + k, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; simp; exists 0
  | succ k ih =>
    intro a b
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (b + 1)); ring_nf; finish

theorem r5r2_chain_odd : ∀ k, ∀ a b, (⟨a + k, b, 0, 0, 2 * k + 1⟩ : Q) [fm]⊢* ⟨a, b + k, 0, 0, 1⟩ := by
  intro k; induction k with
  | zero => intro a b; simp; exists 0
  | succ k ih =>
    intro a b
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (b + 1)); ring_nf; finish

-- k rounds of (R1x3, R3) with e=0, preserving remainder r in b
theorem r1x3_r3_rounds_e0 : ∀ k, ∀ a d r,
    (⟨a, r + 3 * k, 3, d, 0⟩ : Q) [fm]⊢* ⟨a + 2 * k, r, 3, d + 2 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d r; simp; exists 0
  | succ k ih =>
    intro a d r
    rw [show r + 3 * (k + 1) = (r + 3 * k) + 3 from by ring]
    step fm; step fm; step fm
    rw [show d + 1 + 1 + 1 = d + 3 from by ring]
    apply stepStar_trans (step_stepStar (show (⟨a, r + 3 * k, 0, d + 3, 0⟩ : Q) [fm]⊢ ⟨a + 2, r + 3 * k, 3, d + 2, 0⟩ from by simp [fm]))
    apply stepStar_trans (ih (a + 2) (d + 2) r); ring_nf; finish

-- k rounds of (R1x3, R3) with e=1, preserving remainder r in b
theorem r1x3_r3_rounds_e1 : ∀ k, ∀ a d r,
    (⟨a, r + 3 * k, 3, d, 1⟩ : Q) [fm]⊢* ⟨a + 2 * k, r, 3, d + 2 * k, 1⟩ := by
  intro k; induction k with
  | zero => intro a d r; simp; exists 0
  | succ k ih =>
    intro a d r
    rw [show r + 3 * (k + 1) = (r + 3 * k) + 3 from by ring]
    step fm; step fm; step fm
    rw [show d + 1 + 1 + 1 = d + 3 from by ring]
    apply stepStar_trans (step_stepStar (show (⟨a, r + 3 * k, 0, d + 3, 1⟩ : Q) [fm]⊢ ⟨a + 2, r + 3 * k, 3, d + 2, 1⟩ from by simp [fm]))
    apply stepStar_trans (ih (a + 2) (d + 2) r); ring_nf; finish

theorem r3_chain_e1 : ∀ k, ∀ a c, (⟨a, 0, c, k, 1⟩ : Q) [fm]⊢* ⟨a + 2 * k, 0, c + 3 * k, 0, 1⟩ := by
  intro k; induction k with
  | zero => intro a c; simp; exists 0
  | succ k ih =>
    intro a c; step fm
    apply stepStar_trans (ih (a + 2) (c + 3)); ring_nf; finish

theorem main_trans (n : ℕ) :
    (⟨3 * n ^ 2 + 5 * n + 2, 0, 0, 2 * n + 3, 0⟩ : Q) [fm]⊢⁺
    (⟨3 * n ^ 2 + 11 * n + 10, 0, 0, 2 * n + 5, 0⟩ : Q) := by
  -- Phase 1: R3 chain (first step explicit for ⊢⁺)
  have p1 : (⟨3 * n ^ 2 + 5 * n + 2, 0, 0, 2 * n + 3, 0⟩ : Q) [fm]⊢⁺
      ⟨3 * n ^ 2 + 9 * n + 8, 0, 6 * n + 9, 0, 0⟩ := by
    rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
    apply step_stepStar_stepPlus (by unfold fm; rfl)
    have := r3_chain (2 * n + 2) (3 * n ^ 2 + 5 * n + 4) 3
    rw [show 3 * n ^ 2 + 5 * n + 4 + 2 * (2 * n + 2) = 3 * n ^ 2 + 9 * n + 8 from by ring,
        show 3 + 3 * (2 * n + 2) = 6 * n + 9 from by ring] at this; exact this
  -- Phase 2: R4 chain
  have p2 : (⟨3 * n ^ 2 + 9 * n + 8, 0, 6 * n + 9, 0, 0⟩ : Q) [fm]⊢*
      ⟨3 * n ^ 2 + 9 * n + 8, 0, 0, 0, 6 * n + 9⟩ := by
    have := r4_chain (6 * n + 9) (3 * n ^ 2 + 9 * n + 8) 0
    rw [show 0 + (6 * n + 9) = 6 * n + 9 from by ring] at this; exact this
  -- Phase 3: R5/R2 with odd e
  have p3 : (⟨3 * n ^ 2 + 9 * n + 8, 0, 0, 0, 6 * n + 9⟩ : Q) [fm]⊢*
      ⟨3 * n ^ 2 + 6 * n + 4, 3 * n + 4, 0, 0, 1⟩ := by
    rw [show 3 * n ^ 2 + 9 * n + 8 = (3 * n ^ 2 + 6 * n + 4) + (3 * n + 4) from by ring,
        show 6 * n + 9 = 2 * (3 * n + 4) + 1 from by ring]
    have := r5r2_chain_odd (3 * n + 4) (3 * n ^ 2 + 6 * n + 4) 0
    rw [show 0 + (3 * n + 4) = 3 * n + 4 from by ring] at this; exact this
  -- Phase 4a: R5, R3
  have p4a : (⟨3 * n ^ 2 + 6 * n + 4, 3 * n + 4, 0, 0, 1⟩ : Q) [fm]⊢*
      ⟨3 * n ^ 2 + 6 * n + 5, 3 * n + 4, 3, 0, 1⟩ := by
    rw [show 3 * n ^ 2 + 6 * n + 4 = (3 * n ^ 2 + 6 * n + 3) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 4b: R1x3/R3 rounds with e=1, b=3n+4=1+3(n+1), n+1 rounds leaving r=1
  have p4b : (⟨3 * n ^ 2 + 6 * n + 5, 3 * n + 4, 3, 0, 1⟩ : Q) [fm]⊢*
      ⟨3 * n ^ 2 + 8 * n + 7, 1, 3, 2 * n + 2, 1⟩ := by
    rw [show 3 * n + 4 = 1 + 3 * (n + 1) from by ring]
    have := r1x3_r3_rounds_e1 (n + 1) (3 * n ^ 2 + 6 * n + 5) 0 1
    rw [show 3 * n ^ 2 + 6 * n + 5 + 2 * (n + 1) = 3 * n ^ 2 + 8 * n + 7 from by ring,
        show 0 + 2 * (n + 1) = 2 * n + 2 from by ring] at this; exact this
  -- Phase 4c: Final R1 (b=1, c=3→2, d→d+1)
  have p4c : (⟨3 * n ^ 2 + 8 * n + 7, 1, 3, 2 * n + 2, 1⟩ : Q) [fm]⊢*
      ⟨3 * n ^ 2 + 8 * n + 7, 0, 2, 2 * n + 3, 1⟩ := by
    step fm; ring_nf; finish
  -- Phase 4d: R3 chain with e=1
  have p4d : (⟨3 * n ^ 2 + 8 * n + 7, 0, 2, 2 * n + 3, 1⟩ : Q) [fm]⊢*
      ⟨3 * n ^ 2 + 12 * n + 13, 0, 6 * n + 11, 0, 1⟩ := by
    have := r3_chain_e1 (2 * n + 3) (3 * n ^ 2 + 8 * n + 7) 2
    rw [show 3 * n ^ 2 + 8 * n + 7 + 2 * (2 * n + 3) = 3 * n ^ 2 + 12 * n + 13 from by ring,
        show 2 + 3 * (2 * n + 3) = 6 * n + 11 from by ring] at this; exact this
  -- Phase 5: R4 chain
  have p5 : (⟨3 * n ^ 2 + 12 * n + 13, 0, 6 * n + 11, 0, 1⟩ : Q) [fm]⊢*
      ⟨3 * n ^ 2 + 12 * n + 13, 0, 0, 0, 6 * n + 12⟩ := by
    have := r4_chain (6 * n + 11) (3 * n ^ 2 + 12 * n + 13) 1
    rw [show 1 + (6 * n + 11) = 6 * n + 12 from by ring] at this; exact this
  -- Phase 6: R5/R2 with even e
  have p6 : (⟨3 * n ^ 2 + 12 * n + 13, 0, 0, 0, 6 * n + 12⟩ : Q) [fm]⊢*
      ⟨3 * n ^ 2 + 9 * n + 7, 3 * n + 6, 0, 0, 0⟩ := by
    rw [show 3 * n ^ 2 + 12 * n + 13 = (3 * n ^ 2 + 9 * n + 7) + (3 * n + 6) from by ring,
        show 6 * n + 12 = 2 * (3 * n + 6) from by ring]
    have := r5r2_chain (3 * n + 6) (3 * n ^ 2 + 9 * n + 7) 0
    rw [show 0 + (3 * n + 6) = 3 * n + 6 from by ring] at this; exact this
  -- Phase 7a: R5, R3
  have p7a : (⟨3 * n ^ 2 + 9 * n + 7, 3 * n + 6, 0, 0, 0⟩ : Q) [fm]⊢*
      ⟨3 * n ^ 2 + 9 * n + 8, 3 * n + 6, 3, 0, 0⟩ := by
    rw [show 3 * n ^ 2 + 9 * n + 7 = (3 * n ^ 2 + 9 * n + 6) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 7b: n+1 rounds of (R1x3, R3) with e=0, b=3n+6=3+3(n+1), leaving r=3
  have p7b : (⟨3 * n ^ 2 + 9 * n + 8, 3 * n + 6, 3, 0, 0⟩ : Q) [fm]⊢*
      ⟨3 * n ^ 2 + 11 * n + 10, 3, 3, 2 * n + 2, 0⟩ := by
    rw [show 3 * n + 6 = 3 + 3 * (n + 1) from by ring]
    have := r1x3_r3_rounds_e0 (n + 1) (3 * n ^ 2 + 9 * n + 8) 0 3
    rw [show 3 * n ^ 2 + 9 * n + 8 + 2 * (n + 1) = 3 * n ^ 2 + 11 * n + 10 from by ring,
        show 0 + 2 * (n + 1) = 2 * n + 2 from by ring] at this; exact this
  -- Phase 7c: Final R1x3 (b=3, c=3 → b=0, c=0, d+=3)
  have p7c : (⟨3 * n ^ 2 + 11 * n + 10, 3, 3, 2 * n + 2, 0⟩ : Q) [fm]⊢*
      ⟨3 * n ^ 2 + 11 * n + 10, 0, 0, 2 * n + 5, 0⟩ := by
    step fm; step fm; step fm; ring_nf; finish
  -- Compose all phases
  exact stepPlus_stepStar_stepPlus p1
    (stepStar_trans p2 (stepStar_trans p3 (stepStar_trans p4a (stepStar_trans p4b
      (stepStar_trans p4c (stepStar_trans p4d (stepStar_trans p5 (stepStar_trans p6
        (stepStar_trans p7a (stepStar_trans p7b p7c))))))))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 3, 0⟩) (by execute fm 27)
  rw [show (⟨2, 0, 0, 3, 0⟩ : Q) = ⟨3 * 0 ^ 2 + 5 * 0 + 2, 0, 0, 2 * 0 + 3, 0⟩ from by norm_num]
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨3 * n ^ 2 + 5 * n + 2, 0, 0, 2 * n + 3, 0⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  have := main_trans n
  rw [show 3 * n ^ 2 + 11 * n + 10 = 3 * (n + 1) ^ 2 + 5 * (n + 1) + 2 from by ring,
      show 2 * n + 5 = 2 * (n + 1) + 3 from by ring] at this
  exact this

end Sz22_2003_unofficial_1470
