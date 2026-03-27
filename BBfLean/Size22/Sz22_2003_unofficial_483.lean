import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #483: [28/15, 3/22, 175/2, 11/7, 21/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  1  0
 0  0  0 -1  1
 0  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_483

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 repeated: transfer k from d to e
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e; rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih _ _ _); ring_nf; finish

-- R2,R1 chain: k rounds consuming c and e
theorem r2r1_chain : ∀ k, ∀ a c d e, ⟨a + 1, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + k + 1, 0, c, d + k, e⟩ := by
  intro k; induction k with
  | zero => intro a c d e; exists 0
  | succ k ih =>
    intro a c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _ _ _); ring_nf; finish

-- R2 chain: transfer from (a,e) to b
theorem r2_chain : ∀ k, ∀ a b d, ⟨a + k, b, 0, d, k⟩ [fm]⊢* ⟨a, b + k, 0, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d; rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih _ _ _); ring_nf; finish

-- R3 drain: convert a to c (b=0, e=0)
theorem r3_drain : ∀ a, ∀ c d, ⟨a, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c + 2 * a, d + a, 0⟩ := by
  intro a; induction a with
  | zero => intro c d; exists 0
  | succ a ih =>
    intro c d; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish

-- Cascade: (a+1, b, 0, d, 0) -> (0, 0, 2*a+3*b+2, d+a+3*b+1, 0)
theorem cascade : ∀ b, ∀ a d, ⟨a + 1, b, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 2 * a + 3 * b + 2, d + a + 3 * b + 1, 0⟩ := by
  intro b; induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d
    match b with
    | 0 =>
      apply stepStar_trans (r3_drain (a + 1) 0 d); ring_nf; finish
    | 1 =>
      step fm; step fm; step fm
      apply stepStar_trans (r3_drain (a + 1) 3 (d + 3)); ring_nf; finish
    | b + 2 =>
      step fm; step fm; step fm
      apply stepStar_trans (ih b (by omega) (a + 3) (d + 3)); ring_nf; finish

-- Full transition as ⊢⁺
theorem full_transition (c e : ℕ) (hce : c ≤ e + 1) (hec : e ≤ 2 * c) :
    ⟨0, 0, c + 2, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, c + e + 5, 0, 2 * e + 6⟩ := by
  -- R5: (0, 1, c+1, 1, e+1)
  apply stepStar_stepPlus_stepPlus
  · exists 0
  -- R1 gives us one plus step
  step fm; step fm
  -- Now at (2, 0, c, 2, e+1). Apply R2R1 chain of c steps.
  show ⟨2, 0, c, 2, e + 1⟩ [fm]⊢* ⟨0, 0, c + e + 5, 0, 2 * e + 6⟩
  -- Rewrite to match r2r1_chain signature
  have hr2r1 : ⟨1 + 1, 0, 0 + c, 2, (e + 1 - c) + c⟩ [fm]⊢* ⟨1 + c + 1, 0, 0, 2 + c, e + 1 - c⟩ :=
    r2r1_chain c 1 0 2 (e + 1 - c)
  rw [show (1 : ℕ) + 1 = 2 from by ring, show (0 : ℕ) + c = c from by ring,
      show (e + 1 - c) + c = e + 1 from by omega,
      show 1 + c + 1 = c + 2 from by ring, show 2 + c = c + 2 from by ring] at hr2r1
  apply stepStar_trans hr2r1
  -- Now at (c+2, 0, 0, c+2, e+1-c). R2 chain.
  have hr2 : ⟨(2 * c + 1 - e) + (e + 1 - c), 0, 0, c + 2, e + 1 - c⟩ [fm]⊢* ⟨2 * c + 1 - e, 0 + (e + 1 - c), 0, c + 2, 0⟩ :=
    r2_chain (e + 1 - c) (2 * c + 1 - e) 0 (c + 2)
  rw [show (2 * c + 1 - e) + (e + 1 - c) = c + 2 from by omega,
      show 0 + (e + 1 - c) = e + 1 - c from by ring] at hr2
  apply stepStar_trans hr2
  -- Now at (2c+1-e, e+1-c, 0, c+2, 0). Cascade.
  rw [show 2 * c + 1 - e = (2 * c - e) + 1 from by omega]
  apply stepStar_trans (cascade (e + 1 - c) (2 * c - e) (c + 2))
  -- After cascade: (0, 0, 2*(2c-e) + 3*(e+1-c) + 2, (c+2)+(2c-e)+3*(e+1-c)+1, 0)
  -- Simplify to target via R4 drain
  rw [show 2 * (2 * c - e) + 3 * (e + 1 - c) + 2 = c + e + 5 from by omega,
      show c + 2 + (2 * c - e) + 3 * (e + 1 - c) + 1 = 2 * e + 6 from by omega,
      show (2 * e + 6 : ℕ) = 0 + (2 * e + 6) from by ring]
  apply stepStar_trans (d_to_e (2 * e + 6) (c + e + 5) 0 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c + 2, 0, e + 1⟩ ∧ c ≤ e + 1 ∧ e ≤ 2 * c)
  · intro q ⟨c, e, hq, hce, hec⟩
    refine ⟨⟨0, 0, c + e + 5, 0, 2 * e + 6⟩, ⟨c + e + 3, 2 * e + 5, ?_, ?_, ?_⟩, ?_⟩
    · ring_nf
    · omega
    · omega
    · rw [hq]; exact full_transition c e hce hec
  · exact ⟨0, 0, rfl, by omega, by omega⟩
end Sz22_2003_unofficial_483
