import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #824: [35/6, 8/55, 143/2, 3/7, 15/13]

Vector representation:
```
-1 -1  1  1  0  0
 3  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_824

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

theorem r4_drain : ∀ k, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

theorem r3_drain : ∀ k, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih generalizing a e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (e := e + 1) (f := f + 1))
    ring_nf; finish

theorem r2_chain : ∀ k, ⟨a, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨a + 3 * k, 0, c, d, e, f⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 3))
    ring_nf; finish

theorem middle : ∀ b, ∀ c d e f, ⟨3, b, c, d, e + b + c, f⟩ [fm]⊢*
    ⟨2 * b + 3 * c + 3, 0, 0, d + b, e, f⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih
  intro c d e f
  rcases b with _ | _ | _ | b
  · -- b = 0: R2 chain
    simp only [Nat.zero_add, Nat.add_zero, Nat.mul_zero]
    have := r2_chain c (a := 3) (c := 0) (d := d) (e := e) (f := f)
    simp only [Nat.zero_add] at this
    rw [show 3 + 3 * c = 3 * c + 3 from by ring] at this
    exact this
  · -- b = 1: R1, then R2 chain
    simp only [Nat.reduceAdd]
    rw [show e + 1 + c = (e + (c + 1)) from by ring]
    step fm
    have := r2_chain (c + 1) (a := 2) (c := 0) (d := d + 1) (e := e) (f := f)
    simp only [Nat.zero_add] at this
    rw [show 2 + 3 * (c + 1) = 2 * 1 + 3 * c + 3 from by ring] at this
    exact this
  · -- b = 2: R1×2, then R2 chain
    simp only [Nat.reduceAdd]
    rw [show e + 2 + c = (e + (c + 2)) from by ring]
    step fm; step fm
    have := r2_chain (c + 2) (a := 1) (c := 0) (d := d + 2) (e := e) (f := f)
    simp only [Nat.zero_add] at this
    rw [show 1 + 3 * (c + 2) = 2 * 2 + 3 * c + 3 from by ring] at this
    exact this
  · -- b = b + 3: R1×3, R2, then IH(b)
    rw [show e + (b + 3) + c = (e + b + (c + 2)) + 1 from by ring,
        show (b + 3 : ℕ) = (b + 2) + 1 from by ring]
    step fm
    rw [show (b + 2 : ℕ) = (b + 1) + 1 from by ring]
    step fm
    step fm
    rw [show c + 1 + 1 + 1 = (c + 2) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (by omega) (c + 2) (d + 3) e f)
    ring_nf; finish

-- The main transition composing all phases
theorem transition : ∀ d e f,
    ⟨0, 0, 0, d + 1, e + d + 3, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, d + 2, e + 2 * d + 7, f + 2 * d + 7⟩ := by
  intro d e f
  -- Phase 1: R4 drain
  apply stepStar_stepPlus_stepPlus
  · rw [show d + 1 = 0 + (d + 1) from by ring]
    exact r4_drain (d + 1) (b := 0) (d := 0)
  rw [show (0 : ℕ) + (d + 1) = d + 1 from by ring]
  step fm
  -- Now goal should involve (0, d+2, 1, 0, e+d+3, f) ⊢* ...
  -- Phase 3: R2 step. Need c=1 and e+d+3 >= 1
  rw [show e + d + 3 = (e + d + 2) + 1 from by ring]
  step fm  -- R2: matches ⟨a, b, c+1, d, e+1, f⟩
  -- Now at (3, d+2, 0, 0, e+d+2, f) ⊢* ...
  -- Phase 4: Middle section
  apply stepStar_trans
  · show ⟨3, d + 2, 0, 0, e + d + 2, f⟩ [fm]⊢* ⟨2 * d + 7, 0, 0, d + 2, e, f⟩
    have := middle (d + 2) 0 0 e f
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
    rw [show 2 * (d + 2) + 3 = 2 * d + 7 from by ring] at this
    exact this
  -- Phase 5: R3 drain
  have := r3_drain (2 * d + 7) (a := 0) (d := d + 2) (e := e) (f := f)
  simp only [Nat.zero_add] at this
  exact this

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 4, 5⟩)
  · execute fm 10
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨d, e, f⟩ ↦ ⟨0, 0, 0, d + 1, e + d + 3, f + 1⟩) ⟨0, 1, 4⟩
  intro ⟨d, e, f⟩
  exact ⟨⟨d + 1, e + d + 3, f + 2 * d + 6⟩, by
    show ⟨0, 0, 0, d + 1, e + d + 3, f + 1⟩ [fm]⊢⁺
         ⟨0, 0, 0, (d + 1) + 1, (e + d + 3) + (d + 1) + 3, (f + 2 * d + 6) + 1⟩
    rw [show (d + 1) + 1 = d + 2 from by ring,
        show (e + d + 3) + (d + 1) + 3 = e + 2 * d + 7 from by ring,
        show (f + 2 * d + 6) + 1 = f + 2 * d + 7 from by ring]
    exact transition d e f⟩

end Sz22_2003_unofficial_824
