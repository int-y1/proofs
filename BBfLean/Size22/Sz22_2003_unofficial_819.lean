import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #819: [35/6, 8/55, 121/2, 3/7, 14/11]

Vector representation:
```
-1 -1  1  1  0
 3  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_819

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (e := e + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

theorem r2_chain : ∀ c, ⟨a, 0, c, d, E + c⟩ [fm]⊢* ⟨a + 3 * c, 0, 0, d, E⟩ := by
  intro c; induction' c with c ih generalizing a d E
  · exists 0
  · rw [show E + (c + 1) = (E + c) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 3))
    ring_nf; finish

theorem r1r2_chain : ∀ b, ∀ a c d E, a ≥ 1 →
    ⟨a, b, c, d, E + b + c⟩ [fm]⊢* ⟨a + 2 * b + 3 * c, 0, 0, d + b, E⟩ := by
  intro b; induction' b with b ih <;> intro a c d E ha
  · simp only [Nat.add_zero, Nat.mul_zero]
    exact r2_chain c
  · rcases a with _ | _ | a'
    · omega
    · -- a = 1: R1 then R2 then recurse with a=3
      rw [show E + (b + 1) + c = (E + b + c) + 1 from by ring]
      step fm -- R1: (0, b, c+1, d+1, E+b+c+1)
      step fm -- R2: (3, b, c, d+1, E+b+c)
      apply stepStar_trans (ih 3 c (d + 1) E (by omega))
      ring_nf; finish
    · -- a = a'+2 >= 2: R1 then recurse with a=a'+1
      rw [show a' + 2 = (a' + 1) + 1 from by ring,
          show E + (b + 1) + c = E + b + (c + 1) from by ring]
      step fm -- R1: (a'+1, b, c+1, d+1, E+b+(c+1))
      apply stepStar_trans (ih (a' + 1) (c + 1) (d + 1) E (by omega))
      ring_nf; finish

theorem complex_phase (B E : ℕ) :
    ⟨0, B + 1, 0, 0, E + B + 2⟩ [fm]⊢⁺ ⟨2 * B + 3, 0, 0, B + 2, E⟩ := by
  rw [show E + B + 2 = (E + B + 1) + 1 from by ring]
  step fm -- R5: (1, B+1, 0, 1, E+B+1)
  rw [show E + B + 1 = (E + B) + 1 from by ring]
  step fm -- R1: (0, B, 1, 2, E+B+1)
  step fm -- R2: (3, B, 0, 2, E+B)
  rw [show E + B = E + B + 0 from by ring]
  apply stepStar_trans (r1r2_chain B 3 0 2 E (by omega))
  ring_nf; finish

theorem phase12 (a d e : ℕ) :
    ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨0, d, 0, 0, e + 2 * a⟩ := by
  rw [show a = 0 + a from by ring]
  apply stepStar_trans (r3_chain a (a := 0) (d := d) (e := e))
  rw [show d = 0 + d from by ring]
  apply stepStar_trans (r4_chain d (b := 0) (d := 0) (e := e + 2 * a))
  ring_nf; finish

theorem main_trans (n e : ℕ) :
    ⟨2 * n + 3, 0, 0, n + 2, e⟩ [fm]⊢⁺ ⟨2 * n + 5, 0, 0, n + 3, e + 3 * n + 3⟩ := by
  apply stepStar_stepPlus_stepPlus (phase12 (2 * n + 3) (n + 2) e)
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show e + 2 * (2 * n + 3) = (e + 3 * n + 3) + (n + 1) + 2 from by ring]
  have h := complex_phase (n + 1) (e + 3 * n + 3)
  rw [show 2 * (n + 1) + 3 = 2 * n + 5 from by ring,
      show (n + 1) + 2 = n + 3 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 2, 1⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨2 * n + 3, 0, 0, n + 2, e⟩) ⟨0, 1⟩
  intro ⟨n, e⟩
  exact ⟨⟨n + 1, e + 3 * n + 3⟩, main_trans n e⟩
