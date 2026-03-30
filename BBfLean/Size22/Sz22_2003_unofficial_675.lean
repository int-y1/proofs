import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #675: [35/6, 28/55, 847/2, 3/7, 5/3]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  1 -1
-1  0  0  1  2
 0  1  0 -1  0
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_675

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c (d + 1) e)
    ring_nf; finish

theorem r2r1r1_cycle : ∀ k, ∀ c d e, ⟨0, 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k + 1, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 3) e)
    ring_nf; finish

theorem r3r2r2_even : ∀ k, ∀ a d, ⟨a + 1, 0, 2 * k, d, 0⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 3) (d + 3))
    ring_nf; finish

theorem r3r2r2_odd : ∀ k, ∀ a d, ⟨a + 1, 0, 2 * k + 1, d, 0⟩ [fm]⊢* ⟨a + 3 * k + 2, 0, 0, d + 3 * k + 2, 1⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring]
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 3) (d + 3))
    ring_nf; finish

theorem phase12 (b e : ℕ) : ⟨0, 2 * b + 1, 0, 0, e + b + 1⟩ [fm]⊢⁺ ⟨0, 0, b + 1, 3 * b, e + 1⟩ := by
  rw [show 2 * b + 1 = (2 * b) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, (2 * b) + 1, 0, 0, e + b + 1⟩ = some ⟨0, 2 * b, 0 + 1, 0, e + b + 1⟩
    simp [fm]
  rw [show e + b + 1 = (e + 1) + b from by ring]
  apply stepStar_trans (r2r1r1_cycle b 0 0 (e + 1))
  ring_nf; finish

theorem phase3_a (b f : ℕ) :
    ⟨0, 0, b + 1, 3 * b, f + b + 1⟩ [fm]⊢* ⟨0, 6 * b + 3, 0, 0, f + 4 * b + 4⟩ := by
  rw [show b + 1 = 0 + (b + 1) from by omega,
      show f + b + 1 = f + (b + 1) from by ring,
      show 6 * b + 3 = 0 + (6 * b + 3) from by omega,
      show f + 4 * b + 4 = f + 2 * (2 * b + 2) from by ring]
  apply stepStar_trans (r2_chain (b + 1) 0 0 (3 * b) f)
  rw [show 0 + 2 * (b + 1) = 0 + (2 * b + 2) from by ring,
      show 3 * b + (b + 1) = 4 * b + 1 from by ring]
  apply stepStar_trans (r3_chain (2 * b + 2) 0 (4 * b + 1) f)
  rw [show 4 * b + 1 + (2 * b + 2) = 0 + (6 * b + 3) from by ring]
  exact r4_chain (6 * b + 3) 0 0 (f + 2 * (2 * b + 2))

theorem phase3_b_even (e p : ℕ) :
    ⟨0, 0, e + 2 * p + 1, 3 * e + 6 * p, e + 1⟩ [fm]⊢*
    ⟨0, 6 * e + 12 * p + 3, 0, 0, 4 * e + 6 * p + 4⟩ := by
  rw [show e + 1 = 0 + (e + 1) from by omega,
      show e + 2 * p + 1 = 2 * p + (e + 1) from by ring,
      show 6 * e + 12 * p + 3 = 0 + (6 * e + 12 * p + 3) from by omega,
      show 4 * e + 6 * p + 4 = 0 + 2 * (2 * e + 3 * p + 2) from by ring]
  apply stepStar_trans (r2_chain (e + 1) 0 (2 * p) (3 * e + 6 * p) 0)
  rw [show 0 + 2 * (e + 1) = (2 * e + 1) + 1 from by ring,
      show 3 * e + 6 * p + (e + 1) = 4 * e + 6 * p + 1 from by ring]
  apply stepStar_trans (r3r2r2_even p (2 * e + 1) (4 * e + 6 * p + 1))
  rw [show 2 * e + 1 + 3 * p + 1 = 0 + (2 * e + 3 * p + 2) from by ring,
      show 4 * e + 6 * p + 1 + 3 * p = 4 * e + 9 * p + 1 from by ring]
  apply stepStar_trans (r3_chain (2 * e + 3 * p + 2) 0 (4 * e + 9 * p + 1) 0)
  rw [show 4 * e + 9 * p + 1 + (2 * e + 3 * p + 2) = 0 + (6 * e + 12 * p + 3) from by ring]
  exact r4_chain (6 * e + 12 * p + 3) 0 0 (0 + 2 * (2 * e + 3 * p + 2))

theorem phase3_b_odd (e p : ℕ) :
    ⟨0, 0, e + 2 * p + 2, 3 * e + 6 * p + 3, e + 1⟩ [fm]⊢*
    ⟨0, 6 * e + 12 * p + 9, 0, 0, 4 * e + 6 * p + 7⟩ := by
  rw [show e + 1 = 0 + (e + 1) from by omega,
      show e + 2 * p + 2 = (2 * p + 1) + (e + 1) from by ring,
      show 6 * e + 12 * p + 9 = 0 + (6 * e + 12 * p + 9) from by omega,
      show 4 * e + 6 * p + 7 = 1 + 2 * (2 * e + 3 * p + 3) from by ring]
  apply stepStar_trans (r2_chain (e + 1) 0 (2 * p + 1) (3 * e + 6 * p + 3) 0)
  rw [show 0 + 2 * (e + 1) = (2 * e + 1) + 1 from by ring,
      show 3 * e + 6 * p + 3 + (e + 1) = 4 * e + 6 * p + 4 from by ring]
  apply stepStar_trans (r3r2r2_odd p (2 * e + 1) (4 * e + 6 * p + 4))
  rw [show 2 * e + 1 + 3 * p + 2 = 0 + (2 * e + 3 * p + 3) from by ring,
      show 4 * e + 6 * p + 4 + 3 * p + 2 = 4 * e + 9 * p + 6 from by ring]
  apply stepStar_trans (r3_chain (2 * e + 3 * p + 3) 0 (4 * e + 9 * p + 6) 1)
  rw [show 4 * e + 9 * p + 6 + (2 * e + 3 * p + 3) = 0 + (6 * e + 12 * p + 9) from by ring]
  exact r4_chain (6 * e + 12 * p + 9) 0 0 (1 + 2 * (2 * e + 3 * p + 3))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 3, 0, 0, 5⟩) (by execute fm 9)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ b e, q = ⟨0, 2 * b + 1, 0, 0, e + b + 1⟩)
  · intro c ⟨b, e, hq⟩; subst hq
    rcases (show b ≤ e ∨ e < b from by omega) with hbe | hbe
    · obtain ⟨f, rfl⟩ : ∃ f, e = b + f := ⟨e - b, by omega⟩
      refine ⟨⟨0, 6 * b + 3, 0, 0, f + 4 * b + 4⟩, ⟨3 * b + 1, b + f + 2, by ring_nf⟩, ?_⟩
      apply stepPlus_stepStar_stepPlus (phase12 b (b + f))
      have key := phase3_a b f
      convert key using 2; ring_nf
    · rcases Nat.even_or_odd (b - e) with ⟨p, hp⟩ | ⟨p, hp⟩
      · have hb : b = e + 2 * p := by omega
        subst hb
        refine ⟨⟨0, 6 * e + 12 * p + 3, 0, 0, 4 * e + 6 * p + 4⟩,
          ⟨3 * e + 6 * p + 1, e + 2, by ring_nf⟩, ?_⟩
        apply stepPlus_stepStar_stepPlus (phase12 (e + 2 * p) e)
        have key := phase3_b_even e p
        convert key using 2; ring_nf
      · have hb : b = e + 2 * p + 1 := by omega
        subst hb
        refine ⟨⟨0, 6 * e + 12 * p + 9, 0, 0, 4 * e + 6 * p + 7⟩,
          ⟨3 * e + 6 * p + 4, e + 2, by ring_nf⟩, ?_⟩
        apply stepPlus_stepStar_stepPlus (phase12 (e + 2 * p + 1) e)
        have key := phase3_b_odd e p
        convert key using 2; ring_nf
  · exact ⟨1, 3, by ring_nf⟩
