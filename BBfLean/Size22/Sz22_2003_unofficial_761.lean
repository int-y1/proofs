import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #761: [35/6, 4/55, 847/2, 3/7, 6/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  1  2
 0  1  0 -1  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_761

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r3_chain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 2))
    ring_nf; finish

theorem r2_chain : ∀ k a c d, ⟨a, 0, c + k, d, k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k + 1) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 2) c d)
    ring_nf; finish

theorem r1r1r2_chain : ∀ k b c d e,
    ⟨2, b + 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring,
        show d + 1 + 1 = (d + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e)
    ring_nf; finish

theorem tail_lemma : ∀ C, ∀ a d,
    ⟨a + 1, 0, C, d, 0⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * C + a + 1, 2 * a + 3 * C + 2⟩ := by
  intro C; induction C using Nat.strongRecOn with
  | _ C ih =>
  intro a d
  rcases C with _ | C
  · -- C = 0: R3 chain
    have key := r3_chain (a + 1) 0 d 0
    convert key using 1; ring_nf
  rcases C with _ | C
  · -- C = 1: R3, R2, then R3 chain
    rw [show a + 1 = a + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from rfl]
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring,
        show d + 1 + 1 = d + 2 from by ring]
    step fm
    have key := r3_chain (a + 1) 0 (d + 2) 3
    convert key using 1; ring_nf
  · -- C + 2: R3, R2, R2, then ih C
    rw [show (C + 2 : ℕ) = (C + 1) + 1 from by ring]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from rfl]
    step fm
    rw [show C + 1 = C + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show a + 2 + 2 = (a + 3) + 1 from by ring,
        show d + 1 = d + 1 from rfl]
    have key := ih C (by omega) (a + 3) (d + 1)
    convert key using 1; ring_nf

theorem main_trans (p q : ℕ) :
    ⟨0, 0, 0, 2 * p + 2 * q + 1, 2 * p + q + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * p + 4 * q + 5, 4 * p + 3 * q + 5⟩ := by
  -- Phase 1: R4 chain
  have phase1 : ⟨0, 0, 0, 2 * p + 2 * q + 1, 2 * p + q + 2⟩ [fm]⊢*
      ⟨0, 2 * p + 2 * q + 1, 0, 0, 2 * p + q + 2⟩ := by
    rw [show 2 * p + 2 * q + 1 = 0 + (2 * p + 2 * q + 1) from by ring]
    exact r4_chain (2 * p + 2 * q + 1) 0 0 (2 * p + q + 2)
  -- Phase 2+3: R5, R1, R2 (3 steps)
  have phase23 : ⟨0, 2 * p + 2 * q + 1, 0, 0, 2 * p + q + 2⟩ [fm]⊢⁺
      ⟨2, 2 * p + 2 * q + 1, 0, 1, 2 * p + q⟩ := by
    rw [show 2 * p + q + 2 = (2 * p + q) + 1 + 1 from by ring,
        show 2 * p + 2 * q + 1 = (2 * p + 2 * q) + 1 from by ring]
    step fm
    rw [show 2 * p + 2 * q + 1 + 1 = (2 * p + 2 * q + 1) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from rfl,
        show 2 * p + q + 1 = (2 * p + q) + 1 from by ring]
    step fm; finish
  -- Phase 4: (p+q) rounds of R1,R1,R2
  have phase4 : ⟨2, 2 * p + 2 * q + 1, 0, 1, 2 * p + q⟩ [fm]⊢*
      ⟨2, 1, p + q, 2 * p + 2 * q + 1, p⟩ := by
    rw [show 2 * p + 2 * q + 1 = 1 + 2 * (p + q) from by ring,
        show 2 * p + q = p + (p + q) from by ring]
    have key := r1r1r2_chain (p + q) 1 0 1 p
    convert key using 1; ring_nf
  -- Phase 5: R1 step
  have phase5 : ⟨2, 1, p + q, 2 * p + 2 * q + 1, p⟩ [fm]⊢*
      ⟨1, 0, p + q + 1, 2 * p + 2 * q + 2, p⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm; ring_nf; finish
  -- Phase 6: R2 drain p steps
  have phase6 : ⟨1, 0, p + q + 1, 2 * p + 2 * q + 2, p⟩ [fm]⊢*
      ⟨2 * p + 1, 0, q + 1, 2 * p + 2 * q + 2, 0⟩ := by
    rw [show p + q + 1 = (q + 1) + p from by ring]
    have key := r2_chain p 1 (q + 1) (2 * p + 2 * q + 2)
    convert key using 1; ring_nf
  -- Phase 7: tail
  have phase7 : ⟨2 * p + 1, 0, q + 1, 2 * p + 2 * q + 2, 0⟩ [fm]⊢*
      ⟨0, 0, 0, 4 * p + 4 * q + 5, 4 * p + 3 * q + 5⟩ := by
    rw [show 2 * p + 1 = (2 * p) + 1 from by ring]
    have key := tail_lemma (q + 1) (2 * p) (2 * p + 2 * q + 2)
    convert key using 1; ring_nf
  exact stepStar_stepPlus_stepPlus phase1
    (stepPlus_stepStar_stepPlus phase23
      (stepStar_trans phase4
        (stepStar_trans phase5
          (stepStar_trans phase6 phase7))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun s ↦ ∃ p q, s = ⟨0, 0, 0, 2 * p + 2 * q + 1, 2 * p + q + 2⟩)
  · intro c ⟨p, q, hq⟩; subst hq
    exact ⟨⟨0, 0, 0, 4 * p + 4 * q + 5, 4 * p + 3 * q + 5⟩,
      ⟨2 * p + q + 1, q + 1, by ring_nf⟩,
      main_trans p q⟩
  · exact ⟨0, 0, by ring_nf⟩

end Sz22_2003_unofficial_761
