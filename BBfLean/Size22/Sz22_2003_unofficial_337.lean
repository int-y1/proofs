import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #337: [189/10, 2/33, 121/2, 5/7, 10/11]

Vector representation:
```
-1  3 -1  1  0
 1 -1  0  0 -1
-1  0  0  0  2
 0  0  1 -1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_337

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+3, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem d_to_c : ∀ k c e, ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

theorem r3_drain : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih d (e + 2))
    ring_nf; finish

theorem r2_drain : ∀ k a d e, ⟨a, k, 0, d, e + k⟩ [fm]⊢* ⟨a + k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) d e)
    ring_nf; finish

theorem r1r2_loop : ∀ k b d e, ⟨1, b, k + 1, d, e + k⟩ [fm]⊢* ⟨1, b + 2 * k, 1, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · simp; exists 0
  · rw [show k + 1 + 1 = (k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b + 2) (d + 1) e)
    ring_nf; finish

theorem zigzag : ∀ n e, ⟨0, 0, n, 0, e + n + 1⟩ [fm]⊢* ⟨0, 2 * n + 3, 0, n + 1, e⟩ := by
  intro n e
  rw [show e + n + 1 = (e + n) + 1 from by ring]
  step fm
  apply stepStar_trans (r1r2_loop n 0 0 e)
  rw [show 0 + 2 * n = 2 * n from by ring,
      show 0 + n = n from by ring]
  step fm
  finish

theorem main_trans (n r : ℕ) :
    (⟨0, 0, 0, n + 4, r + 3 * n + 16⟩ : Q) [fm]⊢⁺
    ⟨0, 0, 0, n + 5, r + 4 * n + 22⟩ := by
  -- Phase 1: d_to_c
  -- Phase 2: zigzag
  -- Phase 3: r2_drain
  -- Phase 4: r3_drain
  -- Combine all as stepStar, then convert to stepPlus.
  have phase1 : (⟨0, 0, 0, n + 4, r + 3 * n + 16⟩ : Q) [fm]⊢*
      ⟨0, 0, n + 4, 0, r + 3 * n + 16⟩ := by
    have h := d_to_c (n + 4) 0 (r + 3 * n + 16)
    simp at h; exact h
  have phase2 : (⟨0, 0, n + 4, 0, r + 3 * n + 16⟩ : Q) [fm]⊢*
      ⟨0, 2 * n + 11, 0, n + 5, r + 2 * n + 11⟩ := by
    have h := zigzag (n + 4) (r + 2 * n + 11)
    rw [show r + 2 * n + 11 + (n + 4) + 1 = r + 3 * n + 16 from by ring,
        show 2 * (n + 4) + 3 = 2 * n + 11 from by ring,
        show (n + 4) + 1 = n + 5 from by ring] at h
    exact h
  have phase3 : (⟨0, 2 * n + 11, 0, n + 5, r + 2 * n + 11⟩ : Q) [fm]⊢*
      ⟨2 * n + 11, 0, 0, n + 5, r⟩ := by
    have h := r2_drain (2 * n + 11) 0 (n + 5) r
    rw [show r + (2 * n + 11) = r + 2 * n + 11 from by ring] at h
    simp at h; exact h
  have phase4 : (⟨2 * n + 11, 0, 0, n + 5, r⟩ : Q) [fm]⊢*
      ⟨0, 0, 0, n + 5, r + 2 * (2 * n + 11)⟩ := r3_drain (2 * n + 11) (n + 5) r
  have combined : (⟨0, 0, 0, n + 4, r + 3 * n + 16⟩ : Q) [fm]⊢*
      ⟨0, 0, 0, n + 5, r + 2 * (2 * n + 11)⟩ :=
    stepStar_trans phase1 (stepStar_trans phase2 (stepStar_trans phase3 phase4))
  have htarget : (⟨0, 0, 0, n + 5, r + 2 * (2 * n + 11)⟩ : Q) =
      ⟨0, 0, 0, n + 5, r + 4 * n + 22⟩ := by ring_nf
  rw [htarget] at combined
  have hneq : (⟨0, 0, 0, n + 4, r + 3 * n + 16⟩ : Q) ≠ ⟨0, 0, 0, n + 5, r + 4 * n + 22⟩ := by
    intro h; have := congr_arg (fun x : Q ↦ x.2.2.2.1) h; simp at this
  exact stepStar_stepPlus combined hneq

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 16⟩)
  · execute fm 75
  apply progress_nonhalt (fm := fm)
    (P := fun c ↦ ∃ n r, c = (⟨0, 0, 0, n + 4, r + 3 * n + 16⟩ : Q))
  · intro c ⟨n, r, hc⟩
    subst hc
    exact ⟨⟨0, 0, 0, n + 5, r + 4 * n + 22⟩,
      ⟨n + 1, r + n + 3, by ring_nf⟩,
      main_trans n r⟩
  · exact ⟨0, 0, by ring_nf⟩

end Sz22_2003_unofficial_337
