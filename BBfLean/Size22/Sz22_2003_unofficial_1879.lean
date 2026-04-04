import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1879: [9/35, 5/33, 242/5, 7/11, 275/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  1  0 -1
 1  0 -1  0  2
 0  0  0  1 -1
-1  0  2  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1879

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d
  · finish
  · rw [show e + (k + 1) = e + k + 1 from by ring]; step fm
    apply stepStar_trans (ih (d + 1)); ring_nf; finish

theorem r3_chain : ∀ k, ∀ a e, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · finish
  · step fm; apply stepStar_trans (ih (a + 1) (e + 2)); ring_nf; finish

theorem drain_loop_aux : ∀ k, ∀ a b d, ⟨a + k, b, 0, d + 3 * k, 0⟩ [fm]⊢* ⟨a, b + 5 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · finish
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show d + 3 * (k + 1) = (d + 3) + 3 * k from by ring]
    apply stepStar_trans (ih (a + 1) b (d + 3))
    step fm; step fm; step fm; step fm; step fm; ring_nf; finish

theorem drain_loop (k a b d : ℕ) : ⟨a + k, b, 0, d + 3 * k, 0⟩ [fm]⊢* ⟨a, b + 5 * k, 0, d, 0⟩ :=
  drain_loop_aux k a b d

theorem combined_chain : ∀ b, ∀ a c, ⟨a, b, c, 0, 2⟩ [fm]⊢* ⟨a + b + c, 0, 0, 0, 2 * c + b + 2⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro a c
  rcases b with _ | _ | b
  · apply stepStar_trans (r3_chain c a 2); ring_nf; finish
  · step fm; apply stepStar_trans (r3_chain (c + 1) a 1); ring_nf; finish
  · have : ⟨a, b + 2, c, 0, 2⟩ [fm]⊢* ⟨a + 1, b, c + 1, 0, 2⟩ := by
      step fm; step fm; step fm; finish
    apply stepStar_trans this
    apply stepStar_trans (ih b (by omega) (a + 1) (c + 1)); ring_nf; finish

theorem drain_exit_r0 : ⟨a + 1, b + 1, 0, 0, 0⟩ [fm]⊢* ⟨a + b + 3, 0, 0, 0, b + 6⟩ := by
  step fm; step fm; step fm
  apply stepStar_trans (combined_chain b (a + 1) 2); ring_nf; finish

theorem drain_exit_r1 : ⟨a + 1, b + 1, 0, 1, 0⟩ [fm]⊢* ⟨a + b + 4, 0, 0, 0, b + 6⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (combined_chain b (a + 2) 2); ring_nf; finish

theorem drain_exit_r2 : ⟨a + 1, b, 0, 2, 0⟩ [fm]⊢* ⟨a + b + 4, 0, 0, 0, b + 5⟩ := by
  step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (combined_chain (b + 3) (a + 1) 0); ring_nf; finish

theorem full_trans (m a : ℕ) (r : ℕ) (hr : r ≤ 2) :
    ⟨a + (m + 2) + 1, 0, 0, 0, 3 * (m + 2) + r⟩ [fm]⊢*
    ⟨a + 5 * (m + 2) + r + 2, 0, 0, 0, 5 * (m + 2) + 5⟩ := by
  have h1 : ⟨a + (m + 2) + 1, 0, 0, 0, 3 * (m + 2) + r⟩ [fm]⊢*
      ⟨a + (m + 2) + 1, 0, 0, 3 * (m + 2) + r, 0⟩ := by
    rw [show (3 * (m + 2) + r : ℕ) = 0 + (3 * (m + 2) + r) from by ring]
    exact e_to_d (3 * (m + 2) + r) 0
  rcases r with _ | _ | _ | r
  · -- r = 0
    have h2 : ⟨a + (m + 2) + 1, 0, 0, 3 * (m + 2), 0⟩ [fm]⊢*
        ⟨a + 1, 5 * (m + 2), 0, 0, 0⟩ := by
      rw [show a + (m + 2) + 1 = (a + 1) + (m + 2) from by ring,
          show 3 * (m + 2) = 0 + 3 * (m + 2) from by ring]
      apply stepStar_trans (drain_loop (m + 2) (a + 1) 0 0); ring_nf; finish
    have h3 : ⟨a + 1, 5 * (m + 2), 0, 0, 0⟩ [fm]⊢*
        ⟨a + 5 * (m + 2) + 2, 0, 0, 0, 5 * (m + 2) + 5⟩ := by
      rw [show 5 * (m + 2) = 5 * m + 9 + 1 from by ring]
      exact drain_exit_r0 (a := a) (b := 5 * m + 9)
    apply stepStar_trans h1; apply stepStar_trans h2
    apply stepStar_trans h3; ring_nf; finish
  · -- r = 1
    have h2 : ⟨a + (m + 2) + 1, 0, 0, 3 * (m + 2) + 1, 0⟩ [fm]⊢*
        ⟨a + 1, 5 * (m + 2), 0, 1, 0⟩ := by
      rw [show a + (m + 2) + 1 = (a + 1) + (m + 2) from by ring,
          show 3 * (m + 2) + 1 = 1 + 3 * (m + 2) from by ring]
      apply stepStar_trans (drain_loop (m + 2) (a + 1) 0 1); ring_nf; finish
    have h3 : ⟨a + 1, 5 * (m + 2), 0, 1, 0⟩ [fm]⊢*
        ⟨a + 5 * (m + 2) + 3, 0, 0, 0, 5 * (m + 2) + 5⟩ := by
      rw [show 5 * (m + 2) = 5 * m + 9 + 1 from by ring]
      exact drain_exit_r1 (a := a) (b := 5 * m + 9)
    apply stepStar_trans h1; apply stepStar_trans h2
    apply stepStar_trans h3; ring_nf; finish
  · -- r = 2
    have h2 : ⟨a + (m + 2) + 1, 0, 0, 3 * (m + 2) + 2, 0⟩ [fm]⊢*
        ⟨a + 1, 5 * (m + 2), 0, 2, 0⟩ := by
      rw [show a + (m + 2) + 1 = (a + 1) + (m + 2) from by ring,
          show 3 * (m + 2) + 2 = 2 + 3 * (m + 2) from by ring]
      apply stepStar_trans (drain_loop (m + 2) (a + 1) 0 2); ring_nf; finish
    have h3 : ⟨a + 1, 5 * (m + 2), 0, 2, 0⟩ [fm]⊢*
        ⟨a + 5 * (m + 2) + 4, 0, 0, 0, 5 * (m + 2) + 5⟩ := by
      exact drain_exit_r2 (a := a) (b := 5 * (m + 2))
    apply stepStar_trans h1; apply stepStar_trans h2
    apply stepStar_trans h3; ring_nf; finish
  · omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨9, 0, 0, 0, 10⟩) (by execute fm 34)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 6 ∧ 3 * a ≥ e + 3)
  · intro c ⟨a, e, hq, he, ha⟩; subst hq
    obtain ⟨r, m, rfl, hr⟩ : ∃ r m, e = 3 * (m + 2) + r ∧ r ≤ 2 := by
      refine ⟨e % 3, e / 3 - 2, ?_, by omega⟩; omega
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + (m + 2) + 1 := ⟨a - (m + 2) - 1, by omega⟩
    refine ⟨⟨a' + 5 * (m + 2) + r + 2, 0, 0, 0, 5 * (m + 2) + 5⟩,
      ⟨a' + 5 * (m + 2) + r + 2, 5 * (m + 2) + 5, rfl, by omega, by omega⟩, ?_⟩
    exact stepStar_stepPlus (full_trans m a' r hr)
      (by intro h; simp [Q] at h; omega)
  · exact ⟨9, 10, rfl, by omega, by omega⟩
