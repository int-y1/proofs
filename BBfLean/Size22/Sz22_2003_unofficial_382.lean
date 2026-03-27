import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #382: [2/15, 99/14, 1375/2, 7/11, 3/5]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  1
-1  0  3  0  1
 0  0  0  1 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_382

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ j c d e, ⟨0, 0, c, d, e + j⟩ [fm]⊢* ⟨0, 0, c, d + j, e⟩ := by
  intro j; induction' j with j ih <;> intro c d e
  · exists 0
  rw [show e + (j + 1) = (e + j) + 1 from by ring]
  step fm; apply stepStar_trans (ih _ _ _); ring_nf; finish

theorem r1_chain : ∀ j a b c d e, ⟨a, b + j, c + j, d, e⟩ [fm]⊢* ⟨a + j, b, c, d, e⟩ := by
  intro j; induction' j with j ih <;> intro a b c d e
  · exists 0
  rw [show b + (j + 1) = (b + j) + 1 from by ring,
      show c + (j + 1) = (c + j) + 1 from by ring]
  step fm; apply stepStar_trans (ih _ _ _ _ _); ring_nf; finish

theorem r3_chain : ∀ j a c e, ⟨a + j, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 3 * j, 0, e + j⟩ := by
  intro j; induction' j with j ih <;> intro a c e
  · exists 0
  rw [show a + (j + 1) = (a + j) + 1 from by ring]
  step fm; apply stepStar_trans (ih _ _ _); ring_nf; finish

theorem r2_chain_c0 : ∀ j a b d e,
    ⟨a + j, b, 0, d + j, e⟩ [fm]⊢* ⟨a, b + 2 * j, 0, d, e + j⟩ := by
  intro j; induction' j with j ih <;> intro a b d e
  · exists 0
  rw [show a + (j + 1) = (a + j) + 1 from by ring,
      show d + (j + 1) = (d + j) + 1 from by ring]
  step fm; apply stepStar_trans (ih _ _ _ _); ring_nf; finish

-- R1, R1, R2 iterated j+1 times
theorem loop_iter : ∀ j a c d e,
    ⟨a + 1, 2, c + 2 * (j + 1), d + (j + 1), e⟩ [fm]⊢*
    ⟨a + j + 2, 2, c, d, e + j + 1⟩ := by
  intro j; induction' j with j ih <;> intro a c d e
  · step fm; step fm; step fm; ring_nf; finish
  rw [show c + 2 * (j + 1 + 1) = (c + 2 * (j + 1)) + 2 from by ring,
      show d + (j + 1 + 1) = (d + (j + 1)) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- Phase C even: m = 2(p+1)
theorem phaseC_even (p : ℕ) :
    ⟨1, 0, 2 * (p + 1), 2 * (p + 1), 0⟩ [fm]⊢* ⟨1, 2 * (p + 1), 0, 0, 2 * (p + 1)⟩ := by
  step fm; step fm; step fm; step fm
  rcases p with _ | p
  · finish
  apply stepStar_trans
  · show ⟨1, 2, 2 * (p + 1), 2 * (p + 1), 2⟩ [fm]⊢* ⟨p + 2, 2, 0, p + 1, p + 3⟩
    have h := loop_iter p 0 0 (p + 1) 2
    rw [show 0 + 2 * (p + 1) = 2 * (p + 1) from by ring,
        show p + 1 + (p + 1) = 2 * (p + 1) from by ring,
        show 0 + 1 = 1 from by ring,
        show 0 + p + 2 = p + 2 from by ring,
        show 2 + p + 1 = p + 3 from by ring] at h; exact h
  apply stepStar_trans
  · show ⟨p + 2, 2, 0, p + 1, p + 3⟩ [fm]⊢* ⟨1, 2 * (p + 2), 0, 0, 2 * (p + 2)⟩
    have h := r2_chain_c0 (p + 1) 1 2 0 (p + 3)
    rw [show 0 + (p + 1) = p + 1 from by ring,
        show 1 + (p + 1) = p + 2 from by ring] at h
    apply stepStar_trans h; ring_nf; finish
  ring_nf; finish

-- Phase C odd: m = 2(p+1)+1
theorem phaseC_odd (p : ℕ) :
    ⟨1, 0, 2 * (p + 1) + 1, 2 * (p + 1) + 1, 0⟩ [fm]⊢*
    ⟨1, 2 * (p + 1) + 1, 0, 0, 2 * (p + 1) + 1⟩ := by
  step fm; step fm; step fm; step fm
  rcases p with _ | p
  · step fm; step fm; finish
  apply stepStar_trans
  · show ⟨1, 2, 2 * (p + 1) + 1, 2 * (p + 1) + 1, 2⟩ [fm]⊢* ⟨p + 2, 2, 1, p + 2, p + 3⟩
    have h := loop_iter p 0 1 (p + 2) 2
    rw [show 1 + 2 * (p + 1) = 2 * (p + 1) + 1 from by ring,
        show p + 2 + (p + 1) = 2 * (p + 1) + 1 from by ring,
        show 0 + 1 = 1 from by ring,
        show 0 + p + 2 = p + 2 from by ring,
        show 2 + p + 1 = p + 3 from by ring] at h; exact h
  step fm; step fm
  apply stepStar_trans
  · show ⟨p + 2, 3, 0, p + 1, p + 4⟩ [fm]⊢* ⟨1, 2 * (p + 2) + 1, 0, 0, 2 * (p + 2) + 1⟩
    have h := r2_chain_c0 (p + 1) 1 3 0 (p + 4)
    rw [show 0 + (p + 1) = p + 1 from by ring,
        show 1 + (p + 1) = p + 2 from by ring] at h
    apply stepStar_trans h; ring_nf; finish
  ring_nf; finish

theorem phaseC : ∀ m, ⟨1, 0, m, m, 0⟩ [fm]⊢* ⟨1, m, 0, 0, m⟩ := by
  intro m
  rcases m with _ | _ | m
  · exists 0
  · step fm; step fm; finish
  · rcases Nat.even_or_odd (m + 2) with ⟨p, hp⟩ | ⟨p, hp⟩
    · obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      rw [show m + 2 = 2 * (p' + 1) from by omega]
      exact phaseC_even p'
    · obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      rw [show m + 2 = 2 * (p' + 1) + 1 from by omega]
      exact phaseC_odd p'

-- Phase D: strong induction on a+2*b
theorem gen_phaseD : ∀ n a b c e, a + 2 * b ≤ n →
    ⟨a + 1, b, c, 0, e⟩ [fm]⊢* ⟨1, 0, 3 * a + 2 * b + c, 0, e + a + b⟩ := by
  intro n; induction' n using Nat.strongRecOn with n ih; intro a b c e hle
  rcases b with _ | b
  · rcases a with _ | a
    · simp; finish
    · step fm
      apply stepStar_trans (ih (a + 2 * 0) (by omega) a 0 (c + 3) (e + 1) (by omega))
      ring_nf; finish
  · rcases c with _ | c
    · step fm; step fm
      apply stepStar_trans (ih (a + 2 * b) (by omega) a b 2 (e + 1) (by omega))
      ring_nf; finish
    · step fm
      have h := ih (a + 1 + 2 * b) (by omega) (a + 1) b c e (by omega)
      rw [show 3 * (a + 1) + 2 * b + c = 3 * a + 2 * (b + 1) + (c + 1) from by ring,
          show e + (a + 1) + b = e + a + (b + 1) from by ring] at h; exact h

theorem main_trans (n : ℕ) :
    ⟨1, 0, 2 * (n + 1), 0, 2 * (n + 1)⟩ [fm]⊢⁺ ⟨1, 0, 2 * (2 * n + 3), 0, 2 * (2 * n + 3)⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨1, 0, 2 * (n + 1), 0, 2 * (n + 1)⟩ = some ⟨0, 0, 2 * n + 5, 0, 2 * n + 3⟩
    unfold fm; ring_nf
  apply stepStar_trans
  · have h := r4_chain (2 * n + 3) (2 * n + 5) 0 0
    rw [show 0 + (2 * n + 3) = 2 * n + 3 from by ring] at h; exact h
  step fm; step fm
  apply stepStar_trans (phaseC (2 * n + 3))
  apply stepStar_trans
  · have h := gen_phaseD (0 + 2 * (2 * n + 3)) 0 (2 * n + 3) 0 (2 * n + 3) (by omega)
    rw [show 0 + 1 = 1 from by ring] at h; exact h
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 2, 0, 2⟩)
  · execute fm 8
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 2 * (n + 1), 0, 2 * (n + 1)⟩) 0
  intro n
  exact ⟨2 * n + 2, main_trans n⟩

end Sz22_2003_unofficial_382
