import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #244: [11/105, 45/22, 2/3, 49/2, 33/7]

Vector representation:
```
 0 -1 -1 -1  1
-1  2  1  0 -1
 1 -1  0  0  0
-1  0  0  2  0
 0  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_244

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 chain: drain a into d (when b=0, e=0)
theorem a_to_d : ∀ k c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih c (d + 2))
    ring_nf; finish

-- R5/R1 interleave: drain c (when a=0, b=0)
theorem r5r1_drain : ∀ k d e, ⟨0, 0, k, d + 2 * k, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show d + 2 * (k + 1) = d + 2 * k + 1 + 1 from by ring,
        show k + 1 = k + 1 from rfl]
    step fm -- R5: (0, 1, k+1, d+2*k+1, e+1)
    rw [show d + 2 * k + 1 = (d + 2 * k) + 1 from by ring]
    step fm -- R1: (0, 0, k, d+2*k, e+2)
    apply stepStar_trans (ih d (e + 2))
    ring_nf; finish

-- R3/R2 chain: pump b and c from e (when a=0, d=0, b≥1)
theorem r3r2_chain : ∀ k b c, b ≥ 1 → ⟨0, b, c, 0, k⟩ [fm]⊢* ⟨0, b + k, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c hb
  · exists 0
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
    step fm -- R3: (1, b, c, 0, k+1)
    step fm -- R2: (0, b+2, c+1, 0, k)
    apply stepStar_trans (ih (b + 2) (c + 1) (by omega))
    ring_nf; finish

-- R3 chain: drain b into a (when d=0, e=0)
theorem b_to_a : ∀ k a c, ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a + k, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · step fm -- R3
    apply stepStar_trans (ih (a + 1) c)
    ring_nf; finish

-- Main transition: (n+1, 0, n, 0, 0) ⊢⁺ (2*n+2, 0, 2*n+1, 0, 0)
theorem main_trans (n : ℕ) :
    ⟨n + 1, 0, n, 0, 0⟩ [fm]⊢⁺ ⟨2 * n + 2, 0, 2 * n + 1, 0, 0⟩ := by
  -- Phase 1: a_to_d: (n+1, 0, n, 0, 0) →* (0, 0, n, 2*(n+1), 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n, 2 * (n + 1), 0⟩)
  · have h := a_to_d (n + 1) n 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: r5r1_drain: (0, 0, n, 2*(n+1), 0) →* (0, 0, 0, 2, 2*n)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 2, 2 * n⟩)
  · have h := r5r1_drain n 2 0
    rw [show 2 + 2 * n = 2 * (n + 1) from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: 6 steps: (0, 0, 0, 2, 2*n) →⁺ (0, 2, 1, 0, 2*n)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2, 1, 0, 2 * n⟩)
  · step fm; step fm; step fm; step fm; step fm; step fm
    finish
  -- Phase 4: r3r2_chain: (0, 2, 1, 0, 2*n) →* (0, 2*n+2, 2*n+1, 0, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2 * n + 2, 2 * n + 1, 0, 0⟩)
  · have h := r3r2_chain (2 * n) 2 1 (by omega)
    rw [show 2 + 2 * n = 2 * n + 2 from by ring,
        show 1 + 2 * n = 2 * n + 1 from by ring] at h
    exact h
  -- Phase 5: b_to_a: (0, 2*n+2, 2*n+1, 0, 0) →⁺ (2*n+2, 0, 2*n+1, 0, 0)
  have h := b_to_a (2 * n + 2) 0 (2 * n + 1)
  simp only [Nat.zero_add] at h
  exact stepStar_stepPlus h (by
    intro heq
    have : (0 : ℕ) = 2 * n + 2 := congr_arg (fun q : Q => q.1) heq
    omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by execute fm 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n + 1, 0, n, 0, 0⟩) 0
  intro n
  exact ⟨2 * n + 1, by
    show ⟨n + 1, 0, n, 0, 0⟩ [fm]⊢⁺ ⟨(2 * n + 1) + 1, 0, 2 * n + 1, 0, 0⟩
    rw [show (2 * n + 1) + 1 = 2 * n + 2 from by ring]
    exact main_trans n⟩

end Sz22_2003_unofficial_244
