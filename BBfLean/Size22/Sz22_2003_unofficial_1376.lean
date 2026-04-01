import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1376: [63/10, 5/33, 196/3, 11/7, 3/2]

Vector representation:
```
-1  2 -1  1  0
 0 -1  1  0 -1
 2 -1  0  2  0
 0  0  0 -1  1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1376

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: transfer d to e (with b=0, c=0)
theorem d_to_e : ∀ k e, ⟨a, 0, 0, k, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  · step fm
    apply stepStar_trans (ih (e + 1)); ring_nf; finish

-- R2R1 chain: (k, b+1, 0, d, e+k) →* (0, b+k+1, 0, d+k, e)
theorem r2r1_chain : ∀ k b d e, ⟨k, b + 1, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k + 1, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) (d + 1) e); ring_nf; finish

-- R2 drain: (0, b+k, c, d, k) →* (0, b, c+k, d, 0)
theorem r2_drain : ∀ k b c d, ⟨0, b + k, c, d, k⟩ [fm]⊢* ⟨0, b, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) d); ring_nf; finish

-- R3 drain: (a, k, 0, d, 0) →* (a+2k, 0, 0, d+2k, 0)
theorem r3_drain : ∀ k a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 2) (d + 2)); ring_nf; finish

-- R1R1R3 chain: (2, b, c + 2k, d, 0) →* (2, b+3k, c, d+4k, 0)
theorem r1r1r3_chain : ∀ k b c d, ⟨2, b, c + 2 * k, d, 0⟩ [fm]⊢* ⟨2, b + 3 * k, c, d + 4 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k + 1) + 1 from by ring]
    step fm
    rw [show (c + 2 * k + 1 : ℕ) = (c + 2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 3) c (d + 4)); ring_nf; finish

-- Phase F even: (2, 0, 2k, 2k+2, 0) →* (6k+2, 0, 0, 12k+2, 0)
theorem phase_f_even (k : ℕ) :
    ⟨2, 0, 2 * k, 2 * k + 2, 0⟩ [fm]⊢* ⟨6 * k + 2, 0, 0, 12 * k + 2, 0⟩ := by
  have h1 := r1r1r3_chain k 0 0 (2 * k + 2)
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 2 * k + 2 + 4 * k = 6 * k + 2 from by ring]
  apply stepStar_trans (r3_drain (3 * k) 2 (6 * k + 2))
  ring_nf; finish

-- Phase F odd: (2, 0, 2k+1, 2k+3, 0) →* (6k+5, 0, 0, 12k+8, 0)
theorem phase_f_odd (k : ℕ) :
    ⟨2, 0, 2 * k + 1, 2 * k + 3, 0⟩ [fm]⊢* ⟨6 * k + 5, 0, 0, 12 * k + 8, 0⟩ := by
  rw [show (2 * k + 1 : ℕ) = 1 + 2 * k from by ring]
  apply stepStar_trans (r1r1r3_chain k 0 1 (2 * k + 3))
  simp only [Nat.zero_add]
  rw [show 2 * k + 3 + 4 * k = 6 * k + 3 from by ring]
  step fm
  apply stepStar_trans (r3_drain (3 * k + 2) 1 (6 * k + 4))
  ring_nf; finish

-- Phase F: (2, 0, n, n+2, 0) →* (3n+2, 0, 0, 6n+2, 0)
theorem phase_f (n : ℕ) :
    ⟨2, 0, n, n + 2, 0⟩ [fm]⊢* ⟨3 * n + 2, 0, 0, 6 * n + 2, 0⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; rw [hk]
    rw [show 3 * (2 * k) + 2 = 6 * k + 2 from by ring,
        show 6 * (2 * k) + 2 = 12 * k + 2 from by ring]
    exact phase_f_even k
  · rw [hk]
    rw [show 3 * (2 * k + 1) + 2 = 6 * k + 5 from by ring,
        show 6 * (2 * k + 1) + 2 = 12 * k + 8 from by ring,
        show 2 * k + 1 + 2 = 2 * k + 3 from by ring]
    exact phase_f_odd k

-- Main transition: (n+1, 0, 0, 2n, 0) →⁺ (3n+2, 0, 0, 6n+2, 0)
theorem main_trans (n : ℕ) :
    ⟨n + 1, 0, 0, 2 * n, 0⟩ [fm]⊢⁺ ⟨3 * n + 2, 0, 0, 6 * n + 2, 0⟩ := by
  have phaseA : ⟨n + 1, 0, 0, 2 * n, 0⟩ [fm]⊢* ⟨n + 1, 0, 0, 0, 2 * n⟩ := by
    have h := d_to_e (a := n + 1) (2 * n) 0
    simpa using h
  have phaseB : ⟨n + 1, 0, 0, 0, 2 * n⟩ [fm]⊢⁺ ⟨n, 1, 0, 0, 2 * n⟩ := by
    step fm; finish
  have phaseC : ⟨n, 1, 0, 0, 2 * n⟩ [fm]⊢* ⟨0, n + 1, 0, n, n⟩ := by
    have h := r2r1_chain n 0 0 n
    simp only [Nat.zero_add] at h; convert h using 2; ring_nf
  have phaseD : ⟨0, n + 1, 0, n, n⟩ [fm]⊢* ⟨0, 1, n, n, 0⟩ := by
    have h := r2_drain n 1 0 n
    simp only [Nat.zero_add] at h; convert h using 2; ring_nf
  have phaseE : ⟨0, 1, n, n, 0⟩ [fm]⊢⁺ ⟨2, 0, n, n + 2, 0⟩ := by
    step fm; finish
  have phaseF : ⟨2, 0, n, n + 2, 0⟩ [fm]⊢* ⟨3 * n + 2, 0, 0, 6 * n + 2, 0⟩ :=
    phase_f n
  exact stepStar_stepPlus_stepPlus phaseA
    (stepPlus_trans phaseB
      (stepStar_stepPlus_stepPlus phaseC
        (stepStar_stepPlus_stepPlus phaseD
          (stepPlus_stepStar_stepPlus phaseE phaseF))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩)
  · execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 2 * n, 0⟩) 1
  intro n
  refine ⟨3 * n + 1, ?_⟩
  rw [show 3 * n + 1 + 1 = 3 * n + 2 from by ring,
      show 2 * (3 * n + 1) = 6 * n + 2 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1376
