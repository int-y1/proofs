import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #230: [11/105, 15/22, 4/3, 35/2, 9/5]

Vector representation:
```
 0 -1 -1 -1  1
-1  1  1  0 -1
 2 -1  0  0  0
-1  0  1  1  0
 0  2 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_230

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

def C : ℕ → ℕ
  | 0 => 2
  | n + 1 => C n + n + 1

theorem C_ge (n : ℕ) : C n ≥ n + 2 := by
  induction n with
  | zero => simp [C]
  | succ n ih => simp [C]; omega

-- R4 chain: (a+k, 0, c, d, 0) →* (a, 0, c+k, d+k, 0)
theorem r4_chain : ∀ k a c d, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c + k, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; simp; exists 0
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) (d + 1))
    ring_nf; finish

-- Drain: (0, 0, c + 3*k + 2, 2*k + 1, e) →* (0, 1, c, 0, e + 2*k + 1)
theorem drain : ∀ k c e, ⟨0, 0, c + 3 * k + 2, 2 * k + 1, e⟩ [fm]⊢* ⟨0, 1, c, 0, e + 2 * k + 1⟩ := by
  intro k; induction k with
  | zero =>
    intro c e; simp
    step fm
    step fm
    ring_nf; finish
  | succ k ih =>
    intro c e
    rw [show c + 3 * (k + 1) + 2 = (c + 3 * k + 2) + 3 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih c (e + 2))
    rw [show e + 2 + 2 * k + 1 = e + 2 * (k + 1) + 1 from by ring]; finish

-- R3 step: (0, 1, c, 0, e) → (2, 0, c, 0, e)
theorem r3_step (c e : ℕ) : ⟨0, 1, c, 0, e⟩ [fm]⊢ ⟨2, 0, c, 0, e⟩ := by
  rcases c with _ | c <;> rcases e with _ | e <;> simp [fm]

-- Pump odd: (2, b, c, 0, 2*k+1) →* (1, b+k+1, c+2*k+1, 0, 0)
theorem pump_odd : ∀ k b c, ⟨2, b, c, 0, 2 * k + 1⟩ [fm]⊢* ⟨1, b + k + 1, c + 2 * k + 1, 0, 0⟩ := by
  intro k; induction k with
  | zero =>
    intro b c; simp
    step fm
    ring_nf; finish
  | succ k ih =>
    intro b c
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih (b + 1) (c + 2))
    rw [show b + 1 + k + 1 = b + (k + 1) + 1 from by ring,
        show c + 2 + 2 * k + 1 = c + 2 * (k + 1) + 1 from by ring]; finish

-- R3 chain: (a, k, c, 0, 0) →* (a + 2*k, 0, c, 0, 0)
theorem r3_chain : ∀ k a c, ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; simp; exists 0
  | succ k ih =>
    intro a c
    have hstep : fm ⟨a, k + 1, c, 0, 0⟩ = some ⟨a + 2, k, c, 0, 0⟩ := by
      rcases c with _ | c <;> simp [fm]
    apply stepStar_trans (step_stepStar hstep)
    apply stepStar_trans (ih (a + 2) c)
    rw [show a + 2 + 2 * k = a + 2 * (k + 1) from by ring]; finish

-- Main transition
theorem main_trans (n : ℕ) :
    ⟨2 * n + 3, 0, C n, 0, 0⟩ [fm]⊢⁺ ⟨2 * (n + 1) + 3, 0, C (n + 1), 0, 0⟩ := by
  have hC := C_ge n
  -- Simplify target
  rw [show 2 * (n + 1) + 3 = 2 * n + 5 from by ring]
  show ⟨2 * n + 3, 0, C n, 0, 0⟩ [fm]⊢⁺ ⟨2 * n + 5, 0, C n + n + 1, 0, 0⟩
  -- Phase 1: R4 chain (2*n+3 times)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, C n + (2 * n + 3), 2 * n + 3, 0⟩)
  · have h := r4_chain (2 * n + 3) 0 (C n) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: drain (n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 1, C n - n - 2, 0, 2 * n + 3⟩)
  · have h := drain (n + 1) (C n - n - 2) 0
    rw [show C n - n - 2 + 3 * (n + 1) + 2 = C n + (2 * n + 3) from by omega,
        show 2 * (n + 1) + 1 = 2 * n + 3 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R3 step
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2, 0, C n - n - 2, 0, 2 * n + 3⟩)
  · exact step_stepStar (r3_step (C n - n - 2) (2 * n + 3))
  -- Phase 4: pump odd (n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, n + 2, C n + n + 1, 0, 0⟩)
  · have h := pump_odd (n + 1) 0 (C n - n - 2)
    rw [show 2 * (n + 1) + 1 = 2 * n + 3 from by ring,
        show 0 + (n + 1) + 1 = n + 2 from by ring,
        show C n - n - 2 + 2 * (n + 1) + 1 = C n + n + 1 from by omega] at h
    exact h
  -- Phase 5: R3 chain (n+2)
  have h := r3_chain (n + 2) 1 (C n + n + 1)
  rw [show 1 + 2 * (n + 2) = 2 * n + 5 from by ring] at h
  exact stepStar_stepPlus h (by
    intro heq
    have := congr_arg (fun q : Q => q.2.1) heq
    simp at this)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 2, 0, 0⟩) (by execute fm 24)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 3, 0, C n, 0, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_230
