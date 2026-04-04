import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1894: [9/35, 55/6, 8/5, 7/11, 15/2]

Vector representation:
```
 0  2 -1 -1  0
-1 -1  1  0  1
 3  0 -1  0  0
 0  0  0  1 -1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1894

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · step fm; apply stepStar_trans (ih (d + 1)); ring_nf; finish

theorem r2r1_chain : ∀ k a b d e, ⟨a + k, b + 1, 0, d + k, e⟩ [fm]⊢* ⟨a, b + 1 + k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih a (b + 1) d (e + 1)); ring_nf; finish

theorem r3_chain : ∀ k p c e, ⟨p, 0, c + k, 0, e⟩ [fm]⊢* ⟨p + 3 * k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro p c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (p + 3) c e); ring_nf; finish

theorem drain : ∀ B A C E, ⟨A + 1, B + 1, C, 0, E⟩ [fm]⊢* ⟨A + 3 * C + 2 * B + 3, 0, 0, 0, E + B + 1⟩ := by
  intro B; induction' B using Nat.strongRecOn with B IH; intro A C E
  rcases B with _ | B
  · -- B = 0: R2 fires once, then r3_chain
    step fm
    rw [show C + 1 = 0 + (C + 1) from by ring]
    apply stepStar_trans (r3_chain (C + 1) A 0 (E + 1))
    ring_nf; finish
  · rcases A with _ | A'
    · -- A = 0: (1, B+2, C, 0, E). R2: (0, B+1, C+1, 0, E+1). R3: (3, B+1, C, 0, E+1).
      step fm
      apply stepStar_trans (step_stepStar (show (⟨0, B + 1, C + 1, 0, E + 1⟩ : Q) [fm]⊢ ⟨3, B + 1, C, 0, E + 1⟩ from by simp [fm]))
      rw [show (3 : ℕ) = 2 + 1 from by ring]
      apply stepStar_trans (IH B (by omega) 2 C (E + 1))
      show (⟨2 + 3 * C + 2 * B + 3, 0, 0, 0, E + 1 + B + 1⟩ : Q) [fm]⊢* ⟨0 + 3 * C + 2 * (B + 1) + 3, 0, 0, 0, E + (B + 1) + 1⟩
      have : (⟨2 + 3 * C + 2 * B + 3, 0, 0, 0, E + 1 + B + 1⟩ : Q) = ⟨0 + 3 * C + 2 * (B + 1) + 3, 0, 0, 0, E + (B + 1) + 1⟩ := by
        ext <;> simp <;> omega
      rw [this]; finish
    · -- A >= 1: (A'+2, B+2, C, 0, E). R2: (A'+1, B+1, C+1, 0, E+1).
      step fm
      apply stepStar_trans (IH B (by omega) A' (C + 1) (E + 1))
      show (⟨A' + 3 * (C + 1) + 2 * B + 3, 0, 0, 0, E + 1 + B + 1⟩ : Q) [fm]⊢* ⟨A' + 1 + 3 * C + 2 * (B + 1) + 3, 0, 0, 0, E + (B + 1) + 1⟩
      have : (⟨A' + 3 * (C + 1) + 2 * B + 3, 0, 0, 0, E + 1 + B + 1⟩ : Q) = ⟨A' + 1 + 3 * C + 2 * (B + 1) + 3, 0, 0, 0, E + (B + 1) + 1⟩ := by
        ext <;> simp <;> omega
      rw [this]; finish

theorem main_trans_succ : ∀ f e, ⟨f + e + 5, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨f + 2 * e + 10, 0, 0, 0, 2 * e + 3⟩ := by
  intro f e
  apply stepStar_stepPlus_stepPlus (e_to_d (e + 1) 0 (a := f + e + 5))
  rw [show 0 + (e + 1) = e + 1 from by ring]
  step fm; step fm
  -- Goal is ⊢*. State: (f+e+4, 3, 0, e, 0)
  have heq : (⟨f + e + 4, 3, 0, e, 0⟩ : Q) = ⟨(f + 4) + e, 2 + 1, 0, 0 + e, 0⟩ := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))) <;> simp; omega
  rw [heq]
  apply stepStar_trans (r2r1_chain e (f + 4) 2 0 0)
  have heq2 : (⟨f + 4, 2 + 1 + e, 0, 0, 0 + e⟩ : Q) = ⟨(f + 3) + 1, (e + 2) + 1, 0, 0, e⟩ := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))) <;> simp; omega
  rw [heq2]
  apply stepStar_trans (drain (e + 2) (f + 3) 0 e)
  simp only [Nat.mul_zero, Nat.add_zero]
  have heq3 : (⟨f + 3 + 2 * (e + 2) + 3, 0, 0, 0, e + (e + 2) + 1⟩ : Q) = ⟨f + 2 * e + 10, 0, 0, 0, 2 * e + 3⟩ := by
    ext <;> simp <;> omega
  rw [heq3]; finish

theorem main_trans_zero : ∀ f, ⟨f + 4, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨f + 8, 0, 0, 0, 1⟩ := by
  intro f; execute fm 4

theorem main_trans : ∀ f e, ⟨f + e + 4, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨f + 2 * e + 8, 0, 0, 0, 2 * e + 1⟩ := by
  intro f e; rcases e with _ | e
  · simp only [Nat.add_zero, Nat.mul_zero]; exact main_trans_zero f
  · rw [show f + (e + 1) + 4 = f + e + 5 from by ring,
        show f + 2 * (e + 1) + 8 = f + 2 * e + 10 from by ring,
        show 2 * (e + 1) + 1 = 2 * e + 3 from by ring]
    exact main_trans_succ f e

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 1⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨f, e⟩ ↦ ⟨f + e + 4, 0, 0, 0, e⟩) ⟨0, 1⟩
  intro ⟨f, e⟩
  refine ⟨⟨f + 3, 2 * e + 1⟩, ?_⟩
  show ⟨f + e + 4, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨(f + 3) + (2 * e + 1) + 4, 0, 0, 0, 2 * e + 1⟩
  rw [show (f + 3) + (2 * e + 1) + 4 = f + 2 * e + 8 from by ring]
  exact main_trans f e
