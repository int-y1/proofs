import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #135: [9/35, 1/33, 50/3, 11/5, 63/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  0  0 -1
 1 -1  2  0  0
 0  0 -1  0  1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_135

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

theorem c_to_e : ∀ k, ∀ a e, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · simp; exists 0
  step fm
  apply stepStar_trans (h a (e + 1))
  rw [show e + 1 + k = e + (k + 1) from by ring]; finish

theorem drain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e + 2 * k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · simp; exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show e + 2 * (k + 1) = (e + 2 * k) + 1 + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h a (d + 1) e)
  rw [show d + 1 + k = d + (k + 1) from by ring]; finish

theorem tail_even (a d : ℕ) : ⟨a + 1, 0, 0, d, 0⟩ [fm]⊢* ⟨a + 1, 1, 2, d + 1, 0⟩ := by
  step fm; step fm; finish

theorem tail_odd (a d : ℕ) : ⟨a + 1, 0, 0, d, 1⟩ [fm]⊢* ⟨a + 1, 0, 2, d + 1, 0⟩ := by
  step fm; step fm; step fm; finish

theorem r3_chain : ∀ k, ∀ a c, ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a + k, 0, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · simp; exists 0
  step fm
  apply stepStar_trans (h (a + 1) (c + 2))
  rw [show a + 1 + k = a + (k + 1) from by ring,
      show c + 2 + 2 * k = c + 2 * (k + 1) from by ring]; finish

theorem loop_finish : ∀ D, ∀ A B,
    ⟨A, B, 2, D, 0⟩ [fm]⊢* ⟨A + B + 2 * D, 0, 2 * B + 3 * D + 2, 0, 0⟩ := by
  intro D
  induction' D using Nat.strongRecOn with D ih
  intro A B
  match D with
  | 0 =>
    simp
    apply stepStar_trans (r3_chain B A 2)
    ring_nf; finish
  | 1 =>
    step fm; step fm
    apply stepStar_trans (r3_chain (B + 1) (A + 1) 3)
    ring_nf; finish
  | D + 2 =>
    step fm; step fm; step fm
    apply stepStar_trans (ih D (by omega) (A + 1) (B + 3))
    ring_nf; finish

theorem main_even (n m : ℕ) :
    ⟨n + m + 1, 0, 2 * m, 0, 0⟩ [fm]⊢⁺ ⟨n + 2 * m + 4, 0, 3 * m + 7, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨n + m + 1, 0, 0, 0, 2 * m⟩)
  · have h := c_to_e (2 * m) (n + m + 1) 0
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨n + 1, 0, 0, m, 0⟩)
  · have h := drain m (n + 1) 0 0
    rw [show n + 1 + m = n + m + 1 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨n + 1, 1, 2, m + 1, 0⟩)
  · exact tail_even n m
  have h := loop_finish (m + 1) (n + 1) 1
  rw [show n + 1 + 1 + 2 * (m + 1) = n + 2 * m + 4 from by ring,
      show 2 * 1 + 3 * (m + 1) + 2 = 3 * m + 7 from by ring] at h
  exact stepStar_stepPlus h (by
    intro heq
    have := congr_arg (fun q : Q => q.1) heq
    simp at this; omega)

theorem main_odd (n m : ℕ) :
    ⟨n + m + 1, 0, 2 * m + 1, 0, 0⟩ [fm]⊢⁺ ⟨n + 2 * m + 3, 0, 3 * m + 5, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨n + m + 1, 0, 0, 0, 2 * m + 1⟩)
  · have h := c_to_e (2 * m + 1) (n + m + 1) 0
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨n + 1, 0, 0, m, 1⟩)
  · have h := drain m (n + 1) 0 1
    rw [show n + 1 + m = n + m + 1 from by ring,
        show 1 + 2 * m = 2 * m + 1 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨n + 1, 0, 2, m + 1, 0⟩)
  · exact tail_odd n m
  have h := loop_finish (m + 1) (n + 1) 0
  rw [show n + 1 + 0 + 2 * (m + 1) = n + 2 * m + 3 from by ring,
      show 2 * 0 + 3 * (m + 1) + 2 = 3 * m + 5 from by ring] at h
  exact stepStar_stepPlus h (by
    intro heq
    have := congr_arg (fun q : Q => q.1) heq
    simp at this; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 7, 0, 0⟩)
  · exact stepPlus_stepStar (main_even 0 0)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c, q = ⟨a, 0, c, 0, 0⟩ ∧ c + 1 ≤ 2 * a)
  · intro q ⟨a, c, hq, hle⟩; subst hq
    rcases Nat.even_or_odd c with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- c = m + m = 2*m (even)
      have hm2 : c = 2 * m := by omega
      have ham : a ≥ m + 1 := by omega
      set n := a - m - 1 with hn_def
      have ha_eq : a = n + m + 1 := by omega
      refine ⟨⟨n + 2 * m + 4, 0, 3 * m + 7, 0, 0⟩,
              ⟨n + 2 * m + 4, 3 * m + 7, rfl, by omega⟩, ?_⟩
      rw [ha_eq, hm2]
      exact main_even n m
    · -- c = 2*m + 1 (odd)
      have ham : a ≥ m + 1 := by omega
      set n := a - m - 1 with hn_def
      have ha_eq : a = n + m + 1 := by omega
      refine ⟨⟨n + 2 * m + 3, 0, 3 * m + 5, 0, 0⟩,
              ⟨n + 2 * m + 3, 3 * m + 5, rfl, by omega⟩, ?_⟩
      rw [ha_eq, hm]
      exact main_odd n m
  · exact ⟨4, 7, rfl, by omega⟩

end Sz21_140_unofficial_135
