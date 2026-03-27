import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #329: [18/35, 5/363, 7/3, 11/7, 75/2]

Vector representation:
```
 1  2 -1 -1  0
 0 -1  1  0 -2
 0 -1  0  1  0
 0  0  0 -1  1
-1  1  2  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_329

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+2, d, e⟩
  | _ => none

theorem unwind_loop : ∀ k a c e,
    (a + k, 0, c, 0, e + 2 * k) [fm]⊢* (a, 0, c + 3 * k, 0, e) := by
  intro k; induction' k with k ih <;> intro a c e
  · simp; exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (c + 3) e)
    rw [show c + 3 + 3 * k = c + 3 * (k + 1) from by ring]; finish

theorem trans_0 : ∀ a c,
    (a + 1, 0, c, 0, 0) [fm]⊢* (a, 0, c + 2, 1, 0) := by
  intro a c; execute fm 2

theorem trans_1 : ∀ a c,
    (a + 1, 0, c, 0, 1) [fm]⊢* (a, 0, c + 2, 1, 1) := by
  intro a c; execute fm 2

theorem buildup_0 : ∀ n a b,
    (a, b, n + 1, 1, 0) [fm]⊢* (a + n + 1, b + n + 2, 0, 0, 0) := by
  intro n; induction' n with n ih <;> intro a b
  · step fm; ring_nf; finish
  · step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 1))
    rw [show a + 1 + n + 1 = a + (n + 1) + 1 from by ring,
        show b + 1 + n + 2 = b + (n + 1) + 2 from by ring]; finish

theorem buildup_1 : ∀ n a b,
    (a, b, n + 1, 1, 1) [fm]⊢* (a + n + 1, b + n + 2, 0, 0, 1) := by
  intro n; induction' n with n ih <;> intro a b
  · step fm; ring_nf; finish
  · step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 1))
    rw [show a + 1 + n + 1 = a + (n + 1) + 1 from by ring,
        show b + 1 + n + 2 = b + (n + 1) + 2 from by ring]; finish

theorem drain_b_0 : ∀ b a d,
    (a, b, 0, d, 0) [fm]⊢* (a, 0, 0, d + b, 0) := by
  intro b; induction' b with b ih <;> intro a d
  · ring_nf; exists 0
  · step fm; apply stepStar_trans (ih a (d + 1))
    rw [show d + 1 + b = d + (b + 1) from by ring]; finish

theorem drain_b_1 : ∀ b a d,
    (a, b, 0, d, 1) [fm]⊢* (a, 0, 0, d + b, 1) := by
  intro b; induction' b with b ih <;> intro a d
  · ring_nf; exists 0
  · step fm; apply stepStar_trans (ih a (d + 1))
    rw [show d + 1 + b = d + (b + 1) from by ring]; finish

theorem drain_d : ∀ d a e,
    (a, 0, 0, d, e) [fm]⊢* (a, 0, 0, 0, d + e) := by
  intro d; induction' d with d ih <;> intro a e
  · ring_nf; exists 0
  · step fm; apply stepStar_trans (ih a (e + 1))
    rw [show d + (e + 1) = (d + 1) + e from by ring]; finish

theorem post_r5_even : ∀ k a,
    (a + k, 1, 2, 0, 2 * k) [fm]⊢* (a + 3 * k + 2, 0, 0, 0, 3 * k + 3) := by
  intro k; induction' k with k ih <;> intro a
  · step fm
    apply stepStar_trans (buildup_0 1 a 0)
    rw [show a + 1 + 1 = a + 2 from by ring, show (0 : ℕ) + 1 + 2 = 3 from by ring]
    apply stepStar_trans (drain_b_0 3 (a + 2) 0)
    rw [show (0 : ℕ) + 3 = 3 from by ring]
    apply drain_d
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm
    rw [show a + (k + 1) = (a + 1) + k from by ring,
        show 2 * k = 0 + 2 * k from by ring]
    apply stepStar_trans (unwind_loop k (a + 1) 3 0)
    rw [show 3 + 3 * k = 3 * k + 3 from by ring]
    apply stepStar_trans (trans_0 a (3 * k + 3))
    rw [show 3 * k + 3 + 2 = (3 * k + 4) + 1 from by ring]
    apply stepStar_trans (buildup_0 (3 * k + 4) a 0)
    rw [show a + (3 * k + 4) + 1 = a + 3 * (k + 1) + 2 from by ring,
        show (0 : ℕ) + (3 * k + 4) + 2 = 3 * (k + 1) + 3 from by ring]
    apply stepStar_trans (drain_b_0 (3 * (k + 1) + 3) (a + 3 * (k + 1) + 2) 0)
    rw [show (0 : ℕ) + (3 * (k + 1) + 3) = 3 * (k + 1) + 3 from by ring]
    apply drain_d

theorem post_r5_odd : ∀ k a,
    (a + k, 1, 2, 0, 2 * k + 1) [fm]⊢* (a + 3 * k + 2, 0, 0, 0, 3 * k + 4) := by
  intro k; induction' k with k ih <;> intro a
  · step fm
    apply stepStar_trans (buildup_1 1 a 0)
    rw [show a + 1 + 1 = a + 2 from by ring, show (0 : ℕ) + 1 + 2 = 3 from by ring]
    apply stepStar_trans (drain_b_1 3 (a + 2) 0)
    rw [show (0 : ℕ) + 3 = 3 from by ring]
    apply stepStar_trans (drain_d 3 (a + 2) 1)
    rw [show 3 + 1 = 4 from by ring]; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm
    rw [show a + (k + 1) = (a + 1) + k from by ring,
        show 2 * k + 1 = 1 + 2 * k from by ring]
    apply stepStar_trans (unwind_loop k (a + 1) 3 1)
    rw [show 3 + 3 * k = 3 * k + 3 from by ring]
    apply stepStar_trans (trans_1 a (3 * k + 3))
    rw [show 3 * k + 3 + 2 = (3 * k + 4) + 1 from by ring]
    apply stepStar_trans (buildup_1 (3 * k + 4) a 0)
    rw [show a + (3 * k + 4) + 1 = a + 3 * (k + 1) + 2 from by ring,
        show (0 : ℕ) + (3 * k + 4) + 2 = 3 * (k + 1) + 3 from by ring]
    apply stepStar_trans (drain_b_1 (3 * (k + 1) + 3) (a + 3 * (k + 1) + 2) 0)
    rw [show (0 : ℕ) + (3 * (k + 1) + 3) = 3 * (k + 1) + 3 from by ring]
    apply stepStar_trans (drain_d (3 * (k + 1) + 3) (a + 3 * (k + 1) + 2) 1)
    rw [show 3 * (k + 1) + 3 + 1 = 3 * (k + 1) + 4 from by ring]; finish

theorem main_even (k a : ℕ) :
    (a + k + 1, 0, 0, 0, 2 * k) [fm]⊢⁺ (a + 3 * k + 2, 0, 0, 0, 3 * k + 3) := by
  rw [show a + k + 1 = (a + k) + 1 from by ring]
  step fm
  exact post_r5_even k a

theorem main_odd (k a : ℕ) :
    (a + k + 1, 0, 0, 0, 2 * k + 1) [fm]⊢⁺ (a + 3 * k + 2, 0, 0, 0, 3 * k + 4) := by
  rw [show a + k + 1 = (a + k) + 1 from by ring]
  step fm
  exact post_r5_odd k a

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ((2, 0, 0, 0, 3) : Q))
  · execute fm 11
  apply progress_nonhalt (fun (q : Q) ↦ ∃ a e : ℕ, a ≥ 2 ∧ e ≥ 3 ∧ 3 * a ≥ 2 * e ∧ q = (a, 0, 0, 0, e))
  · intro q ⟨a, e, ha2, he3, hinv, hq⟩
    subst hq
    rcases Nat.even_or_odd e with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have hak : a ≥ k + 1 := by omega
      rw [show k + k = 2 * k from by ring] at *
      set m := a - k - 1 with hm_def
      have hm : a = m + k + 1 := by omega
      refine ⟨(m + 3 * k + 2, 0, 0, 0, 3 * k + 3),
        ⟨m + 3 * k + 2, 3 * k + 3, by omega, by omega, by omega, rfl⟩, ?_⟩
      rw [hm]; exact main_even k m
    · have hak : a ≥ k + 1 := by omega
      set m := a - k - 1 with hm_def
      have hm : a = m + k + 1 := by omega
      refine ⟨(m + 3 * k + 2, 0, 0, 0, 3 * k + 4),
        ⟨m + 3 * k + 2, 3 * k + 4, by omega, by omega, by omega, rfl⟩, ?_⟩
      rw [hm]; exact main_odd k m
  · exact ⟨2, 3, by omega, by omega, by omega, rfl⟩

end Sz22_2003_unofficial_329
