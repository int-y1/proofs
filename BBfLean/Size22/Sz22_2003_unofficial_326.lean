import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #326: [18/35, 5/33, 196/3, 11/2, 3/11]

Vector representation:
```
 1  2 -1 -1  0
 0 -1  1  0 -1
 2 -1  0  2  0
-1  0  0  0  1
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_326

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r4_loop : ∀ k d e, (k, 0, 0, d, e) [fm]⊢* (0, 0, 0, d, e + k) := by
  intro k; induction k with
  | zero => intro d e; ring_nf; finish
  | succ k ih => intro d e; step fm; apply stepStar_trans (ih d (e + 1)); ring_nf; finish

theorem r2r1_iter : ∀ n j d e, (j, j + 1, 0, d + n, e + n) [fm]⊢* (j + n, j + n + 1, 0, d, e) := by
  intro n; induction n with
  | zero => intro j d e; ring_nf; finish
  | succ n ih =>
    intro j d e
    rw [show d + (n + 1) = (d + n) + 1 from by ring,
        show e + (n + 1) = (e + n) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (j + 1) d e)
    ring_nf; finish

theorem r3_loop : ∀ k a d, (a, k, 0, d, 0) [fm]⊢* (a + 2 * k, 0, 0, d + 2 * k, 0) := by
  intro k; induction k with
  | zero => intro a d; simp; finish
  | succ k ih =>
    intro a d; step fm; apply stepStar_trans (ih (a + 2) (d + 2)); ring_nf; finish

theorem r2_drain : ∀ k a b c, (a, b + k, c, 0, k) [fm]⊢* (a, b, c + k, 0, 0) := by
  intro k; induction k with
  | zero => intro a b c; ring_nf; finish
  | succ k ih =>
    intro a b c
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b (c + 1))
    ring_nf; finish

theorem abc_phase : ∀ C, ∀ A B, (A, B + 1, C, 0, 0) [fm]⊢* (A + 2 * B + 5 * C + 2, 0, 0, 2 * B + 3 * C + 2, 0) := by
  intro C; induction' C using Nat.strongRecOn with C ih
  rcases C with _ | _ | C
  · intro A B
    apply stepStar_trans (r3_loop (B + 1) A 0)
    ring_nf; finish
  · intro A B
    step fm; step fm; step fm
    apply stepStar_trans (r3_loop (B + 1) (A + 5) 3)
    ring_nf; finish
  · intro A B
    rw [show (C + 2 : ℕ) = C + 2 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih C (by omega) (A + 4) (B + 3))
    ring_nf; finish

-- Case A: a ≤ d, written as (n+1, 0, 0, n+m+1, 0)
theorem main_trans_A : ∀ n m, (n + 1, 0, 0, n + m + 1, 0) [fm]⊢⁺ (3 * n + 2, 0, 0, 2 * n + m + 3, 0) := by
  intro n m
  step fm
  apply stepStar_trans (r4_loop n (n + m + 1) 1)
  rw [show 1 + n = n + 1 from by ring]
  step fm
  -- After r5: (0, 1, 0, n+m+1, n). Need to apply r2r1_iter n 0 (m+1) 0.
  -- r2r1_iter expects (0, 0+1, 0, (m+1)+n, 0+n). Goal has (0, 1, 0, n+m+1, n).
  -- After ring_nf these should match. Let me manually rewrite.
  rw [show n + m + 1 = (m + 1) + n from by ring]
  have h := r2r1_iter n 0 (m + 1) 0
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  apply stepStar_trans (r3_loop (n + 1) n (m + 1))
  ring_nf; finish

-- Case B: a > d, written as (2*p+q+2, 0, 0, p+q+1, 0)
theorem main_trans_B : ∀ p q, (2 * p + q + 2, 0, 0, p + q + 1, 0) [fm]⊢⁺ (6 * p + 3 * q + 5, 0, 0, 3 * p + 2 * q + 4, 0) := by
  intro p q
  step fm
  apply stepStar_trans (r4_loop (2 * p + q + 1) (p + q + 1) 1)
  rw [show 1 + (2 * p + q + 1) = 2 * p + q + 2 from by ring]
  step fm
  -- After r5: (0, 1, 0, p+q+1, 2*p+q+1). Apply r2r1_iter (p+q+1) 0 0 p.
  rw [show 2 * p + q + 1 = p + (p + q + 1) from by ring]
  have h1 := r2r1_iter (p + q + 1) 0 0 p
  simp only [Nat.zero_add] at h1 ⊢
  apply stepStar_trans h1
  -- Now at (p+q+1, p+q+2, 0, 0, p). Apply r2_drain.
  rw [show p + q + 2 = (q + 2) + p from by ring]
  apply stepStar_trans (r2_drain p (p + q + 1) (q + 2) 0)
  rw [show 0 + p = p from by ring, show q + 2 = (q + 1) + 1 from by ring]
  apply stepStar_trans (abc_phase p (p + q + 1) (q + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩)
  · execute fm 3
  apply progress_nonhalt (fm := fm)
    (P := fun s ↦ ∃ a d : ℕ, s = (a, 0, 0, d, 0) ∧ a ≥ 2 ∧ d ≥ 1 ∧ a ≤ 2 * d)
  · intro c ⟨a, d, hc, ha, hd, hle⟩
    subst hc
    by_cases h : a ≤ d
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ a by omega)
      -- a = 1 + n, d = (1 + n) + m
      refine ⟨(3 * n + 2, 0, 0, 2 * n + m + 3, 0),
        ⟨3 * n + 2, 2 * n + m + 3, rfl, by omega, by omega, by omega⟩, ?_⟩
      -- Goal has (1 + n, 0, 0, 1 + n + m, 0), need (n + 1, 0, 0, n + m + 1, 0)
      have := main_trans_A n m
      rwa [show (n + 1 : ℕ) = 1 + n from by ring,
           show n + m + 1 = 1 + n + m from by ring] at this
    · push_neg at h
      obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le (show d + 1 ≤ a by omega)
      -- a = 1 + d + p
      obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le (show p + 1 ≤ d by omega)
      -- d = 1 + p + q, a = 1 + (1 + p + q) + p
      refine ⟨(6 * p + 3 * q + 5, 0, 0, 3 * p + 2 * q + 4, 0),
        ⟨6 * p + 3 * q + 5, 3 * p + 2 * q + 4, rfl, by omega, by omega, by omega⟩, ?_⟩
      have := main_trans_B p q
      rwa [show (2 * p + q + 2 : ℕ) = p + 1 + q + 1 + p from by ring,
           show (p + q + 1 : ℕ) = p + 1 + q from by ring] at this
  · exact ⟨2, 2, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_326
