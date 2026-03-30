import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #769: [35/6, 52/55, 143/2, 3/7, 35/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  1
-1  0  0  0  1  1
 0  1  0 -1  0  0
 0  0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_769

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | _ => none

theorem r3_drain : ∀ k a d e f,
    ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · simp; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1) (f + 1))
    ring_nf; finish

theorem r4_drain : ∀ k b d e f,
    ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · simp; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

-- R2 drain specialized: c = e = k, draining both to 0.
theorem r2_drain_z : ∀ k a d f,
    ⟨a, 0, k, d, k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, 0, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d f
  · simp; finish
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 2) d (f + 1))
    ring_nf; finish

-- R1R1R2 chain: each round does R1, R1, R2.
-- j is the running c-value that accumulates.
theorem r1r1r2_chain : ∀ k b j d e f,
    ⟨2, b + 2 * k, j, d, e + k, f⟩ [fm]⊢* ⟨2, b, j + k, d + 2 * k, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b j d e f
  · simp; finish
  · rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih b (j + 1) (d + 2) e (f + 1))
    ring_nf; finish

-- Combined R3+R4:
-- (n+1, 0, 0, n, e, f) →* (0, n, 0, 0, e+n+1, f+n+1)
theorem r3r4 : ∀ n e f,
    ⟨n + 1, 0, 0, n, e, f⟩ [fm]⊢* ⟨0, n, 0, 0, e + n + 1, f + n + 1⟩ := by
  intro n e f
  -- n + 1 = 0 + (n + 1): need to match r3_drain with a = 0.
  -- But 0 + (n+1) ≠ n+1 definitionally. Use nth_rewrite.
  nth_rewrite 1 [show n + 1 = 0 + (n + 1) from (Nat.zero_add _).symm]
  apply stepStar_trans (r3_drain (n + 1) 0 n e f)
  -- Now goal LHS: (0, 0, 0, n, e+(n+1), f+(n+1)).
  -- R4 drain: need d = 0 + n.
  nth_rewrite 1 [show (n : ℕ) = 0 + n from (Nat.zero_add _).symm]
  apply stepStar_trans (r4_drain n 0 0 (e + (n + 1)) (f + (n + 1)))
  simp only [Nat.zero_add]
  ring_nf; finish

-- Phases 1-4: (n+1, 0, 0, n, 0, F) →⁺ (2, n, 0, 1, n, F+n+1)
theorem phases_1_4 : ∀ n F,
    ⟨n + 1, 0, 0, n, 0, F⟩ [fm]⊢⁺ ⟨2, n, 0, 1, n, F + n + 1⟩ := by
  intro n F
  apply stepStar_stepPlus_stepPlus
  · exact r3r4 n 0 F
  -- State: (0, n, 0, 0, n+1, F+n+1). R5 fires (f >= 1).
  simp only [Nat.zero_add]
  rw [show F + n + 1 = (F + n) + 1 from by ring]
  step fm
  -- State: (0, n, 1, 1, n+1, F+n). R2 fires (c=1, e=n+1>=1).
  step fm
  -- State: (2, n, 0, 1, n, F+n+1).
  ring_nf; finish

-- Even case: (2, 2m, 0, 1, 2m, F) ⊢* (2m+2, 0, 0, 2m+1, 0, F+2m)
theorem phase5_even : ∀ m F,
    ⟨2, 2 * m, 0, 1, 2 * m, F⟩ [fm]⊢* ⟨2 * m + 2, 0, 0, 2 * m + 1, 0, F + 2 * m⟩ := by
  intro m F
  -- Need to match: (2, b + 2*k, j, d, e + k, f) with b=0, k=m, j=0, d=1, e=m.
  -- b + 2*m = 0 + 2*m, e + m = m + m = 2*m.
  -- Rewrite first 2*m to 0 + 2*m (b position), second 2*m to m + m (e position).
  nth_rewrite 1 [show (2 * m : ℕ) = 0 + 2 * m from (Nat.zero_add _).symm]
  nth_rewrite 2 [show (2 * m : ℕ) = m + m from by omega]
  apply stepStar_trans (r1r1r2_chain m 0 0 1 m F)
  simp only [Nat.zero_add]
  -- State: (2, 0, m, 2m+1, m, F+m). R2 drain m steps.
  apply stepStar_trans (r2_drain_z m 2 (1 + 2 * m) (F + m))
  ring_nf; finish

-- Odd case: (2, 2m+1, 0, 1, 2m+1, F) ⊢* (2m+3, 0, 0, 2m+2, 0, F+2m+1)
theorem phase5_odd : ∀ m F,
    ⟨2, 2 * m + 1, 0, 1, 2 * m + 1, F⟩ [fm]⊢* ⟨2 * m + 3, 0, 0, 2 * m + 2, 0, F + 2 * m + 1⟩ := by
  intro m F
  -- R1R1R2 chain: b=1, k=m. b+2m = 1+2m = 2m+1. e+m = (m+1)+m = 2m+1.
  rw [show (2 * m + 1 : ℕ) = 1 + 2 * m from by ring]
  nth_rewrite 2 [show (1 + 2 * m : ℕ) = (m + 1) + m from by omega]
  apply stepStar_trans (r1r1r2_chain m 1 0 1 (m + 1) F)
  simp only [Nat.zero_add]
  -- State: (2, 1, m, 2m+1, m+1, F+m). R1.
  step fm
  -- State: (1, 0, m+1, 2m+2, m+1, F+m). R2 drain (m+1 steps).
  rw [show 1 + 2 * m + 1 = 2 * m + 2 from by ring]
  apply stepStar_trans (r2_drain_z (m + 1) 1 (2 * m + 2) (F + m))
  ring_nf; finish

theorem full_transition (n : ℕ) :
    ⟨n + 1, 0, 0, n, 0, n * n⟩ [fm]⊢⁺
    ⟨n + 2, 0, 0, n + 1, 0, (n + 1) * (n + 1)⟩ := by
  apply stepPlus_stepStar_stepPlus (phases_1_4 n (n * n))
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    apply stepStar_trans (phase5_even m (2 * m * (2 * m) + 2 * m + 1))
    ring_nf; finish
  · subst hm
    apply stepStar_trans (phase5_odd m ((2 * m + 1) * (2 * m + 1) + (2 * m + 1) + 1))
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0, 0⟩) (by finish)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, n, 0, n * n⟩) 0
  intro n; exact ⟨n + 1, full_transition n⟩
