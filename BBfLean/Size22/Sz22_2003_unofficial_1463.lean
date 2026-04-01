import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1463: [7/15, 3/77, 50/7, 11/5, 147/2]

Vector representation:
```
 0 -1 -1  1  0
 0  1  0 -1 -1
 1  0  2 -1  0
 0  0 -1  0  1
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1463

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

-- R5+R2+R2 chain: each cycle uses R5 then two R2s.
-- After k cycles: a decreases by k, e decreases by 2k, b increases by 3k.
theorem drain : ∀ k, ∀ a b e, ⟨a + k, b, 0, 0, e + 2 * k⟩ [fm]⊢* ⟨a, b + 3 * k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm -- R5
    rw [show (e + 2 * k) + 2 = ((e + 2 * k) + 1) + 1 from by ring]
    step fm -- R2
    step fm -- R2
    apply stepStar_trans (ih a (b + 3) e)
    ring_nf; finish

-- R3 chain: convert d to a and c (b=0, e=0).
theorem r3_chain : ∀ k, ∀ a c d, ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a + k, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) (c + 2) d)
    ring_nf; finish

-- R4 chain: convert c to e (b=0, d=0).
theorem r4_chain : ∀ k, ∀ a c e, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a c (e + 1))
    ring_nf; finish

-- Build phase: from (a, b, 0, d+1, 0), reach (a+b+d+1, 0, 0, 0, 2*d+b+2).
theorem build_all : ∀ b, ∀ a d, ⟨a, b, 0, d + 1, 0⟩ [fm]⊢* ⟨a + b + d + 1, 0, 0, 0, 2 * d + b + 2⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro a d
  rcases b with _ | _ | b
  · -- b = 0: R3 chain then R4 chain
    rw [show d + 1 = 0 + (d + 1) from by ring]
    apply stepStar_trans (r3_chain (d + 1) a 0 0)
    rw [show 0 + 2 * (d + 1) = 0 + (2 * d + 2) from by ring]
    apply stepStar_trans (r4_chain (2 * d + 2) (a + (d + 1)) 0 0)
    ring_nf; finish
  · -- b = 1: R3, R1, then R3 chain, R4 chain
    step fm -- R3: (a+1, 1, 2, d, 0)
    step fm -- R1: (a+1, 0, 1, d+1, 0)
    rw [show d + 1 = 0 + (d + 1) from by ring]
    apply stepStar_trans (r3_chain (d + 1) (a + 1) 1 0)
    rw [show 1 + 2 * (d + 1) = 0 + (2 * d + 3) from by ring]
    apply stepStar_trans (r4_chain (2 * d + 3) (a + 1 + (d + 1)) 0 0)
    ring_nf; finish
  · -- b = b+2: R3, R1, R1, then induction hypothesis
    step fm -- R3: (a+1, b+2, 2, d, 0)
    step fm -- R1: (a+1, b+1, 1, d+1, 0)
    step fm -- R1: (a+1, b, 0, d+2, 0)
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih b (by omega) (a + 1) (d + 1))
    ring_nf; finish

-- Combined drain + R5 + build for e even.
-- We split m into 0 and m+1 to avoid match ambiguity.
theorem main_even : ⟨a + m + 1, 0, 0, 0, 2 * m⟩ [fm]⊢⁺ ⟨a + 3 * m + 3, 0, 0, 0, 3 * m + 5⟩ := by
  rcases m with _ | m
  · -- m = 0: just R5 then build
    step fm -- R5: (a, 1, 0, 2, 0)
    apply stepStar_trans (build_all 1 a 1)
    ring_nf; finish
  · -- m = m+1: drain (m+1) cycles, then R5, then build
    rw [show a + (m + 1) + 1 = (a + 1) + (m + 1) from by ring,
        show 2 * (m + 1) = 0 + 2 * (m + 1) from by ring]
    apply stepStar_stepPlus_stepPlus
    · exact drain (m + 1) (a + 1) 0 0
    -- State: (a+1, 3*(m+1), 0, 0, 0) = (a+1, 3*m+3, 0, 0, 0)
    show ⟨a + 1, 0 + 3 * (m + 1), 0, 0, 0⟩ [fm]⊢⁺ _
    rw [show 0 + 3 * (m + 1) = 3 * m + 3 from by ring]
    -- 3*m+3 >= 3 so it's in succ form, but we still can't resolve structurally.
    -- Let's rewrite to (3*m+2)+1 form to help Lean.
    rw [show (3 : ℕ) * m + 3 = (3 * m + 2) + 1 from by ring]
    -- Now fm can match: b = (3*m+2)+1 is definitely a succ.
    -- But c=0, so R1 fails. Then d=0 fails R2,R3. c=0 fails R4.
    -- R5: a+1 matches. But wait, the state is (a+1, (3*m+2)+1, 0, 0, 0).
    -- We can just step directly now.
    step fm -- R5: (a, (3*m+2)+2, 0, 2, 0)
    -- b = (3*m+2)+1+1 = 3*m+4. d = 2 = 1+1.
    show ⟨a, (3 * m + 2) + 1 + 1, 0, 2, 0⟩ [fm]⊢* _
    rw [show (3 : ℕ) * m + 2 + 1 + 1 = 3 * m + 4 from by ring]
    apply stepStar_trans (build_all (3 * m + 4) a 1)
    ring_nf; finish

-- Combined drain + R5 + R2 + build for e odd.
theorem main_odd : ⟨a + m + 1, 0, 0, 0, 2 * m + 1⟩ [fm]⊢⁺ ⟨a + 3 * m + 3, 0, 0, 0, 3 * m + 4⟩ := by
  rcases m with _ | m
  · -- m = 0: R5, R2, then build
    step fm -- R5: (a, 1, 0, 2, 1)
    step fm -- R2: (a, 2, 0, 1, 0)
    apply stepStar_trans (build_all 2 a 0)
    ring_nf; finish
  · -- m = m+1: drain (m+1) cycles, R5, R2, build
    rw [show a + (m + 1) + 1 = (a + 1) + (m + 1) from by ring,
        show 2 * (m + 1) + 1 = 1 + 2 * (m + 1) from by ring]
    apply stepStar_stepPlus_stepPlus
    · exact drain (m + 1) (a + 1) 0 1
    show ⟨a + 1, 0 + 3 * (m + 1), 0, 0, 1⟩ [fm]⊢⁺ _
    rw [show 0 + 3 * (m + 1) = (3 * m + 2) + 1 from by ring]
    step fm -- R5: (a, (3*m+2)+2, 0, 2, 1)
    step fm -- R2: (a, (3*m+2)+3, 0, 1, 0)
    show ⟨a, (3 * m + 2) + 1 + 1 + 1, 0, 1, 0⟩ [fm]⊢* _
    rw [show (3 : ℕ) * m + 2 + 1 + 1 + 1 = 3 * m + 5 from by ring]
    apply stepStar_trans (build_all (3 * m + 5) a 0)
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 5⟩) (by execute fm 10)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 1 ∧ 2 * a ≥ e + 1)
  · intro c ⟨a, e, hq, he, ha⟩; subst hq
    rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- e even: e = m + m = 2*m
      rw [show m + m = 2 * m from by ring] at hm; subst hm
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + m + 1 := ⟨a - m - 1, by omega⟩
      exact ⟨⟨a' + 3 * m + 3, 0, 0, 0, 3 * m + 5⟩,
        ⟨a' + 3 * m + 3, 3 * m + 5, rfl, by omega, by omega⟩,
        main_even⟩
    · -- e odd: e = 2*m + 1
      subst hm
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + m + 1 := ⟨a - m - 1, by omega⟩
      exact ⟨⟨a' + 3 * m + 3, 0, 0, 0, 3 * m + 4⟩,
        ⟨a' + 3 * m + 3, 3 * m + 4, rfl, by omega, by omega⟩,
        main_odd⟩
  · exact ⟨3, 5, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1463
