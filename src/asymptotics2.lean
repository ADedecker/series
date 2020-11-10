import analysis.calculus.deriv
import algebra.group.pi
import normed_linear_ordered_field
import normed_linear_ordered_group

namespace asymptotics

open filter

open_locale topological_space

section normed_field

variables {α β : Type*} [normed_field β] {u v w : α → β} {l : filter α} {c : ℝ}

---

/-- This needs refactoring !!! -/
lemma is_o_iff_tendsto' (huv : ∀ᶠ x in l, u x = 0 → v x = 0) :
  is_o u v l ↔ tendsto (λ x, u x / (v x)) l (𝓝 0) :=
sorry

end normed_field

lemma is_o.tendsto_of_tendsto_const {α E 𝕜 : Type*} [normed_group E] [normed_field 𝕜] {u : α → E}
  {v : α → 𝕜} {l : filter α} {y : 𝕜} (huv : is_o u v l) (hv : tendsto v l (𝓝 y)) : 
  tendsto u l (𝓝 0) :=
begin
  suffices h : is_o u (λ x, (1 : 𝕜)) l,
  { rwa is_o_one_iff at h },
  exact huv.trans_is_O (is_O_one_of_tendsto 𝕜 hv),
end

section normed_linear_ordered_group

variables {α β : Type*} [normed_linear_ordered_group β] {u v w : α → β} {l : filter α} {c : ℝ}

lemma is_O.trans_tendsto_norm_at_top (huv : is_O u v l) 
  (hu : tendsto (λ x, ∥u x∥) l at_top) :
  tendsto (λ x, ∥v x∥) l at_top :=
begin
  rcases huv.exists_pos with ⟨c, hc, hcuv⟩,
  rw is_O_with at hcuv,
  convert tendsto_at_top_div hc (tendsto_at_top_mono' l hcuv hu),
  ext x,
  rw mul_div_cancel_left _ hc.ne.symm,
end

end normed_linear_ordered_group

end asymptotics