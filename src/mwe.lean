import analysis.calculus.deriv

open filter asymptotics

open_locale topological_space

lemma is_o_pow_pow {α : Type*} [normed_field α] [discrete_linear_ordered_field α]
  {p q : ℕ} (hpq : p < q) : is_o (λ (x : α), x^p) (λ x, x^q) at_top :=
begin
  rw is_o_iff_tendsto sorry,
  suffices h : tendsto (λ (x : α), x ^ ((p : ℤ) - q)) at_top (𝓝 0),
  { refine (tendsto_congr' ((eventually_gt_at_top (0 : α)).mono (λ x hx, _))).mp h,
    simp [fpow_sub hx.ne.symm] },
  rw ← neg_sub,
  rw ← int.coe_nat_sub hpq.le,
  have : 1 ≤ q - p := nat.sub_pos_of_lt hpq,
  exact @tendsto_pow_neg_at_top α _ _ (by apply_instance) _ this,
end

lemma tendsto_pow_div_pow {α : Type*} [normed_field α] [discrete_linear_ordered_field α]
  {p q : ℕ} (hpq : p < q) : tendsto (λ (x : α), x^p / x^q) at_top (𝓝 0) :=
begin
  suffices h : tendsto (λ (x : α), x ^ ((p : ℤ) - q)) at_top (𝓝 0),
  { refine (tendsto_congr' ((eventually_gt_at_top (0 : α)).mono (λ x hx, _))).mp h,
    simp [fpow_sub hx.ne.symm] },
  rw ← neg_sub,
  rw ← int.coe_nat_sub hpq.le,
  have : 1 ≤ q - p := nat.sub_pos_of_lt hpq,
  exact @tendsto_pow_neg_at_top α _ _ (by apply_instance) _ this,
end