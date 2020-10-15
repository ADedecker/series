import analysis.specific_limits

open set finset filter
open_locale big_operators topological_space

noncomputable theory

def series (u : ℕ → ℝ) := λ n, (∑ i in range n, u i)

def converges {α : Type*} [topological_space α] (u : ℕ → α) := ∃ l, tendsto u at_top (𝓝 l)

lemma tendsto_geom_series_at_top_of_nonneg_of_lt_one (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
  tendsto (geom_series r) at_top (𝓝 $ 1/(1-r)) :=
begin
  rw tendsto_congr (geom_sum hr₁.ne),
  conv in (𝓝 _) {congr, rw [← neg_div_neg_eq, neg_sub, ← zero_sub]},
  exact ((tendsto_pow_at_top_nhds_0_of_lt_1 hr₀ hr₁).sub tendsto_const_nhds).div_const
end

lemma tendsto_geom_series_at_top_of_one_le (r : ℝ) (hr : 1 ≤ r) :
  tendsto (geom_series r) at_top at_top :=
begin
  by_cases h : r = 1,
  { rw h,
     },
  { have : 1 < r,
    { change _ ≠ _ at h,
      linarith [lt_of_le_of_ne hr h.symm] },
    rw [tendsto_congr (geom_sum h), sub_eq_add_neg],
    refine tendsto_at_top_div (by rwa [← sub_eq_add_neg, sub_pos]) 
      (tendsto_at_top_add_const_right _ _ $ tendsto_pow_at_top_at_top_of_one_lt this) }
end

lemma converges_geom_series_iff_of_nonneg (r : ℝ) (hr : 0 < r) : 
  converges (geom_series r) ↔ r < 1 :=
begin

end

 