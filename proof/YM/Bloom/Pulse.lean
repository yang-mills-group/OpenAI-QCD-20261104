import YM.Bloom.Buzz
/-! # width and cut comparison for spin marks with choose omitted deterministic tables. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bloom.Buzz
open Function Lattice Laurent Bloch Metric RG Filter Arise
open Finset YM.Bank Precision Matrix YM.Bloom
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator Classical
open QCD QCD.Lat QCD.Free QCD.Flume QCD.Bank Next.Free YM.Bloom.TreeP
open QCD.Creek QCD.Anomaly QCD.Cove
variable {c f:Side}{N r k m n l b ℓ s:ℕ}{A J Y:Type}[Fintype A][Fintype J][Fintype Y]
variable (x:Cover)(a:Fiber)(p:Flavor N) (P Q:Parc)(e:Bool)
lemma price_row (i:Lat.Row f): ‖plume f x a P () i‖ ≤ pattern P:= by
     rw [reefs]; unfold Arise.sound; simp only [Finsupp.linearCombination_apply,Finsupp.sum]; apply (norm_sum_le ..).trans (sum_le_sum (fun v _=>?_)); split; rw [norm_smul,pathLength,mul_one]; simp
lemma plume_zone (i:Lat.Row f)(h:plume f x a P () i≠0)(hp:flet P ≤ r): i.1∈ halo r {wrap f x}:=by
     rw [reefs] at h; unfold Arise.sound at h; rw [Finsupp.linearCombination_apply,Finsupp.sum] at h; obtain ⟨z,hz,hq⟩:= exists_ne_zero_of_sum_ne_zero h; split at hq
     next he=> rw [← he]; exact marchO _ _ _ _ hz hp -- syntax
     next=> simp at hq
lemma paint_zone (i:Keys f N)(h:paint f x a p P e () i ≠0)(hp:flet P ≤ r): i∈ limits (halo r {wrap f x}):=by
     rcases e with _|_ <;> cases i <;> simp only [paint, Bool.false_eq_true,↓reduceIte, scrim,of_apply,Sum.elim_inl,Sum.elim_inr,Matrix.zero_apply,flaw] at h
     next i=> split at h; exact mem_filter.mpr ⟨mem_univ _,plume_zone x a P i.1 h hp⟩; simp at h
     next i=> exact (h rfl).elim
     next i=> exact (h rfl).elim
     next i=> split at h; exact mem_filter.mpr ⟨mem_univ _,plume_zone x a P i.1 h hp⟩; simp at h
lemma price_paint (i:Keys f N): ‖paint f x a p P e () i‖ ≤ pattern P:=by
     cases e <;> cases i <;> simp only [paint,Bool.false_eq_true,↓reduceIte,scrim,of_apply, Sum.elim_inl, Sum.elim_inr,Matrix.zero_apply,norm_zero,flaw] <;> first | exact valor_g _ | (split; exact price_row ..; rw[norm_zero]; exact valor_g _)
noncomputable def audit (b N:ℕ):ℝ:= (2*(b+b+1)^4*Fintype.card Fiber*N:ℕ)
lemma audits (u:Site f) : ((limits (F:=N) (halo b {u})).card:ℝ) ≤ audit b N:=by unfold audit; apply Nat.cast_le.mpr; rw [limits_card]; gcongr; simpa using (Lattice.Corona.halo_size ({u}:Support f) b)
lemma money_p : cusp (paint f x a p P e) ()≤ audit (flet P) N * pattern P:= (cupful _ _ _ _ (price_paint x a p P e) (fun i h=>paint_zone x a p P e i h (show flet P≤ flet P from le_rfl))).trans (mul_le_mul_of_nonneg_right (audits _) (valor_g _))
variable {u v d:ℝ}
-- price cuts need project bottom spine: ReachV applies Extended.. can project R.E upper-left block actual kept.C
lemma valves_full (U: Kit.Rail f c)(X:Kit.Rail c f)(o:Site c) (hp:flet P ≤ r) (R:Matrix (Keys f N) (Keys c N) ℂ)(he:∀ i∈ limits (F:=N) (halo r {wrap f x}),∀ j,R i j ≠0 → j ∈ limits (halo b {o}))(h:∀ i,‖(paint f x a p P e*wheel U X N) () i‖ ≤ u)(ht:∀ i,cusp (wheel U X N-R) i ≤ v)(hu:0 ≤ u)(hv:0≤ v) :
    let α:= audit (flet P) N*pattern P * v; cusp (paint f x a p P e*wheel U X N) () ≤ α+audit b N*(α+u):=by
    intro α; let X₁:=paint f x a p P e; let Q:= wheel U X N; let V:= limits (F:=N) (halo b {o}); have hz:=money_p x (f:=f) a p P e; have hα: α≥0:=mul_nonneg ((cups_pos ..).trans hz) hv; apply cup_diff (X₁*Q) (X₁*R) u α (audit b N) V hu hα (audits o) () h
    · rw [← Matrix.mul_sub]; exact cups_tender X₁ _ _ _ hv () hz ht
    intro i hi; rw [Matrix.mul_apply] at hi; obtain ⟨a,ha,hp'⟩:=Finset.exists_ne_zero_of_sum_ne_zero hi; exact he _ (paint_zone _ _ _ _ _ _ (left_ne_zero_of_mul hp') hp) i (right_ne_zero_of_mul hp')
-- canonical cost self.A rank independent but Train r requires p+3.E. 
lemma ready_unit : wheel (1:Sheet f) 1 N=1:=by unfold wheel bladesF; ext i j; cases i <;> cases j <;> simp [Kit.choir,Matrix.blockDiagonal_apply,Matrix.one_apply]; all_goals split_ifs <;> simp_all [Prod.ext_iff]
lemma buy_unit (hp:P∈ tails k ℓ)(hq:Q∈tails l n)(he:ℓ+2≤ r)(hu:n+2≤ r) : ∃ C:ℝ, 0 ≤ C ∧∀ f:Side,∀ (i j:Flavor N)(x y:Cover)(a b:Fiber)(q w:Bool)(D:Train r), ‖(paint f x a i P q*start f D N*(paint f y b j Q w).transpose) () ()‖ ≤ C:=by
     obtain ⟨C,hc,H⟩:=sailS (N:=N) P Q hp hq he hu; refine ⟨C*(gear ⟨1,by simp⟩ k*gear ⟨1,by simp⟩ l), mul_nonneg hc (mul_nonneg (gear_pos ..).le (gear_pos ..).le),?_⟩; intro f i j x y a b q w D; have he:=H i j x y a b q w (YM.Bank.idle f) D _ Giant.unit; rw [ready_unit, transpose_one,Matrix.one_mul,Matrix.mul_one] at he; exact he
-- seam limit unit topics from spin_cost.Domain.F.Scaled. prove on SpinMode leg true pair both.bool first ensuring positive.
open Massive Massive.UV UV.Free YM.Bank.Jule YM.Bloom.Jar
lemma spirals (i:SpinMode k)(j:SpinMode m)(hn:9+k+m≤n)(hr:2 ≤ r)(ht:0<v)(d:ℝ)(q w:Bool)(hp:Rocky none (steps i.1.1) k P)(hq:Rocky none (steps j.1.1) m Q): ∃ C:ℝ,0≤ C ∧∀ᶠ s:ℝ in atTop,∀ z:Cover,posT s n z ∈ Oasis v d →∀ᶠ f:Side in atTop,∀ x y:Cover,x-y=z→∀ D:Train r,s * ‖(s^n)^(3+(steps i.1.1).length+(steps j.1.1).length) • (paint f x i.1.2 i.2 P q*start f D 6*(paint f y j.1.2 j.2 Q w).transpose) () ()-(if q=false∧ w=true then leg i j (posT s n x) (posT s n y) else 0)‖≤ C:=by
     let l:= steps i.1.1; let u:=steps j.1.1; obtain ⟨C,hc,H⟩:=spin_cost l u i.1.2 j.1.2 hn hr ht d ((spine_cost ..).trans_le i.1.1.property) ((spine_cost ..).trans_le j.1.1.property) P Q hp hq
     refine ⟨C,hc,?_⟩; filter_upwards [H] with s hs z hz; filter_upwards [hs z hz] with f hf x y he D; have hp:posT s n x≠posT s n y:= sub_ne_zero.mp (by rw [← unspread,he]; exact door hz ht); unfold start; rw [slice_read]; by_cases hp':q=false∧w=true; swap
     · rw [if_neg (by tauto), if_neg hp', smul_zero,sub_zero,norm_zero,mul_zero]; exact hc
     rw [if_pos hp', Range.tours _ _ i j hp,← unspread,he]; by_cases h:i.2=j.2
     · rw [if_pos ⟨hp'.1,hp'.2,h⟩,if_pos h]; exact hf x y D he
     rw [if_neg (fun hv=>h hv.2.2),if_neg h,smul_zero,sub_zero,norm_zero,mul_zero]; exact hc
end YM.QCD.Bloom.Buzz
#print axioms YM.QCD.Bloom.Buzz.buy_unit
#print axioms YM.QCD.Bloom.Buzz.valves_full
#print axioms YM.QCD.Bloom.Buzz.spirals
