import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Dart
/-! # Core extraction in BULK by mirror polynomial of exact degree FOUR.
 Finite inert faces included before Rotation, no spurious Haar factor.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Slide
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck  Greenbelt
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c C L:Side} {Z D w m:ℕ}

abbrev roller (i:ℕ):ℕ:=3^i
lemma plus_roll (w i:ℕ):w ≤ w*roller i:=Nat.le_mul_of_pos_right _ (by unfold roller; positivity)
lemma roll_cap (w:ℕ)(i:Stars):w*roller i.val ≤81*w:=by fin_cases i <;> norm_num [roller,Stars] <;> omega
def lampR (j:Stars):ℝ:= 1/(![33280, -22464, 62208, -606528, (24261120:ℝ)] j)
abbrev glimmer (w:ℕ)(i:Stars):ℝ:=((2*(w:ℝ))^4)⁻¹ * lampR i
set_option maxHeartbeats 800000 in
private lemma legs (a b: ℝ) (g h k l:ℝ→ℝ) (e f i j:Bool)
   (hb:g=(if e then (fun x=>a+x*b) else Function.const _ (g 0)))
   (he:h=(if f then (fun x=>a+x*b) else Function.const _ (h 0)))
   (hi:k=(if i then (fun x=>a+x*b) else Function.const _ (k 0)))
   (hk:l=(if j then (fun x=>a+x*b) else Function.const _ (l 0))):
   ∑ x:Stars,Slide.lampR x*(g (roller x.val)*h (roller x.val)*k (roller x.val)*l (roller x.val))=if e && f && i && j then b^4 else 0:= by
  conv_lhs => rw [hb,he,hi,hk]
  cases e <;> cases f <;> cases i <;> cases j <;> norm_num [Fin.sum_univ_succ,Stars,lampR,roller] <;> ring

lemma stellarR (v : Petals Z) (hp : 2*Z≤w):
    ∑ i:Stars, Slide.lampR i * ∏ j,(Slide.dinners (w*roller i.val) (v j):ℝ) = if v=Slide.rosy Z then (2*(w:ℝ))^4 else 0:= by
  let u:= (-(2*(Z:ℝ))+1); let g (i:Axis) (x:ℝ):= (match v i with |none => 2*u+x*(2*(w:ℝ))|some ⟨_,k⟩=> (coins k:ℝ))
  let e i:= decide (v i=none); have hx i:g i= if e i then (fun x :ℝ => 2*u+x*(2*(w:ℝ))) else Function.const ℝ (g i 0):= by funext j; simp only [g,e]; cases h:v i with|none=> simp|some val=> rcases val with ⟨b,k⟩; simp
  have hb i (j : ℕ) : (Slide.dinners (w*roller j) (v i):ℝ)=g i (roller j):= by cases h:v i with
    | none=>
      simp only [g,h, dinners,u]; rw [Nat.cast_mul,Nat.cast_add,Nat.cast_sub (by exact hp.trans (plus_roll w j)),Nat.cast_mul,Nat.cast_mul]; push_cast; ring
    | some v'=> obtain ⟨b,k⟩:=v'; dsimp only [g]; rw [h]; rfl
  have hu:e 0 && e 1 && e 2 && e 3 ↔ v=Slide.rosy Z:= by
    simp only [e,Bool.and_eq_true,decide_eq_true_eq]; constructor; · rintro ⟨⟨⟨hx,hv⟩,he⟩,h⟩; funext i; fin_cases i<;> assumption
    rintro rfl; exact ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩
  have h := legs (2*u) (2*(w:ℝ)) (g 0) (g 1) (g 2) (g 3) (e 0) (e 1) (e 2) (e 3) (hx _) (hx _) (hx _) (hx _)
  simp_rw [hb, show (univ:Finset Axis)=({0,1,2,3}:Finset Axis) from (by decide)]; rw [if_congr hu rfl rfl] at h -- edit
  simp at * -- risk
  convert h using 2 with i; ring_nf
lemma vogue (D : Stars→Side) (hp:0< Z) (hq:2*Z≤ w) (he : ∀ i,(D i).val=2*(w*roller i.val)) (f : Petals Z→ℝ) :
    ∑ i:Stars,Slide.glimmer w i * ∑ x:Site (D i), f (charm (w*roller i.val) Z x)= f (Slide.rosy Z):= by
  let b (i:Stars):= charm (C:=D i) (w*roller i.val) Z
  have hb i : ∑ x:Site (D i), f (b i x)=∑ x:Petals Z,(∏ j,(Slide.dinners (w*roller i.val) (x j):ℝ))*f x:= by
    rw [← Finset.sum_fiberwise univ (b i)]; refine sum_congr rfl ?_; intro j _
    rw [sum_congr rfl (show ∀ x∈_, f (b i x)= f j from fun x (hx:x∈univ.filter fun x=>b i x=j)=> congr_arg f ((mem_filter.mp hx).2)), sum_const,nsmul_eq_mul]
    rw [show #(_)=∏ k,dinners (w*roller i.val) (j k) from weighted (he _) (hq.trans (plus_roll w i.val)) hp j,Nat.cast_prod]
  change ∑ i:Stars,glimmer w i * (∑ x, f (b i x))=_; simp_rw [hb,mul_sum, ← mul_assoc]; rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul,glimmer,mul_assoc (((2*(w:ℝ))^4)⁻¹), ← Finset.mul_sum, Slide.stellarR _ hq]; have ht:0<(w:ℝ):=by exact_mod_cast (show 0<w from (by omega))
  simp_rw [mul_ite, mul_zero,inv_mul_cancel₀ (show (2*(w:ℝ))^4≠0 from (pow_pos (by positivity) _).ne')]
  simp
end YM.PhysicalNext.Repeat.Slide
