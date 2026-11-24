import YM.Gust.Ach
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter Analysis MeasureTheory Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind Gala
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix InnerProductSpace Classical
variable {K: Choir}{C: Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf: Foil P K T) {m n k d:ℕ}(a:Axis)
variable (x y:ℝ)(w:K.W)
noncomputable abbrev pet(a:Axis)(s:ℝ):E4:=s • basis a
local notation "κ" s:arg=>pet a s
noncomputable abbrev postX (w:K.W)(s:ℝ)(h:0<s): Hall K a:=⟨[(κ s,w)],(spots _).mpr (by simp),fun z ht=>by rw[List.mem_singleton] at ht; simpa [ht,basis]⟩
variable (Y:Kernel.Gram fun x y: Hall K a=> tone (oppositeS T a x.val++ y.val))
lemma reflectedM(t:ℝ): Ortho.move (Signed.reflect a) (pet a t)= pet a (-t):=by ext i; by_cases h:a=i<;>simp [Signed.mirrored,basis,h]
noncomputable def iconP(a:Axis)(s:ℝ)(w:K.W):= K.total 2 (points ![0,pet a s]) ![T.adj a w,w]
include hf
lemma unitPair(x y:ℝ)(h:x < y) : K.total 2 (points ![pet a x,pet a y]) ![T.adj a w,w]= iconP (T:=T) a (y-x) w:=by
     rw [← hf.translation 2 (points ![pet a x,pet a y]) ?_ (pet a (-x))] -- check direction
     · refine congr_arg (fun i=> K.total 2 i (![T.adj a w,w])) ?_; ext1 i; fin_cases i; · simp[pet, basis, points]
       simp only [Points.across_coord,points_apply,Matrix.cons_val_one]; unfold pet; rw [sub_smul]; simp; abel -- names
     have hh:pet a x≠ pet a y:=by intro hp; exact h.ne (by simpa [pet,basis] using congr_arg (fun p:E4=>p a) hp)
     intro i j he; fin_cases i<;>fin_cases j<;>simp [hh,Ne.symm hh] at *
lemma signal(h:0<x)(ht:0<y) : inner ℂ (Y.plant (postX a w x h)) (Y.plant (postX a w y ht))=iconP (T:=T) a (y+x) w:=by
     rw [Y.measure]; unfold oppositeS; change tone [(Ortho.move (Signed.reflect a) (pet a x),T.adj a w),(pet a y,w)]=_; rw [reflectedM]; apply Eq.trans ?_ (Eq.trans (unitPair hf a w (-x) y (by linarith only [h,ht])) (congr_arg (fun t=> iconP (T:=T) a t w) (sub_neg_eq_add ..)))
     unfold tone; congr 1
     · apply congr_arg (K.total 2); apply PiLp.ext; intro i; fin_cases i <;>rfl
     · ext1 i; fin_cases i <;>rfl
lemma stamina(Y:Kernel.Gram fun x y: Hall K a=> tone (oppositeS T a x.val++ y.val))(hx:0<x)(h:iconP (T:=T) a x w=0)(hy:x/2 < y):iconP (T:=T) a y w=0:=by
      let t:= x/2; let u:= y-t; have hu:0<u:=sub_pos.mpr hy; have ht:0<t:=half_pos hx
      have hz:Y.plant (postX a w t ht)=0 :=by apply (inner_self_eq_zero (𝕜:=ℂ)).mp; rw [signal hf a t t w Y ht ht,show t+t=x from add_halves x]; exact h -- order
      rw [← show u+t=y from sub_add_cancel .., ← signal hf a t u w Y ht hu,hz]; simp
include hK
lemma credible {x:ℝ}(hx:0<x)(h:w≠0): iconP (T:=T) a x w≠ 0:=by
      obtain ⟨Y⟩:= Kernel.host (shines hK hf a); obtain ⟨s,hS,hs⟩:= hf.realPair a w h; intro hQ; let R(k:ℕ):ℝ:= x*(3/4:ℝ)^k; have h(k:ℕ):0<R k:=by unfold R; positivity
      have hv(k:ℕ):iconP (T:=T) a (R k) w=0:=by induction k with|zero=>simpa [R] using hQ|succ k ih=> exact stamina hf a (R k) (R (k+1)) w Y (h _) ih (by rw [show R (k+1)= R k*(3/4) from (by unfold R; rw[pow_succ,mul_assoc])]; linarith [h k])
      have ht:Tendsto R atTop (𝓝 0):=by simpa only [R,mul_zero] using ((tendsto_pow_atTop_nhds_zero_of_lt_one (show 0≤(3/4:ℝ) from by norm_num) (by norm_num)).const_mul x)
      obtain ⟨i,hx⟩:= (ht.eventually_lt_const hS).exists
      have he:= stamina hf a (R i) s w Y (h _) (hv _) (by linarith only[hS,hx]); exact hs.ne' he
end YM.Massive.Gust
#print axioms YM.Massive.Gust.credible
