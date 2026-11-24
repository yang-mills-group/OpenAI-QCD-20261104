import YM.QCD.Pearl.Busk

/-! # real weighted second differences -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free RG Rudder Revolve Free Para Pinch
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology
variable {z p k: Momentum}(C:su.Color){t r:ℝ}
lemma pretty (k:ReP)(a:Axis): |hopC k a| ≤ fry k:=by unfold hopC; split <;> simpa using (fry_sub k _)
lemma capitalBound (k:ReP): |capital k| ≤ lensq k:=by unfold capital; apply abs_le.mpr; constructor <;> nlinarith [ordinate k 1]
lemma bring (C:su.Color)(hC:‖C‖=1)(k:ReP)(hk:0<fry k)(a:Axis): ∃ S L:ℝ,S=trekS C k a 0∧∀ t:ℝ, |t| ≤ fry k/4 →
    |trekS C k a t - (S+t*L+t^2*f0 k a)|≤480*|t|^3/fry k^5:=by
  let r:= fry k; let x:= k a / r; let y:=capital k / lensq k; let z:=hopC k a / r
  let Q t:= 1+2*x*t+t^2; let g (t:ℝ):= Q t; let b:=z-2*x*y; let c:= y*(4*x^2-1)-2*x*z; let π t:= y+b*t+c*t^2
  have hp:r>0:=hk; have he : r^2=lensq k:=fry_sq k
  have hx: |x|≤1:=by unfold x; rw [abs_div,abs_of_pos hp]; exact div_le_one_of_le₀ (fry_sub k a) hp.le -- check needs 0< 
  have hz: |z|≤1:=by unfold z; rw [abs_div,abs_of_pos hp]; exact div_le_one_of_le₀ (pretty k a) hp.le
  have hy: |y|≤1:=by unfold y; have hh:0<lensq k:= he ▸ pow_pos hp _; rw [abs_div,abs_of_pos hh]; exact div_le_one_of_le₀ (capitalBound k) hh.le
  let N:= (12:ℝ)/r^2; have hN:0<N:=by unfold N; positivity
  have hm : f0 k a=N*c/(r^2):=by unfold f0 N c y z x; rw [← he]; field_simp; ring
  have hs (u:ℝ): trekS C k a (u*r)=N*((y+z*u)/Q u):=by
    rw [shipS C hC k a];
    have hh : lensq k+2*k a*(u*r)+(u*r)^2=r^2*Q u:=by unfold Q x; rw [← he]; field_simp
    rw [hh]; unfold N y z; rw [← he]; by_cases hv:Q u=0; · simp [hv]
    field_simp
  refine ⟨N*y,N*b/r,by simpa only [zero_mul, mul_zero, zero_pow (by norm_num : (2:ℕ)≠0), Q,add_zero,div_one] using (hs 0).symm,fun t ht=>?_⟩
  let u:= t/r; have h1:t= u*r:= (div_mul_cancel₀ t hp.ne').symm
  have hu: |u|≤1/4:=by unfold u; rw [abs_div,abs_of_pos hp]; apply (div_le_iff₀ hp).mpr; linarith
  have hV := rational_bill hy hx hz hu
  have hl : trekS C k a t - (N*y+t*(N*b/r)+t^2*f0 k a)= N*((y+z*u)/Q u-π u):=by rw [h1,hs,hm]; unfold π; field_simp
  rw [hl,abs_mul,abs_of_pos hN]; exact (mul_le_mul_of_nonneg_left hV hN.le).trans_eq (by change N*_=_/r^5; unfold N u; rw [abs_div,abs_of_pos hp]; ring)
lemma sparkle (f : ℝ→ℝ)(S L K t e : ℝ)
    (h:|f t-(S+t*L+t^2*K)|≤e)(hk: |f (-t)-(S+(-t)*L+(-t)^2*K)|≤e): |f t+f (-t)-2*S-2*t^2*K|≤2*e:=by
  apply (abs_le.mpr ?_); have h1:=abs_le.mp h; have h2:=abs_le.mp hk; constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]
lemma glistle (hC:‖C‖=1)(k:ReP)(hk:0<fry k)(a:Axis)(ht:0≤t)(h:t≤ fry k/4):
    |trekS C k a t+trekS C k a (-t)-2*trekS C k a 0-2*t^2*f0 k a| ≤2*(480*t^3/fry k^5):=by
  obtain ⟨_,L,rfl,H⟩:=bring C hC k hk a
  apply sparkle (L:=L); · simpa [abs_of_nonneg ht] using H t (by rwa [abs_of_nonneg ht])
  simpa [abs_of_nonneg ht] using H (-t) (by rwa [abs_neg,abs_of_nonneg ht])

lemma cast_N (u:ℝ)(i:Axis): boost (-u) i= -boost u i:=by unfold boost; rw [Complex.ofReal_neg,neg_smul]
lemma camp_cast (t:ℝ)(i):‖boost t i‖= |t|:= (streak ..).trans (by rw [Complex.norm_real]; rfl)


def modelX (A V:Shine→Bundle)(F:Momentum→ Para)(k:ReP)(i:Axis)(t:ℝ):= (spanX F A V (boost t i) (castP k)).re

variable {F: Momentum→Para}{A V: Shine→Bundle}{s c B ε η b q:ℝ}
lemma orbitClose (h:Pinch F s c B)(hS:Pinch shaft s c B)(e:Bright s c B ε)(hη: ε*Real.pi≤η/2)(he:0<η) (hA:Wall η b A)(hQ:Wall η q V)(hX:A (0,0)=touch (echo C)*wave (gamma 1)) (k:ReP)(hk:castP k ∈baseCube) (h0:castP k≠0) (i:Axis) (ht:0≤t)(hR:t< ε*‖castP k‖/4):
  |(modelX A V F k i t+modelX A V F k i (-t)-2*modelX A V F k i 0) - (trekS C k i t+trekS C k i (-t)-2*trekS C k i 0)| ≤ (16*wobble2 s c B η b q)/(ε^2)*t^2/‖castP k‖^3:=by
  let p:= castP k
  let f (x:ℂ):=spanX F A V (x • step i) p-crown (A 0) (x • step i) p
  have hK:0<ε*‖p‖:=mul_pos e.seed (norm_pos_iff.mpr h0)
  have hh:= sided₂ hK f (airlift h hS e hη he hk h0 hA hQ i ·) (fun z hz=> ambient h hS e hη he hk h0 hA hQ (show ‖(z • step i:Momentum)‖ < _ from (streak ..).trans_lt (mem_ball_zero_iff.mp hz))) (↑t:ℂ) (by rwa [Complex.norm_real,Real.norm_of_nonneg ht])
  have hf (t:ℝ) : (f (↑t:ℂ)).re=modelX A V F k i t - trekS C k i t:= by
    unfold f; rw [show A 0= _ from hX,Complex.sub_re]; rfl
  have heq:= (Complex.abs_re_le_norm _).trans hh
  rw [← Complex.ofReal_neg, show f 0=f (↑(0:ℝ):ℂ) by rw [Complex.ofReal_zero],Complex.sub_re,Complex.add_re,Complex.mul_re,hf,hf,hf] at heq; simp only [Complex.re_ofNat, Complex.im_ofNat,zero_mul,sub_zero,Complex.norm_real,Real.norm_of_nonneg ht] at heq
  refine (le_of_eq (congr_arg abs (by ring : _= (modelX A V F k i t-trekS C k i t+(modelX A V F k i (-t)-trekS C k i (-t)) -2*(modelX A V F k i 0-trekS C k i 0))))).trans (heq.trans_eq (by unfold p; ring))
end YM.QCD.Pearl
