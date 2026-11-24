import YM.Bank.Spur
import YM.QCD.Pearl.Culp
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bank
open Matrix RG Function Wilson Finset Lattice Next.Free Lat Flume Laurent Bloch Metric
open QCD.Free
open YM.Bank
open YM.Bank.Merchant
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators ComplexConjugate
variable {c f:Side} {j:ℕ}{H:Ratio c f}{D B : Train j}
lemma comes_g (p: Site c): rangeG D p=Pearl.vase (Dir D) (tuning p):=by unfold rangeG Pearl.vase; rw [Para.live_inv (nonzeroD (dog p) (tune_nonzero p)), full_match (dog p) (tune_nonzero p)]
lemma prices (hj:2≤j) : ∃ C:ℝ,0 ≤ C ∧∀ (D:Train j)(c:Side)(p:Site c), ‖rangeD D p‖≤C*‖tuning p‖ ∧ ‖rangeG D p‖ ≤ C/‖tuning p‖:=by
   obtain ⟨r,v,C,W⟩:=Pearl.boot hj
   have hg:=W (Train.top j); obtain ⟨ε,h,e⟩:=hg.source 1 one_pos; let A:= ‖Pearl.script‖*Pearl.Pinch.city r C; let D':= max A (Pearl.Pinch.purse r v C)
   refine ⟨D', le_trans hg.cost_q (le_max_right ..),fun D c p=> ?_⟩
   have hx:=tune_nonzero p; have h':=W D
   have hm:= norm_pos_iff.mpr hx; have hz:=keyboard p
   refine ⟨?_, ?_⟩; · refine (Pearl.script.le_opNorm (Dir D (tuning p))).trans ?_; apply le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left ..) hm.le); unfold A; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); exact h'.Far (h'.useX h hz hx (h'.friend h hz hx)) hz (by linarith)
   rw [comes_g]; exact (h'.protectedV h hz hx (h'.friend h hz hx)).2.trans (div_le_div_of_nonneg_right (le_max_right ..) hm.le)
lemma torn (x p : Site f): ‖scarf p x‖=(f.val:ℝ)⁻¹^2:=by rw [wave_root,norm_mul,mode_real _ _ (keyboard p).1]; simp
-- price exact row single spine opening. engineering H^-3/2 = (Kit.slope H.count)/H.
def gear (H:Side)(s:ℕ) : ℝ:= Kit.slope H/(H.val:ℝ)^(1+s)
lemma gear_pos (H:Side)(s:ℕ): 0<gear H s:=div_pos (Kit.slope_pos _) (pow_pos (side_pos _) _)
lemma spins (hp:2≤j)(u:List Axis)(hu:u.length+2≤j): ∃ C : ℝ, 0≤C ∧∀ {c f:Side}(H:Ratio c f)(D B:Train j){U X Q},Giant j H D B U X Q→ ∀ i l,
    ‖(oldDiff U u*leaf c) i l‖ ≤ C*gear H.count u.length*(c.val:ℝ)⁻¹^2 ∧ ‖(oldDiff Xᴴ u*leaf c) i l‖ ≤ C*gear H.count u.length*(c.val:ℝ)⁻¹^2:=by
  obtain ⟨C,hc,T⟩:=prices hp; obtain ⟨E,he,HE⟩:=Merchant.fora j; obtain ⟨F,hF,HF⟩:=decay_cost
  let B':=4*C*C*E*μ^u.length; have hs:=μpos
  refine ⟨B'*F,by unfold B'; positivity,fun {c f} H D B {U X Q} h ⟨x,y⟩ ⟨p,q⟩=>?_⟩
  let R:=B'*F*gear H.count u.length*(c.val:ℝ)⁻¹^2
  let G : Site f→Bundle:= rangeG D; let S : Site c→Bundle:=rangeD B; let v:=‖tuning p‖
  have hx (Y:Site f→Bundle)(K:Site c→Bundle)(hY:∀ x, ‖Y x‖ ≤ ‖G x‖)(hK:‖K p‖≤ ‖S p‖):
        ‖(oldDiff (install Y*Qᴴ*install K) u * leaf c) (x,y) (p,q)‖≤R:=by
    rw [tariffs H Y K h.lands h.odd]; apply (norm_sum_le ..).trans
    let l:=H.count; let A:=(l.val:ℝ); have hd:0<A:=side_pos _; have hP:=tune_nonzero p
    let w:= B'*gear l u.length*(c.val:ℝ)⁻¹^2; have hw:0≤w:=by unfold w B'; have hv:= gear_pos l u.length; positivity
    calc
      _ ≤ ∑ i:Site l,decay 2 i*w:=sum_le_sum fun i _=> by
         rw [norm_mul,norm_mul,torn,full_tune H h.odd] -- tag bills
         let τ:=grade i; let s:= τ^u.length; let k:= twins H p i; let r₀:=‖tuning k‖; have hr : 0< r₀:=norm_pos_iff.mpr (tune_nonzero _)
         have ha := T D f k|>.2; have hb := T B c p|>.1; have hg: v≤4*A*r₀:=by unfold v A l r₀ k; rw [full_tune H h.odd]; exact Merchant.core i (keyboard _)
         have h₀ := Merchant.distance (keyboard p) i h.odd u
         let t:= tag H Y K j p i; let J':= decay j i
         have hi:= Kit.slope_pos l
         have ht0: ‖Y k*K p‖ ≤ 4*A*C*C:=by
            apply (norm_mul_le _ _).trans; refine (mul_le_mul ((hY _).trans ha) (hK.trans hb) (norm_nonneg _) (by positivity)).trans ?_;
            change C/r₀*(C*v)≤_; exact ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg hc) (show 0 ≤ C/r₀ from by positivity)).trans_eq (by field_simp)).trans_eq rfl -- remove? equality target hole
         have hm:‖mount j H p i‖ ≤ Kit.slope l* (E*decay j i) :=by unfold mount; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Kit.slope_pos _).le]; apply mul_le_mul_of_nonneg_left _ hi.le; exact (HE _ _ _ h.odd (keyboard p)).1
         have ht : ‖t y q‖ ≤ (Kit.slope l*(E*decay j i))*(4*A*C*C):=by apply (Cost.north _ _ _).trans; unfold t tag; rw [norm_smul,norm_star]; exact mul_le_mul hm ht0 (norm_nonneg _) ((norm_nonneg _).trans hm)
         have hy:= mul_le_mul_of_nonneg_right h₀ (sq_nonneg ((f.val:ℝ)⁻¹)); apply (mul_le_mul hy ht (norm_nonneg _) ((mul_nonneg (norm_nonneg _) (sq_nonneg _)).trans hy)).trans
         refine (le_of_eq ?_).trans (mul_le_mul_of_nonneg_right ((show grade i^u.length*decay j i ≤ _ from ?_).trans (absorbs i u.length 2)) hw)
         · have hq:(f.val:ℝ)=(c.val:ℝ)*A:= by rw [H.exact_size,Nat.cast_mul]
           rw [hq]; unfold w B' gear A l; rw [pow_add]; field_simp
         exact mul_le_mul_of_nonneg_left (decay_anti i (by omega)) (pow_nonneg (grade_pos i).le _)
      _ ≤ F*w:=by rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (HF _) hw
      _ = R:=by unfold w R l; ring
  rw [h.rise,h.fall]; change ‖(oldDiff (install G* Qᴴ*install S) u*leaf c) (x,y) (p,q)‖≤ R ∧ ‖(oldDiff (install S * Q * install G)ᴴ u*leaf c) (x,y) (p,q)‖ ≤ R
  rw [peel_cast]; exact ⟨hx G S (fun _=>le_rfl) le_rfl,hx (fun i=>(G i)ᴴ) (fun i=>(S i)ᴴ) (fun _ => le_of_eq (l2_opNorm_conjTranspose _)) (le_of_eq (l2_opNorm_conjTranspose _))⟩
local notation "N"=> (Fintype.card Fiber:ℝ)
lemma jet_bound {c:Side}(U:Matrix (Lat.Row f) (Lat.Row c) ℂ){a:ℝ}(ha:0≤a)(h:∀ i j, ‖(U*leaf c) i j‖ ≤ a*(c.val:ℝ)⁻¹^2)(x i): ‖U x i‖ ≤ a * N :=by
    have ht: U=U*leaf c*star (leaf c):=by rw [Matrix.mul_assoc,(leaf_u _).2,Matrix.mul_one]
    let z:=(c.val:ℝ)⁻¹^2; have hz:0≤z:=sq_nonneg _
    nth_rw 1 [ht]; rw [Matrix.mul_apply]; apply (norm_sum_le ..).trans; apply (sum_le_sum (g:=fun (_:Lat.Row c)=> a*z*z) fun j _=> ?_).trans_eq
    · have hp:= side_pos c; change ∑ _:Site c×Fiber,a*z*z=_; simp [z]; field_simp -- ring?
    rw [norm_mul]; have he: ‖star (leaf c) j i‖≤ z:=by obtain ⟨i,a⟩:=i; obtain ⟨j,b⟩:=j; rw [star_eq_conjTranspose,conjTranspose_apply,norm_star,bare_leaf,Matrix.one_apply]; split; rw [mul_one,torn]; simp[mul_zero]; exact hz
    exact mul_le_mul (h x _) he (norm_nonneg _) (mul_nonneg ha hz)
lemma aval (hp:2≤j)(u:List Axis)(hu:u.length+2≤j): ∃ C : ℝ, 0≤C ∧∀ {c f:Side}(H:Ratio c f)(D B:Train j){U X Q},Giant j H D B U X Q→ ∀ i l,
    ‖oldDiff U u i l‖ ≤ C*gear H.count u.length ∧ ‖oldDiff Xᴴ u i l‖ ≤ C*gear H.count u.length:=by
   obtain ⟨C,hc,E⟩:=spins hp u hu; refine ⟨C*N,by positivity,fun {c f} H D B {U X Q} h i l=>?_⟩
   rw [mul_right_comm]; exact ⟨jet_bound _ (mul_nonneg hc (gear_pos ..).le) (fun i j=>(E _ _ _ h i j).1) i l, jet_bound _ (mul_nonneg hc (gear_pos ..).le) (fun i j=> (E _ _ _ h i j).2) i l⟩
end YM.QCD.Bank
#print axioms YM.QCD.Bank.aval
