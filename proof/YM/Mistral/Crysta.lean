import YM.Mistral.Daze
import YM.Mistral.Amber
import YM.Mistral.Wock
import YM.Needle.Pond
import YM.Rill.Vault
/- escaping offset stencils: rank using charged top histories rather than proximity through seams.M.N -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Choir
open Function Set Metric Filter QCD Lat Lattice UV Patria Patria.Depth
open Poised Plans Plans.Stamp Intag Intag.Vale Finset
open scoped Topology BigOperators Matrix ComplexOrder ContDiff Classical
variable {d:ℕ}
open Needle Needle.GaugeP Hub YM.Fir YM.Massive.Fir
variable {C:Sequence}{P:Calibration C}
variable (W: Choir) {φ:ℕ→ℕ}(hp:Tendsto φ atTop atTop)(hW:W.Harmony P φ)
variable {β e:ℝ}(hC:C.Path β e)(hr:Sway C.S)
variable (f g:ℕ→ Label d)
variable (Z:Laurel d)(Y:Landing P.sym Z) (S:Pollens P W)(he:Foil P W S)(hP:P.System)(w:Label d)
variable (M:∀ d,Cottage P d)
-- orientation via interpolation in FULL dimension. NOTE `Γ` acts by sums over SECOND columns. Physical reconstruction is in FIRST vector (Ar'), need TRANSPOSE if rows first. quantitative using nearG hermitian.A crucial. Free Gram Hermitian. perturb gives trans also nearG (taking conjugate) . 
set_option maxHeartbeats 540000
private lemma gram_symmetric {I:Type*}[Fintype I](f:I→I→ℂ)(h:∀ c:I→ℂ,0 ≤ ∑ i, ∑ j,star (c i)*f i j*c j)(i j:I): star (f i j)=f j i:=by
      let e(i:I)(K:ℂ): I→ℂ:= Pi.single i K
      let φ(u v:I→ℂ):ℂ:= ∑ i,∑ j,star (u i)*f i j*v j
      have hf(x y z:I→ℂ): φ x (y+z)=φ x y+φ x z:=by simp [φ,mul_add,Finset.sum_add_distrib]
      have hg(x y z:I→ℂ): φ (x+y) z=φ x z+φ y z:=by simp [φ,add_mul,Finset.sum_add_distrib]
      have hΦ(i j:I)(c d:ℂ): φ (e i c) (e j d)= star c*f i j*d:=by simp only [φ,e,Pi.single_apply]; simp [mul_ite,ite_mul, apply_ite] -- danger star. inspect
      let a:= e i 1; let b:= e j 1; let d:= e j Complex.I
      have hS(p:I→ℂ): star (φ p p)= φ p p:= IsSelfAdjoint.star_eq (IsSelfAdjoint.of_nonneg (h p)) -- lemma
      have hX(p q:I→ℂ): star (φ p q)+star (φ q p)= φ p q+φ q p:=by
             have ht:= hS (p+q); rw [hf,hg,hg] at ht; simp only [star_add, hS] at ht; linear_combination ht
      have hx:= hX a b; have hv:=hX a d; unfold a b at hx; unfold a d at hv; simp only [hΦ,star_one,one_mul, mul_one] at hx hv; simp only [star_mul,Complex.star_def,Complex.conj_I,map_neg,neg_mul] at hv; rw [Complex.ext_iff]; simp [Complex.ext_iff,Complex.star_def] at hx hv ⊢; grind -- check multiplication

lemma gems(i j:Stokes d): star (ΦGram P.sym Z (basis timeAxis) i j)=ΦGram P.sym Z (basis timeAxis) j i:=by
      -- from paidGram positivity
      apply gram_symmetric
      intro c; by_cases h:c=0
      · simp [h]
      exact (paidGram P.sym Z c h).le
-- correction Ξ interpolation via conjug.Frame.Apply star vector latex. 
set_option quotPrecheck false
local notation "Lp"=>↥(W.level d)
local notation "Tz"=>Vale.Stokes d
noncomputable def testG (x:E4) (y:E4) (v:Stokes d→ W.W) : ↥(W.level d) →ₗ[ℂ] (Stokes d→ℂ):=LinearMap.pi (fun j=>(W.total 2 (points ![x,y])|>.toLinearMap (![0,v j]) 0) ∘ₗ ((W.level d).subtype))
noncomputable def grade0 (d:ℕ): ↥(W.level d) →ₗ[ℂ] ↥(W.level d):=(S.parity.toLinearMap.comp (W.level d).subtype).codRestrict _ (fun i=>by
       obtain ⟨p,h⟩:= (show ∃ p:Label d,W.focus none d p=i.val from i.property); change S.parity i.val ∈ _; rw [←h,S.p]; exact ⟨_,rfl⟩)
-- operator estimate inverse via transpose map. could bound using dual norm ≤dim*J.T levy. PS budget should account n.M.Ask additionally weight. But Φ hermitian plausible shift swapped.Bra.Ar. use change BasisP F matrix conj and solve Pq via gamma#. Need adapt lemma `braid_r` require nearG g'=star_???` if P not conjug.V complex-linear.S.D.K norm star.D. prove general inverse bound then modify `braid_r`. 

variable (x y:E4)
lemma test_g(v:Tz→ W.W)(z:Lp)(i:Tz): testG W x y v z i=W.total 2 (points ![x,y]) (![z.val,v i]):=by apply congr_arg (W.total 2 (points ![x,y])); ext1 i; fin_cases i<;>simp
lemma gDom (f:Tz → Tz → ℂ)(hp: nearG P.sym Z Y.ε f) : ∀ x:Tz→ℂ,‖x‖ ≤ Y.J* ‖Γ (fun i j=> f j i) x‖:=by
       let B i j:= star (f j i); have hh: nearG P.sym Z Y.ε B:=fun i j=>by let T:= ΦGram P.sym Z (basis timeAxis); change ‖star _-T i j‖ ≤ _; rw [show T i j=star (T j i) from (gems Z j i).symm,← star_sub,norm_star]; exact hp ..
       intro x; have hx: Γ B (star x) = star (Γ (fun i j=> f j i) x):=by
             ext1 i; change ∑ j:Tz, B i j*star (x j)= star (∑ j:Tz,f j i*x j); rw [star_sum]; exact sum_congr rfl fun j _=>by rw [star_mul]; exact mul_comm ..
       have h:=Y.warmth hh (star x); rw[hx] at h; simpa using h
lemma rouse(p:Tz→Lp)(L:Lp →ₗ[ℂ](Tz→ℂ))(qs:Tz→Bool)(hG:∀ i,grade0 W S d (p i)=(if qs i then (-1:ℂ) else 1) • p i)(hr0:W.Domestic)(hx:nearG P.sym Z Y.ε (fun i j=>L (p i) j))(c:Lp)(v:ℝ)(hV:Y.J*‖L c‖≤v)(ht:grade0 W S d c=c) : ∃ x:Tz→ℂ,(∑ i:Tz, x i • p i)=c∧‖x‖≤ v∧∀ i,qs i=true→x i=0:=by
      let f:Tz→Tz→ℂ:=fun i j=>L (p j) i
      let g: (Tz→ℂ)→ₗ[ℂ] Lp:=∑ i:Tz, (LinearMap.proj i).smulRight (p i)
      have hg(w:Tz→ℂ):g w=∑ i:Tz,w i • p i:=by simp [g];
      have hX(w:Tz→ℂ): Γ f w= L (g w):=by funext j; change ∑ i:Tz, f j i*w i=L (g w) j; rw [hg,map_sum,Finset.sum_apply]; exact sum_congr rfl fun i _=>by rw[map_smul,Pi.smul_apply,smul_eq_mul]; unfold f; rw [mul_comm]
      have hp(w:Tz→ℂ): ‖w‖≤ Y.J*‖L (g w)‖:=by rw[← hX]; exact gDom Z Y _ hx w
      have h1 : Injective g:= LinearMap.ker_eq_bot.mp (bot_unique (fun x hx=> (norm_le_zero_iff).mp (le_trans (hp _) (by rw [show g x=0 from hx,map_zero,norm_zero,mul_zero])))); have he :Surjective g:= (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 h1
      swap; · exact (by rw [Module.finrank_fintype_fun_eq_card]; unfold Vale.Stokes; rw[Fintype.card_fin]; exact (hr0.faith d).symm)
      obtain ⟨f,hf⟩:=he c; refine ⟨f,(hg f).symm.trans hf,(hp f).trans (by rw [hf]; exact hV),?_⟩
      let u:Tz→ℂ:= fun i=> f i * (if qs i then (-1:ℂ) else 1); have hu:g u=grade0 W S d (g f):=by rw [hg,hg,map_sum]; exact sum_congr rfl fun i _=> by rw [map_smul,hG,smul_smul]
      have hz:u=f:= h1 (by rw [hu,hf,ht])
      intro i hi; have h:=congr_fun hz i; unfold u at h; rw [if_pos hi] at h; linear_combination (norm:=ring_nf) (-1/2:ℂ)*h
end YM.Massive.Tarn.Choir
#print axioms YM.Massive.Tarn.Choir.rouse
