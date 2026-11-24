import YM.Giles.Magus
/-! Root total Ward readings. They require chart equality not Tally equality for exact Fourier. Derived for local stencils. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
variable {u t a D C v e s:ℝ}{c:Side}{n l d m r k p q w:ℕ}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Complex (exp I)
variable (F Y: Grid c→ Lat.Fields c 6) (g:su.Color)(x:VerseL c)(s:ℂ) (h:Chart k F 1)(hf: Chart k Y 1)(hk:1 ≤ k)
include h hk
lemma tent_join (x:Y★)(hp:Chart k Y 1): tent g (F+Y) x=tent g F x+tent g Y x:=by
      have he: Chart k (F+Y) 1:= h.add hp
      rw[determines g _ x he hk,left_add _ h hp (show List.length [ink g x] ≤ k from hk),determines g F x h hk, determines g Y x hp hk]
lemma tent_grow(x:Y★): tent g (s • F) x=s • tent g F x:=by
      let L: G★→L[ℝ] G★:= s • ContinuousLinearMap.id ℝ G★
      have he: s • F= L ∘ F:=rfl; rw [he]; rw [determines g _ x (show Chart k (L ∘ F) 1 from L.contDiff.contDiffAt.comp _ h) hk,left_linear L [ink g x] h (show List.length _ ≤ _ from hk),determines g _ x h hk]; rfl
lemma rub_plus(hf:Chart k Y 1): rub g (F+Y) x=rub g F x+rub g Y x:=by
      unfold rub; simp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [tent_join F Y g h hk _ hf,tent_join F Y g h hk _ hf,smul_add]; abel
lemma rub_growth : rub g (s • F) x=s • rub g F x:=by
      unfold rub; simp only [LinearMap.coe_mk,AddHom.coe_mk]; rw[tent_grow F g s h hk,tent_grow F g s h hk,smul_add,smul_comm I s]
omit h hk
lemma tent_eq (Y F:Density c 6)(hx : F=ᶠ[𝓝 1] Y): tent g F= tent g Y:=by unfold tent; rw[(hx.comp_tendsto (soonK g)).fderiv_eq]
lemma rub_eq(hx:F=ᶠ[𝓝 1] Y) : rub g F= rub g Y:=by ext1 u; unfold rub; simp only [LinearMap.coe_mk,AddHom.coe_mk,tent_eq g Y F hx]
variable (a b: Axis)(p: Flavor 6)(i j:Fiber)
noncomputable abbrev helm (c:Side):= I*(tick c:ℂ)
noncomputable def river1 (a:Axis)(p:Flavor 6)(i j:Fiber)(F:Density c 6):ℂ:= (helm c)⁻¹ *(oracle1 1 a p i j F-oracle1 0 a p i j F)
noncomputable def river2 (a b:Axis)(p:Flavor 6)(i j:Fiber)(g:su.Color)(F:Density c 6):ℂ:= (helm c)⁻¹ *(oracle2 1 a b p i j g F-oracle2 0 a b p i j g F)
local notation "V"=> river1 a p i j
local notation "W"=> river2 a b p i j g
lemma vote1(Y F:Density c 6)(h:F=ᶠ[𝓝 1] Y) : V F= V Y:=by unfold river1 oracle1; rw [h.eq_of_nhds]
lemma vote2(h:F=ᶠ[𝓝 1] Y): W F=W Y:=by unfold river2 oracle2; rw [rub_eq F Y g h]
lemma phase_g : 0 < ‖helm c‖:= by unfold helm; rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real, Real.norm_of_nonneg (tick_g c).le]; exact tick_g _
lemma race1 : V (F+Y) = V F+V Y:=by unfold river1 oracle1; rw[Pi.add_apply,map_add,map_add]; ring
lemma steps1 : V (s • F)=s*V F:=by unfold river1 oracle1; rw[Pi.smul_apply,map_smul,map_smul,← smul_sub, smul_eq_mul]; ring
lemma zeroRiver1 : V (0:Density c 6) =0:=by unfold river1 oracle1; simp
lemma zeroRiver2 : W (0:Density c 6)=0:=by
     have h(z:VerseL c): rub g (0:Density c 6) z=0:=by simp only[rub,tent,Function.comp_def,Pi.zero_apply,fderiv_fun_const,ContinuousLinearMap.zero_apply,smul_zero,add_zero,LinearMap.coe_mk,AddHom.coe_mk]
     simp only[river2,oracle2,h,map_zero,sub_zero,mul_zero]
lemma frugG(s:ℂ)(h:Chart k F 1): Chart k (s • F) 1:= by
     let L: G★→L[ℝ]G★:= s • ContinuousLinearMap.id ℝ _; change Chart k (L ∘ F) 1; exact L.contDiff.contDiffAt.comp _ h
include h hk
lemma race2 (hf:Chart k Y 1): W (F+Y)=W F+W Y:=by unfold river2 oracle2; rw [rub_plus F Y g _ h hk hf,rub_plus F Y g _ h hk hf,map_add,map_add]; ring
lemma steps2 : W (s • F)=s* W F:=by unfold river2 oracle2; rw [rub_growth F g _ s h hk,rub_growth F g _ s h hk,map_smul,map_smul,← smul_sub, smul_eq_mul]; ring
lemma subW(hf:Chart k Y 1): W (F-Y)=W F-W Y:=by rw[sub_eq_add_neg, ← neg_one_smul ℂ Y,race2 F _ g h hk a b p i j (frugG _ _ hf),steps2 Y g _ hf hk]; ring
omit h
variable {D:Type*}
lemma vote2_sum (Z:D→Density c 6)(q:Finset D)(h:∀ i∈q,Chart k (Z i) 1): W (∑ j∈q,Z j)=∑ j∈q,W (Z j):=by
    classical
    induction q using Finset.induction_on with
    | empty=>rw [sum_empty,sum_empty,zeroRiver2]
    | insert t q hi ih=>
        have h':∀ i∈q,Chart k (Z i) 1:=fun i hi=> h i (mem_insert_of_mem hi)
        have hf:Chart k (∑ i∈q,Z i) 1:=by unfold Chart; simp_rw [Function.comp_def, Finset.sum_apply]; apply ContDiffAt.sum; exact h'
        rw[sum_insert hi, sum_insert hi,race2 (Z t) _ _ (h t (by simp)) hk _ _ _ i j hf, ih h'] -- binder shadow! auto fix
include h
lemma march1(x:Cover):V (march x F)=V F:=by unfold river1; rw[divine1,divine1]
lemma march2(x:Cover): W (march x F)= W F:=by unfold river2; rw[divine2 F x g _ _ _ _ _ _ h hk,divine2 F x g _ _ _ _ _ _ h hk]
-- stunt
variable (k':Axis)(P:Density c 6)(he:∀ᶠ VX in 𝓝 (1:Grid c), IsUnit (P VX))(hp:∀ x:Cover,march x P=P)
omit h
variable (hFr:Chart k (foil P F) 1)
set_option quotPrecheck false
local notation "K"=> step (S:=ℤ) k'
local notation "δQ"=> (1/2:ℝ)
local notation "Kq"=> (1/2:ℂ)
omit hk
lemma guise : foil P (stunt k' F)= (1/2:ℂ) • (foil P (march K F)-foil P (march (-K) F)):=by
    funext x; let Y:= Ring.inverse (P x); let u:=march K F x; let v:=march (-K) F x; change Y*(δQ • (u-v))=Kq • (Y*u-Y*v); rw [← mul_sub,show (1/2:ℂ)=↑(1/2:ℝ) from by norm_num,Complex.coe_smul, mul_smul_comm]
include he hp hFr hk
lemma nixes : V (foil P (stunt k' F))=0∧ W (foil P (stunt k' F))=0 ∧Chart k (foil P (stunt k' F)) 1:=by
    let X(x):= foil P (march x F); let Z:= foil P F
    have H(x:Cover):X x=ᶠ[𝓝 1] march x Z:=course x P F he (hp _)
    have hG(x):Chart k (X x) 1:=frugal _ _ (H x) (marchC x _ hFr)
    rw[guise]; have hb:Chart k (X K-X (-K)) 1:= (hG K).sub (hG _); refine ⟨?_,?_,frugG _ _ hb⟩
    · change V (Kq • (X _-X _))=0; rw [steps1, sub_eq_add_neg (X _),← neg_one_smul ℂ (X (-K)),race1,steps1, vote1 _ _ _ _ _ _ (H _),vote1 _ _ _ _ _ _ (H _),march1 Z hFr hk,march1 Z hFr hk]; ring
    change W (Kq • (X _-X _))=0; rw[steps2 _ g _ hb hk, subW (X K) (X _) g (hG _) hk _ _ _ _ _ (hG _),vote2 _ _ g a b _ i j (H _),vote2 _ _ g a b p i j (H _), march2 Z g hFr hk, march2 Z g hFr hk, sub_self,mul_zero]
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.nixes
#print axioms YM.Massive.Patria.Gall.vote2_sum
