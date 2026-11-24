import YM.Oriole.Finical
/-! Off-shell charged scalar or pseudoscalar.  count by projection.ALL. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b: Flavor 6)(g:Bool)
open Poised.Display Poised.Stative Module Finset Revolve
local notation "T" => SpinMode d
local notation "Ae" => Pairs T
local notation "G"=> pulp g
variable (p q:Multi d)(D:CensusA d)(M:Spike)(s:Signed)
lemma waveP (c:ℂ): wave (c • M)=c • wave M:=by unfold wave; rw [Matrix.smul_kronecker]
lemma nourish (c:ℂ) : bilinear a b (c • M) p q=c • bilinear a b M p q:=by rw[←j_stard,←j_stard,waveP,C_light,map_smul]
noncomputable abbrev claw (g:Bool)(i:Axis): Spike:= gamma i*pulp g
lemma claw_unit(i:Axis) : claw g i∈unitary Spike:= Submonoid.mul_mem _ (show gamma i ∈ _ from ⟨by simp,by simp⟩) (P_high _)
lemma claw_pin (w:EuPin)(i:Axis)(hp:w.Lifts s)(z:ℂ)(h:conjug w G=z • G): conjug w (claw g i) = ((signT s i:ℂ)*z) • (claw g (s.perm i)):=by rw [claw,L_up,h,E_sigma s w hp,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
-- L/R extraction as preferred polarization choose.Lane
noncomputable def one_jet (t:Bool)(i:Axis): Multi 8:= if t then first i else 0
local notation "f"=> one_jet
lemma jet_value(i:Axis)(t:Bool): spinWeight (f t i)+ spinWeight (f (!t) i)=8:=by cases t <;> simp [one_jet,juicy,cost_root]
noncomputable abbrev debt (a b:Flavor 6)(g t:Bool)(i:Axis): Label 8:= satin a b (one_jet t i) (one_jet (!t) i) (claw g i) ((jet_value i t).le)
noncomputable abbrev arbor(a b:Flavor 6)(g t:Bool) : Label 8:= ∑ i:Axis,debt a b g t i
noncomputable abbrev flame (a b:Flavor 6)(g:Bool) (d:ℕ) (hv:6≤d):= mesonCode d a b (pulp g) hv
local notation "F"=> flame a b g 8 (by decide)
local notation "A"=>arbor a b g
lemma arbola (t:Bool): (A t).val= ∑ i:Axis,bilinear a b (claw g i) (f t i) (f (!t) i):=by unfold arbor; rw [AddSubmonoidClass.coe_finset_sum]; rfl
variable (X:Label 8)(h:a≠b)(hx:CharmC a b X.val)(hY: Wings g X.val)
include h hx hY
local notation "V"=> juncoat X.val
local notation "P" => assay a b
lemma gainS (w:EuPin)(t:Bool)(i:Axis)(s:Signed)(hp:w.Lifts s)(z:ℂ)(hz:conjug w G=z • G): conjug w (P (f t i) (f (!t) i) V) = ((signT s i:ℂ)*z) • P (f t (s.perm i)) (f (!t) (s.perm i)) V :=by
    have he:= taste a b g (f t i) (f (!t) i) X h hx hY le_rfl w s hp z hz
    let M:=P (f t i) (f (!t) i) V; let M':=P (f t (s.perm i)) (f (!t) (s.perm i)) V
    let c:ℂ:=signT s i; have h':z • M'= c • conjug w M:=by cases t <;> simpa [hem_first,vital,hem_ground,c,M,M',one_jet] using he
    rw[mul_smul,h',smul_smul]; rw [show c*c=1 from by unfold c; rw [←Complex.ofReal_mul,sign_sq,Complex.ofReal_one],one_smul] -- c let syntax
lemma berry(t:Bool):∃ c:ℂ,∀ i:Axis, P (f t i) (f (!t) i) V=c • claw g i:=by
    let M(i:Axis):= P (f t i) (f (!t) i) V; let Z(i:Axis):Spike:= claw g i
    have he:∃ c:ℂ,M 0=c • Z 0:= shine (Z 0) (M 0) (claw_unit _ _) fun i w hw=> by
         let s:= Signed.mirror i; obtain ⟨c,hp⟩:= chirP g s w hw; exact ⟨_,claw_pin g s w 0 hw c hp,gainS a b g X h hx hY w t 0 s hw c hp⟩
    obtain ⟨c,hc⟩:=he; refine ⟨c,?_⟩; intro i; change M i=c • Z i; let s:= Swing.pure (Equiv.swap 0 i); obtain ⟨w,hp⟩:= EuPin.choice s; obtain ⟨v,hv⟩:= chirP g s w hp
    let u:= (signT s 0:ℂ)*v; have hσ:s.perm 0=i:= Equiv.swap_apply_left ..; have hu:conjug w (Z 0)=u • Z i:= hσ ▸ claw_pin g s w 0 hp v hv; have hU:conjug w (M 0)=u • M i:= hσ ▸ gainS a b g X h hx hY w t 0 s hp v hv; refine smul_right_injective Spike (show u ≠ 0 from ?_) ?_; swap; change u • M i=u • (c • Z i); rw [←hU,hc]; rw [smul_comm u c,← hu]; unfold conjug; rw [Matrix.mul_smul,Matrix.smul_mul]
    have hE:(signT s 0:ℂ)=1:=by rw [show signT s 0=1 from rfl]; simp -- inspect defeq default
    rw [show u=v from by unfold u; rw[hE,one_mul]]; have hv:= p_mag g w v hv |>.2; intro h; rw [h,zero_mul] at hv; exact zero_ne_one hv
-- assemble from snug in cells. cost irrelevant.
omit hx hY h
variable (u v:Multi 8)(B:CensusA 8)
lemma thrustT (t:Bool)(X:Axis→Spike)(k:Axis) (M:CensusA 8) (p':Axis→CensusA 8)(he:∀ k:Axis,p' k=fieldB a b (f t k) (f (!t) k) (wave (X k))) (j:Axis)(p q:Fiber): let D:=∑ i:Axis,p' i; D (((f t j),p),a) (((f (!t) j),q),b)=wave (X j) p q:=by
    intro D; rw [show D=∑ i,p' i from rfl,Matrix.sum_apply,sum_eq_single j]; rw [he,fieldK]; simp
    · intro i _ h; rw [he,fieldK]; cases t <;> simp [one_jet,first_eq,h.symm]
    simp
local notation "TB" x:arg y:arg z:arg=> (∑ i:Axis,fieldB a b (f x i) (f y i) (wave (z i)))
-- reconstruction matrix ext
lemma flaming (hA:snug a b B)(hp:jcoat B∈labels 8) :
         let K(t:Bool)(i:Axis):= P (f t i) (f (!t) i) B; B=fieldB a b 0 0 (wave (P 0 0 B))+TB true false (K true)+ TB false true (K false) :=by
    intro K; let U (t:Bool):= TB t (!t) (K t); let W:CensusA 8:= fieldB a b 0 0 (wave (P 0 0 B)); change B=W+U true+U false
    ext ⟨⟨p,i⟩,c⟩ ⟨⟨q,j⟩,e⟩; rw [Matrix.add_apply,Matrix.add_apply]; let x:SpinMode 8:= ((p,i),c); let y: SpinMode 8:= ((q,j),e); change B x y=W x y+ U true x y+ U false x y
    by_cases h :c=a ∧ e=b∧spinWeight p+spinWeight q ≤8
    · obtain ⟨hc,he,h⟩:=h; subst c e
      have hp: B x y=wave (P p q B) i j:=congr_fun (congr_fun (king a b p q B hp) i) j; have hb:= low q; have hw:=low p
      by_cases hP:p=0; by_cases hQ:q=0 -- nesting syntax
      · subst p q; rw [hp]; have hx (t:Bool): U t x y=0:=by unfold U; rw [Matrix.sum_apply]; refine sum_eq_zero fun k _=>?_ ; rw [fieldK]; cases t <;> simp [one_jet,x,y,(highV k).symm]
        rw [hx,hx,add_zero,add_zero]; exact (congr_fun (congr_fun (coreB a b (0:Multi 8) 0 _) i) j).symm
      · obtain ⟨k,rfl⟩:= halo q (by omega) hQ -- rfl may substitute q
        subst p; unfold W U; simp only [hp,x,y, Matrix.sum_apply, one_jet,↓reduceIte]; -- simplify
        simp [fieldK,one_jet,hQ,first_eq,Matrix.sum_apply,K]
      obtain ⟨k,hpK⟩:= halo p (by omega) hP; subst p; rw [juicy] at h; have hq:q=0:=ground q (by omega); subst q; unfold W U; simp [hp,fieldK, one_jet,x,y,hP,first_eq,Matrix.sum_apply,K]
    have hv: B x y=0:=by by_contra hQ; exact h (hA _ _ hQ)
    have hU(t:Bool):U t x y=0:=by
      unfold U; rw [Matrix.sum_apply]; refine sum_eq_zero fun i _=>?_ ; rw [fieldK]; split; next hK=> obtain ⟨hz,he,hv,hf⟩:=hK; exfalso; change p=f t i at hz; change q=f (!t) i at hv; exact h ⟨he,hf,hz.symm ▸ hv.symm ▸ (jet_value i t).le⟩; -- transport
      next _=>rfl
    have ht: W x y=0:=by rw [show W x y=_ from fieldK a b _ _ _ x y,if_neg]; intro ⟨ha,hx,hb,hy⟩; change p=0 at ha; change q=0 at hb; exact h ⟨hx,hy,ha.symm ▸ hb.symm ▸ (by rw[cost_root]; norm_num)⟩
    rw [hv,hU,hU,ht,add_zero,add_zero]
include hx hY h
lemma rose :∃ c p q:ℂ,X=c • F+p • A true+q • A false:=by
    obtain ⟨hP,hQ⟩:= feathers a b X le_rfl h hx; obtain ⟨c,hc⟩:= beam0 a b g X h hx hY le_rfl; obtain ⟨p,hp⟩:= berry a b g X h hx hY true; obtain ⟨q,hq⟩:= berry a b g X h hx hY false; refine ⟨c,p,q,Subtype.ext ?_⟩; have hv:= flaming a b V hQ (by rw [hP]; exact X.property); let M:= V; change X.val=c • bilinear a b G 0 0 + p • (A true).val+ q • (A false).val
    nth_rw 1[← hP]; nth_rw 1[hv]; rw [map_add,map_add,map_sum,map_sum,j_stard,hc, nourish]; rw [arbola a b g true,arbola a b g false,smul_sum,smul_sum]; apply congr_arg₂ (·+·)
    · congr 1; apply sum_congr rfl; intro i _; rw [j_stard]; simp only at hp ⊢; rw [hp,nourish]; rfl -- `f` booleans reduce
    refine sum_congr rfl fun i _=>?_ ; rw [j_stard]; simp only at hq ⊢; rw [hq,nourish]; rfl
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.rose
