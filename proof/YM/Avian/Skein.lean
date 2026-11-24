import YM.Avian.Uva
import YM.Avian.Nine
/-! Exact combined projection detection matrix API. convenient for future.DA root convergence. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall.Seals
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Tawny Tawny.Cast Tawny.Cast.TableT Tawny.Cast.Rays Perla Fore Perla.BrickM Zinc Carnal
open Pane BendR UV.Free KeysP Clifford
open StressFlux (pairDeriv curl0 curl1 leg0 leg1)
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
local notation "Q★"=> (0:Multi 8)
local notation "Y"=>UV.first
local notation "Z"=>(0:Multi 10)
local notation "B"=> leadR
local notation "X"=> ηR
local notation "I₁"=> (0:Axis)
local notation "J₁"=> (1:Axis)
local notation "S"=> RawVec 10
noncomputable def inquiry (v:Fin 3): S →ₗ[ℂ]ℂ:= capote 10 (mirage v) ∘ₗ LinearMap.proj 0 ∘ₗ (S).subtype
noncomputable def answer (e:ℂ) (v:Fin 3):RawTensor e 8→ₗ[ℂ]ℂ:= ∑ k:Axis,(pan (veil Gpick v) (torchK Gpick v) k) ∘ₗ LinearMap.proj (k,(0:Axis)) ∘ₗ (RawTensor e 8).subtype
noncomputable def seekC(a:Flavor 6)(p q:Fiber): S →ₗ[ℂ]ℂ:= awake2 0 1 a p q Gpick ∘ₗ LinearMap.proj 0 ∘ₗ (RawVec 10).subtype
noncomputable def seekB(a:Flavor 6)(p q:Fiber): S→ₗ[ℂ]ℂ:= point1 1 a p q ∘ₗ LinearMap.proj 0 ∘ₗ (RawVec 10).subtype
variable (a b:Flavor 6)(p q:Fiber)
noncomputable def gaugeQ : S →ₗ[ℂ] (Fin 3→ℂ):= LinearMap.pi inquiry
noncomputable def gaugeA (e:ℂ):RawTensor e 8→ₗ[ℂ](Fin 3→ℂ):=LinearMap.pi (answer e)
lemma gaugeV (e:ℂ)(x:RawTensor e 8)(t:Fin 3):gaugeA e x t=∑ k:Axis, pan (veil Gpick t) (torchK Gpick t) k (x.val (k,0)):=by unfold gaugeA answer; rw [LinearMap.pi_apply,LinearMap.sum_apply]; rfl
noncomputable abbrev Memory:= Flavor 6 → Fiber × Fiber→ℂ
noncomputable def lookQ : S →ₗ[ℂ]Memory:=LinearMap.pi fun p=> LinearMap.pi (fun u:Fiber × Fiber=> seekC p u.1 u.2)
noncomputable def lookB : S →ₗ[ℂ]Memory:= LinearMap.pi fun p=> LinearMap.pi fun u:Fiber × Fiber=> seekB p u.1 u.2
noncomputable def viewsL : S →ₗ[ℂ](FacesT×(Fin 3→ℂ)):= obV.prod gaugeQ
noncomputable def viewsX (s:ℂ): RawTensor s 8→ₗ[ℂ](FacesT×(Fin 3→ℂ)):= (obS s).prod (gaugeA s)
noncomputable def yearL : S →ₗ[ℂ]((FacesT×(Fin 3→ℂ))× Memory):= viewsL.prod lookQ
variable (x:Values 7)(c:Fin 3→ℂ)
lemma punched (h:obV (plaza (x,c)) a=0) : ∀ i: Fin 7, i.val < 6 → x a i=0:=by
    let p:= plaza (x,c); have hh(i:Fin 6): obV p a i=0:=congr_fun h i
    obtain ⟨h0,h1,h2,h3,h4,h5⟩:= life_v a x c
    have he:x a 1=0:=by
         apply probe_zero I₁; let F:= x a 1 • (gamma I₁); have he:F* gamma J₁=0:=by unfold F; rw[Matrix.smul_mul]; exact h1.symm.trans (hh _)
         change F=0; calc F = (F * gamma J₁)*gamma J₁:=by rw [Matrix.mul_assoc,Lat.gamma_sq,mul_one]
                          _=0:=by rw[he,zero_mul]
    intro i hi; have hG := probe_zero I₁ _ (h3.symm.trans (hh _)); have hT:=probe_zero J₁ _ (h4.symm.trans (hh _)); fin_cases i
    · apply probe_one; have hp:=h0.symm.trans (hh _); rw[he,zero_smul,add_zero] at hp; exact hp
    · exact he
    · apply probe_zero I₁; have hp:=h2.symm.trans (hh _); rw[hG,hT,zero_smul,add_zero,add_zero] at hp; exact hp
    · exact hG
    · exact hT
    · exact probe_zero J₁ _ (h5.symm.trans (hh _))
    exact False.elim (Nat.lt_irrefl _ hi)
lemma selected : seekC a p q (starV b)=if a=b then whirl Gpick (gamma J₁) p q else 0:=by
     change awake2 _ _ _ _ _ _ ((starV _).val _)=_; rw [star_val,map_sum]; simp_rw [starsU]; split; swap; · simp [*]
     next h=>
         subst b; try simp only[if_true,↓reduceIte]
         rw[sum_eq_single J₁]; rw [show curl0 0 J₁ (legV Gpick 0 1)= Gpick from (by unfold legV; rw[StressFlux.curl0_leg]; norm_num[basis_eq,Fin.ext_iff])]
         · intro j _ hj; have hx: curl0 (0:Axis) j (legV Gpick 0 1)=0:=by unfold legV; rw [StressFlux.curl0_leg]; simp [basis_eq,Ne.symm hj,hj]
           rw[hx,show whirl 0 (gamma j)=0 from (by
                          have he:= whirl_h (gamma j) Gpick 0; rw[zero_smul, Complex.ofReal_zero,zero_smul] at he; exact he)]; rfl
         simp
lemma unearth (t:Fin 3): gaugeQ (plaza (x,c)) t= pages (mirage t) ((ocean c).val I₁):=p_value 0 (mirage t) x c
lemma gaugeShot (h: gaugeQ (plaza (x,c))=0) : c=0:= cord c fun t=> (unearth x c t).symm.trans (congr_fun h t)
lemma detected (B': Bundle): (∀ i j:Fiber,B' i j=0) → B'=0:= fun h=> Matrix.ext h
open scoped Kronecker
lemma charged_r : whirl Gpick (gamma J₁) ≠ 0:=by
     intro h; have he:= gilt2 (gamma J₁); change gold2 (whirl _ _)=gamma J₁ at he; rw [h,map_zero] at he; have ht:= Lat.gamma_sq J₁; rw[←he,zero_mul] at ht; exact zero_ne_one ht
lemma notices (h:viewsL (plaza (x,c))=0)(hp:lookQ (plaza (x,c))=0): x=0∧ c=0:=by
     have hv:= gaugeShot x c (congr_arg Prod.snd h); have ht:=fun a: Flavor 6=> punched a x c (congr_fun (congr_arg Prod.fst h) a); refine ⟨?_,hv⟩; funext a i; by_cases hI:i.val <6; · exact ht a i hI
     have hT: (plaza (x,c))=∑ i:Flavor 6,x i 6 • starV i:=by
          have he(i:Flavor 6): vectorZ i (x i) = x i 6 • starV i:=by simp only[vectorZ, ht i 0 (by decide), ht i 1 (by decide),ht i 2 (by decide),ht i 3 (by decide),ht i 4 (by decide),ht i 5 (by decide),zero_smul,zero_add]
          rw[hv]; change vectorY x+ ocean 0=_; unfold vectorY; simp [he,ocean]
     have hg(i j:Fiber): seekC a i j (plaza (x,c))=0:= congr_fun (congr_fun hp a) (i,j)
     have hh (i j:Fiber): seekC a i j (∑ i:Flavor 6, x i 6 • starV i)= x a 6 • whirl Gpick (gamma J₁) i j:=by
         rw [map_sum,sum_eq_single a]; rw [map_smul, selected,if_pos rfl]; -- rfl
         · intro b _ hb; rw [map_smul,selected,if_neg hb.symm, smul_zero]
         simp
     have hs: x a 6 • whirl Gpick (gamma J₁)=0:= detected _ fun i j=> (hh i j).symm.trans (hT ▸ hg i j)
     rw[show i=6 from (Fin.ext (by omega))]; exact (smul_eq_zero.mp hs).resolve_right charged_r
lemma scansion : Function.Injective yearL:=by

    apply LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_); intro x h; obtain ⟨⟨v,t⟩,ht⟩:=certified.2 x; rw[←ht] at h; obtain ⟨rfl,rfl⟩:= notices v t (congr_arg Prod.fst h) (congr_arg Prod.snd h); rw[←ht]; exact map_zero TableT.plaza
end YM.Massive.Patria.Gall.Seals
#print axioms YM.Massive.Patria.Gall.Seals.scansion
