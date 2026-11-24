import YM.Gust.Puce
import YM.Gust.Cav.ORoute
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter Analysis Tarn Tarn.Choir QCD QCD.Lat QCD.Grass Wilson UV
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Matrix Classical
variable {C:Sequence}{P:Calibration C}{K:Choir}{d m n:ℕ}{T:Pollens P K}(hK:K.Domestic)(hf:Foil P K T)
open Finset Mater
noncomputable abbrev chosenP(s:Signed):EuPin:= (EuPin.choice s).choose
lemma fromP(s:Signed): EuPin.Lifts (chosenP s) s:=(EuPin.choice s).choose_spec
abbrev Books(T:Pollens P K)(d n:ℕ):= Option (Signed × Bool × ScriptP T d n)
instance : Fintype (Books T d n):=inferInstanceAs (Fintype (Option _))
local notation "Θ"=> Books T d n
noncomputable abbrev actsP (s:Signed)(c:Θ):Θ:= match c with|some (p,q)=> some (s*p,q)|none=>none
noncomputable abbrev fc(T:Pollens P K)(d n:ℕ):Books T d n≃ Fin (Fintype.card (Books T d n)):=Fintype.equivFin _
local notation "i'"=> Fin (Fintype.card (Books T d n))
local notation "Q"=> fc T d n
noncomputable def Ls(T:Pollens P K)(d n:ℕ)(s:Signed) : (Fin (Fintype.card (Books T d n)) → ℂ)→ₗ[ℂ](Fin (Fintype.card (Books T d n)) → ℂ) where
     toFun c i:= c (fc T d n (actsP s⁻¹ ((fc T d n).symm i)))
     map_add' _ _:=rfl
     map_smul' _ _:=rfl
noncomputable abbrev it (c:Θ):i'→ℂ:=Pi.single (Q c) 1
lemma ls_it(s:Signed)(x:Θ): Ls T d n s (it x)= it (actsP s x):=by
     ext1 i; obtain ⟨p,rfl⟩:=(Q).surjective i
     change it x _=_; simp only[it,Equiv.symm_apply_apply, Pi.single_apply,Equiv.apply_eq_iff_eq]; by_cases h:x=actsP s⁻¹ p
     · rw[h,show actsP s (actsP s⁻¹ p)=p from by rcases p with _|⟨a,b,c⟩ <;> simp[actsP]]; simp
     have hh:p≠actsP s x:=by intro hp; apply h; rw [hp]; rcases x with _|⟨a,b,c⟩ <;> simp[actsP]
     simp[h,Ne.symm h,hh,Ne.symm hh]
noncomputable abbrev Factory(T:Pollens P K)(n:ℕ): YM.Spiral.Register su := {
     size:= fun d=>Fintype.card (Books T d n)
     scalar:=fun d=>it (none : Books T d n)
     mirrorGroup:=fun d=> Ls T d n
     mirror_scalar:=fun s d=>ls_it s none
     mirror_mul:=fun p q d v=>by
          funext i; change v _= v _; congr 1; simp only [fc, Equiv.symm_apply_apply]; refine congr_arg _ ?_; generalize (Fintype.equivFin (Books T d n)).symm i = j; cases j <;> simp [actsP,mul_assoc]
     mirror_one:=fun d v=>by
          funext i; change v _=_; rw[show actsP (1:Signed)⁻¹ ((fc T d n).symm i)=(fc T d n).symm i from ?_,Equiv.apply_symm_apply]; cases (fc T d n).symm i <;> simp [actsP]
     star_mirror:= fun _ _ _=>rfl
     bar_scalar:= fun d=>by ext i; simp[it,Pi.single_apply] }
noncomputable def art(c:Books T d n):Stake T n:= match c with
| none=>plant (relic hf n)
| some (p,b,x)=>
   let A:= plant (givenP x)
   let Y:= if b then Complex.I • (A-barK hK timeAxis T n A) else A+ barK hK timeAxis T n A
   axisK hK (fromP p) T n Y
local notation "F"=>Factory T n
noncomputable def launch (n d:ℕ): (Factory T n).Ref d →ₗ[ℂ] Stake T n:= ∑ i:Fin (Fintype.card (Books T d n)), (LinearMap.proj i).smulRight (art hK hf ((fc T d n).symm i))
local notation "B"=> Binds T d n
variable (b:Books T d n)
lemma laurel: launch hK hf n d (it b)= art hK hf b:=by
      unfold launch; rw [LinearMap.sum_apply, Finset.sum_eq_single (Q b)]; · change it b (Q b) • art hK hf ((Q).symm (Q b))=_; rw[Equiv.symm_apply_apply]; simp only [it,Pi.single_eq_same,one_smul]
      · intro j _ h; change it b j • art hK hf ((Q).symm j)=0; simp only[it,Pi.single_eq_of_ne h,zero_smul]
      simp
lemma uσ(s:Signed)(p:EuPin)(hp:p.Lifts s):act hK hp (relic hf n) = relic hf n:=by
     unfold act relic; congr 1; exact funext fun i=> coinσ hp hf
lemma uβ: eye hK timeAxis (relic hf n)= relic hf n:=by
     unfold eye relic; congr 1; funext i; change T.spin _ (T.adj _ (lampU P K))=_; rw [coinL hf timeAxis, coinσ (couture _) hf]
lemma cruise (p:EuPin)(s:Signed)(hp:p.Lifts s): Fees (axisK hK hp T n (art hK hf b)) (art hK hf (actsP s b)):=by
      rcases b with _|⟨q,b,x⟩; · simp[art,actsP,pin_pl,uσ hK hf _ p hp]; exact Fees.older
      exact modern hK hp (fromP _) (fromP _) ((fromP (s*q)).trans (EuPin.life_mul hp (fromP q)).symm) _
lemma bornK: Fees (barK hK timeAxis T n (art hK hf b)) (art hK hf b):=by
       rcases b with _|⟨q,b,x⟩; · simp[art,bar_pl,uβ hK]; exact Fees.older
       unfold art; simp only; refine Fees.hop (Fees.swap (bar_spin hK _ _ _)) (Fees.spin_meets hK (fromP q) ?_)
       let X:=plant (givenP x); cases b
       · change Fees (barK hK timeAxis _ _ (X+_)) (X+_); intro M; rw [map_add,map_add (morph _),map_add (morph M), twice hK timeAxis X M,add_comm]
       · intro M; simp only [↓reduceIte,map_smulₛₗ,map_smul,map_sub]; rw [twice hK timeAxis _ M]; simp [neg_smul,mul_sub]; ring
lemma scrolls : art hK hf b∈B:=by
       cases b with
       | none=> exact enter _ (stay_one hf)
       | some b=>
             rcases b with ⟨p,b,i⟩; let X:=plant (givenP i); let Y:= barK hK timeAxis T n X; let f:= axisK hK (fromP p) T n; have hZ:f X ∈B:=by unfold f X; rw[pin_pl]; exact enter _ (staying hK (fromP p) _ (started _))
             have hP:f Y ∈ B:=by unfold f Y X; rw[bar_pl,pin_pl]; exact enter _ (staying hK (fromP p) _ (pigment hK _ _ (started _)))
             cases b
             · change f (X+Y) ∈_; rw [map_add]; exact Submodule.add_mem _ hZ hP
             · change f (_ •(X-Y))∈_; rw [map_smul,map_sub]; exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hZ hP)
end YM.Massive.Gust
#print axioms YM.Massive.Gust.cruise
#print axioms YM.Massive.Gust.scrolls
#print axioms YM.Massive.Gust.bornK
