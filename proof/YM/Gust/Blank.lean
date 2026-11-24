import YM.Gust.Valley
import YM.Gust.Minter
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxHeartbeats 780000
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter Analysis Tarn Tarn.Choir QCD QCD.Lat QCD.Grass Wilson UV Mater Kind
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Matrix Classical
variable {C:Sequence}{P:Calibration C}{K:Choir}{d m n:ℕ}{T:Pollens P K}(hK:K.Domestic)(hf: Foil P K T)
local notation "J"=>Fin (n+1)
local notation "Ix"=>Kind n
local notation "Sz"=>Stake T n
local notation "Yr"=> Mater T n
open Finset
lemma tags (w:(Factory T n).Ref d): w=∑ b: Books T d n,w (fc T d n b) • it b:=by
       ext1 i; obtain ⟨b,rfl⟩:= (fc T d n).surjective i; rw [Finset.sum_apply,sum_eq_single b]; · simp [it]
       · intro i _ he; have h:= (fc T d n).injective.ne he; simp [it,Pi.single_apply,h,Ne.symm h]
       simp
lemma tags_it (b:Books T d n): star (it b)= it b:=by ext i; simp [it, Pi.single_apply]; -- maybe
variable (u:(Factory T n).Ref d)
private lemma travels {F:Type*}[Fintype F]{z w:F→Stake T n}(hx:∀ i,Fees (z i) (w i)):Fees (∑ i,z i) (∑ i,w i):=by intro M; rw[map_sum,map_sum]; exact sum_congr rfl (fun i _=>hx i _)
set_option quotPrecheck false
local notation "Θ"=> launch hK hf n d
lemma spinning (s:Signed)(p: EuPin)(hp:p.Lifts s): Fees (launch hK hf n d ((Factory T n).mirrorGroup d s u)) (axisK hK hp T n (launch hK hf n d u)):=by
       change Fees (Θ (Ls T d n s u)) _; rw [tags u,map_sum,map_sum,map_sum,map_sum]; apply travels; intro i; rw[map_smul,map_smul,map_smul,map_smul,ls_it,laurel,laurel]; exact Fees.scale (Fees.swap (cruise hK hf _ _ _ hp)) _
lemma walnut(a:Axis):Fees (launch hK hf n d (star u)) (barK hK a T n (launch hK hf n d u)):=by
       rw [tags u,star_sum,map_sum,map_sum,map_sum]; apply travels; intro i; rw[star_smul,map_smul (launch hK hf n d),map_smul (launch hK hf n d),map_smulₛₗ,tags_it,laurel]; exact Fees.scale (Fees.swap (Fees.hop (pale hK _ _) (bornK hK hf _))) _
lemma lunar : launch hK hf n d u ∈ Binds T d n:=by rw[tags u,map_sum]; refine Submodule.sum_mem _ fun i _=>?_ ; rw[map_smul,laurel]; exact Submodule.smul_mem _ _ (scrolls hK hf _)
variable (x:ScriptP T d n)
lemma built : ∃ p,Fees (launch hK hf n d p) (plant (givenP x)):=by
       let a(i:Bool): Books T d n:= some (1,i,x); let V:= plant (givenP x); let W:= barK hK timeAxis T n V
       let Y(i:Bool):= if i then Complex.I • (V-W) else V+W; have h (i:Bool):Fees (Θ (it (a i))) (Y i):=by
            have hh:= modern hK (fromP 1) (q:=1) (u:=1) (v:=1) homeLift homeLift ?_ (Y i) -- equality coord yes
            · simp only [recoil] at hh; rw [laurel]; exact hh
            change _= _; rw[mul_one]; exact ((fromP 1).trans (map_one Signed.inclusionO)).symm
       refine ⟨(2:ℂ)⁻¹ • (it (a false) - Complex.I • it (a true)),?_⟩; intro M; simp only [map_smul,map_sub,h false M,h true M,Y]; simp [map_add,map_sub,mul_sub,←mul_assoc,Complex.I_mul_I]; rw[show morph M V=M _ (givenP x).v from once _ _]; ring -- ring.
lemma united (v:Stake T n)(hu:v∈Binds T d n): ∃ p,Fees (launch hK hf n d p) v:=by
       let O (v:Stake T n):= ∃ p,Fees (Θ p) v; change O v; unfold Binds at hu
       induction hu using Submodule.span_induction with
       | mem x hx=> obtain ⟨w,h,rfl⟩:=hx; obtain ⟨c,hc⟩:= gloss w h; choose F hF using fun i:textP T w.u d=>built hK hf (d:=d) (⟨w.u,i⟩:ScriptP T d n); refine ⟨∑ i,c i • F i, Fees.hop (w:=_) ?_ (Fees.swap hc)⟩; rw [map_sum]; exact travels (fun i=>by rw[map_smul]; exact Fees.scale (hF i) _)
       | zero=> exact ⟨0,by rw [map_zero]; exact Fees.older⟩
       | add x y _ _ hA hB=> obtain ⟨f,hf⟩:=hA; obtain ⟨g,hg⟩:=hB; exact ⟨f+g,by rw[map_add]; exact Fees.together hf _ _ hg⟩
       | smul x y _ h=> obtain ⟨p,hp⟩:=h; exact ⟨x • p,by rw[map_smul]; exact Fees.scale hp _⟩
noncomputable def polarM(n:ℕ) : YM.Spiral.Table (Factory T n) where
       value {m} d x:= (valuation T n m x).compLinearMap fun i=> launch hK hf n (d i)
noncomputable abbrev stint (p:(Factory T n).Token):Stake T n:= launch hK hf n p.1 p.2
lemma starts(x:Points m)(v:Fin m→ (Factory T n).Token): (polarM hK hf n).read x v= valuation T n m x (stint hK hf ∘ v):=rfl
lemma face_any (x:Points m)(u v:Fin m→Stake T n)(h:∀ i,Fees (u i) (v i)): valuation T n m x u= valuation T n m x v:=by
       let X:= valuation T n m x
       have he(a:Finset (Fin m))(u:Fin m→Stake T n)(h1:∀ i,Fees (u i) (v i))(h2:∀ i∉a,u i=v i): X u=X v :=by
             induction a using Finset.induction_on generalizing u with
             | empty=> rw [show u=v from funext fun i=> h2 _ (notMem_empty _)]
             | @insert i a hi ih=>
                 let W:=update u i (v i); have hw:=ih W (fun j=>by
                     unfold W; by_cases h:j=i; · subst j; rw [update_self]; exact Fees.older
                     rw [update_of_ne h]; exact h1 _) (fun j h=>by
                     unfold W; by_cases hh:j=i; · subst j; rw[update_self]
                     rw[update_of_ne hh,h2]; simp[h,hh])
                 refine Eq.trans ?_ hw; have hp:=quotes x i u (u i) (v i) (h1 i); rwa[update_eq_self] at hp
       exact he univ _ h fun i hi=> (hi (mem_univ i)).elim
lemma fire (x:Points m)(v:Fin m→ (Factory T n).Token)(u:Fin m→ Mater T n)(h:∀ i,Fees (stint hK hf (v i)) (plant (u i))): (polarM hK hf n).read x v=ValueP x u:= (face_any x _ _ h).trans (values x u)
end YM.Massive.Gust
#print axioms YM.Massive.Gust.united
#print axioms YM.Massive.Gust.fire
