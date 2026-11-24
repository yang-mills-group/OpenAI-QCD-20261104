import YM.QCD.Finch.Mess
/-! # Dirac stencil and mass relevant alias at the kinetic station -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Finch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f L :Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove Entr YM.Next.Free Bloch Laurent QCD.Free
open Garden Para
variable {t s τ u :ℝ}{j k:ℕ}{B:BudgetPoint}
section eats
variable (P:Flight j k)(e:f.val=c.val*P.L.val)(x:Momentum)
noncomputable def song (P:Flight j k)(x:Momentum)(l:Site P.L):Bundle:= ((P.L.val:ℂ)*(Kit.slope P.L:ℂ)) • shout false P x l
local notation "A₀"=> wave g5
noncomputable def Quixote (P:Flight j k)(x:Momentum): Bundle:= (wave g5)*(∑ l:Site P.L,((song P x l)ᴴ*(wave g5))*song P x l)
set_option quotPrecheck false
local notation "Γ"=> Garden.barP P e
lemma rockP (t:Plan j): peel (Γ *proton P e)= lined fun i:Site c=> Quixote P (tuning i):=by
    let T:= inputM P e; let U:= proton P e; let W:=wave g5; have hx:star (leaf f)*U* leaf c=T:=by rw [Matrix.mul_assoc, ask P e, ← Matrix.mul_assoc,(leaf_u f).1,Matrix.one_mul]
    have he: leaf c *Tᴴ* star (leaf f)=Uᴴ:=by
       rw [← hx]; simp_rw [Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose (leaf _), ← Matrix.star_eq_conjTranspose (star _), star_star, ← Matrix.mul_assoc]; -- ordering
       simp_rw [Matrix.mul_assoc]; -- check
       rw [ (leaf_u f).2,Matrix.mul_one,← Matrix.mul_assoc,(leaf_u c).2,Matrix.one_mul]
    let R:=sliceL P e
    have hp: peel (Garden.barP P e * U)= (lined (fun _:Site c => W))*Tᴴ*(lined (fun _:Site f=>W))*T:=by
       rw [rotateP t,Matrix.mul_assoc, Matrix.mul_assoc,peel_mul]; unfold chirality; rw [peel_spin]; unfold peel; rw [show (proton P e)ᴴ=_ from he.symm]; rw [show onSpin f g5= _ from peel_out (onSpin f g5)]; rw [peel_spin]; -- handle assoc
       change lined _ * (star _*(leaf c*Tᴴ*star (leaf f)*(leaf f*lined _*star (leaf f)*U))*leaf c)= _
       simp only [Matrix.mul_assoc]; simp_rw [← Matrix.mul_assoc (star (leaf f)) (leaf f), (leaf_u f).1,Matrix.one_mul, ← Matrix.mul_assoc (star (leaf c)) (leaf c), (leaf_u c).1, Matrix.one_mul, ←Matrix.mul_assoc (star (leaf f)) U,hx]; rfl
    let S: Sheet c:= Tᴴ * (lined fun _:Site f=> W) * T; let w (i:Site c) :=∑ l:Site P.L,(song P (tuning i) l)ᴴ * W*song P (tuning i) l
    have hB (i:Site c)(l:Site P.L)(a: Lat.Fiber)(x:Site c)(b:Lat.Fiber): T (twins R i l,a) (x,b)=if x=i then song P (tuning i) l a b else 0:=stored P e i l x a b
    have hr (i: Site c)(l: Site P.L)(a b)(v:Site c): (Tᴴ*(lined fun _:Site f=>W)) (v,a) (twins R i l,b)= if v=i then ((song P (tuning i) l)ᴴ*W) a b else 0:=by
       rw [Matrix.mul_apply,Fintype.sum_prod_type,sum_eq_single (twins R i l)]; rotate_left
       · intro j _ hj; exact sum_eq_zero fun a _=>by rw [show lined (fun _:Site f=>W) (j,a) (twins R i l,b)=0 from (if_neg hj),mul_zero]
       · simp
       by_cases h:v=i
       · rw [if_pos h,Matrix.mul_apply]; exact sum_congr rfl fun j _=>congr_arg₂ _ (congr_arg star ((hB i l j v a).trans (if_pos h))) (if_pos rfl) -- star annotation
       rw [if_neg h]; apply sum_eq_zero; intro j _; rw [Matrix.conjTranspose_apply,hB _ _ _ _ _,if_neg h,star_zero,zero_mul]
    have hg:S=lined w :=by
       ext ⟨i,a⟩ ⟨j,b⟩; unfold S; rw [Matrix.mul_apply, Fintype.sum_prod_type,← Equiv.sum_comp (tunes R P.odd),Fintype.sum_prod_type,sum_eq_single i]; rotate_left
       · intro v _ h; exact sum_eq_zero fun l _=> sum_eq_zero fun u _ =>by change (Tᴴ * lined (fun _:Site f=> W)) _ (twins R v l,u)*_=0; rw [hr,if_neg h.symm,zero_mul]
       · simp
       by_cases h:j=i
       · subst j
         rw [show lined w (i,a) (i,b)= _ from (show _= w i a b from if_pos rfl),show w i a b= _ from Matrix.sum_apply ..]; apply sum_congr rfl; intro l _; rw [Matrix.mul_apply]; refine sum_congr rfl fun z _=> ?_
         exact congr_arg₂ _ ((hr i l a z i).trans (if_pos rfl)) ((hB i l z i b).trans (if_pos rfl))
       rw [show lined w (i,a) (j,b)=0 from if_neg (Ne.symm h)]; exact sum_eq_zero fun l _=> sum_eq_zero fun z _=> by change _*T (twins R i l,z) _=0; rw [hB _ _ _ _ _, if_neg h, mul_zero]
    refine hp.trans ?_; rw [Matrix.mul_assoc (lined _) Tᴴ, Matrix.mul_assoc (lined _) (Tᴴ*_)]; change lined _*S=_; rw [hg, lined_law]; rfl
lemma priceH (l:Site P.L): shout false P 0 l = if l=0 then 1 else 0:=by
   have hz: host false P 0=0:=by rw [host, Dir_nil, view_false]; exact map_zero Para.signal
   by_cases h:l=0
   · subst l; unfold shout; simp only [↓reduceIte,hz,mul_zero, sub_zero]; unfold book; rw [alias_zero_eq, narrow,smul_zero]; simp
   unfold shout; rw [if_neg h,hz,mul_zero,smul_zero, if_neg h]
lemma fir (P:Flight j k): Quixote P 0=(P.L.val:ℂ) • 1 :=by
   let d:Side:=P.L; unfold Quixote; rw [sum_eq_single (0:Site P.L)]; rotate_left
   · intro l _ hl; unfold song; rw [priceH,if_neg hl,smul_zero]; rw [Matrix.mul_zero]
   · simp
   unfold song; rw [priceH,if_pos rfl]; rw [← Matrix.star_eq_conjTranspose,star_smul,star_one]; -- annotation
   rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_smul, one_mul,mul_one,Matrix.mul_smul,wave_mul,g5_sq,wave_one, smul_smul]; have hx:(((Kit.slope d:ℝ):ℂ))^2=(d.val:ℂ)⁻¹:=by unfold Kit.slope; rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by positivity)]; simp
   have hQ:0<(P.L.val:ℝ):=side_pos _; rw [star_mul]; apply congr_arg (· • (1:Bundle)); push_cast; simp; unfold d at hx; grind
end eats
end YM.QCD.Finch
