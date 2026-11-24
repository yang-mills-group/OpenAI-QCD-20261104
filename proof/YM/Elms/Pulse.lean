import YM.Elms.Loom
import YM.Elms.Tint
/-! # Spin-difference leading limit on free derivative profiles. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Topology BigOperators TensorProduct Pointwise Classical ContDiff
variable {d:ℕ}
open Papyrus.Purl Papyrus LoomC
namespace Pulses
lemma nearUnique {p q w: UV.Multi d}{a:Axis}(hp:AtNext a p w)(hq:AtNext a q w): p=q:=by
   apply Subtype.ext; funext j; apply Fin.ext; change power p j=power q j; have he:=congr_fun (Eq.trans hp.symm hq) j; by_cases h:j=a <;> simpa [h] using he
lemma nextFound(p:UV.Multi d)(a:Axis): (∃ y,AtNext a y p)↔0<power p a:=by
    constructor
    · rintro ⟨y,hy⟩; rw [show power p a=power y a+1 from by rw [hy,update_self]]; omega
    intro h; let x:=power p a-1; let L:= p.val; have hx:x<d+1:=Nat.lt_of_le_of_lt (Nat.sub_le _ _) (p.val a).isLt; let y:=update p.val a (⟨x,hx⟩:Fin (d+1)); have he(q): (y q).val ≤ (p.val q).val:=by
       by_cases hh:q=a
       · rw [hh]; unfold y; rw [update_self]; exact Nat.sub_le _ _
       rw [show y q=p.val q from update_of_ne hh ..]
    let z:UV.Multi d:=⟨y,(sum_le_sum (fun i _=>he i)).trans p.property⟩; refine ⟨z,?_⟩; unfold AtNext; funext j; by_cases hj:j=a; · rw [hj,update_self]; have hv:power z a=x:=congr_arg Fin.val (show y a= ⟨x,hx⟩ from update_self ..); rw [hv]; exact (Nat.sub_add_cancel h).symm
    rw [Function.update_of_ne hj]; exact congr_arg Fin.val (show p.val j=y j from (Function.update_of_ne hj ..).symm)
private noncomputable def puzzle (x:E4)(a:Axis)(r t:ℝ):= x + (r*t) • basis a
private lemma tick (x:E4)(p:UV.Multi d)(a:Axis)(r:ℝ):
     HasDerivAt (fun t:ℝ=> sings p (puzzle x a r t)) ((r:ℂ) * ∑ y:UV.Multi d, if AtNext a y p then sings y x else 0) 0:=by
     let g(y:UV.Multi d)(i:Axis):ℂ:=(x i:ℂ)^power y i/Nat.factorial (power y i)
     let V(y:UV.Multi d):ℂ:=∏ i ∈ univ.erase a,g y i
     let f(t:ℝ):= x a + r*t; let w:= power p a; have h(t): sings p (puzzle x a r t)=(f t:ℂ)^w/(Nat.factorial w:ℂ) * V p:=by
         unfold sings; let L(i:Axis):ℂ:=(puzzle x a r t i:ℂ)^power p i/Nat.factorial (power p i); change (∏ i:Axis,L i)=_; rw [← mul_prod_erase univ L (mem_univ a)]; congr 1
         · have hx: puzzle x a r t a=f t:=by simp [puzzle,f,YM.basis]
           unfold L; rw [hx]
         apply prod_congr rfl; intro i hi; have hk: puzzle x a r t i=x i:=by simp [puzzle, YM.basis,(mem_erase.mp hi).1]
         unfold L; rw [hk]
     have hf: HasDerivAt f r 0:=by simpa only [mul_one] using (((hasDerivAt_id' (0:ℝ)).const_mul r).const_add _)
     have hf':f 0=x a:=by unfold f; ring
     by_cases hk:∃ y,AtNext a y p
     · obtain ⟨y,hy⟩:=hk; rw [funext h]; rw [sum_eq_single y]
       swap; · intro i _ hi; exact if_neg fun h' => hi (nearUnique h' hy)
       swap; · simp
       rw [if_pos hy]; -- REAL derivative ℂ function; HasDerivAt (ℝ→ℂ) lacks mul? yes
       have hw:w = power y a+1:=by unfold w; rw [show power p a=power y a+1 from by rw [hy,update_self]]
       have hm: V p=V y:=Finset.prod_congr rfl fun i hi=>by unfold g; rw [congr_fun hy i,Function.update_of_ne (mem_erase.mp hi).1]
       let s:= power y a; have hx: HasDerivAt (fun t:ℝ=> (↑(f t):ℂ)) (r:ℂ) 0:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt _ hf; refine ?_
       -- .pow maybe only scalar outputs. derive via calc or lemmas
       have hh:= hx.pow w; -- inspect
       exact (hh.div_const _ |>.mul_const _).congr_deriv (by rw [hf',hw,hm]; unfold sings; rw [← mul_prod_erase _ _ (mem_univ a)]; rw [Nat.add_sub_cancel,Nat.factorial_succ]; change (↑(power y a+1):ℂ)*(_:_)*_/_*(V y)= ↑r*((_ / ↑((power y a).factorial))* V y); push_cast; field_simp)
     rw [funext h]; rw [sum_eq_zero (fun y _=> if_neg (fun hy=> hk ⟨y,hy⟩)),mul_zero]; have hw:w=0:=Nat.eq_zero_of_not_pos (fun H=>hk ((nextFound p a).2 H)); simp_rw [hw,pow_zero]; exact hasDerivAt_const ..
variable (q:Bool)(ψ: Pinor)(k:Hue)(u:Flavor 6)
local notation "S" =>Covec d
local notation "U" p:arg i:arg x:arg => twig (d:=d) p (i,k) u (vector x)
noncomputable def flipD (q:Bool)(m:Spike):Spike:= if q then m.transpose else m
noncomputable def signD (q:Bool):ℝ:= if q then -1 else 1
lemma signdC (a:Axis)(i j:Pinor): flipD q (hi a) i j- flipD q (Lat.lo a) i j= flipD q (Lat.gamma a) i j:=by
    have hv: hi a-Lat.lo a= Lat.gamma a:=by
       rw [Lat.hi,Lat.lo,← smul_sub]; have h: 1+Lat.gamma a-(1-Lat.gamma a)= (2:ℂ) • Lat.gamma a:=by rw [two_smul]; abel
       rw [h,inv_smul_smul₀ (by norm_num)]
    cases q with
    | false=> exact congr_fun (congr_fun hv i) j -- def.N
    | true=> exact congr_fun (congr_fun hv j) i
lemma signdB (a:Axis)(i j:Pinor): flipD q (hi a) i j+flipD q (Lat.lo a) i j= (1:Spike) i j:=by
    rw [add_comm]; have h:= Lat.projectors a; cases q; exact congr_fun (congr_fun h i) j; exact (show _ from congr_fun (congr_fun h j) i).trans (show (1:Spike) j i=(1:Spike) i j from congr_fun (congr_fun (Matrix.transpose_one (n:=Pinor) (α:=ℂ)) i) j)
-- lattice stencil normalization rag(any scale), orientation includes signed shift by +/-
def bySign (p:Bool)(a:Axis): Cover:= if p then -step a else step a
lemma hereB (a:Axis)(x:Cover) : vector (x+bySign q a)= vector x + signD q • basis a:=by ext1 j; cases q <;> by_cases hv:j=a <;> simp [vector,bySign,signD,basis,hv]
lemma hereM (a:Axis)(x:Cover): vector (x-bySign q a)=vector x+ (-signD q) • basis a :=by ext1 j; cases q <;> by_cases hv:j=a <;> simp [vector,bySign,signD,basis,hv,sub_eq_add_neg]
noncomputable def bent (b:Cover):Covec d:= ∑ a:Axis,∑ i:Pinor,(flipD q (Lat.lo a) ψ i • (U q i b - U q i (b+bySign q a))+flipD q (hi a) ψ i • (U q i b - U q i (b-bySign q a)))
noncomputable def plan (x:E4)(t:ℝ):S:= ∑ a:Axis,∑ i:Pinor,(flipD q (Lat.lo a) ψ i • (twig q (i,k) u x - twig q (i,k) u (puzzle x a (signD q) t)) + flipD q (hi a) ψ i • (twig q (i,k) u x -twig q (i,k) u (puzzle x a (-signD q) t)))
def leafD (p:UV.Multi d): Letters d:= if q then Sum.inr ((p,ψ,k),u) else Sum.inl ((p,ψ,k),u)
lemma petite (y:UV.Multi d): petal (leafD q ψ k u y)=∑ a:Axis,∑ i:Pinor, ∑ p:UV.Multi d, if AtNext a y p then flipD q (gamma a) ψ i • trow q p (i,k) u else 0:=by cases q <;> rfl
lemma pace_slot (p:UV.Multi d)(t:ℝ) : pace d t (flora (bphy q p (ψ,k) u))=(t:ℂ)^spinWeight p • flora (bphy q p (ψ,k) u):=by
    let v:=leafD q ψ k u p; let y:PowerPair d:= (0,{v}); have he:bphy q p (ψ,k) u=mono {v}:=by rw [mono_single]; cases q <;> rfl
    rw [he]; change pace _ _ (gen y)= _ • gen y; rw [pace_gen]; have hx: UV.weight y=spinWeight p:=by unfold UV.weight y Labels.height; simp only [map_zero,Nat.mul_zero,Finset.sum_singleton,zero_add]; cases q <;> rfl
    rw [hx]
lemma twig_pace (t:ℝ)(x:E4) : pace d t (flora (Grass.line (twig (d:=d) q (ψ,k) u x)))=(t:ℂ)^3 • flora (Grass.line (twig (d:=d) q (ψ,k) u ((t^2) • x))):=by
    obtain ⟨L,hL⟩:=floraL (d:=d); unfold twig; rw [← hL]; simp_rw [map_sum,map_smul, Finset.smul_sum]; rw [hL]; refine Finset.sum_congr rfl (fun i _=>?_); rw [show pace _ t (flora (Grass.line (trow _ _ _ _)))=_ from pace_slot q ψ k u i t,sing_coe,smul_smul,smul_smul]; congr 1; rw [spinWeight,Complex.ofReal_pow,pow_add,pow_mul]; ring
lemma plan_t (t:ℝ)(b:Cover): pace d t (flora (Grass.line (bent (d:=d) q ψ k u b)))=(t:ℂ)^3 • flora (Grass.line (plan (d:=d) q ψ k u ((t^2) • vector b) (t^2))):=by
   obtain ⟨L,hL⟩:=floraL (d:=d); unfold bent plan; rw [← hL]; simp only [map_add,map_sub,map_smul,map_sum] -- check
   rw [hL]; simp_rw [twig_pace]; rw [Finset.smul_sum]; apply sum_congr rfl; intro a _; rw [Finset.smul_sum]; refine sum_congr rfl (fun i _=>?_); rw [smul_add]; rw [hereB,hereM]; simp only [smul_add,smul_smul,puzzle]; rw [mul_comm (signD q) (t^2),mul_comm (-signD q) (t^2)]; apply congr_arg₂ (·+·); exact brims _ _ _ _; exact brims _ _ _ _
 where
   brims (c f:ℂ)(x y:UV.Pol d): c • (f • x - f • y)=(f*c) • (x-y):=by rw [← smul_sub f x y,smul_smul,mul_comm]
lemma plan_zero (x:E4): plan (d:=d) q ψ k u x 0=0:=by simp [plan,puzzle]
noncomputable def normalD (x:E4) : Covec d:= ∑ p:UV.Multi d,((↑(signD q):ℂ)* sings p x) • petal (leafD q ψ k u p) -- precedence `*` maybe parse wrong
private def tapL (x:E4)(a:Axis)(i:Pinor):S:= ∑ y:UV.Multi d,sings y x • (∑ p:UV.Multi d,if AtNext a y p then trow q p (i,k) u else 0)
private lemma tickP (i:Pinor)(x:E4)(a:Axis)(r:ℝ): HasDerivAt (fun t:ℝ=> twig (d:=d) q (i,k) u (puzzle x a r t)) ((r:ℂ) • tapL (d:=d) q k u x a i) 0:=by
     refine HasDerivAt.congr_deriv (HasDerivAt.fun_sum (u:=Finset.univ) (fun (p:UV.Multi d) _=>(tick x p a r).smul_const (trow q p (i,k) u))) ?_ -- binder names
     unfold tapL; simp_rw [mul_smul,sum_smul, smul_sum]; rw [sum_comm]; refine sum_congr rfl (fun i _=> sum_congr rfl (fun j _=>?_)); split <;> simp
lemma differs (x:E4):HasDerivAt (plan (d:=d) q ψ k u x) (normalD q ψ k u x) 0:=by
     let sa (i z:Pinor)(a:Axis):ℂ:= flipD q (Lat.lo a) i z
     let f(i z:Pinor)(a:Axis):ℂ:=flipD q (hi a) i z
     let g(a:Axis)(i:Pinor):S:=twig q (i,k) u x
     let δ:= signD q
     let F(i:Pinor)(a:Axis)(r:ℝ):ℝ→S:= fun t=>twig q (i,k) u (puzzle x a r t)
     let W(i:Pinor)(a:Axis):S:=tapL q k u x a i
     have h(a:Axis)(i:Pinor): HasDerivAt (fun t:ℝ=>sa ψ i a • (g a i - F i a δ t)+f ψ i a • (g a i - F i a (-δ) t)) ((((δ:ℂ)*flipD q (gamma a) ψ i):ℂ) • (W i a)) 0:=by
          refine HasDerivAt.congr_deriv (((hasDerivAt_const (0:ℝ) (g a i)).sub (tickP q k u i x a δ) |>.const_smul (sa ψ i a)).add (((hasDerivAt_const (0:ℝ) (g a i)).sub (tickP q k u i x a (-δ))).const_smul (f ψ i a))) ?_
          let V:=W i a; rw [Complex.ofReal_neg,neg_smul]; change _ • (0-(δ:ℂ) • V)+_ • (0- -((δ:ℂ) • V))=_; rw [← signdC, mul_sub,sub_smul,mul_comm (δ:ℂ),mul_comm (δ:ℂ), ←smul_smul, ←smul_smul]; unfold sa f; rw [zero_sub,zero_sub, neg_neg, smul_neg]; abel
     have hv:=HasDerivAt.fun_sum (u:=Finset.univ) (fun a _=>HasDerivAt.fun_sum (u:=Finset.univ) (fun i _=> h a i)); apply HasDerivAt.congr_deriv hv; unfold W tapL normalD; -- rewrite sum.V ordering
     -- display state
     simp only [petite,Finset.smul_sum]
     conv_rhs=>rw [Finset.sum_comm]
     apply sum_congr rfl; intro a _; rw [sum_comm]; refine sum_congr rfl (fun i _=> sum_congr rfl (fun y _=> sum_congr rfl (fun p _=>?_))); split
     · rw [smul_smul,smul_smul,mul_right_comm]
     simp
lemma beamSpan (p:UV.Multi d) (T:Submodule ℂ (Covec d)) (hT:∀ x:Cover,normalD q ψ k u (vector x)∈T): petal (leafD q ψ k u p)∈ T:=by
     let r:=signD q; have hv : ∑ i∈ Lattice.box d, (sample p i:ℂ) • normalD (d:=d) q ψ k u (vector i)=(r:ℂ) • petal (leafD q ψ k u p):=by
         unfold r normalD; simp only [Finset.smul_sum]; rw [sum_comm]; simp_rw [smul_smul, sing_cover]; -- sums
         simp_rw [mul_left_comm ((↑(_ : ℝ):ℂ)) ((↑(signD q):ℂ)) (↑(profileL _ _):ℂ), ←sum_smul,← mul_sum,← Complex.ofReal_mul,← Complex.ofReal_sum,sample_Φ]; rw [sum_eq_single p]; simp; intro i _ hi; rw [if_neg hi]; simp; simp
     have hh:(r:ℂ)≠0:=by cases q <;> simp [r,signD]; -- separate lines
     have hs:(r:ℂ) • petal (leafD q ψ k u p) ∈ T:=hv ▸ T.sum_mem fun i _=> T.smul_mem _ (hT _)
     rw [← inv_smul_smul₀ hh (petal _)]; exact T.smul_mem _ hs
end Pulses
end YM.Massive.Elm
