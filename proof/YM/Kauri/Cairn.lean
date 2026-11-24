import YM.Kauri.Horns
set_option maxHeartbeats 480000
set_option autoImplicit false
noncomputable section
namespace YM.Kauri
open Set Function Filter Analysis Lattice MeasureTheory QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder InnerProductSpace
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates Mako
open Module
open Ortho (plane Skew)
open scoped YM.Iceberg
open Lobo
variable {σ:RawSym}(R:Roof σ)
include R
lemma showtime(k:Lobo.Tri): rain (Omega k) 10≠0:=by
      rw [iris (Omega k) (treks k) R]; exact omega_non k σ R.right (fun _=>1) none (one_ne_zero)
lemma midnight (a b:Axis)(h:a≠b)(hx:projection ((TTot.val) (a,b))=0) : projection ((TTot.val) (a,a))=projection ((TTot.val) (b,b)):=by
      let p:=plane a b; let L:=pulseB.toBasis; have hh: feeF ((stall p) (L (a,b)))= rain p 8 (feeF (pulseB (a,b))):=themes R ..
      have hm:(stall p) (L (a,b))=-(L (b,b))+L (a,a):=by rw [stave]; unfold p; simp[L,pulseB,plane,Matrix.single_apply, ite_and,h,Ne.symm h]
      rw[hm,map_add,map_neg, ele,hx,map_zero] at hh -- ele wrong sites target. choose explicit
      exact (ele (a,a)).symm.trans ((eq_of_neg_add_eq_zero hh).symm.trans (ele _))
variable {d:ℕ}(g:Skew)(p q: Label d)(h:∀ a b:Axis,a≠b→projection ((TTot.val) (a,b))=0)
include h R
lemma banks (z:E4)(a b:Axis)(s t:Label 8)(ht:projection s=projection t): ghostQ topY g (χ:=flagX) p q z a b s= ghostQ topY g (χ:=flagX) p q z a b t:=by
      rw[tarG topY rounds g rooms,tarG topY rounds g rooms]; by_cases H: D (basis a) flagX z=0; · simp [Work.A05.weight,H]
      refine congr_arg _ (DawnS.trails _ (Work.A01.separated_of_D rounds (show Table.Window topY flagX from rooms) H) _ _ ?_); intro i; fin_cases i; exact ht; exact rfl; rfl
lemma hug : plumes topY flagX g TTot.val p.val q.val=0:=by
     rw [aliveS topY rounds g rooms p q TTot]; let v(i:Hea)(z:E4):ℂ:= ghostQ topY g (χ:=flagX) p q z i.1 i.2 (TTot.val i)
     have hv(i:Hea): Integrable (v i):= tarbG topY rounds g rooms p q ..
     have he(x:E4): (∑ a:Axis,∑ b:Axis,v (a,b) x)=0:=by
             let p0:=TTot.val (0,0)
             have hp(a:Axis):projection (TTot.val (a,a))=projection p0:=by by_cases ht:a=0; rw [ht]; exact midnight R _ _ ht (h _ _ ht) -- branch rfl
             have hm(a:Axis): (∑ b:Axis,v (a,b) x)= Work.A05.weight flagX a (Work.A05.arm topY g a) x * UV.Free.wick (hill d) (Points.cons x topY) (viva p0 p q):=by
                      rw [Finset.sum_eq_single a]; · exact (banks R g p q h x a a _ _ (hp a)).trans (tarG topY rounds g rooms p q a a p0 x)
                      · intro b _ hv; exact (banks R g p q h x a b _ 0 ((h a b hv.symm).trans (map_zero _).symm)).trans (map_zero _)
                      simp
             simp_rw [hm,← Finset.sum_mul,w_move,zero_mul]
     change -(∑ a:Axis,∑ b:Axis, ∫ x,v (a,b) x)=0
     rw [show (∑ a:Axis,∑ b:Axis, ∫ x,v (a,b) x)= ∫ x, ∑ a:Axis,∑ b:Axis, v (a,b) x from ?_]; simp_rw [he]; simp
     rw [integral_finsetSum _ (fun i _=> integrable_finsetSum _ fun j _=>hv (i,j))]; exact Finset.sum_congr rfl fun i _=>(integral_finsetSum _ (fun j _=>hv (i,j))).symm
lemma drips : rain g d=0:=by
     apply LinearMap.ext; intro x; obtain ⟨u,rfl⟩:= Free.onto x; obtain ⟨v,hv⟩:= Free.onto (rain g d (projection u)); rw[←hv]; refine Hail.shutD σ _ R.right ?_; intro y
     have hp:projection v=∑ i:IceT,(1:ℂ) • gran (oathU g) g (tour g) i d (projection u):=by rw[hv]; unfold rain reachΩ; simp
     have ht:= Heron.taps (oathU g) g (tour g) σ R.right y (fun _=>1) u v hp TTot rfl topY rounds flagX rooms; rw [hug R g u y h,← Hail.wellness] at ht; exact ht.symm
omit h
lemma eyes: ∃ i j:Axis,i≠j∧projection ((TTot.val) (i,j)) ≠ 0:=by by_contra! hh; exact showtime R 0 (drips R _ (fun i j hij=>hh i j hij)) -- by_contra quant
end YM.Kauri
#print axioms YM.Kauri.eyes
