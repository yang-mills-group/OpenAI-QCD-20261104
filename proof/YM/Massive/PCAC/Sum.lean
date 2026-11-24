import YM.Massive.PCAC.Coin
import YM.Massive.PCAC.Echo
/-! # The mass-scaled SCALAR meson in the true cuts, and its actual
transfer along arbitrary Run. An exact interscale difference-mass measurement law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A B:Type*} [Fintype A][Fintype B]
variable {c f:Side}{n N j k F:ℕ}
open Tide
open Finset
open scoped Kronecker
variable (a b:Flavor F)
noncomputable abbrev scaleM (T:Regulator c F)(a b:Flavor F):ℂ:= T.m a-T.m b
-- careful `scaleM` RHS real minus then coe?
noncomputable def scalarWard (R:Regulator c F): Insertion c F:= (scaleM R a b) • (∑ u:Site c,scalarProbe a b u 1)
theorem full_vector (R:Regulator c F): let V:=flavorW 1 a b c; R.density * scalarWard a b R= mark false V R.density - mark true V R.density:=by
     intro V; have he(f:Insertion c F)(g:Bool): ∑ u:Site c, mark g (localF u 1 a b) f= mark g V f:=ContinuousMap.ext fun U=> by rw [ContinuousMap.sum_apply]; exact mark_collect a b 1 g _ _
     rw [← he _ true,← he _ false,← sum_sub_distrib]; simp_rw [vectorWard, ←mul_sum]; unfold scalarWard; rw [smul_sum,sum_add_distrib]
     let p:=∑ u:Site c,∑ v:Site c,current R a b u v; have hh : p= -p:=by
         conv_lhs=> unfold p; rw [sum_comm]; enter [2,u,2,v]; rw [swapped]
         simp only [sum_neg_distrib]; rfl
     have h :p=0:= by
         have he:(2:ℂ) • p=0:=by rw [two_smul]; exact eq_neg_iff_add_eq_zero.mp hh
         exact (smul_eq_zero.mp he).resolve_left (by norm_num)
     rw [show (∑ u:Site c,∑ v:Site c,current R a b u v)=0 from h,add_zero]; -- scale defeq

-- local Ward vanishing with spectators not reaching insertion site
lemma rigid {D:Set (Site c)}(x:Site c)(h:x∉D)(R:Regulator c F)(Y:Insertion c F)(he:Uses D ⇑Y)(ht:a≠b) :
    R.raw (((scaleM R a b) • scalarProbe a b x 1+∑ v:Site c,current R a b x v)*Y)=0:=by
      change joint ⇑(R.density*(_*Y))=_; rw [←mul_assoc]; change joint (⇑((R.density*((((R.m a:ℂ)-(R.m b:ℂ)):ℂ) • scalarProbe a b x 1+∑ v:Site c,current R a b x v))*Y))=_; rw [← vectorWard,sub_mul]; let P:= localF x 1 a b; let B(g:Bool):=mark g P R.density*Y; change joint (⇑(B false-B true))= _; have hm(g:Bool) : joint (⇑(B g))=0:= clears a b x 1 D h g ht R.density Y he
      unfold joint; simp only [ContinuousMap.sub_apply,map_sub]; have hp(g:Bool): Integrable (fun i=>ber _ (B g i)) (prior su c):=(continuous_ber.comp (B g).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _); rw [MeasureTheory.integral_sub (hp false) (hp true), show (∫ U,ber _ (B false U) ∂prior su c)=0 from hm false,show (∫ U,ber _ (B true U) ∂prior su c)=0 from hm true,sub_self]
section path
variable (X Y: Spike){R: Side} {S:Scheme} (A:Run S N R F) (hp:A.Actual)(h:a≠b)
include hp h
local notation "s'"=> S.toStop R A.β A.w
noncomputable def vectorDiff(i:ℕ): Insertion (S.side R i) F:= film X a b A false i-film X a b A true i
noncomputable def axialSum (i:ℕ): Insertion (S.side R i) F:= film X a b A false i + film X a b A true i
local notation "δc"=> vectorDiff a b X A
local notation "εc"=> axialSum a b X A
local notation "T"=> film X a b A true
local notation "V"=> film X a b A false
omit h in
lemma started : vectorDiff a b 1 A N=A.regulator.density*scalarWard a b A.regulator:=by rw [full_vector]; unfold vectorDiff film; rw [show actor A N=A.regulator.density from DFunLike.coe_injective ((act A hp le_rfl).trans hp.start)]
theorem passport (q:ℕ)(hx:q≤N): ∃ M:∀ i:ℕ, Deck (S.side R i) F,
     M q=0 ∧ (∀ i<q,M i=liftM A X a b i (M (i+1))) ∧ ∀ i≤q, (∀ b:Bool,s' q i (if b then T q else V q)=(if b then T i else V i)- passenger (M i)) ∧ s' q i (δc q)=δc i ∧ s' q i (εc q)= εc i - (2:ℂ) • passenger (M i):=by
     obtain ⟨M,hM,hm,H⟩:= deliver X a b A false hp h q hx; obtain ⟨V0,hV,hv,W⟩:= deliver X a b A true hp h q hx; have he(i:ℕ)(hi:i≤q): M i=V0 i:=by
         induction hi using Nat.decreasingInduction with
         | self=> rw [hM,hV]
         | of_succ i hi ih=> rw [hm i hi, hv i hi,ih]
     refine ⟨M,hM,hm,fun i hi=> ?_⟩; have h1:= H i hi; have h2:= W i hi; change s' q i _= _ at h1 h2; rw [←he i hi] at h2; refine ⟨fun b=>by cases b; exact h1; exact h2,?_⟩; unfold vectorDiff axialSum; rw [map_sub,h1,h2,map_add,h1,h2]; constructor <;> try rw [two_smul]
     all_goals abel
-- Projection on total axial sum: exposes precisely where additional probe estimate needed!
theorem charge (hX:X*Y=1)(hY:Y*X=1)(q:ℕ)(hx:q ≤ N)(i:ℕ)(hi:i≤q):
     chord Y a b A i (s' q i (δc q))= A.massRead i a - A.massRead i b ∧
     ∃ M:∀ i:ℕ, Deck (S.side R i) F, M q=0 ∧ (∀ i<q,M i=liftM A X a b i (M (i+1))) ∧ chord Y a b A i (s' q i (εc q))= A.massRead i a + A.massRead i b- 2* chord Y a b A i (passenger (M i)):=by
     obtain ⟨M,hM,h1,hL⟩:= passport a b X A hp h q hx; obtain ⟨-,hv,hw⟩:=hL i hi
     rw [hv]; constructor
     · unfold vectorDiff; rw [chord_sub, answering X Y a b A false hX hY i (hi.trans hx) hp, answering X Y a b A true hX hY i (hi.trans hx) hp]; simp
     refine ⟨M,hM,h1,?_⟩; rw [hw]; unfold axialSum; rw [two_smul,chord_sub,chord_add,chord_add, answering X Y a b A false hX hY i (hi.trans hx) hp, answering X Y a b A true hX hY i (hi.trans hx) hp]; simp only [Bool.false_eq_true,↓reduceIte]; ring

-- Exact probe without scalar/quark normalization assumptions.
theorem reference (i:ℕ)(hx:i ≤ N): chord 1 a b A i (s' N i (A.regulator.density * scalarWard a b A.regulator))= A.massRead i a-A.massRead i b:=by
     rw [← started]; exact (charge a b 1 1 A hp h (by simp) (by simp) N le_rfl i hx).1; exact hp
end path
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.reference
#print axioms YM.Massive.PCAC.charge
#print axioms YM.Massive.PCAC.rigid
