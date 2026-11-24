import YM.Mural.Clan
import YM.Mural.Isle
import YM.Mural.Crew
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plette
open QCD QCD.Grass QCD.Creek Cupola QCD.Cove QCD.Sway QCD.Sway.OrbitG Function Finset Filter MeasureTheory NormedSpace Push.AbsoluteSums
open Plate Stitch Tablet Ribbon Lattice Wilson Lat RG Twist PaletteT
open scoped BigOperators Topology Classical ContDiff
variable {c:Side}(N:ℕ)(p:Unit→Site c)(q:Unit→Bool)(P:Set (Finset Unit))(t:ℝ){I E J:Type} (Y:Patron.Rail c (ample N Unit) E)
local notation "J'"=>Film.Seats N p Y P
open Plate.Film Patron
variable (S:Support c){b u v r τ:ℝ}
noncomputable abbrev zone:= {i:Film.Seats N p Y P // S⊆ (Y.addr i.fst).place}
local notation "It"=>zone N p P Y S
local notation "K!"=>Film.publication N p q Y P t
noncomputable def season : Plate.Film c N Unit It:=⟨(K!).addr ∘ Subtype.val,(K!).z ∘ Subtype.val,(K!).mark ∘ Subtype.val⟩
local notation "Ψ"=> season N p q P t Y S
lemma exempt (h:∀ i V,¬S⊆ (Y.addr i).place → Mint N p t q ∅ (Y.warp i V))(V: Grid c) (i:J')(hi:¬ S⊆ (Y.addr i.fst).place) : (K!).mark i V=0:=by
    let g:= withdraw N p t (Y.warp i.1 V); let k:=i.2.val; have hp:= (h i.1 V hi).shows
    change pick _ _ k g=0; apply Subtype.ext; rw [show (pick (Keys c N) q k g).val=_ from choice ..]; have hz:k.Nonempty:= (mem_filter.mp i.snd.2).2.2.1
    rw [show pluck _ _ _=0 from (hp.spectral _ (fun he=>hz.ne_empty (burstUnique q he))),map_zero]; rfl
-- subforest direct rewriting
lemma conserveV (A: Rail c N J) (h:∀ i V,¬ S⊆(Y.addr i).place→Mint N p t q ∅ (Y.warp i V))(V:Grid c) : reports N Ψ A u V=reports N (K!) A u V:=by
   let T:= Ψ; let G:=K!; let e: J⊕zone N p P Y S ↪ J⊕ J':= Function.Embedding.sumMap (Function.Embedding.refl J) (Function.Embedding.subtype _); let u': Finset (J⊕ It) → Finset (J⊕ J'):= fun X=> X.map e
   let F:= addressSets N G A; let X:= addressSets N T A
   let f i:=spruced N T A i V; let g i:=spruced N G A i V; let K:= RG.flags u V; let H(s:Finset (J⊕J')):= Plate.roof F g K s
   have hp i:e i=e i:=rfl -- edit
   have ht i:F (e i)=X i:=by cases i<;>rfl
   have hw i:g (e i)= f i:=by cases i<;> rfl
   have he:Function.support H ⊆ Set.range u':=by
       intro i hi; change H i≠0 at hi; unfold H Plate.roof at hi; split at hi; swap; next _=>exact False.elim (hi rfl)
       have hx:∀ j∈i, j∈Set.range e:=by
           rintro (j|j) hV; · exact ⟨.inl j,rfl⟩
           by_contra hh; apply hi; apply prod_eq_zero hV; exact exempt N p q P t Y S h V j (fun h=> hh ⟨.inr (⟨j,h⟩:It),rfl⟩)
       refine ⟨i.preimage e e.injective.injOn,Finset.ext (fun j=>?_)⟩; constructor
       · intro hp; obtain ⟨z,hq,rfl⟩:=mem_map.mp hp; exact mem_preimage.mp hq
       intro h; obtain ⟨k',hk'⟩:=hx j h; refine mem_map.mpr ⟨k',mem_preimage.mpr (hk'.symm ▸ h),hk'⟩ -- check
   refine Eq.trans (b:=∑' i,H (u' i)) (?_) ((Finset.map_injective e).tsum_eq he)
   change (∑' i, Plate.roof X f K i)=_; refine tsum_congr fun i=>?_
   have hz:Arm F K (u' i)↔ Arm X K i:=by
       have hx:(u' i).biUnion (fun j=> (F j).inv)= i.biUnion (fun j=>(X j).inv):=by
          ext x; constructor; intro h; obtain ⟨j,hp,hq⟩:=mem_biUnion.mp h; obtain ⟨j,hpp,rfl⟩:=mem_map.mp hp; rw [ht] at hq; exact mem_biUnion.mpr ⟨j,hpp,hq⟩
          intro h; obtain ⟨j,hp,hq⟩:=mem_biUnion.mp h; exact mem_biUnion.mpr ⟨_,mem_map.mpr ⟨j,hp,rfl⟩,(ht j).symm ▸ hq⟩
       unfold Arm; rw [hx]; apply and_congr _ Iff.rfl; constructor
       · intro h x hx y hy hk; change Disjoint (X x).place (X y).place; rw [←ht,←ht]; exact h (mem_map.mpr ⟨x,hx,rfl⟩) (mem_map.mpr ⟨y,hy,rfl⟩) (e.injective.ne hk)
       intro h x hx y hy hr; obtain ⟨x,hX,rfl⟩:=mem_map.mp (show x∈i.map e from hx); obtain ⟨y,hY,rfl⟩:=mem_map.mp (show y∈i.map e from hy); change Disjoint (F _).place (F _).place; rw [ht,ht]; exact h hX hY (fun h=>hr (h ▸ rfl))
   unfold H Plate.roof; rw [show u' i=i.map e from rfl]; apply if_congr hz.symm _ rfl; rw [Finset.prod_map]; exact prod_congr rfl fun _ _=> (hw _).symm
lemma readyVol (ht: Y.Reg u) : Twist.Frails Ψ p q u S:=by
   refine ⟨fun i=> (mem_filter.mp i.val.2.2).2.2.1,fun i=> (mem_filter.mp i.val.2.2).2.2.2, fun i=>?_,fun i U V he hv=>?_,fun i U hv=>?_,fun i U=>?_,fun i=>i.2⟩
   · let u:= (Cupola.pick (Keys c N) q i.val.2.val); exact u.measurable.comp (((withdraw N p t).toLinearMap.toContinuousLinearMap).measurable.comp (ht.reads i.val.1))
   · exact congr_arg (fun x=>Cupola.pick (Keys c N) q _ (withdraw N p t x)) (ht.uses i.val.1 U V he hv)
   · exact ht.buys i.val.1 U (fun hp=>hv (by change Cupola.pick _ _ _ (withdraw N p t (Y.warp i.val.1 U))= _; rw [hp,map_zero,map_zero]))
   refine ⟨choseTuft ..,?_⟩; intro j; change pluck (Keys c N) j (chooseBlade (Keys c N) _ _)∈_; rw [many]; split; exact Cupola.pennied N p t j _ _ (ht.role _ _); exact Subalgebra.zero_mem _
-- propagation wallet direct singletons
open Kites Loom
lemma wealthVol (Q:BudgetPoint)(c0:ℝ)(m:ℝ)(hb:Wage.Lump N p q Y Q t b u)(h:τ≤u)(hr:1 ≤τ)(hm:τ ≤ c0*u)(hk:0≤c0)(hp:0<t): Film.Stock N Ψ Q.B τ b t c0 (fun _=>1):=by
    obtain ⟨g,ht,hq⟩:=hb.tilt.sold.cost; let f (i:It):=g i.val.fst; have hf i:0≤ g i:=(norm_nonneg _).trans (hq i 1)
    refine ⟨f,fun i V=> (?_),fun j=>?_⟩
    · exact (Film.cost_g N p q Y P t hp i.val V (hb.fits ..)).trans (hq _ _)
    let e(i:It):=i.val.fst; have he:Injective e:=by
       rintro ⟨⟨i,h⟩,ih⟩ ⟨⟨i',h'⟩,ih'⟩ hh; change i=i' at hh; subst i'
       have H(i:↥(Film.seats p P (Y.addr i))):i.val=({()}:Finset Unit):= Finset.eq_singleton_iff_unique_mem.mpr ⟨Subsingleton.elim () (mem_filter.mp i.2).2.2.1.choose ▸ (mem_filter.mp i.2).2.2.1.choose_spec,fun _ _=>Subsingleton.elim _ _⟩
       rw [show h'=h from Subtype.ext ((H h').trans (H h).symm)] -- dependent rewrite risky
    refine budget_loosen (?_ : SumBudget _ (c0*1)) (by norm_num); have hF:=budget_pull e he (budget_scale hk (ht j))
    refine budget_mono hF (fun i=>?_) (fun i=>?_ )
    · split; next ha=> unfold Film.fares QCD.GasP.taxed; simp only [abs_one,prod_const_one,one_mul]; exact mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hr) _) (hf _)) (Real.exp_pos _).le
      next hu=> exact le_rfl
    split; next hx=>
       dsimp only; rw [if_pos (show j∈ Ruby.home Y (e i) from hx)]; unfold Film.fares QCD.GasP.taxed; simp only [abs_one,prod_const_one,one_mul]; let n:= (Y.addr (e i)).inv.card; have ht:0<n:=(Finset.card_pos.mpr (Y.addr _).alive); have hu':0 ≤ u:= zero_le_one.trans (hr.trans h)
       have hv:τ^n ≤ c0*u^n:=by
            rw [show n=n-1+1 from by omega,pow_succ,pow_succ]; exact ((mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans hr) h _) hm (zero_le_one.trans hr) (pow_nonneg hu' _)).trans_eq (by ring))
       change τ^n*g (e i)*Real.exp _ ≤ c0*(u^n*g (e i)*Real.exp _); rw [← mul_assoc, ← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hv (hf _)) (Real.exp_pos _).le
    next hp=>exact hF.1 _
end YM.MassiveQCD.Plette
#print axioms YM.MassiveQCD.Plette.conserveV
#print axioms YM.MassiveQCD.Plette.wealthVol
