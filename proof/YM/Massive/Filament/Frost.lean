import YM.QCD.Ruby.Bahn
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Filter.AtTopBot.Finset
/-!
# K = single gas products on η-colored slots. Coalescing theorem

Needed after last K merge: from the analytic final K prices, allocate
λ coefficients to distinct K slots. Although unchanged values can be represented
at any λ by sums of power charges, the law to evaluate is a (constrained) product, not that sum. Prove
exact grouping per ADDRESS-collection powers, retaining flags. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fibre
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ}{t:ℝ} {ι α K: Type}
variable (ρ:ι→α) (W:Rail c N ι) (Z:Rail c N α)
section ind
variable [CommSemiring K](v:ι→K)
set_option quotPrecheck false
variable (G:Finset α)(u:Finset ι)
def board (i:Finset α) (q: Finset ι) :Prop:= Set.InjOn ρ q ∧ q.image ρ=i
lemma film : ∑ x∈ u.powerset,(if board ρ G x then ∏ i∈x,v i else 0)=∏ i ∈ G,(∑ j∈u, if ρ j=i then v j else 0):=by
   let p:=(fun i:↥G=> u.filter fun x=>ρ x=i.1)
   let V:= Fintype.piFinset p
   let y(f:↥G→ι):=univ.image f
   have he f (hf:f∈V) (i:↥G): f i ∈ u ∧ ρ (f i)=i.val:= mem_filter.mp ((Fintype.mem_piFinset.mp hf) i)
   have hy f (hf:f∈V): Function.Injective f:= by intro i j he'; apply Subtype.ext; rw [← (he f hf i).2,← (he f hf j).2,he']
   let U:=u.powerset.filter (board ρ G)
   have hη:V.image y=U:=by
     ext k; constructor
     · intro h; obtain ⟨f,hf,rfl⟩:=mem_image.mp h; refine mem_filter.mpr ⟨mem_powerset.mpr (fun i hi=> ?_), ?_, ?_⟩
       · obtain ⟨a,-,rfl⟩:=mem_image.mp hi; exact (he f hf a).1
       · intro i hi j hj h; obtain ⟨a,-,rfl⟩:=mem_image.mp hi; obtain ⟨b,-,rfl⟩:=mem_image.mp hj; exact congr_arg f (Subtype.ext ((he f hf a).2.symm.trans (h.trans (he f hf b).2)))
       ext i; constructor
       · intro h; obtain ⟨z,hz,rfl⟩:=mem_image.mp h; obtain ⟨j,-,rfl⟩:=mem_image.mp hz; exact (he f hf j).2.symm ▸ j.2
       intro h; let u:↥G:=⟨i,h⟩; exact mem_image.mpr ⟨_,mem_image_of_mem f (mem_univ u),(he f hf u).2⟩
     intro h; obtain ⟨hv,hχ,hS⟩:= mem_filter.mp h
     choose f hf he using fun i:↥G=> mem_image.mp (show i.val∈k.image ρ from hS.symm ▸ i.property)
     refine mem_image.mpr ⟨f,Fintype.mem_piFinset.mpr (fun i=>mem_filter.mpr ⟨mem_powerset.mp hv (hf i),he i⟩), ?_⟩
     ext i; constructor
     · intro h; obtain ⟨j,-,rfl⟩:= mem_image.mp h; exact hf j
     intro h; let j:↥G:= ⟨ρ i,hS ▸ mem_image_of_mem _ h⟩; exact mem_image.mpr ⟨j,mem_univ _, hχ (hf j) h (he j)⟩
   have hU : Set.InjOn y V :=by
      intro f hf g hg hG; funext z; have hz:g z∈ y f:= hG.symm ▸ mem_image_of_mem g (mem_univ z); obtain ⟨k,-,hk⟩:=mem_image.mp hz
      suffices ho:k=z by rw [← ho, hk, ho]
      exact Subtype.ext ((he f hf k).2.symm.trans ((congr_arg ρ hk).trans (he g hg z).2))
   have hX : ∏ i∈ G,(∑ j∈u, if ρ j=i then v j else 0)=∑ f∈V,∏ i:↥G,v (f i):=by
       rw [← Finset.prod_attach G (fun i:α => ∑ j∈u, if ρ j=i then v j else 0)]; simp_rw [←sum_filter]; exact prod_univ_sum p (fun i:↥G=>v)
   rw [←sum_filter, hX]; change ∑ x∈U, (∏ i∈x,v i)=_; rw [← hη, sum_image hU]; exact sum_congr rfl (fun f hf=>prod_image (hy f hf).injOn)
end ind
-- Wallet expansion (analytic justification via summability alone). No sign condition.
variable (U:Grid c) (he : ∀ i,W.addr i= Z.addr (ρ i))
include he
lemma travels (P:Finset ι): separated (blocked (Ruby.home W)) P ↔ Set.InjOn ρ P ∧ separated (blocked (Ruby.home Z)) (P.image ρ):=by
    have h : ∀ i,Ruby.home W i=Ruby.home Z (ρ i):= fun i=>congr_arg Hat.place (he i); rw [GasP.close, GasP.close]; constructor
    · intro hp; constructor
      · intro x hx y hy hb; by_contra hn; obtain ⟨t,ht⟩:= (W.addr x).alive; apply Finset.disjoint_left.mp (hp hx hy hn) (show t∈ Ruby.home W x from (W.addr x).part ht); change t∈ Ruby.home W y; rw [h y,←hb, ← h x]; exact (W.addr x).part ht
      intro i hi j hj he; obtain ⟨x,hx,rfl⟩:= mem_image.mp hi; obtain ⟨y,hy,rfl⟩:= mem_image.mp hj; change Disjoint (Ruby.home Z _) (Ruby.home Z _); rw [← h x,← h y]; exact hp hx hy fun he'=> he (congr_arg _ he')
    rintro ⟨hi,hz⟩ x hx y hy hn; change Disjoint (Ruby.home W x) (Ruby.home W y); rw [h,h]; exact hz (mem_image_of_mem ρ hx) (mem_image_of_mem ρ hy) (fun h=> hn (hi hx hy h))
-- Need weighted occupancy held exactly specified at V each time. fibers hK conditional at *all* i, but no premise about totals.Acc across. |.inv|≥1 inherited. Any sizes.
variable (hp:∀ i,HasSum (fun j=> if ρ j=i then W.warp j U else 0) (Z.warp i U))(hz:Summable (tK W t U))
include hp hz
set_option quotPrecheck false
lemma sum_pallet (x:Finset α): HasSum (fun i:Finset ι=> if i.image ρ=x then tK W t U i else 0) (tK Z t U x):=by
   let f i:= if image ρ i=x then (tK W t U) i else 0
   have hm(i:Finset ι): i.biUnion (oriD W)=(i.image ρ).biUnion (oriD Z):=by rw [image_biUnion]; congr 1; exact funext fun j=>congr_arg Hat.inv (he j)
   have h₀ : Summable f:= by
      refine Summable.of_norm (hz.norm.of_nonneg_of_le (fun _=> norm_nonneg _) fun i=>?_); unfold f; split; exact le_rfl; exact norm_zero.trans_le (norm_nonneg _)
   by_cases hv: separated (blocked (Ruby.home Z)) x ∧ RG.flags t U=x.biUnion (oriD Z)
   · have hh (u:Finset ι): ∑ i∈u.powerset,f i=∏ i∈x, ∑ j∈u,(if ρ j=i then W.warp j U else 0):=by
         rw [← film ρ (fun i=> W.warp i U) x u]; refine sum_congr rfl fun i _=>?_
         unfold f tK board; by_cases hΔ: i.image ρ=x
         · by_cases ht : Set.InjOn ρ i
           · rw [if_pos hΔ,if_pos (show _ ∧ image ρ i=x from ⟨ht,hΔ⟩),if_pos (show _ ∧ RG.flags t U=i.biUnion (oriD W) from ⟨(travels _ _ _ he i).mpr ⟨ht,hΔ.symm ▸ hv.1⟩,hv.2.trans ((hm i).trans (congr_arg (fun X:Finset α=> X.biUnion (oriD Z)) hΔ)).symm⟩)]
           rw [if_pos hΔ,if_neg (fun h=>ht ((travels _ _ _ he i).mp h.1).1), if_neg (fun h=>ht h.1)]
         rw [if_neg hΔ,if_neg (fun h=> hΔ h.2)]
     have hg: HasSum f (tK Z t U x):=by
        have hX:Tendsto (fun u:Finset ι=>∏ i∈x, ∑ j∈u,(if ρ j=i then W.warp j U else 0)) atTop (𝓝 (tK Z t U x)):=by rw [tK,if_pos hv]; exact tendsto_finsetProd x fun i _=>hp i
        have he : (∑' i,f i)=tK Z t U x:= tendsto_nhds_unique ((h₀.hasSum.comp tendsto_finset_powerset_atTop_atTop).congr' (Eventually.of_forall hh)) hX
        exact he ▸ h₀.hasSum
     exact hg
   rw [tK,if_neg hv]; refine hasSum_zero.congr_fun (fun i=>?_); split; next he' => rw [tK,if_neg (fun h=>hv ⟨he' ▸ ((travels ρ W Z he i).1 h.1).2,h.2.trans ((hm i).trans (congr_arg (fun s:Finset α=> s.biUnion (oriD Z)) he'))⟩)]
   next _=> rfl
lemma liftRay : HasSum (tK Z t U) (∑' i, tK W t U i):=by
    refine (hz.hasSum.tsum_fiberwise (fun s=> image ρ s)).congr_fun ?_; intro x; rw [_root_.tsum_subtype,← (sum_pallet ρ W Z U he hp hz x).tsum_eq]; refine tsum_congr (fun i=>?_) -- syntax dependent subst
    simp only [Set.indicator,Set.mem_preimage, Set.mem_singleton_iff]
end YM.QCD.Fibre
#print axioms YM.QCD.Fibre.liftRay
