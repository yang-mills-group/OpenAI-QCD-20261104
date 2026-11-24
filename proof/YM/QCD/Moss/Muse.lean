import YM.QCD.Moss.Coda
import YM.QCD.Tax.Glory
import YM.QCD.Shell.Path
/-! # Transparent local filament. Prototype word for an exact period comparison. Forest, corrected slide choices and seam socks. No-limit letters. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Moss
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory ProbabilityTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Coat Animals
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Loom Loom.Fleet
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat.Deck
open Further.PhysicalPeriodLimitF933 Macrame Stellar Mint
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side}{N D:ℕ} {I J:Type}
variable {P: Teller su} {S: StepData c f} {R: Rep su f}{T:Tube su S}{κ W μ τ:ℝ}
variable {X : ConnectedActivityE6.Target su P} {o:ConnectedActivityE6.Target.Order su W}
variable (K: Cash W τ μ L X o κ T R)
open Fork Run Port Kit Gas GasP Ursell
variable {K}
variable (Y:Fleet K I N)
open Blaze King Silica Patron Sands
-- survivor masked and unmasked localization. proof fossil Pantry rate. Applies before orientation repair.
lemma lengthR (z: Clusters Y.Bright) (i:Option (Fin z.fst)): 1≤ (z.2 i).val.card ∧ (z.2 i).val.card ≤ heft S (z.2 i).val ∧ heft S (z.2 i).val ≤ crestP Y z:=
 ⟨Nat.succ_le_of_lt (Finset.card_pos.mpr (z.2 i).2.1.2.1.1),Nat.le_add_right ..,single_le_sum (f:=fun j=>heft S (z.2 j).val) (fun _ _=>Nat.zero_le _) (mem_univ i)⟩
lemma scopeH (z:Clusters Y.Bright): z.fst+1≤ crestP Y z:=by
   refine le_trans ?_ (sum_le_sum (f:=fun _=>1) (g:=fun i=>heft S (z.2 i).val) (s:=univ) (fun i _=>(lengthR Y z i).1.trans (lengthR Y z i).2.1))
   simp
lemma individualH (z:Clusters Y.Bright)(hr:crestP Y z ≤1)(X:I→Prop)(hv:stand Y X z):∃ p:Y.Bright,∃ i:I,z=individual p ∧ X i ∧ Aliased Y p i:=by
   obtain ⟨i,j,he,hj⟩:=hv; have hh:= scopeH Y z; have hz:z.1=0:=by omega
   have hp :=lengthR Y z i; let P:=z.2 i
   have hE:z=individual (z.2 i):=by
     rcases z with ⟨k,p⟩; dsimp only at hz; subst k; exact congr_arg (Sigma.mk 0) (funext (fun j=> congr_arg p (Subsingleton.elim _ _)))
   exact ⟨P,j,hE,hj, Eq.symm <| eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr (mem_toRight.mp he)) ((hp.2.1.trans (hp.2.2.trans hr)).trans_eq (by rw [card_singleton]))⟩
variable (hp:∀ i x,R.activities.E i x=0)
include hp
lemma noE (i:ℕ)(v:Y.Bright)(h:Opacity.key S i∈ v.val.toLeft)(χ:Chi)(x:Grid c): Y.brisk v.val χ x=0:=by
    let w:= v.val
    have hm i U:R.activities.regularOccurrence R.p i U=0 :=by simp only [Activities.regularOccurrence,masked,Set.indicator,hp]; split<;>rfl
    have hx (F:Tree.Forest S.ratio)(X:Coat T F) (j z): Polar.floating X o.a R W (‹ConnectedActivityE6.Target su P›).table z j (‹ConnectedActivityE6.Target su P›).halo w.toLeft=0:=by
       unfold Polar.floating; apply prod_eq_zero h; change Real.exp (-(R.activities.regularOccurrence _ i _) * _)-1=_; rw [hm,neg_zero,zero_mul,Real.exp_zero,sub_self]
    have he (F:Tree.Forest S.ratio)(X:Coat T F): Y.bandL w X=0:=by
       unfold bandL; split
       · simp only [Fleet.lows,choiceS,regards,hx,zero_smul,smul_zero, integral_zero, sum_const_zero]
       exact rfl
    change Y.brisk w χ x=0; simp only [brisk,he,choiceS,sum_const_zero,smul_zero]
lemma hatching (Y₀:Bouquet K Y)(p:Clusters Y.Bright)(hp':crestP Y p≤2)(hl:moist Y p<1)(hx:∀ i j,j ∈(p.2 i).val.toRight→ j∈ Set.range Y₀.route)(χ:Chi)(U: Grid c)(hF:Y.furnace χ U p≠0)(i:Option (Fin p.fst)) : ∀ j∈(p.2 i).val,j∈ Set.range Y₀.queen:=by
   let k:=(p.2 i).val; intro j hj; rcases j with j|j
   swap; · obtain ⟨v,rfl⟩:= hx i j (mem_toRight.mpr hj); exact ⟨.inr v,rfl⟩
   have hq : shareP Y k <1 := lt_of_le_of_lt (single_le_sum (f:=fun i=>shareP Y (p.2 i).val) (fun _ _=>Nat.cast_nonneg _) (mem_univ i)) hl
   have H: coron S I (.inl j)≤1:=by
     have hp:= lengthR Y p i; have hv :=hp.1; have hh :=hp.2.2; unfold heft at hh; have h := single_le_sum (f:=coron S I) (fun i _=>Nat.zero_le _) hj; omega
   have hh:= mem_toLeft.mpr hj
   have ha: Pipe.born Y.shellF k:= (p.2 i).2.1.2.2
   rcases j with j|j
   · have hE:= Packets.shares_nonzero S _ _ (ha.1.1.checkpoints j (mem_toLeft.mpr hh))
     have hf:1 ≤ Y.shellF.sizeP k:=by rw [← Pipe.whorls]; refine hE.trans (single_le_sum (f:=fun i=>Mixed.shares S i) (fun _ _=>Nat.zero_le _) hh)
     exact False.elim (hq.not_ge (Nat.one_le_cast.mpr hf))
   rcases j with j|j|j
   · have hx':j∈Y.shellF.filterP k.toRight:=ha.2.2 ▸ (show j∈own k.toLeft from mem_toLeft.mpr (mem_toRight.mpr hh))
     obtain ⟨q,hq,hv⟩:= mem_biUnion.mp hx'; obtain ⟨q,rfl⟩:=hx _ _ (show _∈(p.2 i).val.toRight from hq)
     exact False.elim (Finset.notMem_empty _ (Y₀.born q ▸ (show j∈Y.limit (Y₀.route q) from hv))) -- type
   · have hp'': Silica.horn (.inr (.inl j))≤1:= H -- implicit c f
     suffices h : PhysicalNext.Repeat.Beam.Pennies S (.inr (.inr (.inl j))) by
       obtain ⟨y,hy⟩:= (penned ..).1 h; exact ⟨.inl y,congr_arg Sum.inl hy⟩
     refine ⟨j,rfl,?_⟩; rcases j with j|j|j
     · rcases j with j|j|j|j|j|j
       · exfalso; apply hF; unfold furnace termP; rw [prod_eq_zero (mem_univ i) (noE Y hp j _ hh χ U),smul_zero,smul_zero]
       · trivial
       · trivial
       · trivial
       all_goals exact (by contradiction : False).elim
     · trivial
     change 2≤1 at H; omega
   change 2≤1 at H; omega
end YM.QCD.Moss
