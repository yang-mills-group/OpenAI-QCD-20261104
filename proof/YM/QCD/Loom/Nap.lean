import YM.QCD.Loom.Palm
/-! # All scales in a type, reweight sector analytic loans -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Creek
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ:Type}{N:ℕ}
noncomputable def token (c:Side)(N:ℕ)(a:ℝ): EvenA c N→L[ℝ]Grass.Alg (Keys c N):=
 LinearMap.toContinuousLinearMap (((Grass.changeVars (Matrix.diagonal (fun _:Keys c N=>(a:ℂ)))).comp (light (Keys c N))).toLinearMap.restrictScalars ℝ)
lemma pulse (a:ℝ)(x:EvenA c N): ‖token c N a x‖=Creek.load (fun _=>a) (light (Keys c N) x):=rfl
lemma bands (x y:EvenA c N)(a:ℝ) : ‖token c N a (x*y)‖ ≤ ‖token c N a x‖*‖token c N a y‖ :=by rw [pulse,pulse,pulse,map_mul]; exact Creek.load_mul ..
lemma folkl (s:Finset ι)(f:ι→EvenA c N)(a:ℝ): ‖token c N a (∏ i∈s,f i)‖ ≤∏ i∈s,‖token c N a (f i)‖:=by
   induction s using Finset.induction_on with
   | empty=> simp only [prod_empty,pulse,map_one,load_one,le_refl]
   | insert i s hi ih=> rw [prod_insert hi,prod_insert hi]; exact (bands ..).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))
namespace Fleet
def united (A:Fleet H ι N)(B:Fleet H κ N) :Fleet H (ι⊕κ) N where
 limit := Sum.elim A.limit B.limit
 ground:= Sum.elim A.ground B.ground
 fine:= Sum.elim A.fine B.fine
 window:= Sum.elim A.window B.window
 compat i j:= match i,j with|Sum.inl a,Sum.inl b=>A.compat a b|Sum.inr a,Sum.inr b=>B.compat a b|_,_=>True
 works:= Sum.elim A.works B.works
lemma jungle (A:Fleet H ι N)(B:Fleet H κ N)(H:A.Famous)(p:B.Famous): (united A B).Famous:=by
   constructor <;> (rintro (i|i))
   all_goals first|exact H.horizons i|exact H.boot i|exact H.locally i|exact H.read i|exact H.pays i|exact H.roots i|exact H.issued i|exact p.horizons i|exact p.boot i|exact p.locally i|exact p.read i|exact p.pays i|exact p.roots i|exact p.issued i|skip
   all_goals rintro (j|j) h <;> first | exact H.signs i j h|exact p.signs i j h|exact False.elim (h (show True from trivial))
-- ignition. collect anomalous near vertical seed expenditures. No assume compact s.
variable (Y:Fleet H ι N)
structure Theft (F:Tree.Forest S.ratio)(X: ι→Site c)(w:ι→ℝ) (v a:ℝ) (slim: Finset ι)(i n:ℕ) :Prop where
 rate : 0 ≤ a
 grow j: 0 ≤ w j
 pack : ∀ x,(slim.filter fun j=> X j=x).card ≤ n
 rare j :∀ Z:Coat T F,Z.x=τ→ Z.width=o.K→Z.manifest → ∀ z:Air f su, w j < ‖token c N v (Y.coming j Z z)‖ → j∈ slim ∧ ∃ k∈Y.ground j,k∈ Z.seeds.place ∧ separation k (X j) ≤ i
 deck j :∀ Z:Coat T F,Z.x=τ→ Z.width=o.K→ Z.manifest → ∀ z:Air f su,‖token c N v (Y.coming j Z z)‖ ≤ Real.exp a*w j
variable {J κ': ι→ℝ}{Z :ι→ Site c}
lemma riseTiny (YX : Coat T F)(z:Air f su)(x: EvenA c N)(j:ι)(v:ℝ): ‖token c N v (Y.riseP YX z j • x)‖ ≤ ‖token c N v x‖:=by
   rw [map_smul,norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) ((Real.norm_of_nonneg (YX.conserve ..).1).trans_le (YX.conserve ..).2)
lemma watch {v a:ℝ}{slim:Finset ι}{i n:ℕ}(H:Y.Theft F Z J v a slim i n) : (Y.suitcase F).Merit J (a*((Animals.ballCost (i+1):ℝ)*n)) (token c N v):=by
   refine ⟨H.grow,fun s X he ht hs hb hp z=>?_⟩
   let P:= Y.suitcase F; let E:= P.sizeP s
   let W:= s.toRight; let t j:= Y.coming j X z; let S' := W.filter fun j=> J j < ‖token _ _ v (t j)‖
   have hu j (hi:j∈ S') := H.rare j X he ht hs z (show J j< _ from (mem_filter.mp hi).2)
   have hv : S'.card ≤ E*Animals.ballCost (i+1)*n := P.seedPop hp S' Z i (fun y=>
     (Finset.card_le_card (Finset.filter_subset_filter _ fun j hi=> (hu j hi).1)).trans (H.pack y)) fun j h=>by
        obtain ⟨k,hk,hy,hw⟩:= (hu j h).2
        exact ⟨k,hy,P.leP s ((mem_filter.mp h).1) hk,hw⟩ -- fixed
   let p:= Real.exp a
   have hh:1≤p:=Real.one_le_exp H.rate
   let f j:= ‖token _ _ v (t j)‖
   have hy j (hi:j∈W) : f j ≤ (if j∈ S' then p else 1)*J j:=by
      by_cases hg:j∈ S'
      · rw [if_pos hg]; exact H.deck j X he ht hs z
      rw [if_neg hg,one_mul]; exact le_of_not_gt fun hb=> hg (mem_filter.mpr ⟨hi,hb⟩)
   apply (folkl W t v).trans; apply (prod_le_prod (fun _ _=> norm_nonneg _) hy).trans; rw [prod_mul_distrib]; change _* (∏ i∈W,J i) ≤ _*(∏ i∈W,J i)
   apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun _ _=> H.grow _)
   rw [prod_ite]; have hb: W.filter (fun i=> i∈S')=S':= by ext x; rw [mem_filter,and_iff_right_of_imp (fun h=>(filter_subset _ _) h)]
   rw [hb,prod_const,prod_const_one,mul_one]; apply le_trans (pow_le_pow_right₀ hh hv)
   unfold p; rw [← Real.exp_nat_mul]; apply le_of_eq; push_cast; congr 1; unfold E; ring -- P
lemma balanceP {v a:ℝ}{K:Tree.Forest S.ratio}{i j n m:ℕ}{P':Fleet H ι N}(Q':Fleet H κ N){f':ι→ℝ}{g:κ→ℝ}{S':Finset ι}{Z:ι→ Site c}{X:κ→ Site c}{T':Finset κ}(hf:P'.Theft K Z f' v a S' i n)(hg:Q'.Theft K X g v a T' j m): (united P' Q').Theft K (Sum.elim Z X) (Sum.elim f' g) v a (S'.disjSum T') (max i j) (n+m):=by
   constructor
   · exact hf.rate
   · rintro (i|i); swap; exact hg.grow i; exact hf.grow i
   · intro x; rw [show Finset.filter (fun j=> Sum.elim Z X j=x) (S'.disjSum T')=(S'.filter fun j=>Z j=x).disjSum (T'.filter fun j=>X j=x) from ?_,card_disjSum]; exact Nat.add_le_add (hf.pack x) (hg.pack x)
     ext p; rcases p with p|p <;> simp
   · rintro (x|x) U ht hp h z hz
     · obtain ⟨hy,k,hk,he,hh⟩:= hf.rare x U ht hp h z hz; exact ⟨inl_mem_disjSum.mpr hy,k,hk,he,hh.trans (le_max_left ..)⟩
     obtain ⟨hy,k,hk,he,hh⟩:= hg.rare x U ht hp h z hz; exact ⟨inr_mem_disjSum.mpr hy,k,hk,he,hh.trans (le_max_right ..)⟩
   · rintro (x|x) Z ht hp hs z; swap; exact hg.deck x Z ht hp hs z; exact hf.deck x Z ht hp hs z
end Fleet
end YM.QCD.Loom
