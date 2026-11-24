import YM.QCD.Spice.Mace
/-! # Prices for ψ comparison operator. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Spice
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Jets
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun Cove.Fj Jets.Touch MeasureTheory
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y w t b':ℝ}{l b:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "R"=> Junta c f F
local notation "S"=> sliceL G h
variable {T:Grid f→Sheet f}(P:Sun G c f h δ v q u a l T)
lemma talks (U V:Grid f)(i:Keys f F) (ht:0 ≤ u) (h:beamAt (trunkFt (locationP i) b) U V w)(hv:w<δ/2)(hw:0≤w): let Z:Water c f F := short P.Z P.V b (settled U) - short P.Z P.V b (settled V)
    ∑ j:Keys c F, ‖Z i j‖ ≤ (fingers F*q)*(w/(δ/2)):=by
   intro Y'; let Q x j:=spoon P.Z x b x j (settled U)-spoon P.Z x b x j (settled V); let X j x:=spoon P.V x b j x (settled U)-spoon P.V x b j x (settled V)
   have he:Y'=foamB Q X:=by
       ext i j
       rcases i with i|i <;> rcases j with j|j <;> simp only [Y',short,Q,X,Matrix.sub_apply,foamI,foamLR,foamRL,foamR]
       · split <;> simp
       · simp
       · simp
       split <;> simp
   rw [he,mul_assoc]
   let τ:=w/(δ/2); have he:0 ≤ τ := div_nonneg hw (half_pos P.positive).le
   cases i
   next i=>
    let Y i':= duel P.W i.1.1 i' u l *τ
    have hY:0≤Y:=fun i'=> mul_nonneg ((trimming P.Z0 i.1.1 b i.1.1 i').1.trans (coins P.Z0 i.1.1 b i.1.1 i' ht)) he
    refine (foam_at Q X i Y hY _ (le_trans (le_of_eq (Eq.symm (sum_mul ..))) (mul_le_mul_of_nonneg_right (P.Z0.spends i.1.1) he))).1 ?_ -- sum shape
    intro i'; exact (cruise (trimming P.Z0 i.1.1 b i.1.1 i') h P.positive hv hw).trans (mul_le_mul_of_nonneg_right (coins P.Z0 i.1.1 b i.1.1 i' ht) he)
   next i=>
    let Y i':= duel P.B0 i' i.1.1 u l *τ
    have hY:0≤Y:=fun i'=> mul_nonneg ((trimming P.V0 i.1.1 b i' i.1.1).1.trans (coins P.V0 i.1.1 b i' i.1.1 ht)) he
    refine (foam_at Q X i Y hY _ (le_trans (le_of_eq (Eq.symm (sum_mul ..))) (mul_le_mul_of_nonneg_right (P.V0.dues i.1.1) he))).2 ?_
    intro i'; exact (cruise (trimming P.V0 i.1.1 b i' i.1.1) h P.positive hv hw).trans (mul_le_mul_of_nonneg_right (coins P.V0 i.1.1 b i' i.1.1 ht) he)
variable {E K:Type}
-- BeamAt on CORE room for bucks Δ, fringe halo for wipe.
lemma swept (D:Peak (P.equip F b) t x y ξ (fun i=> Real.exp 1*terra P F b x y i))(U V:Grid f)(Q:Rise f F E K)(s: Finset (Fj (Tr f) E K))(h₀:Healthy t (brimW (P.equip F b) Q s) U)(h₁:Healthy t (brimW (P.equip F b) Q s) V)(h:beamAt (brimW (P.equip F b) Q s) U V w)(heG:0≤ w)(haW:w<δ/2)(ht:0≤u)(hz:y*fingers F*q ≤ ξ*x):
    let J:=hooks (F:=F) S (coreW (P.equip F b) Q s); let W:= wipe (Modes f F) (Modes c F); let X:=W ((P.equip F b).shortP U); let Y:=W ((P.equip F b).shortP V); let r:=rateF c f F x y; ∀ i∈ J,
    load (fun _=>y) (X (atom i))≤r i ∧ load (fun _=>y) (Y (atom i))≤r i ∧ load (fun _=>y) (X (atom i)-Y (atom i)) ≤ (ξ*(w/(δ/2)))*r i:=by
   intro J W X Y r i hi
   let p:= w/(δ/2); have hv:= D.bud; have hx:=D.cup; have hh:0≤p:=div_nonneg heG (half_pos P.positive).le
   rcases splits_index i with ⟨j,rfl⟩|⟨j,rfl⟩
   · change ha c f F j∈J at hi -- name conflict ha parameter
     have he:halo (b+1) {locationP j}⊆brimW (P.equip F b) Q s:=by
        unfold J at hi; rw [hooked,rootA] at hi; rw [brim_eq]; exact Corona.halo_mono (le_refl _) (singleton_subset_iff.mpr hi)
     rw [show r _ = _ from wagesA (Modes c F) j x y]
     refine ⟨full_tip hx _ _ (D.earn _ _ (h₀.mono_left he)),full_tip hx _ _ (D.earn _ _ (h₁.mono_left he)),?_⟩
     let g:= P.equip F b; let Z:Water c f F:= g.shortP U - g.shortP V
     rw [show X (atom _)-Y (atom (head (Modes f F) (Modes c F) j))=wipe (Modes f F) (Modes c F) Z (atom (Cove.ha _ _ _ j)) from ?_]; swap
     · unfold X Y W; rw [wiper,wiper,show atom (Cove.ha c f F j)=atom (head (Modes f F) (Modes c F) j) from rfl,wiper,← sum_sub_distrib]; exact sum_congr rfl fun i _=> (sub_smul ..).symm
     apply full_tip hx; apply (mul_le_mul_of_nonneg_left (talks P U V (b:=b) j ht (mores h (Subset.trans (Corona.halo_mono (Nat.le_succ _) (Subset.refl _)) he)) haW heG) hx.le).trans -- heG unnamed
     have hw:=mul_le_mul_of_nonneg_right hz hh; unfold p at hw; linarith
   · unfold X Y W; rw [tails,tails,sub_self,load_atom _ (fun _=>hx), load_zero, show r _ = _ from wagesB (Modes f F) j x y]; have hm:=D.post; exact ⟨le_rfl,le_rfl, mul_nonneg (mul_nonneg (by linarith) hh) hx.le⟩
lemma cycles {D₀ Z : Type} [Fintype D₀] (F' G':Z→EndA D₀) (p:D₀→ℝ)(u:Z→ℝ)(w:ℝ)(W: Finset Z)(h:(W:Set _).Pairwise fun i j=> Commute (F' i) (F' j))(he:(W:Set _).Pairwise fun i j=> Commute (G' i) (G' j))
    (hh:∀ i∈W,Pledge p (F' i) (u i) ∧ Pledge p (G' i) (u i) ∧ Pledge p (F' i-G' i) (u i*w)):
    Pledge p ((W.noncommProd F' h)-(W.noncommProd G' he)) (W.card*w*∏ i∈W,u i):=by
   induction W using Finset.induction_on with
   | empty=> simp only [noncommProd_empty,sub_self,Finset.card_empty,Nat.cast_zero,zero_mul]; refine ⟨le_rfl,fun i=>?_⟩; simp only [ContinuousLinearMap.zero_apply,load_zero,zero_mul]; exact le_rfl
   | insert i s hi ih=>
     let X:= s.noncommProd F' (h.mono (Finset.coe_subset.mpr (Finset.subset_insert ..))); let Y:= s.noncommProd G' (he.mono (Finset.coe_subset.mpr (Finset.subset_insert ..)))
     have hY:Pledge p Y (∏ i∈s,u i):= pledge_spin s _ _ _ (fun j hj=>(hh j (mem_insert_of_mem hj)).2.1) _
     obtain ⟨hp,-,ht⟩:= hh i (mem_insert_self ..)
     have h:Pledge p (F' i * (X-Y)+(F' i-G' i)*Y) _ := plus (hp.combines (ih _ _ fun j hj=>hh j (mem_insert_of_mem hj))) (ht.combines hY)
     rw [noncommProd_insert_of_notMem _ _ _ _ hi,noncommProd_insert_of_notMem _ _ _ _ hi]; rw [show F' i*X-G' i*Y=_ from (by rw [mul_sub,sub_mul]; abel : F' i*X-G' i*Y= F' i*(X-Y)+(F' i-G' i)*Y)] -- rewrite X let
     apply h.bumps; rw [card_insert_of_notMem hi,Nat.cast_add,prod_insert hi,Nat.cast_one]; exact le_of_eq (by ring)
lemma sassy (s:Finset (Fj (Tr f) E K)) (U V:Grid f)(b:ℕ)(Q:Rise f F E K)(D:Peak (P.equip F b) t x y ξ (fun i=> Real.exp 1*terra P F b x y i)) (h:beamAt (brimW (P.equip F b) Q s) U V w)(hv:0≤w)(hw:w<δ/2)(he:∀ i,terra P F b x y i≤1): Pledge (rateF c f F x y) (axle (P.equip F b) U s-axle (P.equip F b) V s) ((ops s).card*(w/(δ/2))*∏ i∈ops s,(Real.exp 1 * terra P F b x y i)):=by
    unfold Cove.axle; apply cycles; intro i hi; let K:=P.equip F b
    have hb : beamAt (roomK i) U V w:=mores h (fun j hj=> native_sub K Q s (mem_biUnion.mpr ⟨Sum.inl i,by simpa [ops] using hi,hj⟩))
    let z:=w/(δ/2); have hz:0 ≤ z:=div_nonneg hv (half_pos P.positive).le
    have hU M := licence P (settled M) (citizenship f P.positive M) D.bud D.cup b i (F:=F)
    exact ⟨D.spare i U,D.spare i V,(whirl (hU U) (hU V) (plumes P F b U V i hb D.bud D.cup hv hw) hz).bumps (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (he _)) (hU U).nn) hz)⟩
end YM.QCD.Spice
