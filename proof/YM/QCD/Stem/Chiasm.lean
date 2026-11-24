import YM.QCD.Stem.Sink
/-! # Supplemental oriented χ pane. Values unmasked for restoration. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stem
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure Precision ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove AnalyticBridge VerifiedReset
variable {C:Side}{D D' w j:ℕ}{d r t t' p p' η b z A:ℝ}{B:BudgetPoint}
open Entr Villa Port Fork Grove YM.Next.Scheduling Footprint Moss Extra.Iteration Song Meadow
section act
variable (T:ℕ→ Atom su j) (U:Grid c)
def codaX (T:ℕ→ Atom su j) (N:ℕ) (b:ℝ)(c:Side): Gem c N (Stave (n:=c)):=⟨pitch T, fun i=> Reggae.ocean _ _ ∘ tuneAtom T (-b) i⟩
noncomputable def joinP (c:Side)(T:ℕ→ Atom su j)(w n:ℕ): Finset (Stave (n:=c)):=univ ×ˢ ((Finset.range n).filter fun i=> (T i).length≤w)
local notation "K"=> codaX T N b c
local notation "Q"=> joinP c T w n
lemma plumeT (i:Seat c) (z:ℕ): (T z).unmasked ((splay c i).view U) 0=(T z).unmasked (pull i.1 0 U) i.2 := by
    have he : (splay c i).view U = Lattice.translate i.2 (pull i.1 0 U) := by rw [← Lattice.pull_one,pull_pull,mul_one,affine,add_zero]; rfl
    rw [he]; simp [Atom.unmasked,Slot.atSite,expand_translate]
lemma shuns (h:Charged T r A)(hk:0<r): HasSum (fun i=> (K).view i U) (baker c N (b*Extra.Iteration.action T U)):=by
   let P x:=∑' i,(T i).unmasked (Seat.view x U) 0; let d:= VerifiedReset.factor*(-b)
   have hv (x: Seat c):HasSum (fun i=> d*(T i).unmasked (x.view U) 0) (d*P x) := by refine (Summable.hasSum (Summable.of_norm_bounded ((h.absolute hk.le).mul_right (2^j)) (fun i=>?_) : Summable _)).mul_left d; exact (T i).unmasked_bound ..
   have he : HasSum (fun i:Stave (n:=c)=> d * (T i.2).unmasked (i.1.view U) 0) (∑ x : Seat c,d * P x):= Raw.finite_start _ _ hv
   have hx: (∑ x:Seat c,d * P x)=-(b*Extra.Iteration.action T U):=by
       rw [← mul_sum,← Equiv.sum_comp (splay c), Fintype.sum_prod_type]; simp_rw [P,plumeT T U]
       unfold d Extra.Iteration.action; change _= -(b*(VerifiedReset.factor*_)); unfold uncut; ring
   rw [hx] at he; have hz:= (Reggae.ocean c N).hasSum he; rw [Reggae.ocean,ContinuousLinearMap.neg_apply,map_neg,neg_neg] at hz; exact hz
open Quotes
lemma leaning (h:Charged T r A)(hk:0<r)(hA:SymmetricAtoms T)(he:0≤t')(hp: preExponent B/B.B≤r/4): Dyed (K) ∧ Scaled (r/4) (fun i:Stave (n:=c)=> (T i.2).length) B (K) (preExponent B) (Quotes.anchoredFee (Song.headline B) (Song.octave j)*Song.tenor su j B r A (-b)) t' :=by
   have hf (i:Stave (n:=c)):= Song.pitch_charge B _ i (-b) hA -- hA def inspect
   refine ⟨⟨fun i U k=>?_,fun i U W hx=> Reggae.thorough ..,fun i U=> Reggae.thorough ..⟩,fun i=> Song.sine B T (-b) i.2,fun i=>wealthy N _ _ _ (hf i).1 (hf i).2 he,Meadow.torque B _ h hk hp (-b)⟩
   refine congr_arg Subtype.val (show sways (Lat.rotates N k) (Reggae.ocean _ _ _)=(K).view i U from ?_); rw [Reggae.thorough]; exact congr_arg _ ((hf i).1.symmetry k U)
lemma reached (i:Stave (n:=c))(h:(T i.2).length ≤ w): ∀ᶠ k in atTop,i∈ joinP c T w k:= (eventually_gt_atTop i.2).mono fun k hk=> mem_product.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_range.mpr hk,h⟩⟩
lemma scarves (i:Stave (n:=c))(h:i∈ joinP c T w n): ((K).addr i).support ⊆ neighbors w i.1.2:=by
   intro y hy; obtain ⟨x,hQ,rfl⟩:= mem_image.mp hy; let s:=i.1; have hz: separation s.2 (affine s.1 s.2 x)= separation (0:Site c) x:= by unfold Lattice.affine; nth_rw 1 [← zero_add s.2]; rw [separation_translate]; nth_rw 1 [← s.1.act_zero]; rw [separation_signed]
   rw [neighbors_mem]; change separation s.2 (affine s.1 s.2 x) ≤ _; rw [hz]; have he:= mem_filter.mp (mem_product.mp h).2; rw [Paths.atom_foot] at hQ; exact (Paths.where_slot 0 (T i.2).leg _ hQ).trans he.2
lemma galX (x:Site c): bust K Q x= (univ×ˢ {x}) ×ˢ ((Finset.range n).filter fun i=>(T i).length≤w):=by
    ext ⟨⟨v,y⟩,i⟩; have hh: ((K).addr ((v,y),i)).site=y:=rfl; simp [bust,joinP,hh,and_comm,and_left_comm,eq_comm]
lemma freezeA (H:C.val=c.val*D)(d:Site C→ℂ)(i:Site C)(V: Grid c):
    let M:=normal (Deck.divides H) H
    axes M d N ((tuckS (codaX T N b C) (joinP C T w n) w).view i (M.links V)) = (tuckS K Q w).view (M.cut i) V:=by
     intro M; let A:=codaX T N b C; have he x: axes M d N (Reggae.ocean C N x)=Reggae.ocean c N x:=by
       unfold Reggae.ocean; simp only [ContinuousLinearMap.neg_apply,gets]; rw [map_neg,show axes M d N (x • 1)=x • axes M d N 1 from map_smul (axes M d N).toLinearMap ..,map_one]
     change axes M d N ((∑ j∈bust A (joinP C T w n) i,A.view j) (M.links V))=(∑ j∈bust K Q (M.cut i), (K).view j) V
     unfold A; simp only [Finset.sum_apply,galX,Finset.sum_product,sum_singleton]; rw [map_sum]; apply sum_congr rfl; intro s _; rw [map_sum]; apply sum_congr rfl; intro k hk
     let θ:Seat C:=(s,i); change axes M d N (Reggae.ocean _ _ (VerifiedReset.factor*(-b)*(T k).unmasked (θ.view _) 0))=Reggae.ocean _ _ (VerifiedReset.factor*(-b)*(T k).unmasked ((pinch H θ).view V) 0)
     rw [he]; change Reggae.ocean _ _ (_* (T k).unmasked (θ.view ((normal _ H).links V)) 0)=_; rw [Meadow.estuary]; refine congr_arg _ (congr_arg (_ * ·) (congr_arg (Atom.poly (T k)) (funext (fun j=>?_))))
     unfold Slot.atSite; rw [(normal (Deck.divides H) H).expansion,show (normal _ H).cut 0=0 from map_zero (Macrame.splitter _)]
end act
end YM.QCD.Stem
