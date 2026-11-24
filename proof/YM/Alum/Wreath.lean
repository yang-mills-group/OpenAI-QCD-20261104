import YM.Alum.Goblet
import YM.Intag.Folio
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Lattice Wilson MeasureTheory QCD QCD.Lat QCD.Tide QCD.Grass Set
open QCD.Cove Finset NormedSpace QCD.RP
open scoped Topology BigOperators Matrix.Norms.L2Operator Classical ComplexOrder
namespace Goblet.Ladder
variable {n c l d:Side}{F:ℕ}
open Chess Cells Romance Massive.Lyre.Array Plum
variable {T W:Tiling n}(E:Ladder T W)
variable (R:Regulator n F)(p:T.Cell) {I:Type}[Fintype I](L:List I)(v:I→ W.Cell)(X:I→ Stud n F) (hn:L.Nodup)(he:∀ i,i∈ L)
open YM.Intag
local notation "τ"=>topH
local notation "Z"=>∏ i:I, topH W R (X i) (v i)
include he hn E
set_option maxHeartbeats 600000
lemma ticks (hr:Injective v)(hv:∀ i,W.chamber (v i) ⊆ T.chamber p)(hx:∀ i,Fence (W.chamber (v i)) (X i)∧ Potion (X i))(h0:R.t=0)(hp:W.kind=.link)(hk:∀ j,(W.chamber j).Nonempty)(hβ:0 ≤ R.β)(hl:4 ≤ n.val)(hR:R.Z≠0) : topH T R (L.map X).prod p ≤ ∏ i:I, topH W R (X i) (v i):=by
    apply le_of_pow_le_pow_left₀ T.cells_positive.ne' (prod_nonneg fun _ _=> top_nn ..)
    rw [top_power]; let s:Finset T.Cell:=Finset.univ; let q(t:T.Cell) : TapeWalk n T:= tag T p t; let J:= T.Cell× I; let C (i:J):= finish W (v i.2) ((q i.1).map E.g); let Y(i:J):= road (pathT T (q i.1)) (X i.2); have hY(i:J): Potion (Y i):=potW _ (X i.2) (hx i.2).2
    have hX(i:J):Fence (W.chamber (C i)) (Y i):=by unfold Y; rw [← E.taps]; exact roadF (X i.2) _ (v i.2) _ (chamber W) (hx i.2).1
    have hrP(i:J):topH W R (Y i) (C i)=topH W R (X i.2) (v i.2):=(earn_eq W hp R (v i.2) (X i.2) (hx i.2).2 ((q i.1).map E.g) _ rfl _ (hY i) (Or.inl (by rw [E.taps]))).symm
    let l(t:T.Cell):= L.map (Prod.mk t); let U:= s.toList.flatMap l; have hM: Folio.Muster (show J→ Site T.period from Prod.fst) l:= ⟨fun i=> hn.map (Prod.mk_right_injective i),fun i x=>⟨by intro hh; obtain ⟨j,_,hj⟩:= List.mem_map.mp hh; exact congr_arg Prod.fst hj.symm,by intro h; exact List.mem_map.mpr ⟨x.2,he _,Prod.ext h.symm rfl⟩⟩⟩; have hL:= Folio.landed _ _ hM
    have hu: SignedEq (loom T (palmH T (L.map X).prod p)) (U.map Y).prod:=by
         unfold U loom; change SignedEq (s.toList.map _).prod _; generalize s.toList=t; induction t with
         | nil=>exact SignedEq.refl _
         | cons i t ih=> rw [List.flatMap_cons,List.map_append,List.prod_append]; change SignedEq (_*_) ((List.map Y (L.map (Prod.mk i))).prod*_);rw [List.map_map]; exact signsM (royalties L X T (q i) (fun i=>(hx i).2)) ih
    rw [signsV R hu]; have h:=Lyre.wardsP W R hp Y C (E.disjointJ _ p (tag_spec T p) v hv hk hr) U hL.1 (fun i=> List.mem_flatMap.mpr ⟨i.1,(by simp[s]),(hM.address i.1 i).2 rfl⟩) (fun i=> ⟨hX i,hY i⟩) h0 hβ hl hR
    apply h.trans_eq ; simp_rw [hrP]; rw [show (∏ i:J,topH W R (X i.2) (v i.2))= (∏ _ : T.Cell, ∏ i:I,topH W R (X i) (v i)) from Fintype.prod_prod_type _,prod_const, card_univ]
-- geometry from ratios. Δ actual.M.Ph.
omit he hn E
variable (r:Ratio c l)(b:Ratio l n)(g: Ratio c n)(hh:Odd r.count.val)(hb:Odd b.count.val)(ho:Even c.val)(hr:Even l.val)(x:Site n)
local notation "T₀"=>mural g ho x
local notation "Wᵢ"=> mural b hr x
open YM.Next.Rank.Station
lemma cut_eq (C D:Cells.Cut n)(hk:C.kind=D.kind)(hp:C.pos=D.pos)(he:C.baseLine=D.baseLine): C=D:=by
     have h:C.half=D.half:=Subtype.ext ((Nat.mul_right_inj (by norm_num:(2:ℕ)≠0)).mp (C.even.symm.trans D.even)); cases C; cases D; congr
include hh hb hr ho
lemma adorn : Nonempty (Ladder (mural g ho x) (mural b hr x)):=by
     let V (a:Site c × Axis) : Site l × Axis:= (r.embed a.1 - (r.count.val/2) • step a.2,a.2); refine ⟨⟨V,fun a=>?_⟩⟩
     have hz:Odd g.count.val:= by rw [size_comp r b]; exact hb.mul hh
     refine cut_eq _ _ rfl rfl ?_
     change (Wᵢ).starts (V a).1 a.2=(T₀).starts a.1 a.2; rw [eq_sub_of_add_eq (behind _ _ _ _ hb a.2),eq_sub_of_add_eq (behind _ _ _ _ hz a.2)];
     let H:=b.count.val; let u:=r.count.val
     rw [embed_comp r b,vaneP r b g hh hb]; unfold V; apply sub_eq_zero.mp
     change ((x+b.root (r.embed a.1 - (r.count.val/2) • step a.2)) a.2-_) - _=_; rw [map_sub,map_nsmul,(show b.root (step a.2)=b.count.val • step a.2 from (Wᵢ).root_step a.2)]; simp only [Pi.add_apply,Pi.sub_apply, Nat.cast_add,Nat.cast_mul]; rw [b.root_embed]; simp; ring
omit hh hb hr ho
include hb hr
lemma fullC (p:Site l): ((mural b hr x).chamber p).Nonempty:= ⟨_, ((mural b hr x).reflected_chamber _ p|>.1 (lies b hr hb x))⟩
omit hb hr
include hh hb hr ho
-- subset whenever some point fits with sufficient large-cell margin. yes.A.Key.Geometry.Pr:
lemma here (i:Site l)(p: Site c)(y:Site n)(hx:y∈(mural b hr x).chamber i)(hy:y ∈ (mural g ho x).margin p b.count.val): (mural b hr x).chamber i ⊆ (mural g ho x).chamber p:=by
       have hz:Odd g.count.val:= by rw[size_comp r b]; exact hb.mul hh
       intro t ht; apply Set.mem_of_mem_of_subset _ ((zero_margin (T₀) p rfl).le)
       rw [key_margin _ _ _ _ _ hz] at hy ⊢; apply le_trans _ hy; have hx:separation t y ≤b.count.val:= (Wᵢ).extent ht hx; have he:= separation_triangle t y (x+g.embed p); omega
-- authenticity all sectors integrated by smaller.C operator.K.V requirement paid from RG service separately.
end Goblet.Ladder
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.Goblet.Ladder.ticks
#print axioms YM.Massive.Lyre.Goblet.Ladder.adorn
#print axioms YM.Massive.Lyre.Goblet.Ladder.here
