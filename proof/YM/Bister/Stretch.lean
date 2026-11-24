import YM.Cardinal.Beau
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate.Stretch
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{I X E:Type}{N:ℕ}{σ v k t:ℝ}
variable (Y:Patron.Rail c N E) (F:E→Hat c)
-- Y larger K structure but no exact flag assertion on expanded support yet
abbrev Orig:= Patron.Rail.mk F Y.warp
local notation "Ω"=> Ruby.home Y
local notation "M"=> Ruby.home (Orig Y F)
local notation "g"=> oriD Y
local notation "g'"=> oriD (Orig Y F)
abbrev pass (s:Finset E): Prop := separated (blocked (Ruby.home (Orig Y F))) s
variable (h:∀ i:E,(F i).place⊆ (Y.addr i).place)(hw:∀ i:E,(F i).inv=(Y.addr i).inv)
def wallet (s:Finset E):Prop:= pass Y F s ∧ Ac.Spark (Ruby.home Y) s
abbrev Quants := {s:Finset E // wallet Y F s}
local notation "Q"=> Quants Y F
def booksY (s:Finset E) : Support c:= s.biUnion (oriD Y)
def coverY (s:Finset E) : Support c:= s.biUnion (Ruby.home Y)
lemma lucre (s:Finset E): booksY Y s ⊆ coverY Y s:=by
    intro i hi; obtain ⟨p,hp,hk⟩:=mem_biUnion.mp hi; exact mem_biUnion.mpr ⟨p,hp,(Y.addr p).part hk⟩
lemma funds (i:Q): (booksY Y i.val).Nonempty:=by obtain ⟨p,hp⟩:=i.2.2.1; exact (Y.addr p).alive.mono (subset_biUnion_of_mem _ hp)
def patientY (s:Finset E)(t:ℝ)(U:Grid c) : EvenA c N:= if RG.flags t U∩coverY Y s=booksY Y s then ∏ i∈s,Y.warp i U else 0
noncomputable def Basin (t:ℝ): Patron.Rail c N Q:= ⟨fun i=> ⟨coverY Y i.val,booksY Y i.val,funds Y F i, lucre Y i.val⟩,fun i=> patientY Y i.val t⟩
def Wholes (s:Finset (Finset E)) := (∀ i∈ s, wallet Y F i) ∧ (s:Set (Finset E)).PairwiseDisjoint (coverY Y)
local notation "P"=> Ac.Parts (Ruby.home Y)
lemma prep_a (s:Finset E)(hp:pass Y F s): Wholes Y F (P s):=by
    refine ⟨fun i hi=> ⟨?_,(Ac.lives Ω s hi).2⟩, Ac.separate .. ⟩; have h₀:= (Ac.lives Ω s hi).1; exact fun j hj k hk=>hp j (h₀ hj) k (h₀ hk)
include h
lemma lift_p (s:Finset (Finset E))(hp:Wholes Y F s): pass Y F (s.biUnion id):=by
    refine (GasP.close E _ _).2 (?_: (↑(_):Set E).PairwiseDisjoint M); intro i hi j hj hn; obtain ⟨p,hp',hi⟩:=mem_biUnion.mp hi; obtain ⟨q,hq,hj⟩:=mem_biUnion.mp hj
    by_cases h:p=q; · subst q; exact ((GasP.close E _ _).1 (hp.1 p hp').1) hi hj hn
    -- shadow var h
    exact Disjoint.mono ((‹∀ i,M i⊆ Ω i› i).trans (subset_biUnion_of_mem _ hi)) ((‹∀ i,M i⊆ Ω i› j).trans (subset_biUnion_of_mem _ hj)) (hp.2 hp' hq h)
omit h
local notation "K"=> Basin Y F
noncomputable def mkL (t:ℝ)(V:Grid c) (s:Finset (Finset E)): EvenA c N:=if Wholes Y F s∧ flags t V=s.biUnion (booksY Y) then ∏ i∈s,patientY Y i t V else 0
lemma cntr (t:ℝ)(U:Grid c)(s:Finset Q) : tK (K t) t U s=mkL Y F t U (s.image Subtype.val):=by
    unfold tK mkL; apply if_congr (and_congr ?_ ?_) ?_ rfl
    · rw [GasP.close]; constructor
      · intro h; refine ⟨fun i hi=>?_,fun i hi j hj hn=>?_⟩
        · obtain ⟨p,hp,rfl⟩:=mem_image.mp hi; exact p.2
        obtain ⟨p,hp,rfl⟩:=mem_image.mp hi; obtain ⟨q,hq,rfl⟩:=mem_image.mp hj; exact h hp hq (fun h=> hn (h ▸ rfl))
      intro h i hi j hj he; exact h.2 (mem_image_of_mem Subtype.val hi) (mem_image_of_mem Subtype.val hj) (fun hh=>he (Subtype.ext hh))
    · rw [image_biUnion]; rfl
    rw [prod_image Subtype.val_injective.injOn]; rfl
include h hw
lemma voltage (t:ℝ)(U: Grid c)(s:Finset (Finset E))(hp: Wholes Y F s): mkL Y F t U s=tK (Orig Y F) t U (s.biUnion id):=by
   let S:=s.biUnion id; have hh :P S=s:= Ac.separates _ _ (fun i hi=> (hp.1 i hi).2) hp.2; have ht:=Ac.different Ω S; rw [hh] at ht; have hz : s.biUnion (booksY Y)= S.biUnion g':=by ext x; rw [show g'=g from funext hw]; simp only [booksY,S,mem_biUnion,id_eq]; grind
   let w:=flags t U; by_cases hV:w=s.biUnion (booksY Y); swap; · rw [mkL,tK,if_neg (fun h=>hV h.2), if_neg (fun hn=>hV (hn.2.trans hz.symm))]
   rw [mkL,tK, if_pos ⟨hp,hV⟩,if_pos ⟨lift_p Y F h s hp,hV.trans hz⟩]; rw [prod_biUnion ht]; apply prod_congr rfl; intro i hi; unfold patientY; rw [if_pos]; try rfl
   change w ∩ coverY Y i = _ ; ext x; rw [hV]; constructor
   · intro h0; obtain ⟨hj,hX⟩:= mem_inter.mp h0; obtain ⟨j,hj,hj'⟩:=mem_biUnion.mp hj; by_cases hz:j=i; exact hz ▸ hj'; exact False.elim (Finset.disjoint_left.mp (hp.2 hj hi hz) (lucre Y j hj') hX)
   intro h0; exact mem_inter.mpr ⟨mem_biUnion.mpr ⟨i,hi,h0⟩,lucre Y i h0⟩
lemma term (t:ℝ)(U:Grid c)(s:Finset E): mkL Y F t U (P s)=tK (Orig Y F) t U s:=by
    by_cases he:pass Y F s; · exact (voltage Y F h hw t U _ (prep_a Y F s he)).trans (congr_arg _ (Ac.reconstruct Ω s))
    have hx : ¬ Wholes Y F (P s):=fun hp=>he ((Ac.reconstruct Ω s) ▸ lift_p Y F h _ hp)
    rw [tK,mkL,if_neg (fun h=>hx h.1),if_neg (fun h=>he h.1)]
lemma petrol (t:ℝ)(U:Grid c)(X:EvenA c N)(hp:HasSum (tK (Orig Y F) t U) X): HasSum (tK (K t) t U) X:=by
    let V (s:Finset E):=P s; let w := mkL Y F t U
    have he : Injective V:=fun i j h=> (Ac.reconstruct Ω i).symm.trans ((congr_arg (fun p:Finset (Finset E)=>p.biUnion id) h).trans (Ac.reconstruct Ω j))
    have hu: HasSum w X:=(he.hasSum_iff (fun i hi=> show w _=0 from if_neg (fun hh=> hi ⟨i.biUnion id,Ac.separates _ _ (fun j hj=> (hh.1.1 j hj).2) hh.1.2⟩))).1 (hp.congr_fun fun i=> term Y F h hw t U i)
    let f i:=Finset.image (fun j:Q=>j.val) i; refine (((show Injective f from image_injective Subtype.val_injective).hasSum_iff (f:=w) ?_).2 hu).congr_fun fun i=>?_
    · intro i hi; unfold w mkL; rw [if_neg]; intro hx; apply hi; let X':=i.preimage Subtype.val (Subtype.val_injective (p:=fun p =>wallet Y F p)).injOn
      refine ⟨X',?_⟩; ext j; constructor
      · intro h; obtain ⟨p,hp,rfl⟩:=mem_image.mp h; exact mem_preimage.mp hp
      intro hj; exact mem_image.mpr ⟨⟨j,hx.1.1 j hj⟩,mem_preimage.mpr hj,rfl⟩
    exact cntr ..
end YM.MassiveQCD.Plate.Stretch
#print axioms YM.MassiveQCD.Plate.Stretch.petrol
