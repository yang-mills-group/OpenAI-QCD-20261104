import YM.QCD.Moss.Vats
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
variable {c f C F L:Side} {P : Teller su}{O:Patch}{D :ℕ}{M:KernelChoices}
variable {h:f.val=c.val*O.L.val}{H:F.val=C.val*O.L.val}{hC:C.val=c.val*D}{he:2≤c.val}
local notation "Lx"=> Lace.project (h:=h) (H:=H) hC he
variable {W κ κ' μ β τ:ℝ} {R:Rep su f}{R':Rep su F}{X:ConnectedActivityE6.Target su P}{o:ConnectedActivityE6.Target.Order su W}
local notation "S"=>stepped M h
local notation "Y"=>stepped M H
variable {T:Tube su (stepped M h)} {T':Tube su (stepped M H)} {N:ℕ}{I J:Type}
variable {K:Cash W τ μ L X o κ T R}{K':Cash W τ μ L X o κ' T' R'}
variable (u:Fleet K I N) (v:Fleet K' J N)(z:EvenA C N →ₐ[ℝ] EvenA c N)
local notation "B"=>radiusB τ
variable {w:Pipe.Clump (stepped M H) J}{r:Pipe.Clump (stepped M h) I}{x:Site C}{n:ℕ}
variable (V:Page hC he u v z w r x n) {E:Tree.Forest (stepped M h).ratio}{G:Tree.Forest (stepped M H).ratio}
variable (hu:u.Famous)(hv:v.Famous) (hN: 2*(2*n+3)<c.val)
variable {A:Coat T E}{A':Coat T' G}
open Bouquet Gas GasP Ursell
section fibres
variable {A B₀ C D:Type}{f:A→ B₀}
lemma loansB (g: C→ D)(P:Finset (A ⊕ C)): ((P.image (Sum.map f g)).toLeft=P.toLeft.image f) ∧ ((P.image (Sum.map f g)).toRight=P.toRight.image g):=by
   constructor <;> ext k
   · simp only [mem_toLeft,mem_image]; constructor
     · rintro ⟨x,h,hx⟩; cases x <;> simp at hx; exact ⟨_,h,hx⟩
     rintro ⟨p,h,rfl⟩; exact ⟨_,h,rfl⟩
   simp only [mem_toRight,mem_image]; constructor
   · rintro ⟨x,h,hx⟩; cases x <;> simp at hx; exact ⟨_,h,hx⟩
   rintro ⟨p,h,rfl⟩; exact ⟨_,h,rfl⟩
lemma permit [DecidableEq B₀] (g:A→ B₀)(U:Finset A)(V:Finset B₀)(hv:V=U.image g)(hp:Set.InjOn g U) : ∃ p:(↥U ≃ ↥V),∀ i,(p i).val=g i.val:=by
    subst V; let f (i: ↥U): ↥(U.image g):= ⟨_,mem_image_of_mem g i.2⟩; refine ⟨Equiv.ofBijective f ⟨fun i j h=>Subtype.ext (hp i.property j.property (congr_arg Subtype.val h)),?_⟩,fun i=>rfl⟩
    intro i; obtain ⟨a,b,c⟩:=mem_image.mp i.2; exact ⟨⟨_,b⟩,Subtype.ext c⟩
end fibres
variable (Y₁:Bouquet K u)(Y₂:Bouquet K' v)
structure Alive (hC:C.val=c.val*D)(he:2≤c.val)(u:Fleet K I N)(v:Fleet K' J N)(z:EvenA C N →ₐ[ℝ] EvenA c N)(Y₁:Bouquet K u)(Y₂:Bouquet K' v):Prop where
 wage : T'=re T
 goal : R'.p= R.p
 wings : R'.beta=R.beta
 birth : R'.path=R.path
 pleat i U V : z (v.works (Y₂.route i) ((Lace.project (h:=h) (H:=H) hC he).high.links U) ((Lace.project (h:=h) (H:=H) hC he).low.links V))=u.works (Y₁.route (calm (Lace.project (h:=h) (H:=H) hC he) i)) U V
variable (hp:Alive hC he u v z Y₁ Y₂)
include hp
lemma pageP (p: BloomV C F)(Z:Site C)(n:ℕ)(hv:Fiat K' p)(hr: Set.InjOn (staid (Lx)) p) (heq:floorV K' p ⊆neighbors n Z): Nonempty (Page hC he u v z (Y₂.springV p) (Y₁.springV (spritz (Lx) p)) Z n):=by
    let r:=spritz (Lx) p; let L:=Lx
    have hz:r.toLeft=wrappers L p.toLeft ∧ r.toRight=p.toRight.image (calm L):= by -- two Decidable proof_irrel but instances
       convert! loansB (f:=verse_down (Lx)) (calm L) p using 3
       all_goals first | (solve|rfl) | (solve|unfold r spritz L staid; congr; exact Subsingleton.elim _ _) | (solve|funext; unfold L wrappers; congr; exact Subsingleton.elim _ _)
    let A:= Y₂.route; let B₀:=Y₁.route; let E:=p.toRight; let U: Finset J:=(Y₂.springV p).toRight; let V:(Finset I):=(Y₁.springV r).toRight
    have hU:U=E.image A:= (Y₂.petalsC _).2.trans (map_eq_image ..)
    have hV: V=r.toRight.image B₀:= (Y₁.petalsC _).2.trans (map_eq_image ..)
    have hR : Set.InjOn (calm L) E:=fun i hi j hj he=> Sum.inr_injective (hr (mem_toRight.mp (show i∈_ from hi)) (mem_toRight.mp (show j∈_ from hj)) (congr_arg Sum.inr (show calm L i=calm L j from he))) -- types
    obtain ⟨a,ha⟩:= permit (calm L) E r.toRight hz.2 hR; obtain ⟨v',hv'⟩:= permit A E U hU A.injective.injOn; obtain ⟨y',hy'⟩:=permit B₀ r.toRight V hV B₀.injective.injOn
    let t:(↥U ≃ ↥V):=v'.symm.trans (a.trans y'); have hx i:(t (v' i)).val=Y₁.route (calm L i.val):=by simp [t,hy',ha,B₀]
    refine ⟨hp.birth,hp.wings,hp.goal,t, ?_, ?_, p.toLeft,(Y₂.petalsC _).1, (Y₁.petalsC _).1.trans (congr_arg _ hz.1),fun i hi=> hv.earn (.inl i) (mem_toLeft.mp hi),?_,(Y₂.nestV p) ▸ heq⟩
    · change ∀ i:↥U, u.window ((t i).val) = (v.window i.val).image _; intro i; obtain ⟨i,rfl⟩:=v'.surjective i; rw [hx,hv',show v.window (A i.val)=_ from Y₂.frame i.val, Y₁.frame]; exact bounce hC he ..
    · change ∀ (i:↥U)(U':Grid f)(V':Grid c), z (v.works i.val (L.high.links U') (L.low.links V'))=u.works (t i).val U' V'; intro i U' V'; obtain ⟨i,rfl⟩:= v'.surjective i; rw [hx,hv']; exact hp.pleat ..
    exact fun i hi j hj he=> Sum.inl_injective (hr (mem_toLeft.mp (show i∈_ from hi)) (mem_toLeft.mp (show j∈_ from hj)) (congr_arg Sum.inl he))
include hu hv
local notation "t'"=> tideP X.halo (radiusB τ)
lemma offersV (p: Wreath C F)(Z:Site C)(D:Mossy K' p)(D':Mossy K (lesson (Lx) p))(V:Grid c)(hV:RG.flags (Pressure.temp τ) V=∅)(hx:Z∈ summitV K' p)(hn: 2*(2*(t')+3)<c.val)(χ:Chi):
    z (v.honest χ ((Lx).low.links V) (Y₂.heightV p D))=u.honest χ V (Y₁.heightV (lesson (Lx) p) D'):=by
    have ha:=palace K' D Z hx; have ht:=receipts hC he (I:=K) (I':=K') Z hp.birth p (lt_of_le_of_lt (show 2*t' ≤ _ from (by omega)) hn) ha D.each
    rw [v.phoenix, u.phoenix]; rotate_left
    · exact hu
    · exact hv
    unfold termP; rw [pay_for z,pay_for z,map_prod,Y₁.strings,Y₂.strings,← ht]
    apply congr_arg; apply congr_arg; refine prod_congr rfl fun i _=> ?_
    have hm:= rings (h:=h) hC he Z p D hx (by omega) i; obtain ⟨Y₀⟩:= pageP u v z Y₁ Y₂ hp (p.2 i) Z t' (D.each i) hm ((eachV (Jx:=K') (z:=p) i).trans ha)
    exact Moss.mermaid u v z Y₀ hu hv hn hp.wage χ V hV (Y₁.genuine _ (D'.each i)).1 (Y₂.genuine _ (D.each i)).1
end YM.QCD.Moss
