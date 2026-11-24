import YM.QCD.Moss.Muse
import YM.QCD.Moss.Will
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
lemma placement (p: Clusters Y.Bright) (B:Bouquet K Y) (k: Option (Fin p.fst))(hp:crestP Y p≤2)(hz:mantel Y p < till τ)(hv : ∀ i∈(p.2 k).val,i∈ Set.range B.queen):∃ i: BloomV c f,∃ Z:Fiat K i,p.2 k=B.kernelV i Z:=by
   let u:=(p.2 k).val; let x:=u.preimage B.queen B.queen.injective.injOn; have hh i:i∈x↔ B.queen i ∈u:=mem_preimage; have hf : B.springV x=u:= by
      ext i; constructor; intro h; obtain ⟨j,hi,rfl⟩:=mem_map.mp h; exact (hh _).1 hi
      intro h; obtain ⟨j,rfl⟩:=hv _ h; exact mem_map_of_mem B.queen ((hh _).2 h)
   have hp': (p.2 k).val.card≤2:=(lengthR Y p k).2.1.trans ((lengthR Y p k).2.2.trans hp)
   have hm: ∀ i:Head S, 0 ≤ Reserves.weight K.supportP (radiusB τ) (Mixed.lengths S K.faresP (ConnectedActivityE6.lengths T R)) i:= by
     rintro (i|i)
     · unfold Reserves.weight; refine add_nonneg (Nat.cast_nonneg _) ?_; unfold Mixed.lengths ; simp only [Sum.elim_inl]; unfold Cash.faresP; change 0 ≤ (0:ℝ) * ↑i.shares; simp
     exact add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
   refine ⟨x,⟨(B.fertile x).2 (hf.symm ▸ (p.2 k).2.1.2.1),le_trans (b:=(p.2 k).val.card) ?_ hp',?_⟩,Subtype.ext hf.symm⟩
   · rw [show (p.2 k).val=u from rfl, ← hf,Bouquet.springV,card_map]
   intro i he; rcases i with i|i
   swap; · exact Nat.zero_le _
   have hi:Mint.disc S i∈u.toLeft:= mem_toLeft.mpr ((hh _).mp he)
   have h : (gradeV R.path (.inl i:PeaceV c f):ℝ) ≤ K.shapeW u.toLeft:=le_trans (b:=weight K.supportP (radiusB τ) (Mixed.lengths S K.faresP (ConnectedActivityE6.lengths T R)) (Mint.disc S i)) (by change (Mint.verse R.path i:ℝ) ≤_+ (exCharge T R (note i):ℝ); rw [Mint.balance T R i]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)) (single_le_sum (fun i _=>hm i) hi)
   have ht:= h.trans (worthG Y u).1; have hf : worthX Y u≤ mantel Y p:= single_le_sum (f:=fun i=>worthX Y (p.2 i).val) (fun i _=>(worthG Y _).2) (mem_univ k); exact (Nat.cast_le (α:=ℝ)).1 (ht.trans (hf.trans (hz.le.trans (Nat.cast_le.mpr (Nat.div_le_self ..)))))
lemma dawnTK (B : Bouquet K Y)(X G:I→Prop)(hz:∀ i, ¬X i → ¬ G i →i ∈Set.range B.route)(p:Clusters Y.Bright)(χ:Chi)(U: Grid c) (he:∀ i x, R.activities.E i x=0)
    (hm: ¬ Dated Y X G τ p)(hv:Y.furnace χ U p≠0)(hp: ¬∃ q:Y.Bright,∃ i:I,G i ∧ p=individual q ∧ Aliased Y q i):∃ i:Wreath c f,∃ Y':Mossy K i,p=B.heightV i Y' :=by
   obtain ⟨hx,hg⟩:= not_or.mp hm; obtain ⟨hf,hq⟩:= not_or.mp hg; obtain ⟨hr,hh⟩:=not_or.mp hq; obtain ⟨hW,h⟩:=not_or.mp hh
   have hz' : ¬stand Y G p:=by
       intro hf; have hz':¬ 2≤crestP Y p:=fun he=> h ⟨he,hf⟩; obtain ⟨j,i,h,hp',hx⟩:= individualH Y p (by omega) G hf; exact hp ⟨j,i,hp',h,hx⟩
   have hh i := hatching Y he B p (by omega) (lt_of_not_ge hf) (fun i j he=> hz j (fun hv=> hW ⟨i,j,he,hv⟩) (fun hx=>hz' ⟨i,j,he,hx⟩)) χ U hv i
   choose f he' hy using fun i=> placement Y p B i (by omega) (lt_of_not_ge hr) (hh i)
   let u:Wreath c _:=⟨p.1,f⟩
   have hN : Mossy K u := by
      refine ⟨show p.1≤1 from (by have h:=scopeH Y p; omega),he',fun h=> hv ?_⟩
      unfold furnace termP; suffices hf:coefficient (blocked Y.lightF) p.2=0 by rw [hf,zero_smul,smul_zero]
      apply Eq.trans _ h; apply Meadow.movement; intro i j; rw [hy,hy]; apply or_congr ((B.aq ..)); unfold Ac.meets; simp_rw [Bouquet.nestV (Y:=B)]; rfl
   exact ⟨u,hN,show p= Sigma.mk p.1 _ from Eq.symm ((congr_arg (Sigma.mk p.1) (show _=p.2 from funext fun i=>(hy i).symm)))⟩
open Leaf Tee Orbit Garden Jets Flume Run YM.Next.Free
variable {δ β b:ℝ}{R:BudgetPoint} {K:Cash W τ μ L X o κ T (trimP T R δ β b)} (J': Fleet K I N) {j k:ℕ}{O:Flight j k}{h:f.val=c.val*O.L.val}{A A' p z Y:ℝ}{π : St f}{U:ℕ→Atom su 2} {B:Plan k}
variable (F': Swathe O h π U B A A' p z Y D)(Γ:Land c (Site c) (Site c))
set_option quotPrecheck false
local notation "VQ"=> tiro J' F' Γ
local notation "X'"=> artV J' F' Γ
-- individual vs all Mighty. Applies as soon as ψ nonzero unmasked; stronger than mask-only. Can't take into account orientations still separate.
lemma peat (p:Clusters (X').Bright)(χ:Chi)(A:Clusters (X').Bright→RegularAddress c) (he:¬ Dated (X') Fury nectarP τ p)(hk:(crude (X') χ A).view p≠0)(hx: ¬∃ q:(X').Bright,∃ i:I,p=individual q∧ Aliased (X') q (.inl i)):
       ∃ i:Wreath c f,∃ P:Mossy K i,p= (VQ).heightV i P:=by
   have hm:∃ U,(X').furnace χ U p ≠0:= by
      by_contra hh; push Not at hh
      apply hk; funext U; change pepper (fun V=>(X').furnace χ V p) U=0; unfold Patron.pepper; simp_rw [hh,map_zero]; exact integral_zero ..
   obtain ⟨V,hV⟩:=hm
   apply dawnTK _ _ Fury nectarP _ p χ V (fun i x=>rfl) he hV
   · rintro ⟨q,i,hi,hV,hp⟩; rcases i with i|i|i; exact hx ⟨q,i,hV,hp⟩; exact False.elim hi; exact False.elim hi
   rintro (i|(⟨i,x⟩|⟨i,x⟩)|⟨i,x⟩) hi hp
   · exact (hp trivial).elim
   · have ht:x=none:=not_not.mp hi; subst x; exact ⟨.inl (.inl i),rfl⟩
   · have ht:x=none:=not_not.mp hi; subst x; exact ⟨.inl (.inr i),rfl⟩
   have ht:x=none:=not_not.mp hi; subst x; exact ⟨.inr i,rfl⟩
end YM.QCD.Moss
#print axioms YM.QCD.Moss.peat
